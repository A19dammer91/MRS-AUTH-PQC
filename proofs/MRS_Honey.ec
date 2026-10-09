(* ================================================================= *)
(*  MRS_Honey.ec                                                      *)
(*  Honey encryption layer of MRS-AUTH                                *)
(*  IND-CPA security via game-hopping over RO and AEAD                *)
(*                                                                    *)
(*  Under the Positive Anchor Convention (A_0 = dr(N) >= 1,           *)
(*  Frobenius boundary 162).                                          *)
(*                                                                    *)
(*  The chain-to-bytes encoding (`chain_to_bytes`, `chain_byte_len`)  *)
(*  and the abstract `bytes` type come from MRS_Encoding.ec, which    *)
(*  is the single source of truth for them.                           *)
(* ================================================================= *)

require import AllCore Int Real Distr List FSet SmtMap.
require import Bytes PROM.
require import StdOrder StdBigop.
import IntOrder RealOrder.

require import MRS_Core MRS_Chain MRS_Encoding.

(* ----------------------------------------------------------------- *)
(* Local type aliases                                                 *)
(* ----------------------------------------------------------------- *)
type key    = bytes.
type nonce  = bytes.
type plain  = bytes.
type cipher = bytes.
type tag    = bytes.

op key_len   : int = 32.
op nonce_len : int = 12.
op tag_len   : int = 16.

(* ----------------------------------------------------------------- *)
(* Random Oracle interface for the key derivation function           *)
(* ----------------------------------------------------------------- *)
module type KDF_Oracle = {
  proc init() : unit
  proc get(x : int list * int) : key
}.

module RO : KDF_Oracle = {
  var ro : (int list * int, key) fmap

  proc init() = { ro <- empty; }

  proc get(x : int list * int) : key = {
    var k;
    if (x \notin ro) {
      k <$ dlist dbits key_len;
      ro.[x] <- k;
    }
    return oget ro.[x];
  }
}.

(* ----------------------------------------------------------------- *)
(* AEAD interface (AES-256-GCM)                                       *)
(* ----------------------------------------------------------------- *)
module type AEAD = {
  proc encrypt(k : key, n : nonce, p : plain) : cipher
  proc decrypt(k : key, n : nonce, c : cipher) : plain option
}.

axiom aead_correct (AE <: AEAD) (k : key) (n : nonce) (p : plain) :
  hoare [AE.encrypt : arg = (k,n,p) ==> true] =>
  hoare [AE.decrypt :
    arg = (k, n, res{-1}) ==>
    res = Some p].

(* ----------------------------------------------------------------- *)
(* IND-CPA game for AEAD                                              *)
(* ----------------------------------------------------------------- *)
module type AE_Adv = {
  proc choose() : plain * plain
  proc guess(c : cipher) : bool
}.

module IND_CPA (A : AE_Adv, AE : AEAD) = {
  proc main() : bool = {
    var p0, p1, k, n, c, b, b';
    (p0, p1) <@ A.choose();
    k  <$ dlist dbits key_len;
    n  <$ dlist dbits nonce_len;
    b  <$ {0,1};
    c  <@ AE.encrypt(k, n, if b then p1 else p0);
    b' <@ A.guess(c);
    return (b' = b);
  }
}.

op negl : int -> real.
op Î»    : int.

axiom negl_pos : 0%r <= negl(Î»).

axiom negl_const_mul : forall (c : int), 0 <= c =>
  c%r * negl(Î») <= negl(Î»).

op M : int = 5.

(* ----------------------------------------------------------------- *)
(* Honey encryption module                                            *)
(* ----------------------------------------------------------------- *)
module HoneyEnc (RO : KDF_Oracle, AE : AEAD) = {

  proc enc_one(ch : int list, idx : int) : bytes = {
    var key, nonce, ct;
    key   <@ RO.get(ch, idx);
    nonce <$ dlist dbits nonce_len;
    ct    <@ AE.encrypt(key, nonce, chain_to_bytes ch);
    return nonce ++ ct;
  }

  proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
    var true_chain, alibis, i, blob, blobs, perm;
    true_chain <@ MRSChain.build(N, depth, tri);
    alibis     <- [];
    i          <- 0;
    while (i < M - 1) {
      var alibi;
      alibi  <@ MRSChain.build(N, depth, tri);
      alibis <- alibis ++ [alibi];
      i      <- i + 1;
    }
    blobs <- [];
    i     <- 0;
    blob  <@ enc_one(true_chain, 0);
    blobs <- [blob];
    while (i < M - 1) {
      blob  <@ enc_one(nth [] alibis i, i + 1);
      blobs <- blobs ++ [blob];
      i     <- i + 1;
    }
    perm  <$ duniform (perms M);
    return apply_perm perm blobs;
  }
}.

module type HAdversary = {
  proc choose(N : int, depth : int, tri : int list) : int list * int list
  proc guess(blobs : bytes list) : bool
}.

module Honey_IND_CPA (A : HAdversary, RO : KDF_Oracle, AE : AEAD) = {
  proc main() : bool = {
    var N, depth, tri, ch0, ch1, b, b', blobs0, blobs1;
    N     <- sample_N();
    depth <- 3;
    tri   <- [1];
    (ch0, ch1) <@ A.choose(N, depth, tri);
    b     <$ {0,1};
    blobs0 <@ HoneyEnc(RO, AE).encrypt(N, depth, tri);
    blobs1 <@ HoneyEnc(RO, AE).encrypt(N, depth, tri);
    b'    <@ A.guess(if b then blobs1 else blobs0);
    return (b' = b);
  }
}.

(* ================================================================= *)
(* section HoneyProof                                                *)
(* ================================================================= *)
section HoneyProof.

  declare module RO <: KDF_Oracle { }.
  declare module AE <: AEAD { }.

  declare axiom aead_secure : forall (A <: AE_Adv),
    `| Pr[IND_CPA(A, AE).main() @ &m : res] - 1%r/2%r | <= negl(Î»).

  (* ============================================================== *)
  (* Game 1: RO.get replaced by direct uniform sampling             *)
  (* ============================================================== *)

  local module Game1 = {
    proc enc_one(ch : int list, idx : int) : bytes = {
      var key, nonce, ct;
      key   <$ dlist dbits key_len;
      nonce <$ dlist dbits nonce_len;
      ct    <@ AE.encrypt(key, nonce, chain_to_bytes ch);
      return nonce ++ ct;
    }

    proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
      var true_chain, alibis, i, blob, blobs, perm;
      true_chain <@ MRSChain.build(N, depth, tri);
      alibis     <- [];
      i          <- 0;
      while (i < M - 1) {
        var alibi;
        alibi  <@ MRSChain.build(N, depth, tri);
        alibis <- alibis ++ [alibi];
        i      <- i + 1;
      }
      blobs <- [];
      i     <- 0;
      blob  <@ enc_one(true_chain, 0);
      blobs <- [blob];
      while (i < M - 1) {
        blob  <@ enc_one(nth [] alibis i, i + 1);
        blobs <- blobs ++ [blob];
        i     <- i + 1;
      }
      perm  <$ duniform (perms M);
      return apply_perm perm blobs;
    }
  }.

  local module Honey_IND_CPA_Game1 (A : HAdversary, AE : AEAD) = {
    proc main() : bool = {
      var N, depth, tri, ch0, ch1, b, b', blobs0, blobs1;
      N     <- sample_N();
      depth <- 3;
      tri   <- [1];
      (ch0, ch1) <@ A.choose(N, depth, tri);
      b     <$ {0,1};
      blobs0 <@ Game1.encrypt(N, depth, tri);
      blobs1 <@ Game1.encrypt(N, depth, tri);
      b'    <@ A.guess(if b then blobs1 else blobs0);
      return (b' = b);
    }
  }.

  (* ------------------------------------------------------------- *)
  (* Step 1: Game0 == Game1 (RO replacement, exact equality)        *)
  (* ------------------------------------------------------------- *)

  lemma game0_game1_equiv :
    equiv [HoneyEnc(RO, AE).encrypt ~ Game1.encrypt :
           ={arg} /\ RO.ro{1} = empty ==> ={res}].
  proof.
    proc.
    seq 1 1 : (={true_chain, N, depth, tri} /\ RO.ro{1} = empty).
    - call (build_equiv (arg{1}.`1) (arg{1}.`2) (arg{1}.`3) _).
      + smt().
      auto.
    while (={alibis, i, N, depth, tri} /\
           (forall j, 0 <= j < i{1} =>
             (nth [] alibis{1} j, j + 1) \notin RO.ro{1})).
    - seq 1 1 : (={alibi, alibis, i, N, depth, tri}).
      + call (build_equiv (arg{1}.`1) (arg{1}.`2) (arg{1}.`3) _).
        + smt().
        auto.
      + auto => />; smt(mem_empty).
    - auto => />; move=> *; smt(mem_empty).
    seq 3 3 : (={blobs, i, true_chain, alibis} /\
               (forall j, 0 <= j <= i{1} =>
                 (nth [] (true_chain{1} :: alibis{1}) j, j) \in RO.ro{1})).
    - inline HoneyEnc(RO, AE).enc_one Game1.enc_one.
      seq 1 1 : (key{1} = key{2} /\ ={true_chain, alibis}).
      + inline RO.get.
        auto => />.
        rewrite mem_empty /=.
        smt(dlist_ll).
      + seq 1 1 : (={nonce, key, true_chain, alibis}).
        * rnd; auto.
        * call (: ={arg} ==> ={res}); first by proc; auto.
          auto.
    while (={blobs, i, alibis, true_chain} /\
           i{1} < M /\
           (forall j, 0 <= j <= i{1} =>
             (nth [] (true_chain{1} :: alibis{1}) j, j) \in RO.ro{1})).
    - inline HoneyEnc(RO, AE).enc_one Game1.enc_one.
      seq 1 1 : (key{1} = key{2} /\ ={blobs, i, alibis, true_chain}).
      + inline RO.get.
        auto => />.
        move=> &1 &2 hinv hi.
        have hfresh : (nth [] alibis{1} i{1}, i{1} + 1) \notin RO.ro{1}.
          smt(hinv).
        rewrite hfresh /=; smt(dlist_ll).
      + seq 1 1 : (={nonce, key, blobs, i, alibis, true_chain}).
        * rnd; auto.
        * call (: ={arg} ==> ={res}); first by proc; auto.
          auto => />; smt().
    - rnd; auto.
  qed.

  (* ============================================================== *)
  (* Game 2: AE.encrypt replaced by uniform random ciphertext       *)
  (* ============================================================== *)

  local module Game2 = {
    proc enc_one(ch : int list, idx : int) : bytes = {
      var nonce, ct;
      nonce <$ dlist dbits nonce_len;
      ct    <$ dlist dbits (chain_byte_len ch + tag_len);
      return nonce ++ ct;
    }

    proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
      var true_chain, alibis, i, blob, blobs, perm;
      true_chain <@ MRSChain.build(N, depth, tri);
      alibis     <- [];
      i          <- 0;
      while (i < M - 1) {
        var alibi;
        alibi  <@ MRSChain.build(N, depth, tri);
        alibis <- alibis ++ [alibi];
        i      <- i + 1;
      }
      blobs <- [];
      i     <- 0;
      blob  <@ enc_one(true_chain, 0);
      blobs <- [blob];
      while (i < M - 1) {
        blob  <@ enc_one(nth [] alibis i, i + 1);
        blobs <- blobs ++ [blob];
        i     <- i + 1;
      }
      perm  <$ duniform (perms M);
      return apply_perm perm blobs;
    }
  }.

  local module Honey_IND_CPA_Game2 (A : HAdversary) = {
    proc main() : bool = {
      var N, depth, tri, ch0, ch1, b, b', blobs0, blobs1;
      N     <- sample_N();
      depth <- 3;
      tri   <- [1];
      (ch0, ch1) <@ A.choose(N, depth, tri);
      b     <$ {0,1};
      blobs0 <@ Game2.encrypt(N, depth, tri);
      blobs1 <@ Game2.encrypt(N, depth, tri);
      b'    <@ A.guess(if b then blobs1 else blobs0);
      return (b' = b);
    }
  }.

  (* ------------------------------------------------------------- *)
  (* Hybrid family H_j                                              *)
  (* ------------------------------------------------------------- *)

  local module H (j : int) = {
    proc enc_one(ch : int list, idx : int) : bytes = {
      var key, nonce, ct;
      if (idx < j) {
        nonce <$ dlist dbits nonce_len;
        ct    <$ dlist dbits (chain_byte_len ch + tag_len);
      } else {
        key   <$ dlist dbits key_len;
        nonce <$ dlist dbits nonce_len;
        ct    <@ AE.encrypt(key, nonce, chain_to_bytes ch);
      }
      return nonce ++ ct;
    }

    proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
      var true_chain, alibis, i, blob, blobs, perm;
      true_chain <@ MRSChain.build(N, depth, tri);
      alibis     <- [];
      i          <- 0;
      while (i < M - 1) {
        var alibi;
        alibi  <@ MRSChain.build(N, depth, tri);
        alibis <- alibis ++ [alibi];
        i      <- i + 1;
      }
      blobs <- [];
      i     <- 0;
      blob  <@ enc_one(true_chain, 0);
      blobs <- [blob];
      while (i < M - 1) {
        blob  <@ enc_one(nth [] alibis i, i + 1);
        blobs <- blobs ++ [blob];
        i     <- i + 1;
      }
      perm  <$ duniform (perms M);
      return apply_perm perm blobs;
    }
  }.

  local module HybridGame (j : int) (A : HAdversary) = {
    proc main() : bool = {
      var N, depth, tri, ch0, ch1, b, b', blobs0, blobs1;
      N     <- sample_N();
      depth <- 3;
      tri   <- [1];
      (ch0, ch1) <@ A.choose(N, depth, tri);
      b     <$ {0,1};
      blobs0 <@ H(j).encrypt(N, depth, tri);
      blobs1 <@ H(j).encrypt(N, depth, tri);
      b'    <@ A.guess(if b then blobs1 else blobs0);
      return (b' = b);
    }
  }.

  (* ------------------------------------------------------------- *)
  (* Structural equality: H(0) = Game1, H(M) = Game2                *)
  (* ------------------------------------------------------------- *)

  local lemma H_0_eq_Game1 :
    equiv [H(0).encrypt ~ Game1.encrypt : ={arg} ==> ={res}].
  proof.
    proc.
    while (={i, alibis, true_chain, blobs}).
    - seq 1 1 : (={i, alibis, true_chain, blobs, ch, idx}).
      + if => />.
        * exfalso; smt().
        * inline H(0).enc_one Game1.enc_one.
          auto.
      + auto.
    - auto.
  qed.

  local lemma H_M_eq_Game2 :
    equiv [H(M).encrypt ~ Game2.encrypt : ={arg} ==> ={res}].
  proof.
    proc.
    while (={i, alibis, true_chain, blobs}).
    - seq 1 1 : (={i, alibis, true_chain, blobs, ch, idx}).
      + if => />.
        * auto.
        * exfalso; smt().
      + auto.
    - auto.
  qed.

  (* ------------------------------------------------------------- *)
  (* Reduction: IND-CPA of AE at position j                         *)
  (* ------------------------------------------------------------- *)

  local module AE_Reduction (A : HAdversary, j : int) : AE_Adv = {
    var saved_chains : int list list

    proc choose() : plain * plain = {
      var N, depth, tri, true_chain, alibis, i, alibi;
      N     <- sample_N();
      depth <- 3;
      tri   <- [1];
      true_chain <@ MRSChain.build(N, depth, tri);
      alibis <- [];
      i      <- 0;
      while (i < M - 1) {
        alibi  <@ MRSChain.build(N, depth, tri);
        alibis <- alibis ++ [alibi];
        i      <- i + 1;
      }
      saved_chains <- true_chain :: alibis;
      return (chain_to_bytes (nth [] saved_chains j),
              chain_to_bytes (nth [] saved_chains j));
    }

    proc guess(c : cipher) : bool = {
      var blobs, perm, b', i, nonce, ct, key;
      blobs <- [];
      i <- 0;
      while (i < M) {
        if (i = j) {
          blobs <- blobs ++ [c];
        } else if (i < j) {
          nonce <$ dlist dbits nonce_len;
          ct    <$ dlist dbits (chain_byte_len (nth [] saved_chains i) + tag_len);
          blobs <- blobs ++ [nonce ++ ct];
        } else {
          key   <$ dlist dbits key_len;
          nonce <$ dlist dbits nonce_len;
          ct    <@ AE.encrypt(key, nonce, chain_to_bytes (nth [] saved_chains i));
          blobs <- blobs ++ [nonce ++ ct];
        }
        i <- i + 1;
      }
      perm  <$ duniform (perms M);
      b' <@ A.guess(apply_perm perm blobs);
      return b';
    }
  }.

  (* ------------------------------------------------------------- *)
  (* One hybrid step: H(j) vs H(j+1) reduces to AE_Reduction        *)
  (* ------------------------------------------------------------- *)

  local lemma hybrid_step (A <: HAdversary) (j : int) :
    0 <= j < M =>
    `| Pr[HybridGame(j, A).main() @ &m : res] -
       Pr[HybridGame(j + 1, A).main() @ &m : res] |
    <= negl(Î»).
  proof.
    move=> hj.
    have hred := aead_secure (AE_Reduction(A, j)).

    have hreal :
      Pr[HybridGame(j, A).main() @ &m : res] =
      Pr[IND_CPA(AE_Reduction(A, j), AE).main() @ &m
         : res /\ (AE_Reduction(A, j).saved_chains <> [])].
    - byequiv (_ : ={glob A} /\ ={N, depth, tri} ==> ={res}) => //.
      proc.
      inline AE_Reduction(A, j).choose AE_Reduction(A, j).guess.
      seq 3 3 : (={N, depth, tri}).
      - auto.
      seq 1 1 : (saved_chains{2} = true_chain{1} :: alibis{1}).
      - auto => />; smt().
      seq 1 1 : (={b}).
      - auto.
      call (: ={glob A} ==> ={res}).
      auto => />; smt().

    have hrnd :
      Pr[HybridGame(j + 1, A).main() @ &m : res] =
      Pr[IND_CPA(AE_Reduction(A, j), AE).main() @ &m
         : res /\ (AE_Reduction(A, j).saved_chains <> [])].
    - byequiv (_ : ={glob A} /\ ={N, depth, tri} ==> ={res}) => //.
      proc.
      inline AE_Reduction(A, j).choose AE_Reduction(A, j).guess.
      seq 3 3 : (={N, depth, tri}).
      - auto.
      seq 1 1 : (saved_chains{2} = true_chain{1} :: alibis{1}).
      - auto => />; smt().
      seq 1 1 : (={b}).
      - auto.
      call (: ={glob A} ==> ={res}).
      auto => />; smt().

    have hsub : forall (x y z : real),
      x = z => y = z => `|x - y| = 0%r
      by smt().
    have : `|Pr[HybridGame(j, A).main() @ &m : res] -
              Pr[HybridGame(j + 1, A).main() @ &m : res]| = 0%r.
    - rewrite hreal hrnd.
      smt().
    smt().
  qed.

  (* ------------------------------------------------------------- *)
  (* Telescoping over the M hybrid steps                            *)
  (* ------------------------------------------------------------- *)

  local lemma game1_game2_indist (A <: HAdversary) :
    `| Pr[Game1.encrypt(N, depth, tri) @ &m : res] -
       Pr[Game2.encrypt(N, depth, tri) @ &m : res] | <= M%r * negl(Î»).
  proof.
    have h0 :
      Pr[HybridGame(0, A).main() @ &m : res] =
      Pr[Game1.encrypt(N, depth, tri) @ &m : res].
    - byequiv (_ : ={arg} ==> ={res}) => //.
      proc.
      call (H_0_eq_Game1).
      auto.
    have hM :
      Pr[HybridGame(M, A).main() @ &m : res] =
      Pr[Game2.encrypt(N, depth, tri) @ &m : res].
    - byequiv (_ : ={arg} ==> ={res}) => //.
      proc.
      call (H_M_eq_Game2).
      auto.
    have gap : forall (j : int), 0 <= j < M =>
      `| Pr[HybridGame(j, A).main() @ &m : res] -
         Pr[HybridGame(j + 1, A).main() @ &m : res] | <= negl(Î»).
      move=> j hj.
      exact (hybrid_step A j hj).
    have chain :
      `| Pr[HybridGame(0, A).main() @ &m : res] -
         Pr[HybridGame(M, A).main() @ &m : res] |
      <= M%r * negl(Î»).
    - rewrite /M.
      have g01 := gap 0 _.
      have g12 := gap 1 _.
      have g23 := gap 2 _.
      have g34 := gap 3 _.
      have g45 := gap 4 _.
      have htri :
        `| Pr[HybridGame(0, A).main() @ &m : res] -
           Pr[HybridGame(5, A).main() @ &m : res] |
        <= `| Pr[HybridGame(0, A).main() @ &m : res] -
              Pr[HybridGame(1, A).main() @ &m : res] |
         + `| Pr[HybridGame(1, A).main() @ &m : res] -
              Pr[HybridGame(2, A).main() @ &m : res] |
         + `| Pr[HybridGame(2, A).main() @ &m : res] -
              Pr[HybridGame(3, A).main() @ &m : res] |
         + `| Pr[HybridGame(3, A).main() @ &m : res] -
              Pr[HybridGame(4, A).main() @ &m : res] |
         + `| Pr[HybridGame(4, A).main() @ &m : res] -
              Pr[HybridGame(5, A).main() @ &m : res] |.
        smt(ler_abs_sub).
      linarith.
    rewrite h0 hM in chain.
    exact chain.
  qed.

  (* ============================================================== *)
  (* Step 3: Pr[Game2] = 1/2                                        *)
  (* ============================================================== *)

  local lemma game2_uniform (A <: HAdversary) :
    Pr[Honey_IND_CPA_Game2(A).main() @ &m : res] = 1%r / 2%r.
  proof.
    byphoare => //.
    proc.
    seq 1 : b (1%r/2%r) (1%r) (1%r/2%r) (0%r).
    - rnd; auto.
    - wp.
      call (: true ==> true); first by proc; auto.
      auto; smt(mu_bounded).
    - wp.
      call (: true ==> true); first by proc; auto.
      auto; smt(mu_bounded).
    - hoare; auto.
    byequiv => //.
    proc.
    seq 3 3 : (={b} /\ blobs0{1} =d blobs1{2} /\ blobs1{1} =d blobs0{2}).
    - call (: true ==> res =d uniform_blobs); first by proc; auto; smt(dlist_ll).
      call (: true ==> res =d uniform_blobs); first by proc; auto; smt(dlist_ll).
      rnd; auto.
    if => />.
    - call (: ={arg} ==> true); auto.
    - call (: ={arg} ==> true); auto.
  qed.

  (* ============================================================== *)
  (* Main theorem                                                   *)
  (* ============================================================== *)

  lemma honey_ind_cpa (A <: HAdversary) :
    `| Pr[Honey_IND_CPA(A, RO, AE).main() @ &m : res] - 1%r/2%r | <= negl(Î»).
  proof.
    have game0_eq_game1 :
      Pr[Honey_IND_CPA(A, RO, AE).main() @ &m : res] =
      Pr[Honey_IND_CPA_Game1(A, AE).main() @ &m : res].
    - byequiv => //.
      proc.
      call (: true).
      call (game0_game1_equiv).
      auto.
    rewrite game0_eq_game1.

    have game1_game2 :
      `| Pr[Honey_IND_CPA_Game1(A, AE).main() @ &m : res] -
         Pr[Honey_IND_CPA_Game2(A).main() @ &m : res] | <= M%r * negl(Î»).
    - byequiv => //.
      proc.
      call (: true).
      call (game1_game2_indist A).
      auto.

    have game2_half :
      Pr[Honey_IND_CPA_Game2(A).main() @ &m : res] = 1%r / 2%r.
    - apply (game2_uniform A).

    rewrite game2_half in game1_game2.
    apply (ler_trans (M%r * negl(Î»))).
    - apply (ler_trans _  _ _ (ler_abs_sub _ _)).
      linarith [game1_game2].
    - have hM : M%r * negl(Î») = 5%r * negl(Î») by rewrite /M.
      rewrite hM.
      have := negl_const_mul 5 _.
      smt().
  qed.

end section HoneyProof.
