(* ================================================================= *)
(*  MRS_Honey.ec                                                      *)
(*  Honey encryption layer of MRS-AUTH                                *)
(*                                                                    *)
(*  Statement: the M blobs are indistinguishable from uniform         *)
(*  strings of the same lengths, with gap <= M * eps, where eps is    *)
(*  the advantage against one challenge query of the AEAD.            *)
(* ================================================================= *)

require import AllCore List Distr DBool DList.
require import StdOrder.
import RealOrder.

require import MRS_Chain.

type key    = bool list.
type nonce  = bool list.
type plain  = bool list.
type cipher = bool list.

op key_len   : int.
op nonce_len : int.
op tag_len   : int.

(* Abstract chain encoding; instantiate with chain_to_bytes. *)
op chain_enc : int list -> plain.

op M : int = 5.

lemma M_val : M = 5.
proof. by rewrite /M. qed.

(* Advantage of the AEAD against one challenge query. *)
op eps : real.

(* ----------------------------------------------------------------- *)
(* AEAD and ciphertext oracles                                        *)
(* ----------------------------------------------------------------- *)
module type AEAD = {
  proc encrypt(k : key, n : nonce, p : plain) : cipher
}.

module type CT_Oracle = {
  proc enc(p : plain) : cipher
  proc real(p : plain) : cipher
}.

module O_real (AE : AEAD) : CT_Oracle = {
  proc real(p : plain) : cipher = {
    var k : key;
    var n : nonce;
    var c : cipher;
    k <$ dlist dbool key_len;
    n <$ dlist dbool nonce_len;
    c <@ AE.encrypt(k, n, p);
    return n ++ c;
  }

  proc enc(p : plain) : cipher = {
    var r : cipher;
    r <@ real(p);
    return r;
  }
}.

module O_rand (AE : AEAD) : CT_Oracle = {
  var first : bool

  proc real(p : plain) : cipher = {
    var k : key;
    var n : nonce;
    var c : cipher;
    k <$ dlist dbool key_len;
    n <$ dlist dbool nonce_len;
    c <@ AE.encrypt(k, n, p);
    return n ++ c;
  }

  proc enc(p : plain) : cipher = {
    var n : nonce;
    var c : cipher;
    var r : cipher;
    if (first) {
      first <- false;
      n <$ dlist dbool nonce_len;
      c <$ dlist dbool (size p + tag_len);
      r <- n ++ c;
    } else {
      r <@ real(p);
    }
    return r;
  }
}.

module type AE_Dist (O : CT_Oracle) = {
  proc run(a : int) : bool
}.

module ExpReal (R : AE_Dist) (AE : AEAD) = {
  proc main(a : int) : bool = {
    var b : bool;
    b <@ R(O_real(AE)).run(a);
    return b;
  }
}.

module ExpRand (R : AE_Dist) (AE : AEAD) = {
  proc main(a : int) : bool = {
    var b : bool;
    O_rand.first <- true;
    b <@ R(O_rand(AE)).run(a);
    return b;
  }
}.

(* ----------------------------------------------------------------- *)
(* Distinguisher: gen builds the M chains (true chain first, then     *)
(* alibis); dist sees the blobs (it may apply the permutation).       *)
(* ----------------------------------------------------------------- *)
module type HDist = {
  proc gen() : int list list
  proc dist(blobs : cipher list) : bool
}.

(* Hybrid j: positions < j are random, the others are encrypted. *)
module Hyb (D : HDist) (AE : AEAD) = {
  proc run(j : int) : bool = {
    var cs : int list list;
    var blobs : cipher list;
    var i : int;
    var k : key;
    var n : nonce;
    var c : cipher;
    var r : cipher;
    var b : bool;
    cs <@ D.gen();
    blobs <- [];
    i <- 0;
    while (i < M) {
      if (i < j) {
        n <$ dlist dbool nonce_len;
        c <$ dlist dbool (size (chain_enc (nth [] cs i)) + tag_len);
        r <- n ++ c;
      } else {
        k <$ dlist dbool key_len;
        n <$ dlist dbool nonce_len;
        c <@ AE.encrypt(k, n, chain_enc (nth [] cs i));
        r <- n ++ c;
      }
      blobs <- blobs ++ [r];
      i <- i + 1;
    }
    b <@ D.dist(blobs);
    return b;
  }

  proc main(j : int) : bool = {
    var b : bool;
    b <@ run(j);
    return b;
  }
}.

(* Reduction: one challenge query, at position j. *)
module Red (D : HDist) (O : CT_Oracle) = {
  proc run(j : int) : bool = {
    var cs : int list list;
    var blobs : cipher list;
    var i : int;
    var n : nonce;
    var c : cipher;
    var r : cipher;
    var b : bool;
    cs <@ D.gen();
    blobs <- [];
    i <- 0;
    while (i < M) {
      if (i < j) {
        n <$ dlist dbool nonce_len;
        c <$ dlist dbool (size (chain_enc (nth [] cs i)) + tag_len);
        r <- n ++ c;
      } else {
        if (i = j) {
          r <@ O.enc(chain_enc (nth [] cs i));
        } else {
          r <@ O.real(chain_enc (nth [] cs i));
        }
      }
      blobs <- blobs ++ [r];
      i <- i + 1;
    }
    b <@ D.dist(blobs);
    return b;
  }
}.

(* The chain generator of the scheme, built from MRSChain. *)
module HoneyGen = {
  proc gen(N : int, depth : int, tri : int list) : int list list = {
    var true_chain : int list;
    var alibis : int list list;
    var a : int list;
    var i : int;
    true_chain <@ MRSChain.build(N, depth, tri);
    alibis <- [];
    i <- 0;
    while (i < M - 1) {
      a <@ MRSChain.build(N, depth, tri);
      alibis <- alibis ++ [a];
      i <- i + 1;
    }
    return true_chain :: alibis;
  }
}.

(* ================================================================= *)
(* section HoneyProof                                                 *)
(* ================================================================= *)
section HoneyProof.

  declare module AE <: AEAD {-O_rand}.
  declare module D  <: HDist {-AE, -O_rand}.

  declare axiom aead_secure :
    forall (R <: AE_Dist {-AE, -O_rand}) (a : int) &m,
      `| Pr[ExpReal(R, AE).main(a) @ &m : res] -
         Pr[ExpRand(R, AE).main(a) @ &m : res] | <= eps.

  (* ------------------------------------------------------------- *)
  (* Hyb(j) = reduction with the real oracle                        *)
  (* ------------------------------------------------------------- *)
  local lemma red_real_equiv :
    equiv [Hyb(D, AE).run ~ Red(D, O_real(AE)).run :
           ={glob D, glob AE, arg} ==> ={res}].
  proof.
    proc.
    seq 3 3 : (={glob D, glob AE, j, cs, blobs, i}).
    - wp; call (_ : true); skip; smt().
    seq 1 1 : (={glob D, glob AE, blobs}).
    - while (={glob D, glob AE, j, cs, blobs, i}).
      + case (i{1} < j{1}).
        * rcondt{1} 1; first by auto => /#.
          rcondt{2} 1; first by auto => /#.
          wp; rnd; rnd; skip; smt().
        * rcondf{1} 1; first by auto => /#.
          rcondf{2} 1; first by auto => /#.
          case (i{1} = j{1}).
          - rcondt{2} 1; first by auto => /#.
            inline *.
            wp; call (_ : true); rnd; rnd; wp; skip; smt().
          - rcondf{2} 1; first by auto => /#.
            inline *.
            wp; call (_ : true); rnd; rnd; wp; skip; smt().
      + skip; smt().
    wp; call (_ : true); skip; smt().
  qed.

  (* ------------------------------------------------------------- *)
  (* Hyb(j+1) = reduction with the random challenge                 *)
  (* ------------------------------------------------------------- *)
  local lemma red_rand_equiv :
    equiv [Hyb(D, AE).run ~ Red(D, O_rand(AE)).run :
           ={glob D, glob AE} /\ j{1} = j{2} + 1 /\ 0 <= j{2}
           /\ O_rand.first{2} ==> ={res}].
  proof.
    proc.
    seq 3 3 : (={glob D, glob AE, cs, blobs, i} /\ j{1} = j{2} + 1
               /\ 0 <= j{2} /\ i{1} = 0 /\ O_rand.first{2}).
    - wp; call (_ : true); skip; smt().
    seq 1 1 : (={glob D, glob AE, blobs}).
    - while (={glob D, glob AE, cs, blobs, i} /\ j{1} = j{2} + 1
             /\ 0 <= j{2} /\ (O_rand.first{2} <=> i{2} <= j{2})).
      + case (i{2} < j{2}).
        * rcondt{1} 1; first by auto => /#.
          rcondt{2} 1; first by auto => /#.
          wp; rnd; rnd; skip; smt().
        * case (i{2} = j{2}).
          - rcondt{1} 1; first by auto => /#.
            rcondf{2} 1; first by auto => /#.
            rcondt{2} 1; first by auto => /#.
            inline *.
            rcondt{2} 2; first by auto => /#.
            wp; rnd; rnd; wp; skip; smt().
          - rcondf{1} 1; first by auto => /#.
            rcondf{2} 1; first by auto => /#.
            rcondf{2} 1; first by auto => /#.
            inline *.
            wp; call (_ : true); rnd; rnd; wp; skip; smt().
      + skip; smt().
    wp; call (_ : true); skip; smt().
  qed.

  (* ------------------------------------------------------------- *)
  (* From procedure equivalences to probabilities                   *)
  (* ------------------------------------------------------------- *)
  local lemma hyb_real (j : int) &m :
    Pr[Hyb(D, AE).main(j) @ &m : res] =
    Pr[ExpReal(Red(D), AE).main(j) @ &m : res].
  proof.
    byequiv (_ : ={glob D, glob AE, arg} ==> ={res}) => //.
    proc.
    wp; call red_real_equiv; skip; smt().
  qed.

  local lemma hyb_rand (j : int) &m :
    0 <= j =>
    Pr[Hyb(D, AE).main(j + 1) @ &m : res] =
    Pr[ExpRand(Red(D), AE).main(j) @ &m : res].
  proof.
    move=> hj.
    byequiv (_ : ={glob D, glob AE} /\ arg{1} = arg{2} + 1 /\ 0 <= arg{2}
                 ==> ={res}) => //.
    proc.
    wp; call red_rand_equiv; wp; skip; smt().
  qed.

  (* ------------------------------------------------------------- *)
  (* One hybrid step costs at most eps                              *)
  (* ------------------------------------------------------------- *)
  local lemma hybrid_gap (j j' : int) &m :
    0 <= j => j < M => j' = j + 1 =>
    `| Pr[Hyb(D, AE).main(j) @ &m : res] -
       Pr[Hyb(D, AE).main(j') @ &m : res] | <= eps.
  proof.
    move=> h0 hM ->.
    rewrite (hyb_real j &m) (hyb_rand j &m h0).
    exact (aead_secure (Red(D)) j &m).
  qed.

  (* ------------------------------------------------------------- *)
  (* Main theorem: M blobs are pseudorandom                         *)
  (* ------------------------------------------------------------- *)
    lemma honey_pseudorandom &m :
    `| Pr[Hyb(D, AE).main(0) @ &m : res] -
       Pr[Hyb(D, AE).main(M) @ &m : res] | <= M%r * eps.
  proof.
    have g0 := hybrid_gap 0 1 &m.
    have g1 := hybrid_gap 1 2 &m.
    have g2 := hybrid_gap 2 3 &m.
    have g3 := hybrid_gap 3 4 &m.
    have g4 := hybrid_gap 4 M &m.
    smt(M_val ler_norml).
  qed.
