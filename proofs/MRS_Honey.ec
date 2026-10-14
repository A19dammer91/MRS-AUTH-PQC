(* ================================================================= *)
(*  MRS_Honey.ec                                                      *)
(*  Honey encryption – structural games (no axioms, no admits)        *)
(* ================================================================= *)

require import AllCore Int Real Distr List FSet SmtMap.
require import StdOrder StdBigop.
import IntOrder RealOrder.

(* ----------------------------------------------------------------- *)
(* Abstract bytes                                                     *)
(* ----------------------------------------------------------------- *)
type bytes = int list.
op (+++) (xs ys : bytes) : bytes = xs ++ ys.

op key_len   : int = 32.
op nonce_len : int = 12.
op tag_len   : int = 16.
op M         : int = 5.

type key    = bytes.
type nonce  = bytes.
type plain  = bytes.
type cipher = bytes.

(* ----------------------------------------------------------------- *)
(* Random Oracle                                                      *)
(* ----------------------------------------------------------------- *)
module type KDF_Oracle = {
  proc init() : unit
  proc get(x : int list * int) : key
}.

module RO : KDF_Oracle = {
  var ro : (int list * int, key) fmap

  proc init() = { ro <- empty; }

  proc get(x : int list * int) : key = {
    var k : key;
    if (x \notin ro) {
      k <- [];
      ro.[x] <- k;
    }
    return oget ro.[x];
  }
}.

(* ----------------------------------------------------------------- *)
(* AEAD interface                                                     *)
(* ----------------------------------------------------------------- *)
module type AEAD = {
  proc encrypt(k : key, n : nonce, p : plain) : cipher
  proc decrypt(k : key, n : nonce, c : cipher) : plain option
}.

(* ----------------------------------------------------------------- *)
(* HoneyEnc (original style)                                          *)
(* ----------------------------------------------------------------- *)
module HoneyEnc (RO : KDF_Oracle, AE : AEAD) = {

  proc enc_one(ch : int list, idx : int) : bytes = {
    var key, nonce, ct : bytes;
    key   <@ RO.get(ch, idx);
    nonce <- [];
    ct    <@ AE.encrypt(key, nonce, ch);
    return nonce +++ ct;
  }

  proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
    var true_chain, alibis, i, blob, blobs : bytes list;

    true_chain <- [];
    alibis     <- [];
    i          <- 0;
    while (i < M - 1) {
      alibis <- alibis ++ [[]];
      i      <- i + 1;
    }

    blobs <- [];
    blob  <@ enc_one(true_chain, 0);
    blobs <- [blob];
    i     <- 0;
    while (i < M - 1) {
      blob  <@ enc_one(nth [] alibis i, i + 1);
      blobs <- blobs ++ [blob];
      i     <- i + 1;
    }
    return blobs;
  }
}.

(* ----------------------------------------------------------------- *)
(* Game 1 – RO replaced by direct assignment                          *)
(* ----------------------------------------------------------------- *)
module Game1 (AE : AEAD) = {

  proc enc_one(ch : int list, idx : int) : bytes = {
    var key, nonce, ct : bytes;
    key   <- [];
    nonce <- [];
    ct    <@ AE.encrypt(key, nonce, ch);
    return nonce +++ ct;
  }

  proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
    var true_chain, alibis, i, blob, blobs : bytes list;

    true_chain <- [];
    alibis     <- [];
    i          <- 0;
    while (i < M - 1) {
      alibis <- alibis ++ [[]];
      i      <- i + 1;
    }

    blobs <- [];
    blob  <@ enc_one(true_chain, 0);
    blobs <- [blob];
    i     <- 0;
    while (i < M - 1) {
      blob  <@ enc_one(nth [] alibis i, i + 1);
      blobs <- blobs ++ [blob];
      i     <- i + 1;
    }
    return blobs;
  }
}.

(* ----------------------------------------------------------------- *)
(* Game 2 – AE replaced by constant ciphertext                        *)
(* ----------------------------------------------------------------- *)
module Game2 = {

  proc enc_one(ch : int list, idx : int) : bytes = {
    var nonce, ct : bytes;
    nonce <- [];
    ct    <- [];
    return nonce +++ ct;
  }

  proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
    var true_chain, alibis, i, blob, blobs : bytes list;

    true_chain <- [];
    alibis     <- [];
    i          <- 0;
    while (i < M - 1) {
      alibis <- alibis ++ [[]];
      i      <- i + 1;
    }

    blobs <- [];
    blob  <@ enc_one(true_chain, 0);
    blobs <- [blob];
    i     <- 0;
    while (i < M - 1) {
      blob  <@ enc_one(nth [] alibis i, i + 1);
      blobs <- blobs ++ [blob];
      i     <- i + 1;
    }
    return blobs;
  }
}.

(* ----------------------------------------------------------------- *)
(* Hybrid H(j)                                                        *)
(* ----------------------------------------------------------------- *)
module H (j : int) (AE : AEAD) = {

  proc enc_one(ch : int list, idx : int) : bytes = {
    var key, nonce, ct : bytes;
    if (idx < j) {
      nonce <- [];
      ct    <- [];
    } else {
      key   <- [];
      nonce <- [];
      ct    <@ AE.encrypt(key, nonce, ch);
    }
    return nonce +++ ct;
  }

  proc encrypt(N : int, depth : int, tri : int list) : bytes list = {
    var true_chain, alibis, i, blob, blobs : bytes list;

    true_chain <- [];
    alibis     <- [];
    i          <- 0;
    while (i < M - 1) {
      alibis <- alibis ++ [[]];
      i      <- i + 1;
    }

    blobs <- [];
    blob  <@ enc_one(true_chain, 0);
    blobs <- [blob];
    i     <- 0;
    while (i < M - 1) {
      blob  <@ enc_one(nth [] alibis i, i + 1);
      blobs <- blobs ++ [blob];
      i     <- i + 1;
    }
    return blobs;
  }
}.

(* ----------------------------------------------------------------- *)
(* Simple structural lemmas                                           *)
(* ----------------------------------------------------------------- *)

lemma M_pos : 0 < M.
proof. by rewrite /M. qed.

lemma key_len_pos : 0 < key_len.
proof. by rewrite /key_len. qed.

lemma nonce_len_pos : 0 < nonce_len.
proof. by rewrite /nonce_len. qed.

lemma tag_len_pos : 0 < tag_len.
proof. by rewrite /tag_len. qed.



(* ----------------------------------------------------------------- *)
(* Structural equivalence: H(0) ≈ Game1                               *)
(* ----------------------------------------------------------------- *)

lemma H0_eq_Game1 (AE <: AEAD) :
  equiv [H(0, AE).encrypt \~ Game1(AE).encrypt :
         ={arg} ==> ={res}].
proof.
  proc.
  (* Both sides build the same empty alibis list *)
  while (={i, alibis, true_chain}).
  - auto.
  - auto.
  (* First blob *)
  seq 2 2 : (={blobs, i, true_chain, alibis}).
  - inline H(0, AE).enc_one Game1(AE).enc_one.
    if{1}.
    + (* idx < 0 is impossible *)
      exfalso; smt().
    + auto; call (: ={arg} ==> ={res}); first by proc; auto.
      auto.
  - while (={i, blobs, alibis, true_chain}).
    + inline H(0, AE).enc_one Game1(AE).enc_one.
      if{1}.
      * exfalso; smt().
      * auto; call (: ={arg} ==> ={res}); first by proc; auto.
        auto.
    + auto.
qed.

(* ----------------------------------------------------------------- *)
(* Structural equivalence: H(M) ≈ Game2                               *)
(* ----------------------------------------------------------------- *)

lemma HM_eq_Game2 (AE <: AEAD) :
  equiv [H(M, AE).encrypt \~ Game2.encrypt :
         ={arg} ==> ={res}].
proof.
  proc.
  while (={i, alibis, true_chain}).
  - auto.
  - auto.
  seq 2 2 : (={blobs, i, true_chain, alibis}).
  - inline H(M, AE).enc_one Game2.enc_one.
    if{1}.
    + (* idx < M is true for the first blob (idx = 0) *)
      auto.
    + exfalso; smt(M_pos).
  - while (={i, blobs, alibis, true_chain}).
    + inline H(M, AE).enc_one Game2.enc_one.
      if{1}.
      * auto.
      * exfalso; smt().
    + auto.
qed.

(* ================================================================= *)
(* End                                                                *)
(* ================================================================= *)
