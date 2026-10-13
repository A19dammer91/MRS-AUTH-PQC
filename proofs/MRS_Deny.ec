(* ================================================================= *)
(*  MRS_Deny.ec                                                       *)
(*  MRS-AUTH: Deniability Experiment                                  *)
(*                                                                    *)
(*  Security target:                                                  *)
(*    Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r      *)
(*                                                                    *)
(*  Axiom baseline: 1 (deny_success_probability).                     *)
(*  The proof of that statement is in MRS_DenyProof.ec.               *)
(* ================================================================= *)

require import AllCore Bool Int IntDiv List Real Distr.
require import MRS_Core.
require import MRS_Distr.
require import MRS_Equiv.
require import MRS_Chain.

(* ================================================================= *)
(* Section 1: Adversary interface                                     *)
(* ================================================================= *)

module type MRSAdversary = {
  proc guess(chain : int list) : bool
}.

(* ================================================================= *)
(* Section 2: Deniability experiment                                  *)
(* ================================================================= *)

module DenyGame (A : MRSAdversary) = {
  proc main(N depth : int, tri : int list) : bool = {
    var bit : int;
    var b : bool;
    var ch0, ch1 : int list;
    var selected : int list;
    var g : bool;

    bit <$ duniform_int 1;
    b <- (bit = 1);

    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);

    if (b) {
      selected <- ch1;
    } else {
      selected <- ch0;
    }

    g <@ A.guess(selected);

    return (g = b);
  }
}.

(* ================================================================= *)
(* Section 3: Fairness of the challenge bit                           *)
(* ================================================================= *)

lemma duniform_int_one_mu1 (x : int) :
  0 <= x <= 1 =>
  mu1 (duniform_int 1) x = 1%r / 2%r.
proof.
  move=> hx.
  rewrite /duniform_int ifF 1:/#.
  rewrite duniform1E_uniq 1:range_uniq.
  rewrite mem_range size_range.
  smt().
qed.

lemma challenge_bit_uniform_zero :
  mu1 (duniform_int 1) 0 = 1%r / 2%r.
proof. by apply duniform_int_one_mu1. qed.

lemma challenge_bit_uniform_one :
  mu1 (duniform_int 1) 1 = 1%r / 2%r.
proof. by apply duniform_int_one_mu1. qed.

(* ================================================================= *)
(* Section 4: Identical distribution of the two chains                *)
(* Own proof: no dependence on the signature of build_equiv.          *)
(* ================================================================= *)

lemma chain_left_right_equiv
    (N depth : int) (tri : int list) :
  equiv [MRSChain.build ~ MRSChain.build :
    arg{1} = (N, depth, tri) /\
    arg{2} = (N, depth, tri) ==> ={res}].
proof.
  proc; sim.
qed.

(* ================================================================= *)
(* Section 5: Main theorem (proved in MRS_DenyProof.ec)               *)
(* ================================================================= *)

axiom deny_success_probability
    (A <: MRSAdversary) &m
    (N depth : int) (tri : int list) :
  islossless A.guess =>
  Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.

(* ================================================================= *)
(* End of MRS_Deny.ec                                                 *)
(* ================================================================= *)
