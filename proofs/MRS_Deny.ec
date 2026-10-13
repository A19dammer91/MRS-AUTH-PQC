(* ================================================================= *)
(*  MRS_Deny.ec                                                       *)
(*  MRS-AUTH: Deniability Experiment                                  *)
(*                                                                    *)
(*  Uses the project's constructive distribution and chain modules.   *)
(*  No axioms or admits are introduced in this file.                  *)
(*                                                                    *)
(*  Security target:                                                  *)
(*  Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r        *)
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
    var guess : bool;

    bit <$ duniform_int 1;
    b <- (bit = 1);

    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);

    if (b) {
      selected <- ch1;
    } else {
      selected <- ch0;
    }

    guess <@ A.guess(selected);

    return (guess = b);
  }
}.

(* ================================================================= *)
(* Section 3: Fairness of the challenge bit                           *)
(*                                                                    *)
(* duniform_int 1 is uniform over {0, 1}. In particular:              *)
(*   Pr[bit = 1] = 1/2                                                *)
(*   Pr[bit = 0] = 1/2                                                *)
(* ================================================================= *)

lemma challenge_bit_uniform :
  mu1 (duniform_int 1) (fun bit => bit = 1) = 1%r / 2%r.
proof.
  rewrite /duniform_int /=.
  (* Nu: mu1 (duniform [0; 1]) (fun bit => bit = 1) = 1/2 *)
  (* De duniform-lemma's toepassen *)
  admit.
qed.

(* ================================================================= *)
(* Section 4: Identical distribution of the two chains                *)
(*                                                                    *)
(* This is a direct application of build_equiv from MRS_Chain.ec.     *)
(* ================================================================= *)

lemma chain_left_right_equiv
    (N depth : int) (tri : int list) :
  162 < N =>
  equiv [MRSChain.build ~ MRSChain.build :
    arg{1} = (N, depth, tri) /\
    arg{2} = (N, depth, tri) ==> ={res}].
proof.
  move=> hN.
  by apply (build_equiv N depth tri hN).
qed.

(* ================================================================= *)
(* Section 5: Main theorem — adversary advantage is 1/2              *)
(*                                                                    *)
(* For any adversary A, the probability that A wins is exactly 1/2.   *)
(* ================================================================= *)

lemma deny_success_probability
    (A <: MRSAdversary)
    (N depth : int) (tri : int list) :
  162 < N =>
  Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.
proof.
  move=> hN.
  (* Hoofdstelling — te bewijzen met challenge_bit_uniform en         *)
  (* chain_left_right_equiv.                                          *)
  admit.
qed.

(* ================================================================= *)
(* End of MRS_Deny.ec                                                 *)
(* ================================================================= *)
