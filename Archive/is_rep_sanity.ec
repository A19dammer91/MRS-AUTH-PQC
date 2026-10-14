(* ================================================================= *)
(*  is_rep_sanity.ec                                                  *)
(*  Sanity check for the representation predicate.                    *)
(*                                                                    *)
(*  Purpose.                                                          *)
(*  This was the first check written when the (19, 9) representation  *)
(*  system was being formalised. It verifies that the predicate       *)
(*  `is_rep N A B` behaves as expected under a basic unfolding, and   *)
(*  that the `smt()` tactic discharges the trivial consequence.       *)
(*                                                                    *)
(*  Context.                                                          *)
(*  The predicate `is_rep N A B` states that the pair `(A, B)` is a   *)
(*  valid representation of `N` in the (19, 9) system, with the       *)
(*  positive-anchor constraint `1 <= A`. The full development of      *)
(*  this predicate, its properties, and its role in the count of      *)
(*  representations lives in MRS_Core.ec and MRS_Framework.ec.        *)
(*                                                                    *)
(*  Status.                                                           *)
(*  This file is NOT part of the verification chain. It is kept as a  *)
(*  historical record. It does not need to compile as part of CI.     *)
(* ================================================================= *)

require import AllCore Int.

(* ----------------------------------------------------------------- *)
(* The representation predicate.                                      *)
(*                                                                    *)
(* A pair `(A, B)` is a representation of `N` if A is at least 1,     *)
(* B is non-negative, and 19*A + 9*B equals N. This is the           *)
(* positive-anchor form of the predicate: A is never allowed to be    *)
(* zero, so every representation carries a real core.                 *)
(* ----------------------------------------------------------------- *)
pred is_rep (N A B : int) =
  1 <= A /\ 0 <= B /\ 19*A + 9*B = N.

(* ----------------------------------------------------------------- *)
(* Sanity check.                                                      *)
(*                                                                    *)
(* If `is_rep N A B` holds, then A is at least 1. This is             *)
(* immediate from the definition — it is the first conjunct —         *)
(* but verifying it confirmed that the predicate unfolds correctly    *)
(* and that `smt()` can discharge the resulting goal.                 *)
(* ----------------------------------------------------------------- *)
lemma test (N A B : int) :
  is_rep N A B => 1 <= A.
proof.
  move=> hrep.
  rewrite /is_rep in hrep.
  smt().
qed.

(* ================================================================= *)
(* End of is_rep_sanity.ec                                           *)
(* ================================================================= *)
