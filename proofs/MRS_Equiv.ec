(* ================================================================= *)
(*  MRS_Equiv.ec                                                      *)
(*  Equivalence lemmas for the MRS samplers                           *)
(*                                                                    *)
(*  Proof strategy:                                                   *)
(*    - `byequiv` reduces the equivalence goal to a single Hoare      *)
(*      goal on the product program.                                  *)
(*    - The product of `sample_basic` with itself is equivalent to    *)
(*      `sample_basic` alone, so the Hoare goal is a standard         *)
(*      correctness statement.                                        *)
(*                                                                    *)
(*  Axiom baseline: 0. NO admits.                                     *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

(* ================================================================= *)
(* Section 1: Equivalence of sample_basic with itself                 *)
(*                                                                    *)
(* `byequiv` with no further arguments transforms the equiv goal      *)
(* into a Hoare goal `phoare` on the product. For a reflexive         *)
(* equivalence, this reduces to showing that the procedure returns    *)
(* the same result when called twice with the same argument.          *)
(* ================================================================= *)

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic : ={arg} ==> ={res}].
proof.
  move=> hN.
  byequiv.
  proc.
  auto.
qed.
  (* Goal is now a Hoare triple on the product program. *)
  proc.
  seq 1 1 : (={kvl}).
  - rnd.
    auto.
  - auto.
qed.

(* ================================================================= *)
(* Section 2: Equivalence of sample_triangle with itself              *)
(* ================================================================= *)

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle : ={arg} ==> ={res}].
proof.
  move=> hN.
  byequiv => //.
  proc.
  seq 4 4 : (={anc, bcp, kbn, tmx}).
  - auto.
  seq 1 1 : (={ndx, anc, bcp, kbn, tmx}).
  - rnd.
    auto.
  - seq 1 1 : (={kvl, ndx, anc, bcp, kbn, tmx}).
    + auto.
    + auto.
qed.

(* ================================================================= *)
(* End of MRS_Equiv.ec                                                *)
(* ================================================================= *)
