
(* ================================================================= *)
(* MRS_Equiv.ec                                                       *)
(* Equivalence lemmas for the MRS samplers                            *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

(* ================================================================= *)
(* Section 1: sample_basic is equivalent to itself                    *)
(* ================================================================= *)

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [
    MRSRep.sample_basic ~ MRSRep.sample_basic
    : ={arg} ==> ={res}
  ].
proof.
  move=> hN.
  byequiv => //.
  proc.
  sim.
qed.

(* ================================================================= *)
(* Section 2: sample_triangle is equivalent to itself                 *)
(* ================================================================= *)

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [
    MRSRep.sample_triangle ~ MRSRep.sample_triangle
    : ={arg} ==> ={res}
  ].
proof.
  move=> hN.
  byequiv => //.
  proc.
  sim.
qed.

(* ================================================================= *)
(* End of MRS_Equiv.ec                                                *)
(* ================================================================= *)
