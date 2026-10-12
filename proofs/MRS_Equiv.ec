(* MRS_Equiv.ec
   Equivalence lemmas for the MRS samplers.
   No axioms or admits in this file.
*)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic :
         ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  auto.
qed.

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle :
         ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  auto.
qed.
