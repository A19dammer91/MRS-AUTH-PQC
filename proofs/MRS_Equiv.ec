(* ================================================================= *)
(*  MRS_Equiv.ec                                                      *)
(*  Equivalence lemmas for the MRS samplers                           *)
(*                                                                    *)
(*  Following the canonical EasyCrypt r2024.09 form for equivalence   *)
(*  of two procedures, the precondition includes the equality of      *)
(*  the global states of the modules involved.                        *)
(*                                                                    *)
(*  Axiom baseline: 0 if proved, 2 if axiomatised.                    *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

(* ================================================================= *)
(* Section 1: Equivalence of sample_basic with itself                 *)
(* ================================================================= *)

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic :
         ={arg} /\ ={glob MRSRep} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 1 1 : (={kvl}).
  - rnd (fun x => x) (fun x => x).
    skip => /=.
    move=> &1 &2 H.
    by [].
  - skip => /=.
    move=> &1 &2 H.
    have hk : kvl{1} = kvl{2} by smt().
    rewrite hk.
    by [].
qed.

(* ================================================================= *)
(* Section 2: Equivalence of sample_triangle with itself              *)
(* ================================================================= *)

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle :
         ={arg} /\ ={glob MRSRep} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 4 4 : (={anc, bcp, kbn, tmx}).
  - auto.
  seq 1 1 : (={ndx, anc, bcp, kbn, tmx}).
  - rnd (fun x => x) (fun x => x).
    skip => /=.
    move=> &1 &2 H.
    by [].
  - seq 1 1 : (={kvl, ndx, anc, bcp, kbn, tmx}).
    + auto.
    + skip => /=.
      move=> &1 &2 H.
      have hk : kvl{1} = kvl{2} by smt().
      rewrite hk.
      by [].
qed.

(* ================================================================= *)
(* End of MRS_Equiv.ec                                                *)
(* ================================================================= *)
