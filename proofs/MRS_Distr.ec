(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Own distribution theory for MRS-AUTH.                             *)
(*                                                                    *)
(*  In EasyCrypt r2024.09 the standard distribution operators         *)
(*  (dbool, dunit, dmap, dinter) are not present in the installed     *)
(*  theory files. We therefore introduce them as axioms, to be        *)
(*  discharged later when a compatible distribution library is        *)
(*  available.                                                        *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* Axiomatic primitive: a single fair coin *)
op dbool : bool distr.

axiom dbool_support : forall (b : bool), b \in dbool.

(* Axiomatic primitive: the unit distribution *)
op dunit : unit distr.

axiom dunit_support : forall (u : unit), u \in dunit.

(* Axiomatic primitive: map on distributions *)
op dmap : forall 'a 'b, ('a -> 'b) -> 'a distr -> 'b distr.

(* ... en zo verder ... *)

(* Uniform over [0, N] via rejection sampling on bits *)
op duniform (N : int) : int distr.

axiom duniform_support (N x : int) :
  0 <= N => x \in duniform N => 0 <= x <= N.
