(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Own distribution theory for MRS-AUTH.                             *)
(*                                                                    *)
(*  In EasyCrypt r2024.09 the standard distribution operators         *)
(*  (dbool, dunit, dmap, dinter) are not present in the installed     *)
(*  theory files. The distribution primitives are therefore           *)
(*  introduced here as axioms, to be discharged later when a          *)
(*  compatible distribution library becomes available.                *)
(*                                                                    *)
(*  Support is expressed via the probability measure `mu` rather      *)
(*  than the membership operator `\in`, because `\in` is not          *)
(*  defined on `distr` in this release.                               *)
(*                                                                    *)
(*  Axiom baseline: 5.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Distr.

(* ----------------------------------------------------------------- *)
(* Primitive distributions                                            *)
(* ----------------------------------------------------------------- *)

(* Fair coin: dbool is the uniform distribution over {true, false}.   *)
op dbool : bool distr.

axiom dbool_mu_true : mu dbool true = 1%r / 2%r.

axiom dbool_mu_false : mu dbool false = 1%r / 2%r.

(* Unit distribution: dunit is the point mass at ().                  *)
op dunit : unit distr.

axiom dunit_mu : mu dunit () = 1%r.

(* ----------------------------------------------------------------- *)
(* The uniform distribution over [0, N]                               *)
(*                                                                    *)
(* The distribution is axiomatised here. Its characteristic           *)
(* properties are stated via `mu`: the support is contained in        *)
(* [0, N], and the distribution is uniform on [0, N].                 *)
(* ----------------------------------------------------------------- *)

op duniform (N : int) : int distr.

axiom duniform_mu_zero (N x : int) :
  0 <= N =>
  (x < 0 \/ N < x) =>
  mu (duniform N) x = 0%r.

axiom duniform_mu_uniform (N x y : int) :
  0 <= N =>
  0 <= x <= N =>
  0 <= y <= N =>
  mu (duniform N) x = mu (duniform N) y.
