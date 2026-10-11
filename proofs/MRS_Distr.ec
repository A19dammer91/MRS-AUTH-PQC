(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Axiomatic distribution theory for MRS-AUTH.                       *)
(*                                                                    *)
(*  In EasyCrypt r2024.09 the standard distribution operators are     *)
(*  not present in the installed theory files, but the distribution   *)
(*  type `int Pervasive.distr` IS available. We therefore use the     *)
(*  built-in type and axiomatise the missing operators `mu`,          *)
(*  `duniform`, and `dpoint`.                                         *)
(*                                                                    *)
(*  Axiom baseline: 5.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.
require import Pervasive.

(* ----------------------------------------------------------------- *)
(* The probability measure on integer distributions                   *)
(*                                                                    *)
(* The built-in type `int Pervasive.distr` is used directly; we only  *)
(* axiomatise the probability measure `mu` and the two distributions  *)
(* `duniform` and `dpoint`, which are not present in r2024.09.        *)
(* ----------------------------------------------------------------- *)

op mu : int distr -> int -> real.

(* ----------------------------------------------------------------- *)
(* Basic property of the probability measure                          *)
(* ----------------------------------------------------------------- *)

axiom mu_ge0 : forall (d : int distr) (x : int), 0%r <= mu d x.

(* ----------------------------------------------------------------- *)
(* The uniform distribution over the closed interval [0, N]           *)
(* ----------------------------------------------------------------- *)

op duniform (N : int) : int distr.

axiom duniform_mu_zero (N x : int) :
  0 <= N =>
  (x < 0 \/ N < x) =>
  mu (duniform N) x = 0%r.

axiom duniform_mu_pos (N x : int) :
  0 <= N =>
  0 <= x <= N =>
  mu (duniform N) x > 0%r.

axiom duniform_mu_uniform (N x y : int) :
  0 <= N =>
  0 <= x <= N =>
  0 <= y <= N =>
  mu (duniform N) x = mu (duniform N) y.

(* ----------------------------------------------------------------- *)
(* The point mass distribution                                        *)
(* ----------------------------------------------------------------- *)

op dpoint (n : int) : int distr.

axiom dpoint_mu_eq (n x : int) :
  mu (dpoint n) x = if x = n then 1%r else 0%r.
