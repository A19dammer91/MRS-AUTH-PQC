(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Axiomatic distribution theory for MRS-AUTH.                       *)
(*                                                                    *)
(*  In EasyCrypt r2024.09 the standard distribution operators         *)
(*  are not present in the installed theory files. The theory is      *)
(*  therefore introduced here entirely axiomatically.                 *)
(*                                                                    *)
(*  To avoid the limitations of EasyCrypt's type system, the type     *)
(*  `distr` is not parametrised: all distributions are over `int`.    *)
(*  This is sufficient for the MRS sampling procedures, which only    *)
(*  sample integers.                                                  *)
(*                                                                    *)
(*  Axiom baseline: 6.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.

(* ----------------------------------------------------------------- *)
(* Distributions over integers and their probability measure         *)
(* ----------------------------------------------------------------- *)

type distr.

op mu : distr -> int -> real.

(* ----------------------------------------------------------------- *)
(* Basic property of the probability measure                          *)
(*                                                                    *)
(* The measure is non-negative. This is the only property of `mu`     *)
(* that is directly required by the MRS correctness proofs: they use  *)
(* it to distinguish values in the support (mu > 0) from values out   *)
(* of the support (mu = 0).                                           *)
(* ----------------------------------------------------------------- *)

axiom mu_ge0 : forall (d : distr) (x : int), 0%r <= mu d x.

(* ----------------------------------------------------------------- *)
(* The uniform distribution over the closed interval [0, N]           *)
(*                                                                    *)
(* duniform N is the uniform distribution over {0, 1, ..., N}. Its    *)
(* three characteristic properties are:                               *)
(*                                                                    *)
(*   - mu (duniform N) x = 0 when x is outside [0, N],                *)
(*   - mu (duniform N) x > 0 when x is inside [0, N],                 *)
(*   - mu (duniform N) x = mu (duniform N) y for any two points       *)
(*     x, y in [0, N].                                                *)
(*                                                                    *)
(* The first property is used to exclude invalid samples. The second  *)
(* is used to establish that the sampling covers the entire interval. *)
(* The third is used when reasoning about the shape of the sampling.  *)
(* ----------------------------------------------------------------- *)

op duniform (N : int) : distr.

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
(*                                                                    *)
(* dpoint n is the distribution that returns n with probability 1.    *)
(* Used by the degenerate branch of sample_triangle. Its two          *)
(* characteristic properties are: the mass at n is 1, and the mass    *)
(* at any other point is 0.                                           *)
(* ----------------------------------------------------------------- *)

op dpoint (n : int) : distr.

axiom dpoint_mu_eq (n x : int) :
  mu (dpoint n) x = if x = n then 1%r else 0%r.
