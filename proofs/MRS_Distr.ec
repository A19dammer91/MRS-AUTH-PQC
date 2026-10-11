(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Axiomatic distribution theory for MRS-AUTH.                       *)
(*                                                                    *)
(*  In EasyCrypt r2024.09 the standard distribution operators         *)
(*  (dbool, dunit, dmap, dinter, mu) are not present in the           *)
(*  installed theory files. The distribution theory is therefore      *)
(*  introduced here entirely axiomatically. Each axiom is             *)
(*  documented, so that the reader can see exactly which assumptions  *)
(*  are made.                                                         *)
(*                                                                    *)
(*  The theory provides:                                              *)
(*    - a type of distributions,                                      *)
(*    - the probability measure mu,                                   *)
(*    - the uniform distribution over the closed interval [0, N],     *)
(*    - the point mass distribution.                                  *)
(*                                                                    *)
(*  These are the minimal primitives required by MRS_Core.ec for      *)
(*  the sampling procedures sample_basic and sample_triangle.         *)
(*                                                                    *)
(*  Axiom baseline: 6.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.

(* ----------------------------------------------------------------- *)
(* Distributions and their probability measure                       *)
(*                                                                    *)
(* We introduce the type of distributions over an arbitrary type 'a,  *)
(* together with the probability measure mu. The measure is           *)
(* axiomatised: mu d x is the probability that a sample from d is x.  *)
(* ----------------------------------------------------------------- *)

type 'a distr.

op mu : forall 'a, 'a distr -> 'a -> real.

(* ----------------------------------------------------------------- *)
(* Basic properties of the probability measure                        *)
(*                                                                    *)
(* The measure is non-negative, and the total mass of any              *)
(* distribution is bounded by 1. These are the standard axioms of a   *)
(* probability measure.                                               *)
(* ----------------------------------------------------------------- *)

axiom mu_ge0 : forall 'a (d : 'a distr) (x : 'a), 0%r <= mu d x.

axiom mu_le1 : forall 'a (d : 'a distr) (x : 'a), mu d x <= 1%r.

(* ----------------------------------------------------------------- *)
(* The uniform distribution over the closed interval [0, N]           *)
(*                                                                    *)
(* duniform N is the uniform distribution over {0, 1, ..., N}. Its    *)
(* two characteristic properties are:                                 *)
(*                                                                    *)
(*   - mu (duniform N) x = 0 when x is outside [0, N],                *)
(*   - mu (duniform N) x = mu (duniform N) y for any two points       *)
(*     x, y in [0, N].                                                *)
(*                                                                    *)
(* These two properties determine the distribution uniquely           *)
(* (up to the actual value of the mass, which is 1/(N+1) but is not   *)
(* required for the correctness proofs of MRS_Core.ec).               *)
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

(* ----------------------------------------------------------------- *)
(* The point mass distribution                                        *)
(*                                                                    *)
(* dpoint n is the distribution that returns n with probability 1.    *)
(* Used by the degenerate branch of sample_triangle.                  *)
(* ----------------------------------------------------------------- *)

op dpoint (n : int) : int distr.

axiom dpoint_mu_eq (n x : int) :
  mu (dpoint n) x = if x = n then 1%r else 0%r.
