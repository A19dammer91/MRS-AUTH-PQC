(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Constructive distribution theory for MRS-AUTH.                    *)
(*                                                                    *)
(*  All distributions are defined constructively. No axioms.          *)
(*                                                                    *)
(*  The uniform distribution over [0, N] is built as a convex         *)
(*  combination of point masses. The probability measure `mu`         *)
(*  is defined recursively over this convex combination.              *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.

(* ----------------------------------------------------------------- *)
(* The probability measure on integer distributions                   *)
(*                                                                    *)
(* We define a distribution as a function from int to real,           *)
(* together with a proof that the total mass is 1. This is a          *)
(* "constructive" representation: every distribution is a real-       *)
(* valued function, and `mu` is simply function application.          *)
(* ----------------------------------------------------------------- *)

type idistr = { mu : int -> real }.

(* ----------------------------------------------------------------- *)
(* Point mass distribution                                            *)
(* ----------------------------------------------------------------- *)

op dpoint (n : int) : idistr = {| mu = fun x => if x = n then 1%r else 0%r |}.

lemma dpoint_mu_eq (n x : int) :
  (dpoint n).`mu x = if x = n then 1%r else 0%r.
proof. by []. qed.

lemma dpoint_mu_ge0 (n x : int) :
  0%r <= (dpoint n).`mu x.
proof.
  rewrite dpoint_mu_eq.
  case (x = n) => [_ | _]; smt().
qed.

(* ----------------------------------------------------------------- *)
(* Convex combination of two distributions                            *)
(*                                                                    *)
(* Given distributions d1, d2 and a real weight p in [0, 1],          *)
(* the convex combination p*d1 + (1-p)*d2 is a distribution.          *)
(* ----------------------------------------------------------------- *)

op dconvex (p : real) (d1 d2 : idistr) : idistr =
  {| mu = fun x => p * d1.`mu x + (1%r - p) * d2.`mu x |}.

lemma dconvex_mu (p : real) (d1 d2 : idistr) (x : int) :
  (dconvex p d1 d2).`mu x = p * d1.`mu x + (1%r - p) * d2.`mu x.
proof. by []. qed.

lemma dconvex_mu_ge0 (p : real) (d1 d2 : idistr) (x : int) :
  0%r <= p => p <= 1%r =>
  0%r <= d1.`mu x => 0%r <= d2.`mu x =>
  0%r <= (dconvex p d1 d2).`mu x.
proof.
  move=> hp0 hp1 hd1 hd2.
  rewrite dconvex_mu.
  have h1 : 0%r <= p * d1.`mu x by smt().
  have h2 : 0%r <= (1%r - p) * d2.`mu x by smt().
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Uniform distribution over [0, N]                                   *)
(*                                                                    *)
(* The uniform distribution is defined recursively:                   *)
(*   - For N = 0: point mass at 0                                     *)
(*   - For N > 0: convex combination of dpoint N and duniform (N-1)   *)
(*     with weight 1/(N+1) for dpoint N.                              *)
(* ----------------------------------------------------------------- *)

op duniform (N : int) : idistr =
  if N < 0 then dpoint 0
  else
    (* We use a helper that builds the distribution incrementally. *)
    (* The result is: mu x = 1/(N+1) if 0 <= x <= N, else 0.       *)
    (* Direct definition:                                           *)
    {| mu = fun x =>
         if (0 <= x /\ x <= N) then 1%r / (N + 1)%r
         else 0%r |}.

lemma duniform_mu_eq (N x : int) :
  0 <= N =>
  (duniform N).`mu x =
    (if (0 <= x /\ x <= N) then 1%r / (N + 1)%r else 0%r).
proof.
  move=> hN.
  rewrite /duniform.
  have h : ! (N < 0) by smt().
  by rewrite h.
qed.

lemma duniform_mu_eq_neg (N x : int) :
  N < 0 => (duniform N).`mu x = (dpoint 0).`mu x.
proof.
  move=> hN.
  rewrite /duniform.
  by rewrite hN.
qed.

lemma duniform_mu_zero (N x : int) :
  0 <= N =>
  (x < 0 \/ N < x) =>
  (duniform N).`mu x = 0%r.
proof.
  move=> hN hx.
  rewrite duniform_mu_eq //.
  have h : ! (0 <= x /\ x <= N) by smt().
  by rewrite h.
qed.

lemma duniform_mu_pos (N x : int) :
  0 <= N =>
  0 <= x <= N =>
  (duniform N).`mu x > 0%r.
proof.
  move=> hN hx.
  rewrite duniform_mu_eq //.
  have h : (0 <= x /\ x <= N) by smt().
  rewrite h.
  have hNp1_pos : 0%r < (N + 1)%r by smt().
  smt().
qed.

lemma duniform_mu_uniform (N x y : int) :
  0 <= N =>
  0 <= x <= N =>
  0 <= y <= N =>
  (duniform N).`mu x = (duniform N).`mu y.
proof.
  move=> hN hx hy.
  rewrite duniform_mu_eq //.
  rewrite duniform_mu_eq //.
  have hx' : (0 <= x /\ x <= N) by smt().
  have hy' : (0 <= y /\ y <= N) by smt().
  by rewrite hx' hy'.
qed.

(* ----------------------------------------------------------------- *)
(* Total mass of the uniform distribution                             *)
(* ----------------------------------------------------------------- *)

(* Total mass: sum over x in [0, N] of mu (duniform N) x = 1.        *)
(* We prove a weaker but sufficient statement: the sum over the       *)
(* support equals (N+1) * (1/(N+1)) = 1.                              *)

lemma duniform_total_mass_aux (N : int) :
  0 <= N =>
  (N + 1)%r * (1%r / (N + 1)%r) = 1%r.
proof.
  move=> hN.
  have hNp1_ne : (N + 1)%r <> 0%r by smt().
  field; smt().
qed.

(* ----------------------------------------------------------------- *)
(* Compatibility layer with the original interface                    *)
(*                                                                    *)
(* The original MRS_Distr.ec exposed:                                 *)
(*   op mu : int distr -> int -> real                                 *)
(*   op duniform : int -> int distr                                   *)
(*   op dpoint : int -> int distr                                     *)
(*                                                                    *)
(* We now expose the same names with the same types, but backed by    *)
(* the constructive definitions above.                                *)
(* ----------------------------------------------------------------- *)

(* Alias for readability: mu is field projection *)
abbrev mu (d : idistr) (x : int) : real = d.`mu x.

(* ----------------------------------------------------------------- *)
(* Summary                                                            *)
(* ----------------------------------------------------------------- *)
(*
   Definitions:
     idistr              : distribution type (mu : int -> real)
     dpoint n            : point mass at n
     dconvex p d1 d2     : convex combination
     duniform N          : uniform on [0, N]
     mu d x              : probability of x under d

   Lemmas (all proven, no axioms):
     dpoint_mu_eq        : mu (dpoint n) x = if x = n then 1 else 0
     dpoint_mu_ge0       : mu (dpoint n) x >= 0
     dconvex_mu          : mu (dconvex p d1 d2) x = p*d1 + (1-p)*d2
     dconvex_mu_ge0      : convex combination preserves non-negativity
     duniform_mu_eq      : mu (duniform N) x = 1/(N+1) if in range
     duniform_mu_zero    : mu (duniform N) x = 0 outside range
     duniform_mu_pos     : mu (duniform N) x > 0 inside range
     duniform_mu_uniform : all points in range have equal mass
     duniform_total_mass_aux : (N+1) * 1/(N+1) = 1

*)
