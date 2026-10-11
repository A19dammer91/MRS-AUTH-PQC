(* ================================================================= *)
(*  MRS_Distr.ec                                                      *)
(*  Constructive distribution theory for MRS-AUTH.                    *)
(*                                                                    *)
(*  All distributions are defined constructively. No axioms.          *)
(*                                                                    *)
(*  Two layers are exposed:                                           *)
(*    - idistr        : constructive record type for specification    *)
(*    - int distr     : EasyCrypt's built-in type for `<$` sampling   *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.
require import Distr.

(* ================================================================= *)
(* Layer 1: Constructive specification                                *)
(* ================================================================= *)

type idistr = { mass : int -> real }.

op dpoint (n : int) : idistr =
  {| mass = fun x => if x = n then 1%r else 0%r |}.

lemma dpoint_mu_eq (n x : int) :
  (dpoint n).`mass x = if x = n then 1%r else 0%r.
proof. by rewrite /dpoint. qed.

lemma dpoint_mu_ge0 (n x : int) :
  0%r <= (dpoint n).`mass x.
proof.
  rewrite dpoint_mu_eq.
  case (x = n) => [_ | _]; smt().
qed.

op dconvex (p : real) (d1 d2 : idistr) : idistr =
  {| mass = fun x => p * d1.`mass x + (1%r - p) * d2.`mass x |}.

lemma dconvex_mu (p : real) (d1 d2 : idistr) (x : int) :
  (dconvex p d1 d2).`mass x = p * d1.`mass x + (1%r - p) * d2.`mass x.
proof. by rewrite /dconvex. qed.

lemma dconvex_mu_ge0 (p : real) (d1 d2 : idistr) (x : int) :
  0%r <= p => p <= 1%r =>
  0%r <= d1.`mass x => 0%r <= d2.`mass x =>
  0%r <= (dconvex p d1 d2).`mass x.
proof.
  move=> hp0 hp1 hd1 hd2.
  rewrite dconvex_mu.
  have h1 : 0%r <= p * d1.`mass x by smt().
  have h2 : 0%r <= (1%r - p) * d2.`mass x by smt().
  smt().
qed.

op duniform (N : int) : idistr =
  if N < 0 then dpoint 0
  else
    {| mass = fun x =>
         if (0 <= x /\ x <= N) then 1%r / (N + 1)%r
         else 0%r |}.

lemma duniform_mu_eq (N x : int) :
  0 <= N =>
  (duniform N).`mass x =
    (if (0 <= x /\ x <= N) then 1%r / (N + 1)%r else 0%r).
proof.
  move=> hN.
  rewrite /duniform.
  have h : ! (N < 0) by smt().
  by rewrite h.
qed.

lemma duniform_mu_eq_neg (N x : int) :
  N < 0 => (duniform N).`mass x = (dpoint 0).`mass x.
proof.
  move=> hN.
  rewrite /duniform.
  by rewrite hN.
qed.

lemma duniform_mu_zero (N x : int) :
  0 <= N =>
  (x < 0 \/ N < x) =>
  (duniform N).`mass x = 0%r.
proof.
  move=> hN hx.
  rewrite duniform_mu_eq //.
  have h : ! (0 <= x /\ x <= N) by smt().
  by rewrite h.
qed.

lemma duniform_mu_pos (N x : int) :
  0 <= N =>
  0 <= x <= N =>
  (duniform N).`mass x > 0%r.
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
  (duniform N).`mass x = (duniform N).`mass y.
proof.
  move=> hN hx hy.
  rewrite duniform_mu_eq //.
  rewrite duniform_mu_eq //.
  have hx' : (0 <= x /\ x <= N) by smt().
  have hy' : (0 <= y /\ y <= N) by smt().
  by rewrite hx' hy'.
qed.

lemma duniform_total_mass_aux (N : int) :
  0 <= N =>
  (N + 1)%r * (1%r / (N + 1)%r) = 1%r.
proof.
  move=> hN.
  have hNp1_ne : (N + 1)%r <> 0%r by smt().
  field; smt().
qed.

op mu (d : idistr) (x : int) : real = d.`mass x.

lemma mu_dpoint (n x : int) :
  mu (dpoint n) x = if x = n then 1%r else 0%r.
proof. by rewrite /mu /dpoint. qed.

lemma mu_duniform (N x : int) :
  0 <= N =>
  mu (duniform N) x =
    (if (0 <= x /\ x <= N) then 1%r / (N + 1)%r else 0%r).
proof.
  move=> hN.
  rewrite /mu.
  by apply duniform_mu_eq.
qed.

(* ================================================================= *)
(* Layer 2: Bridge to EasyCrypt's built-in `int distr`                *)
(* ================================================================= *)

op duniform_int (N : int) : int distr = duniform N.

op dpoint_int (n : int) : int distr = dunit n.
