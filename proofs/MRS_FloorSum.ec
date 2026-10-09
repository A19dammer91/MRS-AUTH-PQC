(* ================================================================= *)
(*  MRS_FloorSum.ec                                                   *)
(*  The floor sum at the heart of the weighted CDF sampler.           *)
(*                                                                    *)
(*  The Rust implementation (src/sampler/cdf_sampler.rs) computes:    *)
(*                                                                    *)
(*    floor_sum_ct(n, m, a, b) = sum_{i=0}^{n-1} floor((a*i + b)/m)   *)
(*                                                                    *)
(*  using a fixed 64-iteration AtCoder shift-and-add loop. Here we    *)
(*  specify its value as an ordinary sum and prove the properties     *)
(*  that MRS_Sampler.ec needs: monotonicity in the range and in the   *)
(*  offset, non-negativity on non-negative arguments, and positivity  *)
(*  on the valid range.                                               *)
(*                                                                    *)
(*  The AtCoder shift-and-add reduction used by the Rust              *)
(*  implementation is not modelled here. Its correctness is           *)
(*  established by the unit tests in cdf_sampler.rs; the fact that    *)
(*  it computes the same value as the plain sum below is a            *)
(*  functional specification, not a formal refinement claim.          *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.
require import StdOrder StdBigop.
import IntOrder RealOrder.

(* ================================================================= *)
(* Definition                                                         *)
(* ================================================================= *)

op floor_sum (n m a b : int) : int =
  bigi predT (fun i => (a * i + b) %/ m) 0 n.

(* ================================================================= *)
(* Basic properties                                                   *)
(* ================================================================= *)

lemma floor_sum_zero_upper (m a b : int) :
  floor_sum 0 m a b = 0.
proof. by rewrite /floor_sum. qed.

lemma floor_sum_step (n m a b : int) :
  0 <= n =>
  floor_sum (n + 1) m a b = floor_sum n m a b + (a * n + b) %/ m.
proof.
  move=> hn.
  rewrite /floor_sum.
  have h := bigiD predT (fun i => (a * i + b) %/ m) 0 n 1.
  have h' : bigi predT (fun i => (a * i + b) %/ m) n (n + 1)
          = (a * n + b) %/ m.
    have -> : bigi predT (fun i => (a * i + b) %/ m) n (n + 1)
            = bigi predT (fun i => (a * i + b) %/ m) n n
              + (if predT n then (a * n + b) %/ m else 0).
      by apply bigi_rec.
    rewrite bigi_empt //.
  smt.
qed.

(* ================================================================= *)
(* Monotonicity in b                                                  *)
(* ================================================================= *)

lemma floor_sum_monotone_b (n m a b1 b2 : int) :
  0 <= n => 0 < m => b1 <= b2 =>
  floor_sum n m a b1 <= floor_sum n m a b2.
proof.
  move=> hn hm hle.
  rewrite /floor_sum.
  apply bigi_monotone.
  move=> i hi.
  apply divz_monotone_le => //.
  smt.
qed.

(* ================================================================= *)
(* Monotonicity in n, for non-negative arguments                      *)
(* ================================================================= *)

lemma floor_sum_monotone_n (n1 n2 m a b : int) :
  0 <= n1 => n1 <= n2 =>
  0 < m => 0 <= a => 0 <= b =>
  floor_sum n1 m a b <= floor_sum n2 m a b.
proof.
  move=> hn1 hle hm ha hb.
  move: hle. move: n2.
  elim/(well_founded_ind _) => n2 ih hle.
  case (n2 = n1) => [heq | hne].
  - by rewrite heq.
  - have hlt : n1 < n2 by smt.
    have hn2 : 1 <= n2 by smt.
    have hn1' : 0 <= n2 - 1 by smt.
    have hrec := ih (n2 - 1) _ (by smt).
    have hstep := floor_sum_step (n2 - 1) m a b hn1'.
    have hterm : 0 <= (a * (n2 - 1) + b) %/ m.
      apply divz_ge0 => //; smt.
    smt.
qed.

(* ================================================================= *)
(* Non-negativity                                                     *)
(* ================================================================= *)

lemma floor_sum_nonneg (n m a b : int) :
  0 <= n => 0 < m => 0 <= a => 0 <= b =>
  0 <= floor_sum n m a b.
proof.
  move=> hn hm ha hb.
  rewrite /floor_sum.
  apply bigi_nonneg.
  move=> i hi.
  apply divz_ge0 => //; smt.
qed.

(* ================================================================= *)
(* Positivity of the first term                                       *)
(* ================================================================= *)

lemma floor_sum_first_term_pos (m a b : int) :
  0 < m => 0 <= a => b >= m =>
  1 <= floor_sum 1 m a b.
proof.
  move=> hm ha hb.
  rewrite (floor_sum_step 0 m a b _).
  - by rewrite floor_sum_zero_upper /=.
  - by smt.
qed.

(* ================================================================= *)
(* Prefix weight                                                      *)
(* ================================================================= *)
(*                                                                   *)
(* The prefix_weight function used by the sampler is:                 *)
(*                                                                    *)
(*   prefix_weight(t_filter, t, t_max, e_prime) =                     *)
(*     if t < t_filter then 0                                         *)
(*     else                                                           *)
(*       let end_t = min(t, t_max) in                                 *)
(*       let n = end_t - t_filter + 1 in                              *)
(*       floor_sum(n, 171, 9, e_prime) + n                            *)
(*                                                                    *)
(* The "+ n" accounts for the "+ 1" that every weight term has        *)
(* (1 + floor((9*i + e_prime)/171)); see weight_params_ct in          *)
(* cdf_sampler.rs.                                                    *)
(* ================================================================= *)

op prefix_weight (t_filter t t_max e_prime : int) : int =
  if t < t_filter then 0
  else
    let end_t = if t > t_max then t_max else t in
    let n = end_t - t_filter + 1 in
    floor_sum n 171 9 e_prime + n.

(* ----------------------------------------------------------------- *)
(* Zero before t_filter                                               *)
(* ----------------------------------------------------------------- *)

lemma prefix_weight_zero_before
    (t_filter t t_max e_prime : int) :
  t < t_filter => prefix_weight t_filter t t_max e_prime = 0.
proof.
  move=> hlt.
  by rewrite /prefix_weight hlt.
qed.

(* ----------------------------------------------------------------- *)
(* Monotonicity in t                                                  *)
(* ----------------------------------------------------------------- *)

lemma prefix_weight_monotone
    (t_filter t1 t2 t_max e_prime : int) :
  t_filter <= t1 => t1 <= t2 => t2 <= t_max =>
  prefix_weight t_filter t1 t_max e_prime
    <= prefix_weight t_filter t2 t_max e_prime.
proof.
  move=> h1 h12 h2max.
  case (t1 < t_filter) => [hlt1 | hge1].
  - have hzero : prefix_weight t_filter t1 t_max e_prime = 0.
      by apply prefix_weight_zero_before.
    have hnonneg : 0 <= prefix_weight t_filter t2 t_max e_prime.
      case (t2 < t_filter) => [hlt2 | hge2].
      + by rewrite (prefix_weight_zero_before _ _ _ _ hlt2).
      + rewrite /prefix_weight.
        have hnot : ! (t2 < t_filter) by smt.
        rewrite hnot /=.
        have hn : 0 <= (if t2 > t_max then t_max else t2) - t_filter + 1 by smt.
        have hfs : 0 <= floor_sum
                     ((if t2 > t_max then t_max else t2) - t_filter + 1)
                     171 9 e_prime.
          apply floor_sum_nonneg => //; smt.
        smt.
    smt.
  - have hge2 : t_filter <= t2 by smt.
    rewrite /prefix_weight.
    have h1' : ! (t1 < t_filter) by smt.
    have h2' : ! (t2 < t_filter) by smt.
    rewrite h1' h2' /=.
    have hmin : (if t1 > t_max then t_max else t1)
              <= (if t2 > t_max then t_max else t2) by smt.
    have hn1 : 0 <= (if t1 > t_max then t_max else t1) - t_filter + 1 by smt.
    have hn2 : (if t1 > t_max then t_max else t1) - t_filter + 1
             <= (if t2 > t_max then t_max else t2) - t_filter + 1 by smt.
    have hfs := floor_sum_monotone_n
      ((if t1 > t_max then t_max else t1) - t_filter + 1)
      ((if t2 > t_max then t_max else t2) - t_filter + 1)
      171 9 e_prime hn1 hn2 _ _ _.
    + by done.
    + by done.
    + by done.
    smt.
qed.

(* ----------------------------------------------------------------- *)
(* Positivity on the valid range                                      *)
(* ----------------------------------------------------------------- *)

lemma prefix_weight_positive
    (t_filter t t_max e_prime : int) :
  t_filter <= t => t <= t_max => 171 <= e_prime =>
  0 < prefix_weight t_filter t t_max e_prime.
proof.
  move=> h1 h2 he.
  rewrite /prefix_weight.
  have hnot : ! (t < t_filter) by smt.
  rewrite hnot /=.
  have hmin : (if t > t_max then t_max else t) = t by smt.
  rewrite hmin.
  have hn : 1 <= t - t_filter + 1 by smt.
  have hfloor : 1 <= floor_sum (t - t_filter + 1) 171 9 e_prime.
    have hrec := floor_sum_step (t - t_filter) 171 9 e_prime.
    have hnn : 0 <= t - t_filter by smt.
    rewrite (hrec hnn).
    have hterm : 1 <= (9 * (t - t_filter) + e_prime) %/ 171.
      apply divz_ge1 => //; linarith.
    have htail : 0 <= floor_sum (t - t_filter) 171 9 e_prime.
      apply floor_sum_nonneg => //; smt.
    linarith.
  linarith.
qed.

(* ================================================================= *)
(* End of MRS_FloorSum.ec                                             *)
(* ================================================================= *)
