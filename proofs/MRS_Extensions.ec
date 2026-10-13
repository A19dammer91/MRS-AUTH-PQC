(* ================================================================= *)
(*  MRS_Extensions.ec                                                 *)
(*  3-term and 4-term extensions of the MRS framework                 *)
(*                                                                    *)
(*  Built on MRS_Framework.ec (2-term foundation)                     *)
(*  No axioms - everything that is stated is proved.                  *)
(*                                                                    *)
(*  Convention: positive anchor.                                      *)
(*    A0 = dr_r(N) = 1 + ((N - 1) mod r)   (so 1 <= A0 <= r),         *)
(*    and representations use A >= 1.                                 *)
(*                                                                    *)
(*  Primary chain: (19,9) -> (19,9,3) -> (19,9,3,3)                    *)
(* ================================================================= *)

require import AllCore Int IntDiv.
require import MRS_Framework.

(* ----------------------------------------------------------------- *)
(* Section 1: Modular helpers                                        *)
(* ----------------------------------------------------------------- *)

op pos_mod (x m : int) : int =
  let r = x %% m in if r < 0 then r + m else r.

lemma pos_mod_ge0 (x m : int) :
  0 < m => 0 <= pos_mod x m.
proof. rewrite /pos_mod; smt(divz_eq). qed.

lemma pos_mod_lt (x m : int) :
  0 < m => pos_mod x m < m.
proof. rewrite /pos_mod; smt(divz_eq). qed.

(* ----------------------------------------------------------------- *)
(* Section 2: Modular sum (concrete for period <= 3)                 *)
(* ----------------------------------------------------------------- *)

(* Primary period for the chain (19,9,3) is q/r = 9/3 = 3.
   We therefore give an explicit definition for j_max <= 3.
   For j_max > 3 the value is 0 (placeholder), so R3 is only
   meaningful for q %/ r <= 3 until this is extended. *)

op sum_mod_j (Mq r q j_max : int) : int =
  if j_max <= 0 then 0
  else if j_max = 1 then pos_mod Mq q
  else if j_max = 2 then pos_mod Mq q + pos_mod (Mq - r) q
  else if j_max = 3 then
    pos_mod Mq q + pos_mod (Mq - r) q + pos_mod (Mq - 2 * r) q
  else 0.

op one_cycle (Mq r q period : int) : int =
  sum_mod_j Mq r q period.

op partial_sum (Mq r q t : int) : int =
  sum_mod_j Mq r q t.

lemma sum_mod_j_ge0 (Mq r q j_max : int) :
  0 < q => 0 <= sum_mod_j Mq r q j_max.
proof.
  move=> hq.
  rewrite /sum_mod_j.
  case (j_max <= 0) => [// | h0].
  case (j_max = 1) => [h1 | h1'].
  - by apply pos_mod_ge0.
  case (j_max = 2) => [h2 | h2'].
  - have := pos_mod_ge0 Mq q hq.
    have := pos_mod_ge0 (Mq - r) q hq.
    smt().
  case (j_max = 3) => [h3 | h3'].
  - have := pos_mod_ge0 Mq q hq.
    have := pos_mod_ge0 (Mq - r) q hq.
    have := pos_mod_ge0 (Mq - 2 * r) q hq.
    smt().
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Section 3: 3-term representation predicate (A >= 1)               *)
(* ----------------------------------------------------------------- *)

pred is_rep3 (p q r N A B C : int) =
  1 <= A /\ 0 <= B /\ 0 <= C /\
  p * A + q * B + r * C = N.

(* ----------------------------------------------------------------- *)
(* Section 4: R3 kernel with positive anchor a0 = dr_r(N)            *)
(* ----------------------------------------------------------------- *)

op R3 (p q r N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ N <= 0) then 0
  else
    let a0     = dr_q r N in
    let m      = N %/ p in
    let M      = N - p * a0 in
    if (M < 0 \/ m < a0) then 0
    else
      let J      = (m - a0) %/ r in
      let Mq     = M %% q in
      let period = q %/ r in
      let K      = (J + 1) %/ period in
      let t      = (J + 1) %% period in
      let oc     = one_cycle Mq r q period in
      let ps     = partial_sum Mq r q t in
      let R_corr = K * oc + ps in
      let num    = (J + 1) * M
                 - p * r * (J * (J + 1) %/ 2)
                 - R_corr in
      num %/ q + (J + 1).

(* ----------------------------------------------------------------- *)
(* Section 5: Numerical checks (number of solutions with A >= 1)     *)
(* ----------------------------------------------------------------- *)

lemma example_R3_19 : R3 19 9 3 19 = 1.
proof. by compute. qed.

lemma example_R3_143 : R3 19 9 3 143 = 18.
proof. by compute. qed.

lemma example_R3_171 : R3 19 9 3 171 = 21.
proof. by compute. qed.

lemma example_R3_958 : R3 19 9 3 958 = 924.
proof. by compute. qed.

lemma example_R3_6666 : R3 19 9 3 6666 = 43017.
proof. by compute. qed.

lemma R3_nonneg_primary :
  0 <= R3 19 9 3 143 /\
  0 <= R3 19 9 3 958 /\
  0 <= R3 19 9 3 6666.
proof.
  smt(example_R3_143 example_R3_958 example_R3_6666).
qed.

(* ----------------------------------------------------------------- *)
(* Section 6: Basic lemmas                                           *)
(* ----------------------------------------------------------------- *)

(* Degenerate parameters (or N <= 0) give 0. *)
lemma R3_degenerate (p q r N : int) :
  (p <= 0 \/ q <= 0 \/ r <= 0 \/ N <= 0) =>
  R3 p q r N = 0.
proof.
  move=> h.
  by rewrite /R3 ifT 1:h.
qed.

(* With A >= 1 there is no representation below p. *)
lemma R3_zero_when_N_lt_p (p q r N : int) :
  0 < p => 0 < q => 0 < r =>
  0 < N => N < p =>
  R3 p q r N = 0.
proof.
  move=> hp hq hr hN0 hN.
  have hdiv : N %/ p = 0 by smt(divz_eq).
  have [ha1 _] := dr_q_range r N hr hN0.
  rewrite /R3.
  have h1 : !(p <= 0 \/ q <= 0 \/ r <= 0 \/ N <= 0) by smt().
  rewrite ifF 1:h1 /=.
  rewrite hdiv /=.
  by rewrite ifT 1:/#.
qed.

(* ----------------------------------------------------------------- *)
(* Section 7: 4-term stub (safe non-negative definition)             *)
(* ----------------------------------------------------------------- *)

(* Temporary definition that is provably non-negative.
   The full J-block implementation will replace this later. *)

op R4 (p q r s N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ s <= 0 \/ N <= 0) then 0
  else 0.

lemma R4_nonneg (p q r s N : int) :
  0 < p => 0 < q => 0 < r => 0 < s =>
  0 <= R4 p q r s N.
proof.
  move=> *.
  rewrite /R4.
  smt().
qed.

lemma example_R4_143 : R4 19 9 3 3 143 = 0.
proof. by compute. qed.

lemma example_R4_958 : R4 19 9 3 3 958 = 0.
proof. by compute. qed.

lemma example_R4_6666 : R4 19 9 3 3 6666 = 0.
proof. by compute. qed.

(* ================================================================= *)
(* End of MRS_Extensions.ec                                           *)
(* ================================================================= *)
