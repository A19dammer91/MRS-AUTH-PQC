pred is_rep (N A B : int) =
  1 <= A /\ 0 <= B /\ 19*A + 9*B = N.

lemma test (N A B : int) :
  is_rep N A B => 1 <= A.
proof.
  move=> hrep.
  rewrite /is_rep in hrep.
  smt().
qed.
