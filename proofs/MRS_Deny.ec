(* ================================================================= *)
(* MRS_Deny.ec                                                        *)
(* MRS-AUTH: Deniability Experiment                                   *)
(*                                                                     *)
(* Uses the project's constructive distribution and chain modules.     *)
(* No axioms or admits are introduced in this file.                    *)
(*                                                                     *)
(* Security target:                                                    *)
(* Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r         *)
(* This target requires a separate formal proof.                       *)
(* ================================================================= *)

require import AllCore Bool Int IntDiv List.
require import MRS_Core.
require import MRS_Distr.
require import MRS_Equiv.
require import MRS_Chain.

(* ================================================================= *)
(* Adversary interface                                                *)
(* ================================================================= *)

module type MRSAdversary = {
  proc guess(chain : int list) : bool
}.

(* ================================================================= *)
(* Deniability experiment                                             *)
(*                                                                     *)
(* 1. Sample an integer uniformly from {0, 1}.                         *)
(* 2. Generate two independent chains.                                 *)
(* 3. Select one chain using the secret bit.                           *)
(* 4. Give only the selected chain to the adversary.                   *)
(* 5. Return whether the adversary guessed the bit correctly.          *)
(* ================================================================= *)

module DenyGame (A : MRSAdversary) = {
  proc main(N depth : int, tri : int list) : bool = {
    var bit : int;
    var b : bool;
    var ch0, ch1 : int list;
    var selected : int list;
    var guess : bool;

    bit <$ duniform_int 1;
    b <- (bit = 1);

    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);

    if (b) {
      selected <- ch1;
    } else {
      selected <- ch0;
    }

    guess <@ A.guess(selected);

    return (guess = b);
  }
}.
