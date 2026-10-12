(* MRS_Deny.ec
   MRS-AUTH: Deniability game
   No axioms or admits.
*)

require import AllCore Bool DBool Int IntDiv Real List.
require import MRS_Core.
require import MRS_Distr.
require import MRS_Equiv.
require import MRS_Chain.

module type MRSAdversary = {
  proc guess(chain : int list) : bool
}.

module DenyGame (A : MRSAdversary) = {
  proc main(N depth : int, tri : int list) : bool = {
    var bit : int;
    var b : bool;
    var ch0, ch1, selected : int list;
    var guess : bool;

    bit <$ duniform_int 0 1;
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
