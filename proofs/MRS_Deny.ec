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
    var b : bool;
    var ch0, ch1, selected : int list;
    var guess : bool;

    (* Uniform challenge bit *)
    b <$ {0, 1};

    (* Independently generated chains *)
    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);

    (* Reveal only the selected chain *)
    if (b) {
      selected <- ch1;
    } else {
      selected <- ch0;
    }

    (* The adversary sees the chain, not b *)
    guess <@ A.guess(selected);

    return (guess = b);
  }
}.
