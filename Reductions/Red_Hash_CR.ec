require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import Hash.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H3_Ballot.
require import H4_Tally.

module ReduceH3H4_to_Hash_CR(A : PCR_REAL_ADV) : HASH_CR_ADV = {
  proc find_collision() : hash_input * hash_input = {
    return ([], []);
  }
}.

lemma red_hash_cr_advantage (lambda : int) :
  exists (delta_h : real),
    0%r <= delta_h /\ delta_h <= advantage_Hash_cr lambda.
proof.
admit.
qed.
