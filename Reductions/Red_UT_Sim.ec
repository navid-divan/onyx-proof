require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import UT.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H3_Ballot.
require import H4_Tally.

module ReduceH3H4_to_UT_Sim(A : PCR_REAL_ADV) : UT_ADV = {
  proc choose_input(pp : ut_pp) : ut_input = {
    return [];
  }
  proc corrupt(pp : ut_pp) : int fset = {
    return fset0;
  }
  proc choose_circuit() : ut_circuit = {
    return witness;
  }
  proc guess(eval_list : ut_partial_eval list) : bool = {
    return false;
  }
}.

lemma red_ut_sim_advantage (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  exists (UT_term MIX_term DDEC_term HASH_term : real),
    `| Pr[Hybrid_H3(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
     - Pr[Hybrid_H4(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
    <= advantage_UT_sim lambda
     + advantage_MixNet_shuf lambda
     + (n_T)%r * advantage_MixNet_ddec lambda
     + advantage_Hash_cr lambda.
proof.
admit.
qed.
