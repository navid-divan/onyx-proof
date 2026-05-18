require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import UT.
require import MixNet.
require import Hash.
require import VotingScheme.
require import Policy.
require import PCR.
require import Onyx.
require import H3_Ballot.

module Hybrid_H4(A : PCR_REAL_ADV) = {
  var bb : election_bb
  var st : pcr_state_map
  var disc : int fset
  var beta_bit : bool
  var pk_v : election_pk
  var shares_v : (election_sk_share * election_hint) list
  var creds : election_credential list
  var reg_R : election_register_record
  var corrupt_D : int fset
  var coerce_H : int fset
  var alphas : (int, int) fmap

  proc simulated_tally(plaintext_board : behavior_list) :
    election_result * election_tally_proof = {
    var r : election_result;
    var pi : election_tally_proof;
    var sort_sim_pf : ut_partial_eval list;
    var shuf_sim_pf : mixnet_proof;
    var ddec_sim_pfs : (mixnet_partial list * mixnet_ddec) list;

    sort_sim_pf <- [];
    shuf_sim_pf <- witness;
    ddec_sim_pfs <- [];
    r <- result_func (policy_func (cleanse_func plaintext_board));
    pi <- witness;
    return (r, pi);
  }

  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

lemma hybrid_H3_H4_bound (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H3(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H4(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= advantage_UT_sim lambda_sec
   + advantage_MixNet_shuf lambda_sec
   + (n_T)%r * advantage_MixNet_ddec lambda_sec
   + advantage_Hash_cr lambda_sec.
proof.
admit.
qed.
