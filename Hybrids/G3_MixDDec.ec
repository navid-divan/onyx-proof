require import AllCore Distr Real List FSet FMap Bool DBool.
require import Preamble.
require import Negligible.
require import DFHE.
require import NIZK.
require import UT.
require import MixNet.
require import Hash.
require import VotingScheme.
require import Policy.
require import PCR.
require import Onyx.
require import G1_UT.
require import G2_MixShuf.

module G3_MixDDec(A : PCR_REAL_ADV) = {
  var bb : election_bb
  var st : pcr_state_map
  var disc : int fset
  var beta_bit : bool
  var pk_v : election_pk
  var shares_v : (election_sk_share * election_hint_t) list
  var creds : election_credential list
  var reg_R : election_register_record
  var corrupt_D : int fset
  var coerce_H : int fset
  var alphas : (int, int) fmap
  var ut_sim_pp : ut_pp
  var ut_sim_shares : ut_share list
  var mix_sim_pp : mixnet_pp
  var mix_sim_pf : mixnet_proof
  var ddec_sim_parts : (mixnet_partial list * mixnet_ddec) list
  var shadow_record : behavior_list

  proc main(lambda nT t nV nA nC : int) : bool = {
    var d : bool;
    var msgs : bb_message list;
    var valid_msgs : ballot list;
    var ballot_seq : behavior_list;
    var i : int;
    var v : vote;
    var rho : randomness;
    var b_cur : election_ballot;
    var r_result : election_result;
    var pi_result : election_tally_proof;
    var gated : bool;
    var b_post : bool;
    var dummy_cts : mixnet_ciphertext list;
    var dummy_mixed : mixnet_ciphertext list;
    var dummy_sks : mixnet_skey list;
    var dummy_plaintexts : int list;

    bb <- [];
    st <- empty;
    disc <- fset0;
    shadow_record <- [];
    (ut_sim_pp, ut_sim_shares) <$ ut_sim_setup lambda nT t;
    dummy_cts <- [];
    dummy_mixed <- [];
    dummy_sks <- [];
    dummy_plaintexts <- [];
    mix_sim_pp <- witness;
    mix_sim_pf <$ mixnet_sim_mix mix_sim_pp dummy_cts dummy_mixed;
    ddec_sim_parts <$ mixnet_sim_ddec mix_sim_pp dummy_sks dummy_cts dummy_plaintexts;
    (pk_v, shares_v) <@ Onyx.setup(lambda, nT, t);
    (creds, reg_R) <@ Onyx.register(lambda, pk_v, nV);
    corrupt_D <@ A.corrupt(reg_R);
    (coerce_H, alphas) <@ A.coerce_choose(creds);
    ballot_seq <- [];
    beta_bit <$ {0,1};
    ballot_seq <- coerce_adjust ballot_seq coerce_H alphas beta_bit;
    i <- 0;
    d <- false;
    while (i < size ballot_seq) {
      msgs <@ A.board_phase(bb);
      valid_msgs <- extract_valid_ballots pk_v msgs bb;
      bb <- bb ++ valid_msgs;
      v <- snd (nth witness ballot_seq i);
      rho <- witness;
      b_cur <@ Onyx.vote(pk_v, nth witness creds (fst (nth witness ballot_seq i) - 1), v, rho);
      bb <- bb ++ [b_cur];
      shadow_record <- shadow_record ++ [nth witness ballot_seq i];
      i <- i + 1;
    }
    msgs <@ A.final_post(bb);
    valid_msgs <- extract_valid_ballots pk_v msgs bb;
    bb <- bb ++ valid_msgs;
    r_result <- result_func shadow_record;
    pi_result <- witness;
    A.post_tally(r_result, pi_result);
    gated <- coerce_H \subset disc;
    if (! gated) {
      b_post <$ {0,1};
      d <- b_post;
    } else {
      d <@ A.final_guess();
    }
    return d;
  }
}.

axiom hop_G2_G3 (A <: PCR_REAL_ADV {-G2_MixShuf, -G3_MixDDec}) &m lambda nT t nV nA nC :
  `| Pr[G2_MixShuf(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G3_MixDDec(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= (n_T)%r * advantage_MixNet_ddec lambda.
