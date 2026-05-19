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
require import G7_DiscRand.

op final_negl_gap : int -> real.

axiom final_negl_gap_nonneg (lambda : int) : 0%r <= final_negl_gap lambda.
axiom final_negl_gap_negligible : negligible final_negl_gap.

module OnyxSim(A : PCR_REAL_ADV) : PCR_IDEAL_ADV = {
  var sim_corrupt : int fset
  var sim_coerce : int fset
  var sim_alphas : (int, int) fmap

  proc setup() : int fset = {
    var dummy_reg : election_register_record;
    dummy_reg <- witness;
    sim_corrupt <@ A.corrupt(dummy_reg);
    return sim_corrupt;
  }

  proc coerce_choose() : int fset * (int, int) fmap = {
    var dummy_creds : election_credential list;
    dummy_creds <- [];
    (sim_coerce, sim_alphas) <@ A.coerce_choose(dummy_creds);
    return (sim_coerce, sim_alphas);
  }

  proc fill_corrupt(sz : int) : (int, int) fmap * bool = {
    return (empty, false);
  }

  proc final_guess(r : election_result, claims : (int * int) list) : bool = {
    var dummy_pi : election_tally_proof;
    var d : bool;
    dummy_pi <- witness;
    A.post_tally(r, dummy_pi);
    d <@ A.final_guess();
    return d;
  }
}.

axiom hop_G7_G8 (A <: PCR_REAL_ADV {-G7_DiscRand, -OnyxSim, -PCR_Ideal_Experiment}) &m lambda nT t nV nA nC :
  `| Pr[G7_DiscRand(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[PCR_Ideal_Experiment(OnyxSim(A)).main(lambda, nV, nA, nC) @ &m : res] |
  <= final_negl_gap lambda.
