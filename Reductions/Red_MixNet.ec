require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import MixNet.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H3_Ballot.
require import H4_Tally.

module ReduceH3H4_to_MixNet_Shuf(A : PCR_REAL_ADV) : MixNet_SHUF_ADV = {
  proc choose(pp : mixnet_pp) : mixnet_ciphertext list = {
    return [];
  }
  proc distinguish(orig : mixnet_ciphertext list, mixed : mixnet_ciphertext list,
                   pf : mixnet_proof) : bool = {
    return false;
  }
}.

module ReduceH3H4_to_MixNet_DDec(A : PCR_REAL_ADV) : MixNet_DDEC_ADV = {
  proc choose_corrupt(pp : mixnet_pp) : int fset = {
    return fset0;
  }
  proc choose_cts() : mixnet_ciphertext list = {
    return [];
  }
  proc distinguish(parts : (mixnet_partial list * mixnet_ddec) list) : bool = {
    return false;
  }
}.

lemma red_mixnet_shuf_advantage (lambda : int) :
  exists (delta_shuf : real),
    0%r <= delta_shuf /\ delta_shuf <= advantage_MixNet_shuf lambda.
proof.
admit.
qed.

lemma red_mixnet_ddec_advantage (lambda : int) :
  exists (delta_ddec : real),
    0%r <= delta_ddec /\ delta_ddec <= (n_T)%r * advantage_MixNet_ddec lambda.
proof.
admit.
qed.
