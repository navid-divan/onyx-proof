require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import NIZK.
require import UT.
require import MixNet.
require import VotingScheme.
require import PCR.
require import Onyx.

module Hybrid_H0(A : PCR_REAL_ADV) = {
  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    d <@ PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC);
    return d;
  }
}.

lemma H0_equiv_real (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  Pr[Hybrid_H0(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] =
  Pr[PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC) @ &m : res].
proof.
admit.
qed.
