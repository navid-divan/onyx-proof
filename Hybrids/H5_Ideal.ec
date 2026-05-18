require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import VotingScheme.
require import Policy.
require import PCR.
require import Onyx.
require import H4_Tally.

module OnyxSimulator : PCR_IDEAL_ADV = {
  proc setup() : int fset = {
    return fset0;
  }
  proc coerce_choose() : int fset * (int, int) fmap = {
    return (fset0, empty);
  }
  proc fill_corrupt(size : int) : (int, int) fmap * bool = {
    return (empty, false);
  }
  proc final_guess(r : election_result, claims : (int * int) list) : bool = {
    return false;
  }
}.

module Hybrid_H5(A : PCR_REAL_ADV) = {
  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    d <@ PCR_Ideal_Experiment(OnyxSimulator).main(lambda, nV, nA, nC);
    return d;
  }
}.

lemma hybrid_H4_H5_eq (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  Pr[Hybrid_H4(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] =
  Pr[Hybrid_H5(A).main(lambda, nT, t, nV, nA, nC) @ &m : res].
proof.
admit.
qed.

lemma H5_equiv_ideal (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  Pr[Hybrid_H5(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] =
  Pr[PCR_Ideal_Experiment(OnyxSimulator).main(lambda, nV, nA, nC) @ &m : res].
proof.
admit.
qed.
