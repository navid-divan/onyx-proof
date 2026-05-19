require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import UT.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G1_UT.

module B_U(A : PCR_REAL_ADV) : UT_ADV = {
  var stored_pp : ut_pp
  var stored_corrupt : int fset

  proc choose_input(pp : ut_pp) : ut_input = {
    stored_pp <- pp;
    return [];
  }
  proc corrupt(pp : ut_pp) : int fset = {
    stored_corrupt <- fset0;
    return fset0;
  }
  proc choose_circuit() : ut_circuit = {
    return witness;
  }
  proc guess(eval_list : ut_partial_eval list) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_UT_correctness (A <: PCR_REAL_ADV {-B_U}) &m lambda nT t nV nA nC :
  `| Pr[PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G1_UT(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= `| Pr[UT_Real_Game(B_U(A)).main() @ &m : res]
      - Pr[UT_Ideal_Game(B_U(A)).main() @ &m : res] |.
