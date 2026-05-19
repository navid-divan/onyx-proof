require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import Hash.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G3_MixDDec.
require import G4_Hash.

module B_H(A : PCR_REAL_ADV) : HASH_CR_ADV = {
  var stored_chal_pairs : (hash_input * hash_input) list
  proc find_collision() : hash_input * hash_input = {
    stored_chal_pairs <- [];
    return ([], []);
  }
}.

axiom Red_Hash_correctness (A <: PCR_REAL_ADV {-B_H}) &m lambda nT t nV nA nC :
  `| Pr[G3_MixDDec(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G4_Hash(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= Pr[Hash_CR_Game(B_H(A)).main() @ &m : res].
