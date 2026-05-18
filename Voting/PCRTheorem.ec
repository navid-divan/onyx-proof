require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import VotingScheme.
require import PCR.

op pcr_secure : (int -> real) -> bool.

axiom pcr_secure_def (f : int -> real) :
  pcr_secure f <=> negligible f.
