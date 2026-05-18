require import AllCore Distr Real List Bool.
require import Preamble.
require import Negligible.

type hash_input = int list.
type hash_output = int.

op hash_func : hash_input -> hash_output.

module type HASH_CR_ADV = {
  proc find_collision() : hash_input * hash_input
}.

module Hash_CR_Game(A : HASH_CR_ADV) = {
  proc main() : bool = {
    var x1, x2 : hash_input;
    (x1, x2) <@ A.find_collision();
    return x1 <> x2 /\ hash_func x1 = hash_func x2;
  }
}.

axiom hash_cr_advantage_bound :
  forall (A <: HASH_CR_ADV) &m,
    Pr[Hash_CR_Game(A).main() @ &m : res] <= advantage_Hash_cr lambda_sec.
