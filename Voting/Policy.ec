require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import VotingScheme.

op last_vote : int -> behavior_list -> vote option.

axiom last_vote_empty i : last_vote i [] = None.

op cleanse_keep_last (B : behavior_list) : behavior_list.

axiom cleanse_keep_last_def B :
  cleanse_func B = cleanse_keep_last B.

op result_count : behavior_list -> int -> int.

axiom result_count_zero c : result_count [] c = 0.

op result_tally_func : behavior_list -> election_result.

axiom result_func_def B :
  result_func B = result_tally_func (policy_func (cleanse_func B)).

axiom coerce_adjust_disobey B H alphas :
  coerce_adjust B H alphas false = B.

axiom coerce_adjust_obey B H alphas :
  forall j, j \in H =>
    (forall v, !((j, v) \in coerce_adjust B H alphas true)) \/
    (oget alphas.[j] <> phi_abstain /\ (j, oget alphas.[j]) \in coerce_adjust B H alphas true).
