require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.

type election_pk.
type election_sk_share.
type election_hint_t = election_hint.
type election_credential = credential.
type election_register_record = registration_record.
type election_ballot = ballot.
type election_local_state = local_state.
type election_voter_state = voter_state.
type election_result = tally_result.
type election_tally_proof = tally_proof.
type election_bb = ballot_board.
type election_setup_state.

op claim_value (x : int) : bool = valid_candidate x.

type behavior_entry = int * vote.

type behavior_list = behavior_entry list.

module type VotingScheme = {
  proc setup(lambda : int, nT : int, t : int) :
    election_pk * (election_sk_share * election_hint_t) list

  proc register(lambda : int, pk : election_pk, nV : int) :
    election_credential list * election_register_record

  proc vote(pk : election_pk, c : election_credential, v : vote, r : randomness) :
    election_ballot

  proc valid(pk : election_pk, b : election_ballot, bb : election_bb) : bool

  proc tally(bb : election_bb, reg : election_register_record, pk : election_pk,
             shares : (election_sk_share * election_hint_t) list, t : int) :
    election_result * election_tally_proof

  proc verify(pk : election_pk, bb : election_bb, reg : election_register_record,
              r : election_result, pi : election_tally_proof) : bool

  proc fake(ls : election_local_state, v_star : vote, c_star : election_credential,
            vs : election_voter_state) :
    election_credential * vote * randomness * randomness * randomness

  proc fakecred(pk : election_pk) : election_credential
}.

op result_func : behavior_list -> election_result.
op policy_func : behavior_list -> behavior_list.
op cleanse_func : behavior_list -> behavior_list.

op apply_revote_policy : behavior_list -> behavior_list.
axiom apply_revote_policy_def (b : behavior_list) : apply_revote_policy b = policy_func b.

op coerce_adjust : behavior_list -> int fset -> (int, int) fmap -> bool -> behavior_list.
