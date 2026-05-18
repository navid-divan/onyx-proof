require import AllCore.
require import Int.
require import Real.
require import Distr.
require import List.
require import FSet.
require import FMap.
require import Bool.

type security_parameter = int.

type randomness = int list.

type pkey.
type skey.
type trapdoor.
type crs_type.
type election_hint.

type vote = int.

type candidate = int.

type credential.

type ciphertext.

type plaintext = int.

type proof_type.

type ballot_id = int.

type roster_entry.

type ballot = ciphertext * ciphertext * proof_type.

type bb_message.

type tally_result.

type tally_proof.

type voter_state.

type local_state.

type registration_record.

type setup_public_params.

type ut_share.

type ut_partial_eval.

type ut_proof.

type vss_share.

type vss_proof.

type mixnet_proof.

type mixnet_ddec.

type behavior_pair = int * vote.

type behavior_distribution = int fset -> int -> behavior_pair list distr.

op n_T : int.
op t_thresh : int.
op n_V : int.
op n_A : int.
op n_C : int.
op n_R : int.
op t_R : int.
op q_b : int.
op q_d : int.
op lambda_sec : int.
op delta_sec : real.

op phi_abstain : int.

axiom n_T_pos : 0 < n_T.
axiom t_thresh_pos : 0 < t_thresh.
axiom t_thresh_lt : t_thresh < n_T.
axiom n_V_pos : 0 < n_V.
axiom n_A_nonneg : 0 <= n_A.
axiom n_A_lt : n_A <= n_V.
axiom n_C_pos : 0 < n_C.
axiom n_R_pos : 0 < n_R.
axiom t_R_pos : 0 < t_R.
axiom n_R_threshold : 2 * t_R + 1 <= n_R.

op valid_candidate (x : int) : bool =
  (1 <= x <= n_C) \/ x = phi_abstain.

op valid_vote_index (x : int) : bool =
  1 <= x <= n_C.

type ballot_board = ballot list.

op board_publish (bb : ballot_board) : ballot_board = bb.

op negligible : (int -> real) -> bool.

axiom negligible_zero : negligible (fun _ => 0%r).

axiom negligible_sum (f g : int -> real) :
  negligible f => negligible g => negligible (fun n => f n + g n).

axiom negligible_scalar (c : real) (f : int -> real) :
  negligible f => negligible (fun n => c * f n).

axiom negligible_le (f g : int -> real) :
  negligible g =>
  (forall n, 0%r <= f n) =>
  (forall n, f n <= g n) =>
  negligible f.
