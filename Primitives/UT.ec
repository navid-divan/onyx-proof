require import AllCore Distr Real List Bool FSet.
require import Preamble.
require import Negligible.

type ut_pp = setup_public_params.
type ut_circuit.
type ut_input = int list.
type ut_output = bool.

op ut_setup : int -> int -> int -> ut_input -> (ut_pp * ut_share list) distr.
op ut_eval : ut_pp -> ut_share -> ut_circuit -> ut_partial_eval.
op ut_verify : ut_pp -> ut_partial_eval -> ut_circuit -> bool.
op ut_combine : ut_pp -> ut_partial_eval list -> ut_output.

op ut_circuit_apply : ut_circuit -> ut_input -> ut_output.

axiom ut_correctness (pp : ut_pp) (shares : ut_share list) (s_list : ut_share list)
                     (cc : ut_circuit) (x : ut_input) :
  (pp, shares) \in ut_setup lambda_sec n_T t_thresh x =>
  ut_combine pp (map (fun s => ut_eval pp s cc) s_list) = ut_circuit_apply cc x.

axiom ut_verify_correctness (pp : ut_pp) (shares : ut_share list)
                            (s : ut_share) (cc : ut_circuit) (x : ut_input) :
  (pp, shares) \in ut_setup lambda_sec n_T t_thresh x =>
  ut_verify pp (ut_eval pp s cc) cc = true.

module type UT_ADV = {
  proc choose_input(pp : ut_pp) : ut_input
  proc corrupt(pp : ut_pp) : int fset
  proc choose_circuit() : ut_circuit
  proc guess(eval_list : ut_partial_eval list) : bool
}.

module UT_Real_Game(A : UT_ADV) = {
  proc main() : bool = {
    var pp : ut_pp;
    var shares : ut_share list;
    var x : ut_input;
    var cc : ut_circuit;
    var y_list : ut_partial_eval list;
    var b : bool;
    var corrupt_set : int fset;

    x <- [];
    (pp, shares) <$ ut_setup lambda_sec n_T t_thresh x;
    corrupt_set <@ A.corrupt(pp);
    cc <@ A.choose_circuit();
    y_list <- map (fun s => ut_eval pp s cc) shares;
    b <@ A.guess(y_list);
    return b;
  }
}.

op ut_sim_setup : int -> int -> int -> (ut_pp * ut_share list) distr.
op ut_sim_eval : ut_pp -> ut_circuit -> ut_output -> ut_partial_eval list.

module UT_Ideal_Game(A : UT_ADV) = {
  proc main() : bool = {
    var pp : ut_pp;
    var shares : ut_share list;
    var x : ut_input;
    var cc : ut_circuit;
    var y_list : ut_partial_eval list;
    var outv : ut_output;
    var b : bool;
    var corrupt_set : int fset;

    x <- [];
    (pp, shares) <$ ut_sim_setup lambda_sec n_T t_thresh;
    corrupt_set <@ A.corrupt(pp);
    cc <@ A.choose_circuit();
    outv <- ut_circuit_apply cc x;
    y_list <- ut_sim_eval pp cc outv;
    b <@ A.guess(y_list);
    return b;
  }
}.

axiom ut_security_advantage_bound :
  forall (A <: UT_ADV) &m,
    `| Pr[UT_Real_Game(A).main() @ &m : res] - Pr[UT_Ideal_Game(A).main() @ &m : res] |
      <= advantage_UT_sim lambda_sec.

module type UT_ROB_ADV = {
  proc setup_choice(pp : ut_pp, shares : ut_share list) : ut_partial_eval
  proc circuit_choice() : ut_circuit
}.

module UT_Robust_Game(A : UT_ROB_ADV) = {
  proc main() : bool = {
    var pp : ut_pp;
    var shares : ut_share list;
    var x : ut_input;
    var y_star : ut_partial_eval;
    var cc : ut_circuit;
    var s_idx : ut_share;

    x <- [];
    (pp, shares) <$ ut_setup lambda_sec n_T t_thresh x;
    y_star <@ A.setup_choice(pp, shares);
    cc <@ A.circuit_choice();
    s_idx <- head witness shares;
    return ut_verify pp y_star cc /\ (y_star <> ut_eval pp s_idx cc);
  }
}.

axiom ut_robustness_advantage_bound :
  forall (A <: UT_ROB_ADV) &m,
    Pr[UT_Robust_Game(A).main() @ &m : res] <= advantage_UT_robust lambda_sec.
