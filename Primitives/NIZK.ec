require import AllCore Distr Real List Bool.
require import Preamble.
require import Negligible.

type nizk_crs = crs_type.
type nizk_td = trapdoor.
type nizk_statement = (ciphertext * ciphertext * setup_public_params).
type nizk_witness = (vote * credential * randomness * randomness).
type nizk_proof = proof_type.
type nizk_randomness = randomness.

op nizk_relation : nizk_statement -> nizk_witness -> bool.

op nizk_setup : int -> (nizk_crs * nizk_td) distr.
op nizk_prove : nizk_crs -> nizk_td -> nizk_statement -> nizk_witness -> nizk_randomness -> nizk_proof.
op nizk_verify : nizk_crs -> nizk_statement -> nizk_proof -> bool.
op nizk_fake : nizk_crs -> nizk_td -> nizk_statement -> nizk_witness -> nizk_randomness -> nizk_witness -> nizk_randomness.

op nizk_rand_distr : nizk_randomness distr.

axiom nizk_rand_distr_ll : is_lossless nizk_rand_distr.

axiom nizk_completeness crs td x w r :
  (crs, td) \in nizk_setup lambda_sec =>
  nizk_relation x w =>
  nizk_verify crs x (nizk_prove crs td x w r) = true.

axiom nizk_fake_consistency crs td x w r w_star :
  nizk_relation x w =>
  nizk_relation x w_star =>
  nizk_prove crs td x w r = nizk_prove crs td x w_star (nizk_fake crs td x w r w_star).

module type NIZK_KS_ADV = {
  proc prove(crs : nizk_crs, td : nizk_td) : nizk_statement * nizk_proof
}.

module NIZK_KS_Game(A : NIZK_KS_ADV) = {
  proc main() : bool = {
    var crs : nizk_crs;
    var td : nizk_td;
    var x : nizk_statement;
    var pi : nizk_proof;
    var w : nizk_witness;
    var accepting : bool;
    var extract_fail : bool;

    (crs, td) <$ nizk_setup lambda_sec;
    (x, pi) <@ A.prove(crs, td);
    accepting <- nizk_verify crs x pi;
    w <- witness;
    extract_fail <- !nizk_relation x w;
    return accepting /\ extract_fail;
  }
}.

axiom nizk_ks_advantage_bound :
  forall (A <: NIZK_KS_ADV) &m,
    Pr[NIZK_KS_Game(A).main() @ &m : res] <= advantage_NIZK_ks lambda_sec.

module type NIZK_ZK_ADV = {
  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness
  proc distinguish(pi : nizk_proof) : bool
}.

op nizk_simulate : nizk_crs -> nizk_statement -> nizk_proof distr.

module NIZK_ZK_Real(A : NIZK_ZK_ADV) = {
  proc main() : bool = {
    var crs : nizk_crs;
    var td : nizk_td;
    var x : nizk_statement;
    var w : nizk_witness;
    var r : nizk_randomness;
    var pi : nizk_proof;
    var b : bool;

    (crs, td) <$ nizk_setup lambda_sec;
    (x, w) <@ A.choose(crs);
    r <$ nizk_rand_distr;
    pi <- nizk_prove crs td x w r;
    b <@ A.distinguish(pi);
    return b;
  }
}.

module NIZK_ZK_Sim(A : NIZK_ZK_ADV) = {
  proc main() : bool = {
    var crs : nizk_crs;
    var td : nizk_td;
    var x : nizk_statement;
    var w : nizk_witness;
    var pi : nizk_proof;
    var b : bool;

    (crs, td) <$ nizk_setup lambda_sec;
    (x, w) <@ A.choose(crs);
    pi <$ nizk_simulate crs x;
    b <@ A.distinguish(pi);
    return b;
  }
}.

axiom nizk_zk_advantage_bound :
  forall (A <: NIZK_ZK_ADV) &m,
    `| Pr[NIZK_ZK_Real(A).main() @ &m : res] - Pr[NIZK_ZK_Sim(A).main() @ &m : res] |
      <= advantage_NIZK_zk lambda_sec.

module type NIZK_RD_ADV = {
  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness * nizk_witness
  proc distinguish(w_disclosed : nizk_witness, r : nizk_randomness, pi : nizk_proof) : bool
}.

module NIZK_RD_Real(A : NIZK_RD_ADV) = {
  proc main() : bool = {
    var crs : nizk_crs;
    var td : nizk_td;
    var x : nizk_statement;
    var w, w_star : nizk_witness;
    var r : nizk_randomness;
    var pi : nizk_proof;
    var b : bool;

    (crs, td) <$ nizk_setup lambda_sec;
    (x, w, w_star) <@ A.choose(crs);
    r <$ nizk_rand_distr;
    pi <- nizk_prove crs td x w r;
    b <@ A.distinguish(w, r, pi);
    return b;
  }
}.

module NIZK_RD_Fake(A : NIZK_RD_ADV) = {
  proc main() : bool = {
    var crs : nizk_crs;
    var td : nizk_td;
    var x : nizk_statement;
    var w, w_star : nizk_witness;
    var r, r_star : nizk_randomness;
    var pi : nizk_proof;
    var b : bool;

    (crs, td) <$ nizk_setup lambda_sec;
    (x, w, w_star) <@ A.choose(crs);
    r <$ nizk_rand_distr;
    pi <- nizk_prove crs td x w r;
    r_star <- nizk_fake crs td x w r w_star;
    b <@ A.distinguish(w_star, r_star, pi);
    return b;
  }
}.

axiom nizk_rd_advantage_bound :
  forall (A <: NIZK_RD_ADV) &m,
    `| Pr[NIZK_RD_Real(A).main() @ &m : res] - Pr[NIZK_RD_Fake(A).main() @ &m : res] |
      <= advantage_NIZK_rd lambda_sec.
