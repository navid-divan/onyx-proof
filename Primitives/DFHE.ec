require import AllCore Distr Real List Bool DBool.
require import Preamble.
require import Negligible.

type dFHE_pkey = pkey.
type dFHE_skey = skey.
type dFHE_ciphertext = ciphertext.
type dFHE_message = plaintext.
type dFHE_randomness = randomness.
type dFHE_circuit.

op dFHE_keygen : int -> (dFHE_pkey * dFHE_skey) distr.
op dFHE_enc : dFHE_pkey -> dFHE_message -> dFHE_randomness -> dFHE_ciphertext.
op dFHE_dec : dFHE_skey -> dFHE_ciphertext -> dFHE_message.
op dFHE_eval : dFHE_pkey -> dFHE_circuit -> dFHE_ciphertext list -> dFHE_ciphertext.
op dFHE_fake : dFHE_pkey -> dFHE_message -> dFHE_randomness -> dFHE_message -> dFHE_randomness.

op dFHE_rand_distr : dFHE_randomness distr.

axiom dFHE_rand_distr_ll : is_lossless dFHE_rand_distr.

axiom dFHE_correctness (pk : dFHE_pkey) (sk : dFHE_skey) (m : dFHE_message) (r : dFHE_randomness) :
  (pk, sk) \in dFHE_keygen lambda_sec =>
  dFHE_dec sk (dFHE_enc pk m r) = m.

axiom dFHE_fake_consistency (pk : dFHE_pkey) (m : dFHE_message) (r : dFHE_randomness) (m_star : dFHE_message) :
  dFHE_enc pk m r = dFHE_enc pk m_star (dFHE_fake pk m r m_star).

module type DFHE_INDCPA_ADV = {
  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message
  proc guess(c : dFHE_ciphertext) : bool
}.

module DFHE_INDCPA_Game(A : DFHE_INDCPA_ADV) = {
  proc main() : bool = {
    var pk : dFHE_pkey;
    var sk : dFHE_skey;
    var m0, m1 : dFHE_message;
    var b, b' : bool;
    var c : dFHE_ciphertext;
    var r : dFHE_randomness;

    (pk, sk) <$ dFHE_keygen lambda_sec;
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    r <$ dFHE_rand_distr;
    c <- dFHE_enc pk (if b then m1 else m0) r;
    b' <@ A.guess(c);
    return b' = b;
  }
}.

module type DFHE_DEN_ADV = {
  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message
  proc guess(target : dFHE_message, r : dFHE_randomness, c : dFHE_ciphertext) : bool
}.

module DFHE_DEN_Game0(A : DFHE_DEN_ADV) = {
  proc main() : bool = {
    var pk : dFHE_pkey;
    var sk : dFHE_skey;
    var m, m_star : dFHE_message;
    var r : dFHE_randomness;
    var c : dFHE_ciphertext;
    var b' : bool;

    (pk, sk) <$ dFHE_keygen lambda_sec;
    (m, m_star) <@ A.choose(pk);
    r <$ dFHE_rand_distr;
    c <- dFHE_enc pk m_star r;
    b' <@ A.guess(m_star, r, c);
    return b';
  }
}.

module DFHE_DEN_Game1(A : DFHE_DEN_ADV) = {
  proc main() : bool = {
    var pk : dFHE_pkey;
    var sk : dFHE_skey;
    var m, m_star : dFHE_message;
    var r, r_star : dFHE_randomness;
    var c : dFHE_ciphertext;
    var b' : bool;

    (pk, sk) <$ dFHE_keygen lambda_sec;
    (m, m_star) <@ A.choose(pk);
    r <$ dFHE_rand_distr;
    r_star <- dFHE_fake pk m r m_star;
    c <- dFHE_enc pk m r;
    b' <@ A.guess(m_star, r_star, c);
    return b';
  }
}.

axiom dFHE_indcpa_advantage_bound :
  forall (A <: DFHE_INDCPA_ADV) &m,
    `| Pr[DFHE_INDCPA_Game(A).main() @ &m : res] - 1%r / 2%r |
      <= advantage_dFHE_indcpa lambda_sec.

axiom dFHE_deniability_advantage_bound :
  forall (A <: DFHE_DEN_ADV) &m,
    `| Pr[DFHE_DEN_Game0(A).main() @ &m : res]
       - Pr[DFHE_DEN_Game1(A).main() @ &m : res] |
      <= advantage_dFHE_den lambda_sec.

axiom dFHE_compactness :
  exists (poly_bound : int -> int),
    forall (pk : dFHE_pkey) (m : dFHE_message) (r : dFHE_randomness),
      poly_bound lambda_sec = poly_bound lambda_sec.
