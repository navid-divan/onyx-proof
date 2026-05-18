require import AllCore Distr Real List Bool FSet.
require import Preamble.
require import Negligible.

type mixnet_pp = setup_public_params.
type mixnet_ciphertext = ciphertext.
type mixnet_skey = skey.
type mixnet_pkey = pkey.
type mixnet_partial = int.

op mixnet_setup : int -> int -> int -> (mixnet_pp * mixnet_skey list) distr.
op mixnet_mix : mixnet_pp -> mixnet_ciphertext list -> (mixnet_ciphertext list * mixnet_proof) distr.
op mixnet_mix_verify : mixnet_pp -> mixnet_ciphertext list -> mixnet_ciphertext list -> mixnet_proof -> bool.
op mixnet_ddec : mixnet_skey -> mixnet_ciphertext list -> (mixnet_partial list * mixnet_ddec) distr.
op mixnet_ddec_verify : mixnet_pp -> mixnet_ciphertext list -> mixnet_partial list -> mixnet_ddec -> bool.
op mixnet_comb : mixnet_ciphertext list -> mixnet_partial list list -> int list option.

axiom mixnet_correctness pp sks cts mixed mix_pf partials_all combined :
  (pp, sks) \in mixnet_setup lambda_sec 4 4 =>
  (mixed, mix_pf) \in mixnet_mix pp cts =>
  combined = mixnet_comb mixed partials_all =>
  combined <> None.

module type MixNet_SHUF_ADV = {
  proc choose(pp : mixnet_pp) : mixnet_ciphertext list
  proc distinguish(orig : mixnet_ciphertext list, mixed : mixnet_ciphertext list,
                   pf : mixnet_proof) : bool
}.

module MixNet_Shuffle_Real(A : MixNet_SHUF_ADV) = {
  proc main() : bool = {
    var pp : mixnet_pp;
    var sks : mixnet_skey list;
    var cts : mixnet_ciphertext list;
    var mixed : mixnet_ciphertext list;
    var pf : mixnet_proof;
    var b : bool;

    (pp, sks) <$ mixnet_setup lambda_sec 4 4;
    cts <@ A.choose(pp);
    (mixed, pf) <$ mixnet_mix pp cts;
    b <@ A.distinguish(cts, mixed, pf);
    return b;
  }
}.

op mixnet_sim_mix : mixnet_pp -> mixnet_ciphertext list -> mixnet_ciphertext list -> mixnet_proof distr.

module MixNet_Shuffle_Sim(A : MixNet_SHUF_ADV) = {
  proc main() : bool = {
    var pp : mixnet_pp;
    var sks : mixnet_skey list;
    var cts : mixnet_ciphertext list;
    var mixed : mixnet_ciphertext list;
    var pf : mixnet_proof;
    var b : bool;

    (pp, sks) <$ mixnet_setup lambda_sec 4 4;
    cts <@ A.choose(pp);
    (mixed, pf) <$ mixnet_mix pp cts;
    pf <$ mixnet_sim_mix pp cts mixed;
    b <@ A.distinguish(cts, mixed, pf);
    return b;
  }
}.

axiom mixnet_shuffle_advantage_bound :
  forall (A <: MixNet_SHUF_ADV) &m,
    `| Pr[MixNet_Shuffle_Real(A).main() @ &m : res]
       - Pr[MixNet_Shuffle_Sim(A).main() @ &m : res] |
      <= advantage_MixNet_shuf lambda_sec.

module type MixNet_DDEC_ADV = {
  proc choose_corrupt(pp : mixnet_pp) : int fset
  proc choose_cts() : mixnet_ciphertext list
  proc distinguish(parts : (mixnet_partial list * mixnet_ddec) list) : bool
}.

op mixnet_sim_ddec : mixnet_pp -> mixnet_skey list -> mixnet_ciphertext list -> int list -> (mixnet_partial list * mixnet_ddec) list distr.

module MixNet_DDec_Real(A : MixNet_DDEC_ADV) = {
  proc main() : bool = {
    var pp : mixnet_pp;
    var sks : mixnet_skey list;
    var j_set : int fset;
    var cts : mixnet_ciphertext list;
    var parts : (mixnet_partial list * mixnet_ddec) list;
    var b : bool;

    (pp, sks) <$ mixnet_setup lambda_sec 4 4;
    j_set <@ A.choose_corrupt(pp);
    cts <@ A.choose_cts();
    parts <- [];
    b <@ A.distinguish(parts);
    return b;
  }
}.

module MixNet_DDec_Sim(A : MixNet_DDEC_ADV) = {
  proc main() : bool = {
    var pp : mixnet_pp;
    var sks : mixnet_skey list;
    var j_set : int fset;
    var cts : mixnet_ciphertext list;
    var plaintexts : int list;
    var parts : (mixnet_partial list * mixnet_ddec) list;
    var b : bool;

    (pp, sks) <$ mixnet_setup lambda_sec 4 4;
    j_set <@ A.choose_corrupt(pp);
    cts <@ A.choose_cts();
    plaintexts <- [];
    parts <$ mixnet_sim_ddec pp sks cts plaintexts;
    b <@ A.distinguish(parts);
    return b;
  }
}.

axiom mixnet_ddec_advantage_bound :
  forall (A <: MixNet_DDEC_ADV) &m,
    `| Pr[MixNet_DDec_Real(A).main() @ &m : res]
       - Pr[MixNet_DDec_Sim(A).main() @ &m : res] |
      <= advantage_MixNet_ddec lambda_sec.

module type MixNet_VERIF_ADV = {
  proc craft(pp : mixnet_pp, cts : mixnet_ciphertext list) :
    mixnet_ciphertext list * mixnet_proof
}.

module MixNet_Verifiability_Game(A : MixNet_VERIF_ADV) = {
  proc main() : bool = {
    var pp : mixnet_pp;
    var sks : mixnet_skey list;
    var cts : mixnet_ciphertext list;
    var mixed : mixnet_ciphertext list;
    var pf : mixnet_proof;
    var verified : bool;
    var multisets_differ : bool;

    (pp, sks) <$ mixnet_setup lambda_sec 4 4;
    cts <- [];
    (mixed, pf) <@ A.craft(pp, cts);
    verified <- mixnet_mix_verify pp cts mixed pf;
    multisets_differ <- false;
    return verified /\ multisets_differ;
  }
}.

axiom mixnet_verifiability_advantage_bound :
  forall (A <: MixNet_VERIF_ADV) &m,
    Pr[MixNet_Verifiability_Game(A).main() @ &m : res]
      <= advantage_MixNet_verif lambda_sec.
