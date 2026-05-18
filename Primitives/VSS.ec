require import AllCore Distr Real List FSet Bool.
require import Preamble.
require import Negligible.

type vss_secret = int.
type vss_randomizer = int.

op vss_share_alg : vss_secret -> int -> int -> ((vss_share * vss_randomizer) list * vss_proof) distr.
op vss_verify_share : int -> vss_share -> vss_randomizer -> vss_proof -> bool.
op vss_reconstruct : (int * vss_share * vss_randomizer) list -> vss_proof -> vss_secret.

axiom vss_correctness (s : vss_secret) (t : int) (n : int)
                      (shares : (vss_share * vss_randomizer) list) (pi : vss_proof) :
  (shares, pi) \in vss_share_alg s t n =>
  forall (i : int), 1 <= i <= n =>
    vss_verify_share i (fst (nth witness shares (i-1))) (snd (nth witness shares (i-1))) pi = true.

axiom vss_correct_reconstruct (s : vss_secret) (t : int) (n : int)
                              (shares : (vss_share * vss_randomizer) list) (pi : vss_proof)
                              (S : int fset) :
  (shares, pi) \in vss_share_alg s t n =>
  t + 1 <= card S =>
  vss_reconstruct (map (fun (i : int) => (i, fst (nth witness shares (i-1)),
                                              snd (nth witness shares (i-1))))
                       (elems S)) pi = s.

module type VSS_VERIF_ADV = {
  proc craft(n : int, t : int) : (vss_share * vss_randomizer) list * vss_proof
  proc honest_set() : int fset
}.

module VSS_Verifiability_Game(A : VSS_VERIF_ADV) = {
  proc main() : bool = {
    var shares : (vss_share * vss_randomizer) list;
    var pi : vss_proof;
    var honest_set : int fset;
    var all_verify : bool;
    var two_secrets_diff : bool;

    (shares, pi) <@ A.craft(n_R, t_R);
    honest_set <@ A.honest_set();
    all_verify <- true;
    two_secrets_diff <- false;
    return (all_verify /\ two_secrets_diff);
  }
}.

axiom vss_verifiability_advantage_bound :
  forall (A <: VSS_VERIF_ADV) &m,
    Pr[VSS_Verifiability_Game(A).main() @ &m : res] <= advantage_VSS_verif lambda_sec.

module type VSS_UNPRED_ADV = {
  proc corrupt() : int fset
  proc guess(shares_corrupt : (vss_share * vss_randomizer) list, pi : vss_proof) : vss_secret
}.

op uniform_secret_distr : vss_secret distr.

axiom uniform_secret_ll : is_lossless uniform_secret_distr.

module VSS_Unpredict_Game(A : VSS_UNPRED_ADV) = {
  proc main() : bool = {
    var s : vss_secret;
    var s' : vss_secret;
    var shares : (vss_share * vss_randomizer) list;
    var pi : vss_proof;
    var q_set : int fset;
    var corrupt_shares : (vss_share * vss_randomizer) list;

    s <$ uniform_secret_distr;
    q_set <@ A.corrupt();
    (shares, pi) <$ vss_share_alg s t_R n_R;
    corrupt_shares <- map (fun (i : int) => nth witness shares (i-1)) (elems q_set);
    s' <@ A.guess(corrupt_shares, pi);
    return s' = s;
  }
}.

axiom vss_unpredict_advantage_bound :
  forall (A <: VSS_UNPRED_ADV) &m,
    Pr[VSS_Unpredict_Game(A).main() @ &m : res] <= advantage_VSS_unpredict lambda_sec.
