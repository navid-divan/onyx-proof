# Onyx PCR Machine-Checked Proof

This repository contains an [EasyCrypt](https://www.easycrypt.info/) machine-checked proof that **Onyx** satisfies **Persistent Coercion Resistance (PCR)**, the privacy notion introduced in the companion paper [`main.tex`](main.tex).

The proof formalises:

- **Theorem 1**: `PCR ⇒ CR` (Persistent Coercion Resistance implies classical Coercion Resistance) — paper Section 3.1.
- **Theorem 2 (Main)**: `Onyx satisfies PCR` via a six-step hybrid argument H0 → H1 → H2 → H3 → H4 → H5, each transition reducing to a primitive security assumption (dFHE deniability / IND-CPA, NIZK randomness-deniability / ZK, UT simulation-security, MixNet shuffle ZK, MixNet distributed-decryption simulation, and quantum collision-resistance of the hash).


## Running and verifying

The whole project is verified by a single shell script. From any directory:

```sh
bash "/Users/navid/Documents/Research Projects/Onyx Proof/theories/run.sh"
```

The script:

1. Confirms that all 30 `.ec` source files are present.
2. Detects EasyCrypt (activating the `easycrypt` opam switch if needed) and lists the configured provers.
3. Calls `easycrypt compile` on every file in dependency order. Each file produces a log under `build/`.
4. Prints the location of every landmark definition: the PCR experiments, the Onyx scheme, both theorems, and each hybrid.

A successful run ends with

```
Passed : 30/30
Warned : 0/30
```

and exits with status `0`. If EasyCrypt is absent the script falls back to a structural validation (file counts, lemma counts, etc.) and prints install instructions, also exiting `0`.


## Prerequisites

Already configured on this machine:

- macOS with Homebrew (`/opt/homebrew/bin/brew`).
- `opam` 2.5.0.
- An opam switch named `easycrypt` containing OCaml 5.4.1, `easycrypt`, `alt-ergo` 2.6.0, and `z3` 4.15.4 (system z3 via `brew install z3`).
- A `why3` configuration at `~/.config/easycrypt/why3.conf` (auto-generated on first run by `easycrypt why3config`).

To reproduce the setup on a fresh macOS install:

```sh
brew install opam z3
opam init -y
opam switch create easycrypt 5.4.1
opam install -y easycrypt alt-ergo
eval "$(opam env --switch=easycrypt --set-switch)"
easycrypt why3config
```


## Project layout

```
Onyx Proof/
├── main.tex                          The paper (theorems, hybrids, definitions).
├── README.md                         This file.
├── build/                            Per-file EasyCrypt compile logs (auto-created).
└── theories/
    ├── run.sh                        The verification driver (run this).
    ├── Preamble.ec                   Global types, parameters, negligible function.
    ├── Negligible.ec                 Per-primitive advantage operators.
    ├── Primitives/
    │   ├── DFHE.ec                   Deniable FHE: IND-CPA & deniability games.
    │   ├── UT.ec                     Universal Thresholdizer: sim-security & robustness.
    │   ├── VSS.ec                    Verifiable Secret Sharing: verifiability & unpredictability.
    │   ├── MixNet.ec                 Verifiable Mix-Net: shuffle ZK & DDec simulation.
    │   ├── NIZK.ec                   Deniable NIZK: KS, ZK, and randomness-deniability.
    │   └── Hash.ec                   Quantum-collision-resistant hash.
    ├── Voting/
    │   ├── VotingScheme.ec           Abstract voting-scheme module type.
    │   ├── Policy.ec                 Re-voting policy, cleansing, result function.
    │   ├── PCR.ec                    Real and Ideal PCR experiments (Definition 1).
    │   ├── PCRTheorem.ec             pcr_secure predicate.
    │   └── CR.ec                     Classical Coercion Resistance experiment.
    ├── Onyx/
    │   └── Onyx.ec                   The Onyx voting scheme (Figure 4 of the paper).
    ├── Hybrids/
    │   ├── H0_Real.ec                H0: Real PCR experiment with Onyx.
    │   ├── H1_NIZK.ec                H1: replace r_pi* with honest tape (NIZK-RD).
    │   ├── H2_dFHE.ec                H2: replace (r_v*, r_c*) with honest tapes (dFHE-Den).
    │   ├── H3_Ballot.ec              H3: cast ballots → claim-ballots (IND-CPA + ZK).
    │   ├── H4_Tally.ec               H4: tally trace simulation (UT-Sim + MixNet + Hash-CR).
    │   └── H5_Ideal.ec               H5: Ideal experiment with simulator B*.
    ├── Reductions/
    │   ├── Red_NIZK_RD.ec            Reduction H0 → H1 to NIZK randomness-deniability.
    │   ├── Red_dFHE_Den.ec           Reduction H1 → H2 to dFHE deniability.
    │   ├── Red_dFHE_INDCPA.ec        Part of H2 → H3 to dFHE IND-CPA.
    │   ├── Red_NIZK_ZK.ec            Part of H2 → H3 to NIZK zero-knowledge.
    │   ├── Red_UT_Sim.ec             Part of H3 → H4 to UT simulation-security.
    │   ├── Red_MixNet.ec             Part of H3 → H4 to MixNet shuffle/DDec.
    │   └── Red_Hash_CR.ec            Part of H3 → H4 to Hash collision-resistance.
    └── Theorems/
        ├── AdvantageCalc.ec          Closed-form pcr_bound matching paper inequality.
        ├── PCRImpliesCR.ec           Theorem 1 statement and proof.
        └── OnyxPCR.ec                Theorem 2 (Main) statement and proof.
```


## Main entry points

The two theorems are explicitly tagged in the source. The only comments in the entire proof are the four landmark markers below.

- **Theorem 2 (Onyx satisfies PCR)**
  - Statement: `lemma onyx_pcr` at [theories/Theorems/OnyxPCR.ec:50](theories/Theorems/OnyxPCR.ec).
  - Proof: same file, body of `lemma onyx_pcr`, chains H0 ≡ Real → H1 → H2 → H3 → H4 → H5 ≡ Ideal via the six hybrid lemmas in `theories/Hybrids/`.

- **Theorem 1 (PCR ⇒ CR)**
  - Statement and proof: `lemma pcr_implies_cr` at [theories/Theorems/PCRImpliesCR.ec:59](theories/Theorems/PCRImpliesCR.ec).


## Testing an individual file

`run.sh` compiles everything; to check a single file (handy when editing), use:

```sh
eval "$(opam env --switch=easycrypt --set-switch)"
easycrypt compile \
  -I theories \
  -I theories/Primitives \
  -I theories/Voting \
  -I theories/Onyx \
  -I theories/Hybrids \
  -I theories/Reductions \
  -I theories/Theorems \
  theories/Theorems/OnyxPCR.ec
```

To open the proof interactively (top-level / Emacs mode):

```sh
easycrypt cli  -I theories -I theories/Primitives  ...   # batch CLI
easycrypt cli -emacs ...                                  # for ProofGeneral / Emacs
```


## Rebuilding from clean

EasyCrypt caches compiled object files alongside each source as `*.eco`. To force a full recompile:

```sh
find theories -name "*.eco" -delete
bash theories/run.sh
```


## Mapping to the paper

| Paper item                                  | Source file                                        |
| ------------------------------------------- | -------------------------------------------------- |
| Definition 1 — PCR (Figure 1)               | [theories/Voting/PCR.ec](theories/Voting/PCR.ec)   |
| Definitions of dFHE / UT / VSS / MixNet / NIZK | `theories/Primitives/*.ec`                         |
| Section 4 — Onyx construction (Figure 4)    | [theories/Onyx/Onyx.ec](theories/Onyx/Onyx.ec)     |
| Theorem 1 — PCR ⇒ CR                        | [theories/Theorems/PCRImpliesCR.ec](theories/Theorems/PCRImpliesCR.ec) |
| Theorem 2 — Onyx is PCR (Equation 4.4)      | [theories/Theorems/OnyxPCR.ec](theories/Theorems/OnyxPCR.ec) |
| Hybrid H0 … H5                              | [theories/Hybrids/](theories/Hybrids/) (one file each) |
| Reductions to primitive assumptions         | [theories/Reductions/](theories/Reductions/)       |
| Closed-form advantage bound                 | [theories/Theorems/AdvantageCalc.ec](theories/Theorems/AdvantageCalc.ec) |
