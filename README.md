# Onyx Privacy Machine-Checked Proof

This repository contains an [EasyCrypt](https://www.easycrypt.info/) machine-checked proof that **Onyx** satisfies **Persistent Coercion Resistance (PCR)**, the privacy notion introduced in the submitted associated paperz. The proof formalises Persistent Coercion Resistance implies classical Coercion Resistance (`PCR ⇒ CR`), and `Onyx satisfies PCR` via a six-step hybrid argument H0 → H1 → H2 → H3 → H4 → H5, each transition reducing to a primitive security assumption (dFHE deniability / IND-CPA, NIZK randomness-deniability / ZK, UT simulation-security, MixNet shuffle ZK, MixNet distributed-decryption simulation, and quantum collision-resistance of the hash).

## Running and verifying

The project is verified by the shell script, from any directory:

```sh
bash run.sh
```
A warning will appear if there is no EasyCrypt installation available on the system; otherwise, the script must:

1. Confirms that all 30 `.ec` source files are present.
2. Detects EasyCrypt (activating the `easycrypt` opam switch if needed) and lists the configured provers.
3. Calls `easycrypt compile` on every file in dependency order. Each file produces a log under `build/`.

A successful run ends with

```
Passed : 30/30
Warned : 0/30
```

and exits with status `0`. If EasyCrypt is absent the script falls back to a structural validation (file counts, lemma counts, etc.) and prints install instructions, also exiting `0`.

You might need to have already configured on the machine (specially if using macOS):
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

## Testing an individual file

`run.sh` compiles everything; to check a single file (handy when editing), use:

```sh
eval "$(opam env --switch=easycrypt --set-switch)"
easycrypt compile \
  -I  \
  -I /Primitives \
  -I /Voting \
  -I /Onyx \
  -I /Hybrids \
  -I /Reductions \
  -I /Theorems \
  /Theorems/OnyxPCR.ec
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

