# BARReL: **B** **A**utomated t**R**anslation for **Re**asoning in Lean

BARReL bridges Atelier B proof obligations to Lean. It parses `.pog` files (the PO XML format produced by Atelier B), converts the obligations into Lean terms, and lets you discharge them with Lean tactics.

## Repository layout
- [`B/`](B/): a lightweight Lean embedding of the B syntax and basic pretty-printing.
- [`B4Lean/`](B4Lean/): the encoding layer: built-in B sets and relations ([`Builtins.lean`](B4Lean/Builtins.lean)), translation to Lean expressions ([`Encoder.lean`](B4Lean/Encoder.lean)), and the proof-obligation discharger macros ([`Discharger.lean`](B4Lean/Discharger.lean)).
- [`POGReader/`](POGReader/): XML parsing for Atelier B POG files ([`Parser.lean`](POGReader/Parser.lean)), schema definitions, and extraction of goals ([`Extractor.lean`](POGReader/Extractor.lean)).
- [`Extra/`](Extra/): utility formatting helpers.
- [`specs/`](specs/): sample B machines (`.mch`)
- [`Test.lean`](Test.lean): an example script showing how to call the discharger on the sample machines.
- [`Main.lean`](Main.lean): minimal executable stub.

## Prerequisites
- Lean 4 (see [`lean-toolchain`](lean-toolchain) for version).
- Mathlib (pulled automatically by Lake).
- For `mch_discharger`: an Atelier B installation with `bin/bxml` and `bin/pog` available. Point BARReL to it with `set_option b4lean.atelierb "<path-to-atelierb-root>"` (the directory that contains `bin/` and `include/`).

## Quick start
### Setting up the environment
```bash
lake update     # fetch mathlib and dependencies
lake build      # build all libraries
```

To experiment with the sample machines, open `Test.lean` in your editor or run:
```bash
lake env lean Test.lean
```

### Quick example
Consider the B machine [`Counter.mch`](specs/Counter.mch):
```
MACHINE Counter
VARIABLES x
INVARIANT
  x ∈ NAT & x ≤ 10
INITIALISATION
  x := 0
OPERATIONS
  inc =
    PRE x < 10 THEN
      x := x + 1
    END
END
```
This machine generates four proof obligations:
- _Initialisation_:
  - $0 ∈ \mathrm{NAT}$
  - $0 \leq 10$.
- _Invariant preservation_ for `inc`:
  - $\forall x ∈ \mathrm{NAT}, x \leq 10 \to x < 10 \to x + 1 ∈ \mathrm{NAT}$
  - $\forall x ∈ \mathrm{NAT}, x \leq 10 \to x < 10 \to x + 1 \leq 10$

In Lean, we can discharge them as follows:

```hs
import B4Lean.Discharger

set_option b4lean.atelierb "/<path-to-atelierb-root>/atelierb-free-arm64-24.04.2.app/Contents/Resources"

mch_discharger "specs/Counter.mch"
next -- 0 ∈ NAT
  grind
next -- 0 ≤ 10
  grind
next -- ∀ x ∈ NAT, x ≤ 10 → x < 10 → x + 1 ∈ NAT
  rintro x ⟨_, _⟩ _ _
  grind
next -- ∀ x ∈ NAT, x ≤ 10 → x < 10 → x + 1 ≤ 10
  grind
```

## Using the discharger
Two commands are provided to discharge proof obligations from B machines:

- `pog_discharger "<path.pog>"` — consume an existing POG file.
- `mch_discharger "<path.mch>"` — call Atelier B (`bxml` then `pog`) to generate the POG on the fly, then consume it.

Each command expands to a sequence of proof goals. Provide one `next` block per goal with the tactic script you want to use:

```hs
set_option b4lean.atelierb "/<path-to-atelierb-root>/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- Work directly from a machine
mch_discharger "specs/Counter.mch"
next
  ...

-- Work from a pre-generated POG file
pog_discharger "specs/Forall.pog"
next
  ...
```

Each `next` corresponds to one simple goal inside the POG. If fewer `next` blocks are provided than goals, the command fails and reports how many remain. Theorems are added under the current namespace using the POG tag and an index (see [`Discharger.lean`](B4Lean/Discharger.lean) for naming details).

The discharger also produces Lean theorems named after the POG tags–e.g. `Counter.Initialisation_<i>`, which can be used as lemmas in subsequent proofs, if needed.

## How it works (high level)
1. **Parse POG XML**: read types, definitions, and proof obligations from Atelier B’s PO XML schema.
2. **Extract logical goals**: turn the schema into `Goal` records containing variables, hypotheses, and the goal term.
3. **Encode to Lean**: map B terms and types to Lean expressions, using the set-theoretic primitives in `B4Lean/Builtins.lean` and Lean's meta-programming features.
4. **Discharge**: generate Lean theorem declarations for each goal and run the user-supplied tactics. Generated goals should closely resemble the original B proof obligations.

## Sample models
The `specs/` folder contains small machines used during development:
- `Counter.mch`, `Nat.mch`, `Forall.mch`, `Exists.mch`, `Injective.mch`, `HO.mch`, `Enum.mch`, `Lambda.mch`, and their corresponding `.pog` files.
You can copy these as templates when adding new B models.


## Contributing
Contributions and bug reports are very welcome!
