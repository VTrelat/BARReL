
# BARReL: **B** **A**utomated t**R**anslation for **Re**asoning in **L**ean <img src=".assets/barrel.png" height="80px" style="vertical-align:middle;" align="right"/>

BARReL bridges Atelier B proof obligations to Lean. It parses `.pog` files (the PO XML format produced by Atelier B), converts the obligations into Lean terms, and lets you discharge them with Lean tactics.

## Repository layout
- [`B/`](B/): a lightweight Lean embedding of the B syntax and basic pretty-printing.
- [`Barrel/`](Barrel/): the encoding layer: built-in B sets and relations ([`Builtins.lean`](Barrel/Builtins.lean)), translation to Lean expressions ([`Encoder.lean`](Barrel/Encoder.lean)), and the proof-obligation discharger macros ([`Discharger.lean`](Barrel/Discharger.lean)).
- [`POGReader/`](POGReader/): XML parsing for Atelier B POG files ([`Parser.lean`](POGReader/Parser.lean)), schema definitions, and extraction of goals ([`Extractor.lean`](POGReader/Extractor.lean)).
- [`Extra/`](Extra/): utility formatting helpers.
- [`specs/`](specs/): sample B machines (`.mch`)
- [`Test.lean`](Test.lean): an example script showing how to call the discharger on the sample machines.

## Prerequisites
- Lean 4 (see [`lean-toolchain`](lean-toolchain) for version).
- Mathlib (pulled automatically by Lake).
- For `mch_discharger`: an Atelier B installation with `bin/bxml` and `bin/pog` available. Point BARReL to it with `set_option barrel.atelierb "<path-to-atelierb-root>"` (the directory that contains `bin/` and `include/`).

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
Consider the B machine [`CounterMin.mch`](specs/CounterMin.mch):
```
MACHINE CounterMin
VARIABLES X
INVARIANT
  X ∈ FIN1(ℤ) ∧ max(X) = -min(X)
INITIALISATION
  X := {0}
OPERATIONS
  inc =
  ANY z WHERE z ∈ ℕ THEN
    X := (-z)..z
  END
END
```
This machine generates four proof obligations:
- _Initialisation_:
  - `{0} ∈ FIN₁(INTEGER)`
  - `max({0}) = -min({0})`
- _Invariant preservation_ for `inc`:
  - `∀ z ∈ ℤ, ∀ X ∈ FIN₁(ℤ), max(X) = -min(X) → z ∈ ℕ → (-z)..z ∈ FIN₁(ℤ)`
  - `∀ z ∈ ℤ, ∀ X ∈ FIN₁(ℤ), max(X) = -min(X) → z ∈ ℕ → max((-z)..z) = -min((-z)..z)`

In Lean, we can discharge them as follows:

```lean
import Barrel.Discharger

set_option barrel.atelierb "/<path-to-atelierb-root>/atelierb-free-arm64-24.04.2.app/Contents/Resources"

mch_discharger "specs/CounterMin.mch"
next
  exact FIN₁.singleton_mem trivial
next
  exists max.WF_singleton, min.WF_singleton
  simp
next
  rintro z X hX
  exists max.WF_of_finite hX, min.WF_of_finite hX
  rintro - hz
  exact interval.FIN₁_mem (neg_le_self hz)
next
  intro z X hX
  exists max.WF_of_finite hX, min.WF_of_finite hX
  rintro _ hz
  exists
    max.WF_of_finite (interval.FIN₁_mem (neg_le_self hz)),
    min.WF_of_finite (interval.FIN₁_mem (neg_le_self hz))
  rw [interval.max_eq (neg_le_self hz),
      interval.min_eq (neg_le_self hz),
      Int.neg_neg]
```

> [!NOTE]
> By default, option `barrel.show_goal_names` is set to `true`, which will display the name of each proof obligation at each `next`, but it can be disabled with:
> ```lean
> set_option barrel.show_goal_names false
> ```

## Using the discharger
Two commands are provided to discharge proof obligations from B machines:

- `pog_discharger "<path.pog>"` — consume an existing POG file.
- `mch_discharger "<path.mch>"` — call Atelier B (`bxml` then `pog`) to generate the POG on the fly, then consume it.

Each command expands to a sequence of proof goals. Provide one `next` block per goal with the tactic script you want to use:

```lean
set_option barrel.atelierb "/<path-to-atelierb-root>/atelierb-free-arm64-24.04.2.app/Contents/Resources"

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

Each `next` corresponds to one simple goal inside the POG. If fewer `next` blocks are provided than goals, the command fails and reports how many remain. Theorems are added under the current namespace using the POG tag and an index (see [`Discharger.lean`](Barrel/Discharger.lean) for naming details).

The discharger also produces Lean theorems named after the POG tags–e.g. `Counter.Initialisation_<i>`, which can be used as lemmas in subsequent proofs, if needed.

## How it works (high level)
1. **Parse PO XML**: read types, definitions, and proof obligations from Atelier B’s PO XML schema.
2. **Extract logical goals**: turn the schema into `Goal` records containing variables, hypotheses, and the goal term.
3. **Encode to Lean**: map B terms and types to Lean expressions, using the set-theoretic primitives in `Barrel/Builtins.lean` and Lean's meta-programming features.
4. **Discharge**: generate Lean theorem declarations for each goal and run the user-supplied tactics. Generated goals should closely resemble the original B proof obligations.

## Sample models
The `specs/` folder contains small machines used during development:
- `Counter.mch`, `Nat.mch`, `Forall.mch`, `Exists.mch`, `Injective.mch`, `HO.mch`, `Enum.mch`, `Lambda.mch`, and their corresponding `.pog` files.
You can copy these as templates when adding new B models.


## Contributing
Contributions and bug reports are very welcome!
