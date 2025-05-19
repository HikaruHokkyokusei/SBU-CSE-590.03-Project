# SBU-CSE-590.03 Project

This repository contains the fully verified **Specification** for the SBU CSE 590.03 project, comprising:

1. **High-Level State Machine**
2. **Low-Level State Machine** (First refinement: Refines the High-Level State Machine)
3. **Implementation** (Second refinement: Refines the Low Level State Machine specification)

> **Note:** This README covers *only* items 1 and 2 (“Specification”). The `master` branch,
> which this submission is about, only contains "Specification."
> The implementation layer is under separate development (on a different branch `Multi-Paxos`)
> and is **NOT** part of this submission.

---

## Table of Contents

- [Repository](#repository)
- [Specification Layers](#specification-layers)
- [Verification & Toolchain Requirements](#verification--toolchain-requirements)
- [Building & Checking the Specification](#building--checking-the-specification)
- [AI Tools & External Guidance](#ai-tools--external-guidance)
- [Acknowledgements & References](#acknowledgements--references)

---

## Repository

**Primary:** `master` branch (The latest commit contains complete specification)

```bash
git clone https://github.com/HikaruHokkyokusei/SBU-CSE-590.03-Project.git

cd SBU-CSE-590.03-Project
```

---

## Specification Layers

The specification is developed via a two‑level refinement:

1. **High-Level State Machine**
    * Abstract model of hosts, messages, and network
    * Captures protocol invariants at a coarse granularity
2. **Low-Level State Machine**
    * First refinement of the high‑level
    * Introduces concrete state representations (maps, sets, ballots)
    * Proves refinement relation to the high‑level spec

> ⚙️ This is a **complete, ground‑up** specification: **all proofs fully verified**, with **zero** `assume`/`admit`.

---

## Verification & Toolchain Requirements

* **Verus** (Release): `any build ≥ March 25, 2025` (Latest is **HIGHLY** recommended over other past versions)
* **Rust Toolchain**: `1.82.0-x86_64-pc-windows-msvc`
* Platform Tested: **Windows**

> The Verus proofs rely on the latest release; ensure you have a Verus build ≥ March 25, 2025.
> At this stage, it is **NOT** possible for me to downgrade verus.

> Setting a custom Verus binary in `VS Code`'s Verus Extension is straight forward.
> Go to `File > Preferences > Setting > Search - Verus Binary > Add path to verus binary in setting.json`

---

## Building & Checking the Specification

1. Install Rust 1.82.0 and add to `PATH`.
2. Install Verus (see [Verus docs](https://github.com/verus-lang/verus)).
3. To verify the proof, run `verus src/main.rs` in the repo root. Assuming `verus` command points to minimum required verus binary.
4. All proofs should be verified successfully.

---

## AI Tools & External Guidance

* **AI Assistants:** ChatGPT (o4-mini-high), Cursor, Claude
    * Direct AI-derived content ≈ 5–10% (basic proof steps)
    * Indirect AI guidance (hints, suggestions) ≈ 60–70%

> While AI and community guidance were helpful, **all** core proofs were manually written and verified.

---

## Acknowledgements & References

* **Verus Language & Library:** Code, axioms, examples
* **Verus Maintainers:** [Bryan Parno](https://github.com/parno), [Travis Hance](https://github.com/tjhance), [Jay Lorch](https://github.com/jaylorch), [Matthias Brun](https://github.com/matthias-brun)
* **GitHub Issues / Discussions**:
  * **[#1525](https://github.com/verus-lang/verus/issues/1525)**: Finiteness of the empty set → now treated finite by default in newer Verus versions.
  * **[#1543](https://github.com/verus-lang/verus/issues/1543) / [#1544](https://github.com/verus-lang/verus/discussions/1544)**: Oversight in set-property proofs.
  * **[#1574](https://github.com/verus-lang/verus/discussions/1574)**: Assertions (`==>`), `implies`, quantifiers, and triggers.
  * **[#1592](https://github.com/verus-lang/verus/discussions/1592)**: Further help with quantifiers and triggers.
* **Professor Shuai Mu:** High‑Level design & debugging
* **Verus Documentation:** Specification patterns and library internals

---
