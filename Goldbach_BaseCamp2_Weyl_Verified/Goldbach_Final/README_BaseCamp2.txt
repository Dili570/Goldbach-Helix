# Goldbach Conjecture Formalization Project
### An AI-Assisted Formal Verification Experiment

**Project Lead:** Dylan Shay  
**Tools:** Lean 4, Mathlib, Google Gemini (Advanced)

#### **Project Overview**
This repository documents a "Human-in-the-Loop" experiment to formalize the **Circle Method** and **Weyl's Inequality** using Lean 4. As a construction professional (Chief Architect/Project Manager) with no formal background in academic mathematics, I utilized Large Language Models (LLMs) to bridge the gap between geometric intuition and formal theorem proving.

#### **Current Status: Base Camp 2 (Verified)**
* **Objective:** Define the "Major/Minor Arc" decomposition and state Weyl's Bound.
* **Result:** Successfully defined the `RationalApprox` structure and `IsMinorArc` conditions.
* **Verification:** The `minor_arc_weyl_bound` theorem has been type-checked by the Lean 4 compiler (Mathlib compatible). The proof body is currently abstracted (`sorry`) to focus on structural integrity.

#### **Why This Matters**
This project serves as a case study in **Auto-formalization** and **AI-Assisted Education**. It demonstrates that complex Analytic Number Theory concepts can be architected and verified by non-traditional researchers when supported by high-reasoning AI tools.

**Key Files:**
* `GoldbachFinal.lean` - The active formalization file containing the Weyl Bound logic.