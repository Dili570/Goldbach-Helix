# Goldbach Conjecture Formalization Project
### An AI-Assisted Formal Verification Experiment

**Project Lead:** Dylan Shay  
**Role:** Chief Architect / Independent Researcher  
**Tools:** Lean 4, Mathlib, Google Gemini (Advanced)

---

### **Project Overview**
This repository documents a "Human-in-the-Loop" experiment to architect a formal proof structure for the **Goldbach Conjecture** using the Circle Method.

As a construction professional with no prior academic background in Number Theory, I utilized Large Language Models to bridge the gap between geometric intuition and formal theorem proving. The goal is to demonstrate that AI-assisted formalization can enable domain experts to produce high-integrity, machine-verifiable research.

---

### **Current Status: Base Camp 3 (Signal & Noise Defined)**
**Status: VERIFIED (Green)**

We have successfully formalized the two critical structural components of the Circle Method:

#### **1. The "Noise" Control (Minor Arcs)**
* **Objective:** Prove that the "static" from non-aligned prime numbers is negligible.
* **Implementation:** Defined `IsMinorArc` based on large denominators ($q > \log^{10} N$).
* **Key Theorem:** `minor_arc_weyl_bound`
* **Result:** The compiler accepts the logic that Weyl's Inequality forces the exponential sum to be small on these arcs.

#### **2. The "Signal" Amplifier (Major Arcs)**
* **Objective:** Prove that the "music" from aligned prime numbers is strong and predictable.
* **Implementation:** Defined `IsMajorArc` for small denominators and constructed the `SingularSeries` (the "Volume Knob").
* **Key Fix:** Resolved complex syntax errors by replacing symbolic notation (`∏`) with robust functional programming (`Finset.prod`) to ensure stability.
* **Key Theorem:** `major_arc_signal_strength`
* **Result:** The compiler verifies the definition of the Singular Series and its relationship to the integral.

---

### **Technical Challenges Overcome**
* **Hardware Constraints:** Optimized import structures to run on consumer-grade hardware without crashing the Lean language server.
* **Type Casting:** Solved the "Neg ℕ" (Negative Natural Number) error by implementing rigorous type-casting to Real numbers (`N : ℝ`) for all Calculus operations.
* **Syntax Translation:** Successfully translated the visual intuition of "Prime Circles" ($e^{2\pi i \alpha}$) into verified Lean 4 syntax.

---

### **Next Steps: Base Camp 4**
The next phase ("The Summit") involves assembling these two components into the **Main Theorem**. We will combine the Minor Arc bound and the Major Arc signal to state the formal condition for the Goldbach Conjecture.

**Contact:**
[Your Link / Contact Info]