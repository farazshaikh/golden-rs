---
name: Paper Reference Setup
overview: Save the Golden DKG paper into a papers/ folder and update the .cursor/PLAN.md master plan to instruct all subagents to reference the paper before implementing.
todos:
  - id: save-paper
    content: Save Golden DKG paper content to papers/golden_dkg.md
    status: completed
  - id: update-plan
    content: Update .cursor/PLAN.md with subagent paper-reference protocol
    status: completed
isProject: false
---

# Paper Reference Setup

## Step 1: Create papers/ folder with the Golden paper

Save the full paper content as a markdown reference at `/wrk/tmt/goldenkeysharing/papers/golden_dkg.md` -- this captures all the protocol definitions, equations, and pseudocode (Figure 4) that subagents need when implementing.

The paper source is: [https://eprint.iacr.org/2025/1924.pdf](https://eprint.iacr.org/2025/1924.pdf)

## Step 2: Update `.cursor/PLAN.md` master plan

Add a new top-level section to `[.cursor/PLAN.md](/wrk/tmt/goldenkeysharing/.cursor/PLAN.md)` with a "Subagent Protocol" block that says:

- Before implementing ANY phase, read `papers/golden_dkg.md` first
- Cross-reference the paper's Figure 4 (Round0 / Round1 pseudocode) for protocol correctness
- Reference Section 4 for eVRF construction details
- Reference Section 3.3 for Shamir / Lagrange definitions
- Reference Section 5.3 for batch optimizations
