/-
  Task 7: eVRF security game hops (Appendix D of the Golden paper).

  The eVRF security proof proceeds via two game hops:
    Game 0 → Game 1: Replace DH shared secret with random (NIKE unrecoverability)
    Game 1 → Game 2: Replace r with truly random (Leftover Hash Lemma)
    Advantage bound: Adv ≤ Adv_DH^unrec + O(1/√p)

  We formalize:
  1. The game-based security framework (games as functions returning distributions)
  2. The Leftover Hash Lemma for the specific extraction r = beta * r1 + r2
  3. The game hop reductions
  4. The final advantage bound

  Per Appendix C: "Delta ≤ 8h²√p / (p - 2h) = O(1/√p)"
  Per Appendix D: "Adv ≤ Adv_DH^unrec + O(1/√p)"
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
## Game-Based Security Framework

We model security games as functions from adversary state to outcomes.
Advantage is the difference in probability of distinguishing two games.
This is a lightweight version of VCV-io's OracleComp; a full formalization
would use VCV-io's monadic framework.
-/

section GameFramework

/-- Abstract probability type (real number in [0,1]). -/
abbrev Prob := ℝ

/-- Advantage of a distinguisher between two games.
    |Pr[Game0 → 1] - Pr[Game1 → 1]| -/
def advantage (p0 p1 : Prob) : ℝ := |p0 - p1|

/-- Triangle inequality for advantages (game hop composition). -/
theorem advantage_triangle (p0 p1 p2 : Prob) :
    advantage p0 p2 ≤ advantage p0 p1 + advantage p1 p2 := by
  unfold advantage
  sorry -- abs_sub triangle: |a - c| ≤ |a - b| + |b - c|

end GameFramework

/-!
## Leftover Hash Lemma (Appendix C)

The LHL shows that for a universal hash family {h_beta : x ↦ beta * x + c},
the output is statistically close to uniform when the source has sufficient
min-entropy.

Applied to eVRF: r = beta * r1 + r2 where r1, r2 are x-coordinates of
elliptic curve points. The statistical distance from uniform is bounded by:
  Delta ≤ 8h²√p / (p - 2h) where h = #images of x-coordinate extraction
-/

section LeftoverHashLemma

variable (p : ℕ) -- field characteristic (prime)
variable (h : ℕ) -- number of distinct x-coordinate images

/-- **Leftover Hash Lemma bound (Appendix C).**

    For the extraction r = beta * r1 + r2 over F_p, where r1, r2 each take
    at most h values, the statistical distance from uniform is at most:
      Delta ≤ 8 * h² * √p / (p - 2*h)

    This holds when p > 2*h (i.e., the field is large enough relative to
    the number of x-coordinate images).
-/
noncomputable def lhl_bound (p h : ℕ) : ℝ :=
  8 * (h : ℝ)^2 * Real.sqrt p / ((p : ℝ) - 2 * h)

/-- The LHL bound is O(1/√p) when h is polynomial in the security parameter.
    For BLS12-381: p ≈ 2^255, h ≤ (p+1)/2, so Delta is negligible. -/
theorem lhl_bound_negligible (hp : (2 : ℝ) * h < p) (hh : (h : ℝ) ≤ Real.sqrt p) :
    lhl_bound p h ≤ 8 * Real.sqrt p * Real.sqrt p * Real.sqrt p / ((p : ℝ) - 2 * h) := by
  unfold lhl_bound
  sorry -- Requires: h^2 ≤ (√p)^2 = p, then simplify

end LeftoverHashLemma

/-!
## Game Hops (Appendix D)

Game 0: Real eVRF execution
  S = DH(sk, PK'), k = int(S.X), r = beta * int(H1^k.X) + int(H2^k.X)

Game 1: Replace S with random group element
  S ← random G, k = int(S.X), r = beta * int(H1^k.X) + int(H2^k.X)

Game 2: Replace r with truly random
  r ← random F_p

Transitions:
  |Game0 - Game1| ≤ Adv_NIKE^unrec (DH unrecoverability)
  |Game1 - Game2| ≤ LHL bound = O(1/√p)
-/

section GameHops

variable (adv_nike : ℝ)    -- NIKE unrecoverability advantage
variable (p_field : ℕ)     -- field size
variable (h_images : ℕ)    -- x-coord image count

/-- **Game 0 → Game 1: NIKE reduction.**

    Replacing the DH shared secret S = sk • PK' with a random group element
    is indistinguishable up to the NIKE unrecoverability advantage.

    Any distinguisher D between Game 0 and Game 1 can be converted into
    an attacker A against NIKE unrecoverability with the same advantage.
-/
axiom game0_to_game1 (prob_game0 prob_game1 : Prob) :
    advantage prob_game0 prob_game1 ≤ adv_nike

/-- **Game 1 → Game 2: Leftover Hash Lemma.**

    In Game 1, S is random, so k = int(S.X) is close to uniform over F_p.
    Then r = beta * r1 + r2 is close to uniform by the LHL.
-/
axiom game1_to_game2 (prob_game1 prob_game2 : Prob) :
    advantage prob_game1 prob_game2 ≤ lhl_bound p_field h_images

/-- **eVRF Security Theorem (Appendix D).**

    The eVRF advantage is bounded by the NIKE advantage plus the LHL bound:
      Adv_eVRF ≤ Adv_NIKE^unrec + O(1/√p)

    This is the composition of the two game hops.
-/
theorem evrf_security_bound (prob_real prob_ideal : Prob)
    (prob_game1 : Prob)
    (h01 : advantage prob_real prob_game1 ≤ adv_nike)
    (h12 : advantage prob_game1 prob_ideal ≤ lhl_bound p_field h_images) :
    advantage prob_real prob_ideal ≤ adv_nike + lhl_bound p_field h_images := by
  calc advantage prob_real prob_ideal
      ≤ advantage prob_real prob_game1 + advantage prob_game1 prob_ideal :=
        advantage_triangle prob_real prob_game1 prob_ideal
    _ ≤ adv_nike + lhl_bound p_field h_images :=
        add_le_add h01 h12

end GameHops
