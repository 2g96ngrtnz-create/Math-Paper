import Mathlib

/-!
# Finite product probability

The random orientation of a finite graph is a finite product of independent Bernoulli variables.
Here `ι` is a finite index set (later, the edges), an outcome is `ω : ι → Bool`, and coordinate `i`
is `true` with probability `ρ`. The weight of `ω` is `wt ρ ω = ∏ᵢ (ρ if ω i else 1 − ρ)`.
Expectations and probabilities are finite sums:
`expectP ρ f = ∑_ω wt ρ ω · f ω` and `prob ρ A = expectP ρ 1_A`.

No measure theory is needed. This file proves the facts the paper uses:
* total mass `1`, linearity and monotonicity;
* the union bound, and `P(A ∩ B) ≥ P(A) − P(Bᶜ)`;
* **cylinders**: `P(ω i = c i for all i ∈ s) = ∏_{i ∈ s} (ρ if c i else 1 − ρ)`;
* **independence**: if `f` depends only on the coordinates in `s`, `g` only on those in `t`,
  and `s`, `t` are disjoint, then `E[fg] = E[f] E[g]`. The same holds for finitely many functions
  of pairwise disjoint blocks.
-/

namespace HubRemoval

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P(ω i = b)` for one coordinate. -/
def pb (ρ : ℝ) (b : Bool) : ℝ := if b then ρ else 1 - ρ

/-- The weight of an outcome. -/
def wt (ρ : ℝ) (ω : ι → Bool) : ℝ := ∏ i, pb ρ (ω i)

/-- Expectation. -/
def expectP (ρ : ℝ) (f : (ι → Bool) → ℝ) : ℝ := ∑ ω, wt ρ ω * f ω

open Classical in
/-- Probability of an event. -/
noncomputable def prob (ρ : ℝ) (A : (ι → Bool) → Prop) : ℝ :=
  expectP ρ fun ω => if A ω then 1 else 0

/-- `prob` computed with any decidability instance. -/
theorem prob_eq (ρ : ℝ) (A : (ι → Bool) → Prop) [DecidablePred A] :
    prob ρ A = ∑ ω, wt ρ ω * (if A ω then 1 else 0) := by
  unfold prob expectP
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : A ω <;> simp [h]

theorem pb_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (b : Bool) : 0 ≤ pb ρ b := by
  cases b <;> simp [pb] <;> linarith

omit [DecidableEq ι] in
theorem wt_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (ω : ι → Bool) : 0 ≤ wt ρ ω :=
  prod_nonneg fun _ _ => pb_nonneg h0 h1 _

/-- The weights sum to `1`. -/
theorem sum_wt (ρ : ℝ) : ∑ ω : ι → Bool, wt ρ ω = 1 := by
  unfold wt
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) => pb ρ b)]
  simp [pb]

theorem expectP_const (ρ c : ℝ) : expectP ρ (fun _ : ι → Bool => c) = c := by
  unfold expectP
  rw [← sum_mul, sum_wt, one_mul]

theorem expectP_add (ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    expectP ρ (fun ω => f ω + g ω) = expectP ρ f + expectP ρ g := by
  unfold expectP
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => mul_add _ _ _

theorem expectP_sub (ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    expectP ρ (fun ω => f ω - g ω) = expectP ρ f - expectP ρ g := by
  unfold expectP
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun ω _ => mul_sub _ _ _

theorem expectP_const_mul (ρ c : ℝ) (f : (ι → Bool) → ℝ) :
    expectP ρ (fun ω => c * f ω) = c * expectP ρ f := by
  unfold expectP
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by ring

theorem expectP_sum {α : Type*} (ρ : ℝ) (S : Finset α) (f : α → (ι → Bool) → ℝ) :
    expectP ρ (fun ω => ∑ a ∈ S, f a ω) = ∑ a ∈ S, expectP ρ (f a) := by
  unfold expectP
  simp_rw [mul_sum]
  exact sum_comm

theorem expectP_mono {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {f g : (ι → Bool) → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) : expectP ρ f ≤ expectP ρ g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (wt_nonneg h0 h1 ω)

open Classical in
theorem prob_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (A : (ι → Bool) → Prop) :
    0 ≤ prob ρ A :=
  sum_nonneg fun ω _ => mul_nonneg (wt_nonneg h0 h1 ω) (by dsimp only; split_ifs <;> norm_num)

open Classical in
theorem prob_mono {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {A B : (ι → Bool) → Prop}
    (hAB : ∀ ω, A ω → B ω) : prob ρ A ≤ prob ρ B :=
  expectP_mono h0 h1 fun ω => by
    by_cases hA : A ω
    · simp [hA, hAB ω hA]
    · simp only [hA, ↓reduceIte]
      split_ifs <;> norm_num

open Classical in
theorem prob_le_one {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (A : (ι → Bool) → Prop) :
    prob ρ A ≤ 1 :=
  calc prob ρ A ≤ expectP ρ (fun _ : ι → Bool => (1 : ℝ)) :=
        expectP_mono h0 h1 fun ω => by split_ifs <;> norm_num
    _ = 1 := expectP_const ρ 1

open Classical in
theorem prob_not (ρ : ℝ) (A : (ι → Bool) → Prop) :
    prob ρ (fun ω => ¬ A ω) = 1 - prob ρ A := by
  have h : prob ρ (fun ω => ¬ A ω) + prob ρ A = 1 := by
    unfold prob
    rw [← expectP_add]
    convert expectP_const (ι := ι) ρ 1 using 2
    funext ω
    by_cases hA : A ω <;> simp [hA]
  linarith

open Classical in
/-- `P(A ∩ B) ≥ P(A) − P(Bᶜ)`. -/
theorem prob_and_ge {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (A B : (ι → Bool) → Prop) :
    prob ρ A - prob ρ (fun ω => ¬ B ω) ≤ prob ρ (fun ω => A ω ∧ B ω) := by
  unfold prob
  rw [← expectP_sub]
  exact expectP_mono h0 h1 fun ω => by
    by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

open Classical in
/-- The union bound, for two events. -/
theorem prob_or_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (A B : (ι → Bool) → Prop) :
    prob ρ (fun ω => A ω ∨ B ω) ≤ prob ρ A + prob ρ B := by
  unfold prob
  rw [← expectP_add]
  exact expectP_mono h0 h1 fun ω => by
    by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

open Classical in
/-- The union bound over a finite family. -/
theorem prob_exists_le {α : Type*} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (S : Finset α)
    (A : α → (ι → Bool) → Prop) :
    prob ρ (fun ω => ∃ a ∈ S, A a ω) ≤ ∑ a ∈ S, prob ρ (A a) := by
  unfold prob
  rw [← expectP_sum]
  refine expectP_mono h0 h1 fun ω => ?_
  by_cases hex : ∃ a ∈ S, A a ω
  · obtain ⟨a, ha, hA⟩ := hex
    simp only [show ∃ a ∈ S, A a ω from ⟨a, ha, hA⟩, ↓reduceIte]
    calc (1 : ℝ) = (fun a => if A a ω then (1 : ℝ) else 0) a := by simp [hA]
      _ ≤ ∑ b ∈ S, (fun a => if A a ω then (1 : ℝ) else 0) b :=
          single_le_sum (f := fun a => if A a ω then (1 : ℝ) else 0)
            (fun b _ => by split_ifs <;> norm_num) ha
  · simp only [hex, ↓reduceIte]
    exact sum_nonneg fun b _ => by split_ifs <;> norm_num

/-- The factor used to write a cylinder's indicator times the weight as a product. -/
def cylFactor (ρ : ℝ) (s : Finset ι) (c : ι → Bool) (i : ι) (b : Bool) : ℝ :=
  if i ∈ s then (if b = c i then pb ρ b else 0) else pb ρ b

open Classical in
/-- **Cylinders.** `P(ω i = c i for all i ∈ s) = ∏_{i ∈ s} P(ω i = c i)`. -/
theorem prob_cylinder (ρ : ℝ) (s : Finset ι) (c : ι → Bool) :
    prob ρ (fun ω => ∀ i ∈ s, ω i = c i) = ∏ i ∈ s, pb ρ (c i) := by
  set f := cylFactor ρ s c with hfdef
  have hprod : ∀ ω : ι → Bool,
      wt ρ ω * (if ∀ i ∈ s, ω i = c i then 1 else 0) = ∏ i, f i (ω i) := by
    intro ω
    by_cases hcyl : ∀ i ∈ s, ω i = c i
    · rw [ite_eq_left hcyl, mul_one, wt]
      refine Fintype.prod_congr _ _ fun i => ?_
      by_cases hi : i ∈ s
      · simp [hfdef, cylFactor, hi, hcyl i hi]
      · simp [hfdef, cylFactor, hi]
    · rw [ite_eq_right hcyl, mul_zero]
      push Not at hcyl
      obtain ⟨i, hi, hne⟩ := hcyl
      exact (prod_eq_zero (mem_univ i) (by simp [hfdef, cylFactor, hi, hne])).symm
  rw [prob_eq]
  simp_rw [hprod]
  rw [← Fintype.prod_sum f]
  have hsum : ∀ i, ∑ b, f i b = if i ∈ s then pb ρ (c i) else 1 := by
    intro i
    by_cases hi : i ∈ s
    · rw [Fintype.sum_bool]
      cases hc : c i <;> simp [hfdef, cylFactor, hi, hc]
    · rw [Fintype.sum_bool]
      simp [hfdef, cylFactor, hi, pb]
  simp_rw [hsum]
  rw [prod_ite_mem univ s, univ_inter]

/-- `f` depends only on the coordinates in `s`. -/
def DependsOnCoords (f : (ι → Bool) → ℝ) (s : Finset ι) : Prop :=
  ∀ ω ω' : ι → Bool, (∀ i ∈ s, ω i = ω' i) → f ω = f ω'

/-- The weight splits along a partition of the coordinates into `s` and its complement. -/
theorem wt_split (ρ : ℝ) (s : Finset ι)
    (x : ({i // i ∈ s} → Bool) × ({i // i ∉ s} → Bool)) :
    wt ρ ((Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bool)).symm x) =
      wt ρ x.1 * wt ρ x.2 := by
  have h1 : ∏ i : {i // i ∈ s},
      pb ρ ((Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bool)).symm x i) =
      ∏ i, pb ρ (x.1 i) :=
    Fintype.prod_congr _ _ fun i => by simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  have h2 : ∏ i : {i // i ∉ s},
      pb ρ ((Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bool)).symm x i) =
      ∏ i, pb ρ (x.2 i) :=
    Fintype.prod_congr _ _ fun i => by simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  unfold wt
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ s)]
  convert congrArg₂ (· * ·) h1 h2 using 3
  congr 1
  exact Subsingleton.elim _ _

/-- **Independence.** If `f` depends only on the coordinates in `s`, `g` only on those in `t`,
and `s` and `t` are disjoint, then `E[fg] = E[f] E[g]`. -/
theorem expectP_mul_of_disjoint (ρ : ℝ) {s t : Finset ι} (hst : Disjoint s t)
    {f g : (ι → Bool) → ℝ} (hf : DependsOnCoords f s) (hg : DependsOnCoords g t) :
    expectP ρ (fun ω => f ω * g ω) = expectP ρ f * expectP ρ g := by
  set e := Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bool)
  set F : ({i // i ∈ s} → Bool) → ℝ := fun σ => f (e.symm (σ, fun _ => false))
  set G : ({i // i ∉ s} → Bool) → ℝ := fun τ => g (e.symm (fun _ => false, τ))
  have hfe : ∀ x, f (e.symm x) = F x.1 := fun x =>
    hf _ _ fun i hi => by simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hge : ∀ x, g (e.symm x) = G x.2 := fun x =>
    hg _ _ fun i hi => by
      have hi' : i ∉ s := fun h => disjoint_left.mp hst h hi
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi']
  -- Rewrite each expectation as a double sum over `(σ, τ)`.
  have key : ∀ h : (ι → Bool) → ℝ, expectP ρ h =
      ∑ σ : {i // i ∈ s} → Bool, ∑ τ : {i // i ∉ s} → Bool,
        wt ρ σ * wt ρ τ * h (e.symm (σ, τ)) := by
    intro h
    unfold expectP
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
    rw [wt_split]
  have hF : expectP ρ f = ∑ σ : {i // i ∈ s} → Bool, wt ρ σ * F σ := by
    rw [key]
    refine sum_congr rfl fun σ _ => ?_
    simp_rw [hfe]
    rw [← sum_mul, ← mul_sum, sum_wt, mul_one]
  have hG : expectP ρ g = ∑ τ : {i // i ∉ s} → Bool, wt ρ τ * G τ := by
    rw [key]
    simp_rw [hge]
    rw [sum_comm]
    refine sum_congr rfl fun τ _ => ?_
    rw [← sum_mul, ← sum_mul, sum_wt, one_mul]
  rw [key, hF, hG, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  rw [hfe, hge]
  ring

/-- **Independence for finitely many blocks.** If the blocks `s y`, `y ∈ Y`, are pairwise
disjoint and each `h y` depends only on `s y`, then `E[∏_y h y] = ∏_y E[h y]`. -/
theorem expectP_prod_of_pairwiseDisjoint {α : Type*} [DecidableEq α] (ρ : ℝ) (Y : Finset α)
    (s : α → Finset ι) (h : α → (ι → Bool) → ℝ)
    (hdisj : (Y : Set α).PairwiseDisjoint s) (hdep : ∀ y ∈ Y, DependsOnCoords (h y) (s y)) :
    expectP ρ (fun ω => ∏ y ∈ Y, h y ω) = ∏ y ∈ Y, expectP ρ (h y) := by
  induction Y using Finset.induction_on with
  | empty => simpa using expectP_const ρ 1
  | insert y₀ Y hy₀ ih =>
    have hdisj' : (Y : Set α).PairwiseDisjoint s :=
      hdisj.subset (by simp [Set.subset_insert])
    have hdep' : ∀ y ∈ Y, DependsOnCoords (h y) (s y) := fun y hy => hdep y (mem_insert_of_mem hy)
    have hrest : DependsOnCoords (fun ω => ∏ y ∈ Y, h y ω) (Y.biUnion s) := fun ω ω' hωω' =>
      prod_congr rfl fun y hy =>
        hdep' y hy ω ω' fun i hi => hωω' i (mem_biUnion.mpr ⟨y, hy, hi⟩)
    have hst : Disjoint (s y₀) (Y.biUnion s) := by
      rw [disjoint_biUnion_right]
      intro y hy
      exact hdisj (mem_insert_self y₀ Y) (mem_insert_of_mem hy)
        (fun h => hy₀ (h ▸ hy))
    simp_rw [prod_insert hy₀]
    rw [expectP_mul_of_disjoint ρ hst (hdep y₀ (mem_insert_self y₀ Y)) hrest, ih hdisj' hdep']

end HubRemoval
