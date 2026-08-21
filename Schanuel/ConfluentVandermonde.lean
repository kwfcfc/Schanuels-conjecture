import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The repeated-node polynomial zero estimate

This file records the algebraic injectivity statement underlying a confluent
Vandermonde matrix.  If a polynomial of degree less than `m * #ι` and its
first `m - 1` derivatives vanish at `#ι` distinct points, then the polynomial
is zero.

For exponential-polynomial jets at one point, the transpose of the jet matrix
is precisely this Hermite-evaluation map.  Thus this is the sharp algebraic
zero estimate used in auxiliary-function counts; it contains no arithmetic or
transcendence hypothesis.
-/

namespace Schanuel

open Polynomial

noncomputable section

/-- The monic polynomial realizing multiplicity `m` at every node. -/
def confluentVanishingPolynomial
    {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) (m : ℕ) : K[X] :=
  ∏ i : ι, (X - C (x i)) ^ m

theorem confluentVanishingPolynomial_monic
    {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) (m : ℕ) :
    (confluentVanishingPolynomial x m).Monic := by
  rw [confluentVanishingPolynomial]
  exact monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C (x i)).pow m

/-- The degree threshold in the repeated-node zero estimate is attained. -/
theorem confluentVanishingPolynomial_natDegree
    {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) (m : ℕ) :
    (confluentVanishingPolynomial x m).natDegree = Fintype.card ι * m := by
  have hmonic : ∀ i ∈ (Finset.univ : Finset ι),
      ((X - C (x i)) ^ m : K[X]).Monic :=
    fun i _ ↦ (monic_X_sub_C (x i)).pow m
  rw [confluentVanishingPolynomial,
    natDegree_prod_of_monic (Finset.univ : Finset ι)
      (fun i ↦ (X - C (x i)) ^ m) hmonic]
  simp

/-- The polynomial realizing the threshold has the prescribed vanishing jets. -/
theorem confluentVanishingPolynomial_jet_zero
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (x : ι → K) (m : ℕ) (i : ι) (k : ℕ) (hk : k < m) :
    eval (x i) ((derivative^[k]) (confluentVanishingPolynomial x m)) = 0 := by
  classical
  let p := confluentVanishingPolynomial x m
  have hp : p ≠ 0 := (confluentVanishingPolynomial_monic x m).ne_zero
  have hdiv : (X - C (x i)) ^ m ∣ p := by
    exact Finset.dvd_prod_of_mem (fun j : ι ↦ (X - C (x j)) ^ m)
      (Finset.mem_univ i)
  have hmultiplicity : m ≤ p.rootMultiplicity (x i) :=
    (le_rootMultiplicity_iff hp).mpr hdiv
  exact isRoot_iterate_derivative_of_lt_rootMultiplicity
    (hk.trans_le hmultiplicity)

/-- A polynomial of degree strictly less than the total prescribed
multiplicity cannot vanish to multiplicity `m` at a finite family of distinct
points unless it is zero. -/
theorem polynomial_eq_zero_of_confluent_zeros
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (p : K[X]) (x : ι → K) (hx : Function.Injective x) (m : ℕ)
    (hjet : ∀ i (k : ℕ), k < m → eval (x i) ((derivative^[k]) p) = 0)
    (hdegree : p.natDegree < Fintype.card ι * m) :
    p = 0 := by
  classical
  by_contra hp
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    simp [this] at hdegree
  have hmultiplicity (i : ι) :
      m ≤ p.rootMultiplicity (x i) := by
    have hroot : ∀ k ≤ m - 1, ((derivative^[k]) p).IsRoot (x i) := by
      intro k hk
      rw [IsRoot.def]
      exact hjet i k (by omega)
    have hlt : m - 1 < p.rootMultiplicity (x i) :=
      lt_rootMultiplicity_of_isRoot_iterate_derivative hp hroot
    omega
  let s : Finset K := Finset.univ.image x
  have hsum_counts :
      ∑ a ∈ s, p.roots.count a ≤ p.roots.card := by
    let t : Finset K := s ∪ p.roots.toFinset
    calc
      ∑ a ∈ s, p.roots.count a ≤ ∑ a ∈ t, p.roots.count a := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_union_left)
      _ = p.roots.card := by
        apply Multiset.sum_count_eq_card
        intro a ha
        exact Finset.mem_union_right s (Multiset.mem_toFinset.mpr ha)
  have hsum_image :
      ∑ i : ι, p.roots.count (x i) = ∑ a ∈ s, p.roots.count a := by
    dsimp [s]
    exact (Finset.sum_image (f := fun a ↦ p.roots.count a)
      (s := Finset.univ) (fun i _ j _ hij ↦ hx hij)).symm
  have hlarge : Fintype.card ι * m ≤ p.natDegree := by
    calc
      Fintype.card ι * m = ∑ _i : ι, m := by simp
      _ ≤ ∑ i : ι, p.rootMultiplicity (x i) :=
        Finset.sum_le_sum fun i _ ↦ hmultiplicity i
      _ = ∑ i : ι, p.roots.count (x i) := by simp
      _ = ∑ a ∈ s, p.roots.count a := hsum_image
      _ ≤ p.roots.card := hsum_counts
      _ ≤ p.natDegree := Polynomial.card_roots' p
  exact (Nat.not_lt_of_ge hlarge) hdegree

end

end Schanuel
