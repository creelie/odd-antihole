import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import OddAntihole.Cycle

/-!
# The odd antihole

The odd antihole on `2m + 1` vertices has chromatic number `m + 1`, and it is strongly
`(m + 1)`-chromatic-choosable for `m ≥ 2`: this is Conjecture 9 of Fiujlaali and McDonald.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- The odd antihole `C̄_{2m+1}`, the complement of the cycle of length `2m+1`. -/
def oddAntihole (m : ℕ) : SimpleGraph (Fin (2 * m + 1)) :=
  (SimpleGraph.cycleGraph (2 * m + 1))ᶜ

theorem cyc_adj_iff {n : ℕ} (hn : 2 ≤ n) (u v : Fin n) :
    (SimpleGraph.cycleGraph n).Adj u v ↔ cadj n u.val v.val := by
  rw [SimpleGraph.cycleGraph_adj']
  have hu := u.isLt
  have hv := v.isLt
  have h1 : ((u - v : Fin n) : ℕ) =
      if v.val ≤ u.val then u.val - v.val else n + u.val - v.val := by
    split_ifs with h
    · exact Fin.coe_sub_iff_le.2 (Fin.le_def.2 h)
    · exact Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 (by omega))
  have h2 : ((v - u : Fin n) : ℕ) =
      if u.val ≤ v.val then v.val - u.val else n + v.val - u.val := by
    split_ifs with h
    · exact Fin.coe_sub_iff_le.2 (Fin.le_def.2 h)
    · exact Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 (by omega))
  rw [h1, h2]
  unfold cadj
  by_cases h3 : v.val ≤ u.val
  · rw [if_pos h3]
    by_cases h4 : u.val ≤ v.val
    · rw [if_pos h4]; constructor <;> intro h <;> omega
    · rw [if_neg h4]; constructor <;> intro h <;> omega
  · rw [if_neg h3, if_pos (by omega : u.val ≤ v.val)]; constructor <;> intro h <;> omega

/-- A proper colouring of `G` from the lists `L`. -/
def ListColorable {V : Type*} (G : SimpleGraph V) {β : Type*} (L : V → Finset β) : Prop :=
  ∃ f : V → β, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v

theorem antihole_lists [Inhabited α] (m : ℕ) (hm : 2 ≤ m) (L : Fin (2 * m + 1) → Finset α)
    (hL : ∀ v, m ≤ (L v).card) (hnc : ¬ ListColorable (oddAntihole m) L) :
    ∀ u v, L u = L v := by
  let L' : ℕ → Finset α := fun v => if h : v < 2 * m + 1 then L ⟨v, h⟩ else ∅
  have hL' : ∀ v < 2 * m + 1, m ≤ (L' v).card := by
    intro v hv
    simp only [L', dif_pos hv]
    exact hL _
  have hnc' : ¬ CCol (2 * m + 1) L' := by
    rintro ⟨f, hf, hadj⟩
    apply hnc
    refine ⟨fun v => f v.val, fun v => ?_, fun u v huv hfe => ?_⟩
    · have := hf v.val v.isLt
      simp only [L', dif_pos v.isLt] at this
      exact this
    · rw [oddAntihole, SimpleGraph.compl_adj] at huv
      exact huv.2 ((cyc_adj_iff (by omega) u v).2
        (hadj u.val u.isLt v.val v.isLt (Fin.val_ne_of_ne huv.1) hfe))
  intro u v
  have := cycle_main m hm L' hL' hnc' u.val u.isLt v.val v.isLt
  simp only [L', dif_pos u.isLt, dif_pos v.isLt] at this
  exact this

theorem antihole_colorable (m : ℕ) (hm : 1 ≤ m) : (oddAntihole m).Colorable (m + 1) := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨v.val / 2, by have := v.isLt; omega⟩) ?_⟩
  intro u v huv hfe
  rw [oddAntihole, SimpleGraph.compl_adj, cyc_adj_iff (by omega : 2 ≤ 2 * m + 1)] at huv
  have h1 := Fin.val_ne_of_ne huv.1
  have h2 : u.val / 2 = v.val / 2 := congrArg Fin.val hfe
  apply huv.2
  unfold cadj
  omega

theorem antihole_not_colorable (m : ℕ) (hm : 2 ≤ m) : ¬ (oddAntihole m).Colorable m := by
  rintro ⟨C⟩
  obtain ⟨y, -, hy⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (univ : Finset (Fin (2 * m + 1)))) (t := (univ : Finset (Fin m))) (f := C) (n := 2)
    (fun a _ => mem_univ _)
    (by rw [card_univ, card_univ, Fintype.card_fin, Fintype.card_fin]; omega)
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := two_lt_card_iff.1 hy
  rw [mem_filter] at ha hb hd
  have key : ∀ x z : Fin (2 * m + 1), C x = C z → x ≠ z → cadj (2 * m + 1) x.val z.val := by
    intro x z hxz hne
    by_contra hc
    have hadj : (oddAntihole m).Adj x z := by
      rw [oddAntihole, SimpleGraph.compl_adj, cyc_adj_iff (by omega : 2 ≤ 2 * m + 1)]
      exact ⟨hne, hc⟩
    exact C.valid hadj hxz
  have h1 := key a b (ha.2.trans hb.2.symm) hab
  have h2 := key a d (ha.2.trans hd.2.symm) had
  have h3 := key b d (hb.2.trans hd.2.symm) hbd
  have n1 := Fin.val_ne_of_ne hab
  have n2 := Fin.val_ne_of_ne had
  have n3 := Fin.val_ne_of_ne hbd
  have l1 := a.isLt
  have l2 := b.isLt
  have l3 := d.isLt
  unfold cadj at h1 h2 h3
  omega

theorem antihole_chromaticNumber (m : ℕ) (hm : 2 ≤ m) :
    (oddAntihole m).chromaticNumber = ((m + 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact (antihole_colorable m (by omega)).chromaticNumber_le
  · rw [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff]
    exact not_le.1 (fun h => antihole_not_colorable m hm
      (SimpleGraph.chromaticNumber_le_iff_colorable.1 h))

end OddAntihole

universe u

open OddAntihole in
/-- `G` is strongly `ℓ`-chromatic-choosable: its chromatic number is `ℓ`, and every assignment
of lists of size `ℓ - 1` from which `G` cannot be coloured gives every vertex the same list. -/
def StronglyChromaticChoosable {V : Type*} (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  G.chromaticNumber = ℓ ∧
    ∀ (β : Type u) [DecidableEq β] (L : V → Finset β), (∀ v, (L v).card = ℓ - 1) →
      ¬ ListColorable G L → ∀ u v, L u = L v

open OddAntihole in
/-- **Conjecture 9 of Fiujlaali and McDonald.** For every `ℓ ≥ 3` the odd antihole on `2ℓ - 1`
vertices is strongly `ℓ`-chromatic-choosable. -/
theorem odd_antihole_strongly_chromatic_choosable (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    StronglyChromaticChoosable.{u} (oddAntihole (ℓ - 1)) ℓ := by
  refine ⟨?_, ?_⟩
  · rw [antihole_chromaticNumber (ℓ - 1) (by omega), Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
  · intro β _ L hL hnc
    obtain ⟨x, -⟩ := card_pos.1 (by rw [hL 0]; omega : 0 < (L 0).card)
    have : Inhabited β := ⟨x⟩
    exact antihole_lists (ℓ - 1) (by omega) L (fun v => (hL v).ge) hnc
