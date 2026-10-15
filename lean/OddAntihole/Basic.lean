import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Colourings of complements of unions of paths

`Col S L` says that the complement of the graph on `S ⊆ ℕ` whose edges join consecutive integers
can be coloured from the lists `L`. This file proves Hall's theorem in the form of a system of
distinct representatives, a double-counting bound, and the lemma of Erdős, Rubin and Taylor.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- `Col S L`: the complement of the graph on `S ⊆ ℕ` whose edges join consecutive integers
has an `L`-colouring, i.e. two distinct vertices may share a colour only when they are
consecutive integers. -/
def Col (S : Finset ℕ) (L : ℕ → Finset α) : Prop :=
  ∃ f : ℕ → α, (∀ v ∈ S, f v ∈ L v) ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → (u + 1 = v ∨ v + 1 = u)

/-- Hall's theorem in the form used throughout: a system of distinct representatives. -/
theorem hall_sdr [Inhabited α] (X : Finset ℕ) (L : ℕ → Finset α)
    (h : ∀ W ⊆ X, W.card ≤ (W.biUnion L).card) :
    ∃ f : ℕ → α, (∀ v ∈ X, f v ∈ L v) ∧ ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v := by
  have key := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : X => L x)).1 (by
      intro W
      have hsub : W.map (Function.Embedding.subtype _) ⊆ X := by
        intro x hx
        rw [mem_map] at hx
        obtain ⟨a, _, rfl⟩ := hx
        exact a.2
      have h1 := h _ hsub
      have h2 : (W.map (Function.Embedding.subtype _)).biUnion L = W.biUnion (fun x : X => L x) := by
        ext c; simp
      rw [card_map, h2] at h1
      exact h1)
  obtain ⟨g, hg, hgL⟩ := key
  refine ⟨fun v => if hv : v ∈ X then g ⟨v, hv⟩ else default, ?_, ?_⟩
  · intro v hv
    simp only [hv, dite_true]
    exact hgL _
  · intro u hu v hv huv
    simp only [hu, hv, dite_true] at huv
    exact congrArg Subtype.val (hg huv)

/-- A system of distinct representatives is a colouring. -/
theorem col_of_sdr [Inhabited α] (X : Finset ℕ) (L : ℕ → Finset α)
    (h : ∀ W ⊆ X, W.card ≤ (W.biUnion L).card) : Col X L := by
  obtain ⟨f, hf, hinj⟩ := hall_sdr X L h
  exact ⟨f, hf, fun u hu v hv huv hf' => absurd (hinj u hu v hv hf') huv⟩

/-- Double counting: if every colour lies in the lists of at most `q` vertices of `W`, and
every list has at least `q > 0` colours, then `|W| ≤ |N(W)|`. -/
theorem card_le_of_bounded (W : Finset ℕ) (L : ℕ → Finset α) (q : ℕ) (hq : 0 < q)
    (hL : ∀ v ∈ W, q ≤ (L v).card)
    (hc : ∀ c, (W.filter (fun v => c ∈ L v)).card ≤ q) :
    W.card ≤ (W.biUnion L).card := by
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun v c => c ∈ L v) (s := W) (t := W.biUnion L)
  have habove : ∀ v ∈ W, (Finset.bipartiteAbove (fun v c => c ∈ L v) (W.biUnion L) v).card
      = (L v).card := by
    intro v hv
    unfold Finset.bipartiteAbove
    congr 1
    ext c
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨⟨v, hv, h⟩, h⟩
  rw [sum_congr rfl habove] at hdc
  have hle1 : ∑ v ∈ W, q ≤ ∑ v ∈ W, (L v).card := sum_le_sum hL
  have hle2 : ∑ c ∈ W.biUnion L, (Finset.bipartiteBelow (fun v c => c ∈ L v) W c).card
      ≤ ∑ c ∈ W.biUnion L, q := sum_le_sum (fun c _ => hc c)
  simp only [sum_const, smul_eq_mul] at hle1 hle2
  have : W.card * q ≤ (W.biUnion L).card * q := by
    calc W.card * q ≤ _ := hle1
      _ = _ := hdc
      _ ≤ _ := hle2
  exact Nat.le_of_mul_le_mul_right this hq

/-- The lemma of Erdős, Rubin and Taylor in fibre form: if `X` is partitioned by `π` into at most
`q` classes, each a set of pairwise consecutive integers, and every list has at least `q` colours,
then `X` is colourable. -/
theorem ert [Inhabited α] : ∀ (q : ℕ) (X P : Finset ℕ) (π : ℕ → ℕ) (L : ℕ → Finset α),
    P.card ≤ q → (∀ v ∈ X, π v ∈ P) →
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v → π u = π v → (u + 1 = v ∨ v + 1 = u)) →
    (∀ v ∈ X, q ≤ (L v).card) → Col X L := by
  intro q
  induction q with
  | zero =>
    intro X P π L hP hπ _ _
    have hP0 : P = ∅ := card_eq_zero.1 (by omega)
    have hX : X = ∅ := by
      ext v
      simp only [notMem_empty, iff_false]
      intro hv
      have := hπ v hv
      simp [hP0] at this
    exact ⟨fun _ => default, by simp [hX], by simp [hX]⟩
  | succ q ih =>
    intro X P π L hP hπ hfib hL
    by_cases hpair : ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ π u = π v ∧ (L u ∩ L v).Nonempty
    · obtain ⟨u, hu, v, hv, huv, hπuv, c, hc⟩ := hpair
      rw [mem_inter] at hc
      have huvadj := hfib u hu v hv huv hπuv
      have hX' : ∀ w ∈ (X.erase u).erase v, π w ∈ P.erase (π u) := by
        intro w hw
        have hwv := ne_of_mem_erase hw
        have hw' := mem_of_mem_erase hw
        have hwu := ne_of_mem_erase hw'
        have hwX := mem_of_mem_erase hw'
        refine mem_erase.2 ⟨?_, hπ w hwX⟩
        intro hπw
        have h1 := hfib w hwX u hu hwu hπw
        have h2 := hfib w hwX v hv hwv (hπw.trans hπuv)
        omega
      have hcard : (P.erase (π u)).card ≤ q := by
        rw [card_erase_of_mem (hπ u hu)]; omega
      obtain ⟨f', hf'L, hf'⟩ := ih ((X.erase u).erase v) (P.erase (π u)) π
        (fun w => (L w).erase c) hcard hX'
        (fun a ha b hb hab h => hfib a (mem_of_mem_erase (mem_of_mem_erase ha)) b
          (mem_of_mem_erase (mem_of_mem_erase hb)) hab h)
        (fun w hw => by
          have := hL w (mem_of_mem_erase (mem_of_mem_erase hw))
          have := pred_card_le_card_erase (s := L w) (a := c)
          omega)
      refine ⟨fun w => if w = u ∨ w = v then c else f' w, ?_, ?_⟩
      · intro w hw
        by_cases h : w = u ∨ w = v
        · simp only [h, ite_true]
          rcases h with rfl | rfl
          · exact hc.1
          · exact hc.2
        · simp only [h, ite_false]
          push Not at h
          have := hf'L w (mem_erase.2 ⟨h.2, mem_erase.2 ⟨h.1, hw⟩⟩)
          exact mem_of_mem_erase this
      · intro a ha b hb hab hfab
        by_cases h1 : a = u ∨ a = v <;> by_cases h2 : b = u ∨ b = v
        · rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact absurd rfl hab
          · exact huvadj
          · omega
          · exact absurd rfl hab
        · simp only [h1, h2, ite_true, ite_false] at hfab
          push Not at h2
          have := hf'L b (mem_erase.2 ⟨h2.2, mem_erase.2 ⟨h2.1, hb⟩⟩)
          rw [← hfab] at this
          simp at this
        · simp only [h1, h2, ite_true, ite_false] at hfab
          push Not at h1
          have := hf'L a (mem_erase.2 ⟨h1.2, mem_erase.2 ⟨h1.1, ha⟩⟩)
          rw [hfab] at this
          simp at this
        · simp only [h1, h2, ite_false] at hfab
          push Not at h1 h2
          exact hf' a (mem_erase.2 ⟨h1.2, mem_erase.2 ⟨h1.1, ha⟩⟩)
            b (mem_erase.2 ⟨h2.2, mem_erase.2 ⟨h2.1, hb⟩⟩) hab hfab
    · push Not at hpair
      apply col_of_sdr
      intro W hW
      apply card_le_of_bounded W L (q + 1) (by omega) (fun v hv => hL v (hW hv))
      intro c
      calc (W.filter (fun v => c ∈ L v)).card ≤ P.card := by
            apply card_le_card_of_injOn π
            · intro v hv
              exact hπ v (hW (mem_filter.1 hv).1)
            · intro a ha b hb hab
              by_contra hne
              have ha' := mem_filter.1 ha
              have hb' := mem_filter.1 hb
              have := hpair a (hW ha'.1) b (hW hb'.1) hne hab
              have hcab : c ∈ L a ∩ L b := mem_inter.2 ⟨ha'.2, hb'.2⟩
              rw [this] at hcab
              simp at hcab
        _ ≤ q + 1 := hP



end OddAntihole
