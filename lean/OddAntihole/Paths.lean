import OddAntihole.Basic

/-!
# Unions of odd paths

The vertex set `S` is a union of paths with an odd number of vertices whose end vertices are even
integers. This file proves the maximal-deficiency step and the counting facts used by the path
theorem.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- `Good S`: every odd element of `S` has both neighbours in `S`. The components of the graph on
`S` joining consecutive integers are then paths with an odd number of vertices, beginning and
ending at even integers. -/
def Good (S : Finset ℕ) : Prop := ∀ v ∈ S, v % 2 = 1 → v - 1 ∈ S ∧ v + 1 ∈ S

/-- The even elements of `S`: the outer vertices of the paths. -/
def ev (S : Finset ℕ) : Finset ℕ := S.filter (fun v => v % 2 = 0)

/-- The odd elements of `S`: the inner vertices of the paths. -/
def od (S : Finset ℕ) : Finset ℕ := S.filter (fun v => v % 2 = 1)

theorem card_ev_add_od (S : Finset ℕ) : (ev S).card + (od S).card = S.card := by
  have h := card_filter_add_card_filter_not (s := S) (fun v => v % 2 = 0)
  have h2 : S.filter (fun v => ¬ v % 2 = 0) = od S := by
    unfold od; apply filter_congr; intro x _; omega
  rw [h2] at h
  exact h

theorem mem_ev {S : Finset ℕ} {v : ℕ} : v ∈ ev S ↔ v ∈ S ∧ v % 2 = 0 := mem_filter
theorem mem_od {S : Finset ℕ} {v : ℕ} : v ∈ od S ↔ v ∈ S ∧ v % 2 = 1 := mem_filter

/-- Colouring a consecutive pair with a common colour. -/
theorem col_of_pair (S : Finset ℕ) (L : ℕ → Finset α) (a b : ℕ) (c : α)
    (hab : a + 1 = b ∨ b + 1 = a) (hca : c ∈ L a) (hcb : c ∈ L b)
    (h : Col ((S.erase a).erase b) (fun v => (L v).erase c)) : Col S L := by
  obtain ⟨f', hf'L, hf'⟩ := h
  refine ⟨fun w => if w = a ∨ w = b then c else f' w, ?_, ?_⟩
  · intro w hw
    by_cases h : w = a ∨ w = b
    · simp only [h, ite_true]
      rcases h with rfl | rfl
      · exact hca
      · exact hcb
    · simp only [h, ite_false]
      push Not at h
      exact mem_of_mem_erase (hf'L w (mem_erase.2 ⟨h.2, mem_erase.2 ⟨h.1, hw⟩⟩))
  · intro x hx y hy hxy hfxy
    by_cases h1 : x = a ∨ x = b <;> by_cases h2 : y = a ∨ y = b
    · rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · omega
      · exact absurd rfl hxy
    · simp only [h1, h2, ite_true, ite_false] at hfxy
      push Not at h2
      have := hf'L y (mem_erase.2 ⟨h2.2, mem_erase.2 ⟨h2.1, hy⟩⟩)
      rw [← hfxy] at this
      simp at this
    · simp only [h1, h2, ite_true, ite_false] at hfxy
      push Not at h1
      have := hf'L x (mem_erase.2 ⟨h1.2, mem_erase.2 ⟨h1.1, hx⟩⟩)
      rw [hfxy] at this
      simp at this
    · simp only [h1, h2, ite_false] at hfxy
      push Not at h1 h2
      exact hf' x (mem_erase.2 ⟨h1.2, mem_erase.2 ⟨h1.1, hx⟩⟩)
        y (mem_erase.2 ⟨h2.2, mem_erase.2 ⟨h2.1, hy⟩⟩) hxy hfxy

/-- Removing an end pair of a path keeps a union of odd paths. -/
theorem good_erase_end (S : Finset ℕ) (hS : Good S) (a b : ℕ) (ha : a % 2 = 0)
    (hend : (b = a + 1 ∧ ∀ v ∈ S, v + 1 ≠ a) ∨ (a = b + 1 ∧ a + 1 ∉ S)) :
    Good ((S.erase a).erase b) := by
  intro v hv hodd
  have hvb := ne_of_mem_erase hv
  have hva := ne_of_mem_erase (mem_of_mem_erase hv)
  have hvS := mem_of_mem_erase (mem_of_mem_erase hv)
  obtain ⟨h1, h2⟩ := hS v hvS hodd
  refine ⟨mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, h1⟩⟩, mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, h2⟩⟩⟩
  · omega
  · rcases hend with ⟨hb, _⟩ | ⟨hb, hn⟩
    · omega
    · intro h; apply hn; rw [← h]; have : v - 1 + 1 = v := by omega
      rw [this]; exact hvS
  · omega
  · rcases hend with ⟨hb, hn⟩ | ⟨hb, _⟩
    · exact hn v hvS
    · omega

theorem ev_erase_end (S : Finset ℕ) (a b : ℕ) (hb : b % 2 = 1) :
    ev ((S.erase a).erase b) = (ev S).erase a := by
  ext v
  simp only [ev, mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1, h2⟩, h3⟩

/-- The induction hypothesis of the path theorem, for sets smaller than `S`. -/
def PathIH (α : Type*) [DecidableEq α] (n : ℕ) : Prop :=
  ∀ S' : Finset ℕ, S'.card < n → Good S' → ∀ L' : ℕ → Finset α,
    (∀ v ∈ S', (ev S').card - 1 ≤ (L' v).card) → ¬ Col S' L' →
    ∀ u ∈ ev S', ∀ v ∈ ev S', L' u = L' v ∧ (L' u).card = (ev S').card - 1

/-- Step B: a common colour on an end pair forces the other outer lists to agree. -/
theorem endpair (S : Finset ℕ) (hS : Good S) (L : ℕ → Finset α) (IH : PathIH α S.card)
    (hL : ∀ v ∈ S, (ev S).card - 1 ≤ (L v).card) (hnc : ¬ Col S L)
    (a b : ℕ) (haS : a ∈ S) (hbS : b ∈ S) (ha : a % 2 = 0)
    (hend : (b = a + 1 ∧ ∀ v ∈ S, v + 1 ≠ a) ∨ (a = b + 1 ∧ a + 1 ∉ S))
    (c : α) (hca : c ∈ L a) (hcb : c ∈ L b) :
    ∀ u ∈ ev S, ∀ v ∈ ev S, u ≠ a → v ≠ a →
      L u = L v ∧ c ∈ L u ∧ (L u).card = (ev S).card - 1 := by
  have hb : b % 2 = 1 := by omega
  have hev := ev_erase_end S a b hb
  have haev : a ∈ ev S := mem_ev.2 ⟨haS, ha⟩
  have hs2 : 2 ≤ (ev S).card := by
    obtain ⟨h1, h2⟩ := hS b hbS hb
    have : 1 < (ev S).card := by
      rw [one_lt_card]
      exact ⟨b - 1, mem_ev.2 ⟨h1, by omega⟩, b + 1, mem_ev.2 ⟨h2, by omega⟩, by omega⟩
    omega
  have hs : (ev ((S.erase a).erase b)).card = (ev S).card - 1 := by
    rw [hev, card_erase_of_mem haev]
  have hcard : ((S.erase a).erase b).card < S.card := by
    have hb' : b ∈ S.erase a := mem_erase.2 ⟨by omega, hbS⟩
    rw [card_erase_of_mem hb', card_erase_of_mem haS]
    have : 0 < S.card := card_pos.2 ⟨a, haS⟩
    omega
  have hab : a + 1 = b ∨ b + 1 = a := by omega
  have key := IH _ hcard (good_erase_end S hS a b ha hend) (fun v => (L v).erase c)
    (by
      intro v hv
      rw [hs]
      have := hL v (mem_of_mem_erase (mem_of_mem_erase hv))
      have := pred_card_le_card_erase (s := L v) (a := c)
      omega)
    (fun h => hnc (col_of_pair S L a b c hab hca hcb h))
  have hc_in : ∀ u ∈ ev S, u ≠ a → c ∈ L u := by
    intro u hu hua
    have hu' : u ∈ ev ((S.erase a).erase b) := by rw [hev]; exact mem_erase.2 ⟨hua, hu⟩
    have h1 := (key u hu' u hu').2
    rw [hs] at h1
    by_contra hcu
    rw [erase_eq_of_notMem hcu] at h1
    have := hL u (mem_ev.1 hu).1
    omega
  intro u hu v hv hua hva
  have hu' : u ∈ ev ((S.erase a).erase b) := by rw [hev]; exact mem_erase.2 ⟨hua, hu⟩
  have hv' : v ∈ ev ((S.erase a).erase b) := by rw [hev]; exact mem_erase.2 ⟨hva, hv⟩
  obtain ⟨h1, h2⟩ := key u hu' v hv'
  rw [hs] at h2
  have hcu := hc_in u hu hua
  have hcv := hc_in v hv hva
  refine ⟨?_, hcu, ?_⟩
  · rw [← insert_erase hcu, ← insert_erase hcv]
    rw [h1]
  · have := card_erase_of_mem hcu
    have := card_pos.2 ⟨c, hcu⟩
    omega


/-- The union of the lists over `W`. -/
abbrev nb (L : ℕ → Finset α) (W : Finset ℕ) : Finset α := W.biUnion L

/-- Step A: if a proper subset `X` has maximal deficiency, then the whole set is colourable. -/
theorem maxdef_col [Inhabited α] (S : Finset ℕ) (hS : Good S) (L : ℕ → Finset α)
    (IH : PathIH α S.card) (hL : ∀ v ∈ S, (ev S).card - 1 ≤ (L v).card)
    (hP : ¬ ∀ u ∈ ev S, ∀ v ∈ ev S, L u = L v ∧ (L u).card = (ev S).card - 1)
    (X : Finset ℕ) (hXS : X ⊆ S) (hXne : X ≠ S)
    (hmax : ∀ Y ⊆ S, (Y.card : ℤ) - (nb L Y).card ≤ (X.card : ℤ) - (nb L X).card) :
    Col S L := by
  -- colour `X`
  have hX : Col X L := by
    by_cases hw : ∃ w ∈ ev S, w ∉ X
    · obtain ⟨w, hw, hwX⟩ := hw
      have hwS := (mem_ev.1 hw).1
      have hw0 := (mem_ev.1 hw).2
      refine ert ((ev S).card - 1) X ((ev S).erase w)
        (fun v => if v % 2 = 0 then v else if v < w then v - 1 else v + 1) L
        (by rw [card_erase_of_mem hw]) ?_ ?_ (fun v hv => hL v (hXS hv))
      · intro v hv
        have hvS := hXS hv
        by_cases hv0 : v % 2 = 0
        · simp only [hv0, ite_true]
          exact mem_erase.2 ⟨fun h => hwX (h ▸ hv), mem_ev.2 ⟨hvS, hv0⟩⟩
        · have hv1 : v % 2 = 1 := by omega
          obtain ⟨h1, h2⟩ := hS v hvS hv1
          simp only [hv0, ite_false]
          by_cases hvw : v < w
          · simp only [hvw, ite_true]
            exact mem_erase.2 ⟨by omega, mem_ev.2 ⟨h1, by omega⟩⟩
          · simp only [hvw, ite_false]
            exact mem_erase.2 ⟨by omega, mem_ev.2 ⟨h2, by omega⟩⟩
      · intro u _ v _ huv h
        split_ifs at h <;> omega
    · push Not at hw
      have hgood : Good X := by
        intro v hv hodd
        obtain ⟨h1, h2⟩ := hS v (hXS hv) hodd
        exact ⟨hw _ (mem_ev.2 ⟨h1, by omega⟩), hw _ (mem_ev.2 ⟨h2, by omega⟩)⟩
      have hevX : ev X = ev S := by
        ext v
        simp only [mem_ev]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨hXS h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨hw v (mem_ev.2 ⟨h1, h2⟩), h2⟩
      have hlt : X.card < S.card := card_lt_card (ssubset_of_subset_of_ne hXS hXne)
      by_contra hXc
      apply hP
      have := IH X hlt hgood L (by rw [hevX]; exact fun v hv => hL v (hXS hv)) hXc
      rw [hevX] at this
      exact this
  -- Hall's condition on the rest with the colours of `X` removed
  have hrest : ∀ Z ⊆ S \ X, Z.card ≤ (Z.biUnion (fun v => L v \ nb L X)).card := by
    intro Z hZ
    have hdisj : Disjoint X Z := by
      rw [disjoint_left]
      intro v hvX hvZ
      exact (mem_sdiff.1 (hZ hvZ)).2 hvX
    have hY : X ∪ Z ⊆ S := union_subset hXS (fun v hv => (mem_sdiff.1 (hZ hv)).1)
    have h1 := hmax (X ∪ Z) hY
    rw [card_union_of_disjoint hdisj] at h1
    have h2 : nb L (X ∪ Z) = nb L X ∪ Z.biUnion (fun v => L v \ nb L X) := by
      ext c
      simp only [nb, mem_biUnion, mem_union, mem_sdiff]
      constructor
      · rintro ⟨v, hv, hc⟩
        by_cases hcX : ∃ x ∈ X, c ∈ L x
        · exact Or.inl hcX
        · right
          rcases hv with hv | hv
          · exact absurd ⟨v, hv, hc⟩ hcX
          · exact ⟨v, hv, hc, hcX⟩
      · rintro (⟨v, hv, hc⟩ | ⟨v, hv, hc, _⟩)
        · exact ⟨v, Or.inl hv, hc⟩
        · exact ⟨v, Or.inr hv, hc⟩
    have h3 : Disjoint (nb L X) (Z.biUnion (fun v => L v \ nb L X)) := by
      rw [disjoint_left]
      intro c hc hc'
      simp only [mem_biUnion, mem_sdiff] at hc'
      obtain ⟨_, _, _, hcn⟩ := hc'
      exact hcn (mem_biUnion.1 hc)
    rw [h2, card_union_of_disjoint h3] at h1
    push_cast at h1
    omega
  obtain ⟨σ, hσL, hσinj⟩ := hall_sdr (S \ X) (fun v => L v \ nb L X) hrest
  obtain ⟨g, hgL, hg⟩ := hX
  refine ⟨fun v => if v ∈ X then g v else σ v, ?_, ?_⟩
  · intro v hv
    by_cases hvX : v ∈ X
    · simp only [hvX, ite_true]; exact hgL v hvX
    · simp only [hvX, ite_false]
      exact (mem_sdiff.1 (hσL v (mem_sdiff.2 ⟨hv, hvX⟩))).1
  · intro u hu v hv huv hfuv
    by_cases huX : u ∈ X <;> by_cases hvX : v ∈ X
    · simp only [huX, hvX, ite_true] at hfuv
      exact hg u huX v hvX huv hfuv
    · simp only [huX, hvX, ite_true, ite_false] at hfuv
      have h1 := hσL v (mem_sdiff.2 ⟨hv, hvX⟩)
      rw [← hfuv] at h1
      exact absurd (mem_biUnion.2 ⟨u, huX, hgL u huX⟩) (mem_sdiff.1 h1).2
    · simp only [huX, hvX, ite_true, ite_false] at hfuv
      have h1 := hσL u (mem_sdiff.2 ⟨hu, huX⟩)
      rw [hfuv] at h1
      exact absurd (mem_biUnion.2 ⟨v, hvX, hgL v hvX⟩) (mem_sdiff.1 h1).2
    · simp only [huX, hvX, ite_false] at hfuv
      exact absurd (hσinj u (mem_sdiff.2 ⟨hu, huX⟩) v (mem_sdiff.2 ⟨hv, hvX⟩) hfuv) huv

/-- Consequences of Step A in a counterexample: the whole set has positive deficiency and every
proper subset has smaller deficiency. -/
theorem defect_facts [Inhabited α] (S : Finset ℕ) (hS : Good S) (L : ℕ → Finset α)
    (IH : PathIH α S.card) (hL : ∀ v ∈ S, (ev S).card - 1 ≤ (L v).card)
    (hP : ¬ ∀ u ∈ ev S, ∀ v ∈ ev S, L u = L v ∧ (L u).card = (ev S).card - 1)
    (hnc : ¬ Col S L) :
    (∀ W ⊆ S, W ≠ S → (W.card : ℤ) - (nb L W).card < (S.card : ℤ) - (nb L S).card) ∧
    (nb L S).card + 1 ≤ S.card := by
  obtain ⟨X, hXmem, hXmax⟩ := exists_max_image S.powerset
    (fun Y => (Y.card : ℤ) - (nb L Y).card) ⟨∅, empty_mem_powerset S⟩
  have hXS : X ⊆ S := mem_powerset.1 hXmem
  have hmax : ∀ Y ⊆ S, (Y.card : ℤ) - (nb L Y).card ≤ (X.card : ℤ) - (nb L X).card :=
    fun Y hY => hXmax Y (mem_powerset.2 hY)
  have hXeq : X = S := by
    by_contra hne
    exact hnc (maxdef_col S hS L IH hL hP X hXS hne hmax)
  subst hXeq
  refine ⟨?_, ?_⟩
  · intro W hW hWne
    have h1 := hmax W hW
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      apply hnc
      exact maxdef_col X hS L IH hL hP W hW hWne (fun Y hY => (hmax Y hY).trans h.ge)
  · by_contra hlt
    apply hnc
    apply col_of_sdr
    intro W hW
    have := hmax W hW
    push Not at hlt
    have h4 : X.card ≤ (nb L X).card := by omega
    have : ((nb L X).card : ℤ) ≥ X.card := by exact_mod_cast h4
    have h3 : (W.card : ℤ) ≤ (nb L W).card := by linarith
    exact_mod_cast h3

/-- The largest element of a union of odd paths is even. -/
theorem max_even (S : Finset ℕ) (hS : Good S) (hne : S.Nonempty) : S.max' hne % 2 = 0 := by
  by_contra h
  have hm := max'_mem S hne
  have := (hS _ hm (by omega)).2
  have := le_max' S _ this
  omega

/-- Counting the inner vertices: there is at least one path, so `|inner| + 1 ≤ |outer|`. -/
theorem od_card_lt (S : Finset ℕ) (hS : Good S) (hne : S.Nonempty) :
    (od S).card + 1 ≤ (ev S).card := by
  have hM := max'_mem S hne
  have hMev : S.max' hne ∈ ev S := mem_ev.2 ⟨hM, max_even S hS hne⟩
  have h := card_le_card_of_injOn (fun v => v - 1) (s := od S) (t := (ev S).erase (S.max' hne))
    (by
      intro v hv
      show v - 1 ∈ _
      have hv' := mem_od.1 hv
      have h1 := (hS v hv'.1 hv'.2).1
      have h2 := le_max' S v hv'.1
      exact mem_erase.2 ⟨by omega, mem_ev.2 ⟨h1, by omega⟩⟩)
    (by
      intro u hu v hv huv
      have hu' := (mem_od.1 hu).2
      have hv' := (mem_od.1 hv).2
      simp only at huv
      omega)
  rw [card_erase_of_mem hMev] at h
  have : 0 < (ev S).card := card_pos.2 ⟨_, hMev⟩
  omega

/-- If the count is tight, the union is a single path: `S` is an interval. -/
theorem convex_of_card (S : Finset ℕ) (hS : Good S) (hne : S.Nonempty)
    (h : (od S).card + 1 = (ev S).card) :
    ∀ u ∈ S, ∀ w ∈ S, ∀ x, u ≤ x → x ≤ w → x ∈ S := by
  have hM := max'_mem S hne
  have hMev : S.max' hne ∈ ev S := mem_ev.2 ⟨hM, max_even S hS hne⟩
  have hmaps : ∀ v ∈ od S, v - 1 ∈ (ev S).erase (S.max' hne) := by
    intro v hv
    have hv' := mem_od.1 hv
    have h1 := (hS v hv'.1 hv'.2).1
    have h2 := le_max' S v hv'.1
    exact mem_erase.2 ⟨by omega, mem_ev.2 ⟨h1, by omega⟩⟩
  have hinj : Set.InjOn (fun v => v - 1) (od S : Set ℕ) := by
    intro u hu v hv huv
    have hu' := (mem_od.1 hu).2
    have hv' := (mem_od.1 hv).2
    simp only at huv
    omega
  have himg : (od S).image (fun v => v - 1) = (ev S).erase (S.max' hne) := by
    apply eq_of_subset_of_card_le
    · intro e he
      obtain ⟨v, hv, rfl⟩ := mem_image.1 he
      exact hmaps v hv
    · rw [card_image_of_injOn hinj, card_erase_of_mem hMev]
      omega
  have hsucc : ∀ v ∈ S, v < S.max' hne → v + 1 ∈ S := by
    intro v hv hlt
    by_cases hv0 : v % 2 = 0
    · have : v ∈ (od S).image (fun v => v - 1) := by
        rw [himg]; exact mem_erase.2 ⟨by omega, mem_ev.2 ⟨hv, hv0⟩⟩
      obtain ⟨x, hx, hxv⟩ := mem_image.1 this
      have hx' := mem_od.1 hx
      have : x = v + 1 := by omega
      rw [← this]; exact hx'.1
    · exact (hS v hv (by omega)).2
  intro u hu w hw
  have hwM := le_max' S w hw
  have key : ∀ d, u + d ≤ w → u + d ∈ S := by
    intro d
    induction d with
    | zero => intro _; simpa using hu
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have := hsucc (u + d) h1 (by omega)
      simpa [Nat.add_assoc] using this
  intro x hux hxw
  have := key (x - u) (by omega)
  rwa [Nat.add_sub_cancel' hux] at this



end OddAntihole
