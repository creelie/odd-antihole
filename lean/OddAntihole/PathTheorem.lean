import OddAntihole.KeyLemma

/-!
# The path theorem

On a union of odd paths with `s` outer vertices and lists of size at least `s - 1`, the
complement is colourable unless every outer vertex has the same list of size `s - 1`.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- The induction step of the path theorem. -/
theorem path_step [Inhabited α] (S : Finset ℕ) (hS : Good S) (L : ℕ → Finset α)
    (IH : PathIH α S.card) (hL : ∀ v ∈ S, (ev S).card - 1 ≤ (L v).card) (hnc : ¬ Col S L) :
    ∀ u ∈ ev S, ∀ v ∈ ev S, L u = L v ∧ (L u).card = (ev S).card - 1 := by
  by_contra hP
  obtain ⟨hdef, hC1⟩ := defect_facts S hS L IH hL hP hnc
  have hsplit := card_ev_add_od S
  have hsub : ∀ u ∈ S, L u ⊆ nb L S := fun u hu => subset_biUnion_of_mem L hu
  rcases (od S).eq_empty_or_nonempty with hod | ⟨v, hv⟩
  · apply hP
    rw [hod, card_empty] at hsplit
    have heq : ∀ u ∈ S, L u = nb L S ∧ (L u).card = (ev S).card - 1 := by
      intro u hu
      have h1 := hL u hu
      have h2 := card_le_card (hsub u hu)
      have h3 : L u = nb L S := eq_of_subset_of_card_le (hsub u hu) (by omega)
      exact ⟨h3, by rw [h3]; omega⟩
    intro u hu w hw
    obtain ⟨h1, h2⟩ := heq u (mem_ev.1 hu).1
    exact ⟨h1.trans (heq w (mem_ev.1 hw).1).1.symm, h2⟩
  rw [mem_od] at hv
  obtain ⟨hvS, hvodd⟩ := hv
  -- a disjoint pair of lists on two vertices forces the extremal count and the key lemma
  have key : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (L p) (L q) → False := by
    intro p hp q hq hpq hd
    have h1 := card_le_card (union_subset (hsub p hp) (hsub q hq))
    rw [card_union_of_disjoint hd] at h1
    have h2 := hL p hp
    have h3 := hL q hq
    have h4 := od_card_lt S hS ⟨v, hvS⟩
    have hodpos : 1 ≤ (od S).card := card_pos.2 ⟨v, mem_od.2 ⟨hvS, hvodd⟩⟩
    have hk : (od S).card + 1 = (ev S).card := by omega
    apply hP
    refine star S L ((ev S).card - 1) (by omega) (by omega) (by omega) (fun w hw => hL w hw) ?_
      (convex_of_card S hS ⟨v, hvS⟩ hk) hnc
    intro W hWS hWne
    have := hdef W hWS hWne
    omega
  -- the bottom end of the path through `v`
  set TL := S.filter (fun x => x ≤ v ∧ Icc x v ⊆ S) with hTL
  have hvTL : v ∈ TL := by
    rw [hTL, mem_filter]
    refine ⟨hvS, le_rfl, fun y hy => ?_⟩
    rw [mem_Icc] at hy
    have : y = v := by omega
    rw [this]; exact hvS
  set a := TL.min' ⟨v, hvTL⟩ with ha_def
  have haTL : a ∈ TL := min'_mem TL _
  rw [hTL, mem_filter] at haTL
  obtain ⟨haS, hav, haI⟩ := haTL
  have hbot : ∀ w ∈ S, w + 1 ≠ a := by
    intro w hw hwa
    have hwTL : w ∈ TL := by
      rw [hTL, mem_filter]
      refine ⟨hw, by omega, fun y hy => ?_⟩
      rw [mem_Icc] at hy
      by_cases hyw : y = w
      · rw [hyw]; exact hw
      · exact haI (mem_Icc.2 ⟨by omega, hy.2⟩)
    have := min'_le TL w hwTL
    rw [← ha_def] at this
    omega
  have haeven : a % 2 = 0 := by
    by_contra h
    have := (hS a haS (by omega)).1
    exact hbot (a - 1) this (by omega)
  have ha1 : a + 1 ∈ S := haI (mem_Icc.2 ⟨by omega, by omega⟩)
  -- the top end
  set TH := S.filter (fun x => v ≤ x ∧ Icc v x ⊆ S) with hTH
  have hvTH : v ∈ TH := by
    rw [hTH, mem_filter]
    refine ⟨hvS, le_rfl, fun y hy => ?_⟩
    rw [mem_Icc] at hy
    have : y = v := by omega
    rw [this]; exact hvS
  set a' := TH.max' ⟨v, hvTH⟩ with ha'_def
  have ha'TH : a' ∈ TH := max'_mem TH _
  rw [hTH, mem_filter] at ha'TH
  obtain ⟨ha'S, hva', ha'I⟩ := ha'TH
  have htop : a' + 1 ∉ S := by
    intro h
    have hTH1 : a' + 1 ∈ TH := by
      rw [hTH, mem_filter]
      refine ⟨h, by omega, fun y hy => ?_⟩
      rw [mem_Icc] at hy
      by_cases hy1 : y = a' + 1
      · rw [hy1]; exact h
      · exact ha'I (mem_Icc.2 ⟨hy.1, by omega⟩)
    have := le_max' TH (a' + 1) hTH1
    rw [← ha'_def] at this
    omega
  have ha'even : a' % 2 = 0 := by
    by_contra h
    exact htop (hS a' ha'S (by omega)).2
  have ha'1 : a' - 1 ∈ S := ha'I (mem_Icc.2 ⟨by omega, by omega⟩)
  have hne : a ≠ a' := by omega
  by_cases hA : (L a ∩ L (a + 1)).Nonempty
  · by_cases hB : (L a' ∩ L (a' - 1)).Nonempty
    · obtain ⟨c, hc⟩ := hA
      obtain ⟨c', hc'⟩ := hB
      rw [mem_inter] at hc hc'
      have E1 := endpair S hS L IH hL hnc a (a + 1) haS ha1 haeven (Or.inl ⟨rfl, hbot⟩)
        c hc.1 hc.2
      have E2 := endpair S hS L IH hL hnc a' (a' - 1) ha'S ha'1 ha'even
        (Or.inr ⟨by omega, htop⟩) c' hc'.1 hc'.2
      have haev : a ∈ ev S := mem_ev.2 ⟨haS, haeven⟩
      have ha'ev : a' ∈ ev S := mem_ev.2 ⟨ha'S, ha'even⟩
      have hLa : (L a).card = (ev S).card - 1 := (E2 a haev a haev hne hne).2.2
      have hca' : c ∈ L a' := (E1 a' ha'ev a' ha'ev (Ne.symm hne) (Ne.symm hne)).2.1
      have hLa' : (L a').card = (ev S).card - 1 :=
        (E1 a' ha'ev a' ha'ev (Ne.symm hne) (Ne.symm hne)).2.2
      have hcross : L a = L a' := by
        by_cases h3 : ∃ z ∈ ev S, z ≠ a ∧ z ≠ a'
        · obtain ⟨z, hz, hza, hza'⟩ := h3
          exact (E2 a haev z hz hne hza').1.trans (E1 z hz a' ha'ev hza (Ne.symm hne)).1
        · push Not at h3
          have hsub2 : ev S ⊆ {a, a'} := by
            intro z hz
            rw [mem_insert, mem_singleton]
            by_cases hza : z = a
            · exact Or.inl hza
            · exact Or.inr (h3 z hz hza)
          have hc2 := card_le_card hsub2
          rw [card_pair hne] at hc2
          have hp1 := card_pos.2 ⟨c, hc.1⟩
          have hp2 := card_pos.2 ⟨c, hca'⟩
          have h1 : L a = {c} := by
            obtain ⟨x, hx⟩ := card_eq_one.1 (show (L a).card = 1 by omega)
            have hcx := hc.1
            rw [hx, mem_singleton] at hcx
            rw [hx, hcx]
          have h2 : L a' = {c} := by
            obtain ⟨x, hx⟩ := card_eq_one.1 (show (L a').card = 1 by omega)
            have hcx := hca'
            rw [hx, mem_singleton] at hcx
            rw [hx, hcx]
          rw [h1, h2]
      have hall : ∀ u ∈ ev S, L u = L a := by
        intro u hu
        by_cases hua : u = a
        · rw [hua]
        · rw [hcross]; exact (E1 u hu a' ha'ev hua (Ne.symm hne)).1
      exact hP (fun u hu w hw => ⟨(hall u hu).trans (hall w hw).symm, by rw [hall u hu]; exact hLa⟩)
    · exact key a' ha'S (a' - 1) ha'1 (by omega)
        (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 hB))
  · exact key a haS (a + 1) ha1 (by omega)
      (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 hA))

theorem path_all [Inhabited α] : ∀ n, PathIH α n := by
  intro n
  induction n with
  | zero => unfold PathIH; intro S' h; omega
  | succ n ih =>
    unfold PathIH
    intro S' hS' hG L' hL hnc
    refine path_step S' hG L' ?_ hL hnc
    unfold PathIH
    intro S'' h
    exact ih S'' (by omega)

/-- The path theorem: on a union of odd paths with lists of size at least `s - 1`, `s` the
number of outer vertices, the complement is colourable unless all outer lists are one list of
size `s - 1`. -/
theorem gpath [Inhabited α] (S : Finset ℕ) (hS : Good S) (L : ℕ → Finset α)
    (hL : ∀ v ∈ S, (ev S).card - 1 ≤ (L v).card) (hnc : ¬ Col S L) :
    ∀ u ∈ ev S, ∀ v ∈ ev S, L u = L v ∧ (L u).card = (ev S).card - 1 :=
  path_step S hS L (path_all S.card) hL hnc



end OddAntihole
