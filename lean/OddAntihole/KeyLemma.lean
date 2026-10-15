import OddAntihole.Paths

/-!
# The key lemma

A path on `2k + 1` vertices whose lists have size `k` and use `2k` colours in all, with Hall's
condition on every proper subset, is either colourable or has complementary consecutive lists.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- `W` is a tight set (`|N(W)| ≤ |W|`), nonempty, proper, and minimal with these properties. -/
def MinTight (S : Finset ℕ) (L : ℕ → Finset α) (W : Finset ℕ) : Prop :=
  W ⊆ S ∧ W ≠ S ∧ W.Nonempty ∧ (nb L W).card ≤ W.card ∧
    ∀ Y ⊆ W, Y.Nonempty → (nb L Y).card ≤ Y.card → Y = W

/-- Hall's condition on every proper subset. -/
def HallProper (S : Finset ℕ) (L : ℕ → Finset α) : Prop :=
  ∀ W ⊆ S, W ≠ S → W.card ≤ (nb L W).card

theorem exists_mintight (S : Finset ℕ) (L : ℕ → Finset α) (k : ℕ) (hS : S.card = 2 * k + 1)
    (hk : 1 ≤ k) (hC : (nb L S).card = 2 * k) (x : ℕ) (hx : x ∈ S) :
    ∃ W, MinTight S L W ∧ x ∉ W := by
  let T := (S.erase x).powerset.filter (fun W => W.Nonempty ∧ (nb L W).card ≤ W.card)
  have hT : S.erase x ∈ T := by
    simp only [T, mem_filter, mem_powerset]
    refine ⟨Subset.rfl, ?_, ?_⟩
    · rw [← card_pos, card_erase_of_mem hx]; omega
    · rw [card_erase_of_mem hx]
      have h1 : nb L (S.erase x) ⊆ nb L S :=
        biUnion_subset_biUnion_of_subset_left _ (erase_subset x S)
      have := card_le_card h1
      omega
  obtain ⟨W, hWT, hWmin⟩ := exists_min_image T card ⟨_, hT⟩
  simp only [T, mem_filter, mem_powerset] at hWT
  obtain ⟨hWsub, hWne, hWt⟩ := hWT
  have hxW : x ∉ W := fun h => notMem_erase x S (hWsub h)
  refine ⟨W, ?_, hxW⟩
  unfold MinTight
  refine ⟨hWsub.trans (erase_subset x S), fun h => hxW (h ▸ hx), hWne, hWt, ?_⟩
  intro Y hY hYne hYt
  have hYT : Y ∈ T := by
    simp only [T, mem_filter, mem_powerset]
    exact ⟨hY.trans hWsub, hYne, hYt⟩
  exact eq_of_subset_of_card_le hY (hWmin Y hYT)

theorem pm_erase [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (hH : HallProper S L)
    (x : ℕ) (hx : x ∈ S) :
    ∃ N : ℕ → α, (∀ v ∈ S.erase x, N v ∈ L v) ∧
      ∀ u ∈ S.erase x, ∀ v ∈ S.erase x, N u = N v → u = v :=
  hall_sdr (S.erase x) L (fun W hW => hH W (hW.trans (erase_subset x S))
    (fun h => by rw [h] at hW; exact notMem_erase x S (hW hx)))

/-- A matching of `S - x` maps a tight set `W` onto its neighbourhood, so it sends every vertex
outside `W` outside `N(W)`. -/
theorem pm_outside (S : Finset ℕ) (L : ℕ → Finset α) (W : Finset ℕ)
    (hWt : (nb L W).card ≤ W.card) (x : ℕ) (hxW : x ∉ W) (hWS : W ⊆ S) (N : ℕ → α)
    (hNL : ∀ v ∈ S.erase x, N v ∈ L v)
    (hNinj : ∀ u ∈ S.erase x, ∀ v ∈ S.erase x, N u = N v → u = v) :
    ∀ v ∈ S.erase x, v ∉ W → N v ∉ nb L W := by
  have hWsub : W ⊆ S.erase x := fun w hw => mem_erase.2 ⟨fun h => hxW (h ▸ hw), hWS hw⟩
  have himg : W.image N = nb L W := by
    apply eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
      exact mem_biUnion.2 ⟨w, hw, hNL w (hWsub hw)⟩
    · rw [card_image_of_injOn (fun a ha b hb h => hNinj a (hWsub ha) b (hWsub hb) h)]
      exact hWt
  intro v hv hvW hNv
  rw [← himg] at hNv
  obtain ⟨w, hw, hwv⟩ := mem_image.1 hNv
  exact hvW (hNinj w (hWsub hw) v hv hwv ▸ hw)

/-- A path edge leaving a minimal tight set whose ends share a colour is good. -/
theorem cross [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (hH : HallProper S L)
    (W : Finset ℕ) (hW : MinTight S L W) (x y : ℕ) (hxS : x ∈ S) (hxW : x ∉ W) (hyW : y ∈ W)
    (hxy : x + 1 = y ∨ y + 1 = x) (c : α) (hcx : c ∈ L x) (hcy : c ∈ L y) : Col S L := by
  obtain ⟨hWS, _, _, hWt, hWmin⟩ := hW
  obtain ⟨N, hNL, hNinj⟩ := pm_erase S L hH x hxS
  have hout := pm_outside S L W hWt x hxW hWS N hNL hNinj
  have hHall : ∀ Y ⊆ W.erase y, Y.card ≤ (Y.biUnion (fun v => (L v).erase c)).card := by
    intro Y hY
    rcases Y.eq_empty_or_nonempty with rfl | hYne
    · simp
    · have hYW : Y ⊆ W := hY.trans (erase_subset y W)
      have hYneW : Y ≠ W := fun h => by rw [h] at hY; exact notMem_erase y W (hY hyW)
      have h1 : Y.card < (nb L Y).card := by
        by_contra h
        push Not at h
        exact hYneW (hWmin Y hYW hYne h)
      have h2 : Y.biUnion (fun v => (L v).erase c) = (nb L Y).erase c := by
        ext d
        simp only [mem_biUnion, mem_erase]
        constructor
        · rintro ⟨v, hv, hd, hdv⟩; exact ⟨hd, v, hv, hdv⟩
        · rintro ⟨hd, v, hv, hdv⟩; exact ⟨v, hv, hd, hdv⟩
      rw [h2]
      have := pred_card_le_card_erase (s := nb L Y) (a := c)
      omega
  obtain ⟨g, hgL, hginj⟩ := hall_sdr (W.erase y) (fun v => (L v).erase c) hHall
  have hcD : c ∈ nb L W := mem_biUnion.2 ⟨y, hyW, hcy⟩
  have hval : ∀ v ∈ S, ¬(v = x ∨ v = y) →
      (if v ∈ W then g v else N v) ≠ c ∧
      ((if v ∈ W then g v else N v) ∈ nb L W ↔ v ∈ W) := by
    intro v hv h1
    push Not at h1
    by_cases h2 : v ∈ W
    · simp only [h2, ite_true, iff_true]
      have := hgL v (mem_erase.2 ⟨h1.2, h2⟩)
      exact ⟨ne_of_mem_erase this, mem_biUnion.2 ⟨v, h2, mem_of_mem_erase this⟩⟩
    · simp only [h2, ite_false, iff_false]
      have := hout v (mem_erase.2 ⟨h1.1, hv⟩) h2
      exact ⟨fun h => this (h ▸ hcD), this⟩
  refine ⟨fun v => if v = x ∨ v = y then c else if v ∈ W then g v else N v, ?_, ?_⟩
  · intro v hv
    by_cases h1 : v = x ∨ v = y
    · simp only [h1, ite_true]
      rcases h1 with rfl | rfl
      · exact hcx
      · exact hcy
    · simp only [h1, ite_false]
      push Not at h1
      by_cases h2 : v ∈ W
      · simp only [h2, ite_true]
        exact mem_of_mem_erase (hgL v (mem_erase.2 ⟨h1.2, h2⟩))
      · simp only [h2, ite_false]
        exact hNL v (mem_erase.2 ⟨h1.1, hv⟩)
  · intro u hu v hv huv hfuv
    by_cases h1 : u = x ∨ u = y <;> by_cases h2 : v = x ∨ v = y
    · rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl huv
      · exact hxy
      · omega
      · exact absurd rfl huv
    · simp only [h1, h2, ite_true, ite_false] at hfuv
      exact absurd hfuv.symm (hval v hv h2).1
    · simp only [h1, h2, ite_true, ite_false] at hfuv
      exact absurd hfuv (hval u hu h1).1
    · simp only [h1, h2, ite_false] at hfuv
      have hu' := hval u hu h1
      have hv' := hval v hv h2
      push Not at h1 h2
      by_cases huW : u ∈ W <;> by_cases hvW : v ∈ W
      · simp only [huW, hvW, ite_true] at hfuv
        exact absurd (hginj u (mem_erase.2 ⟨h1.2, huW⟩) v (mem_erase.2 ⟨h2.2, hvW⟩) hfuv) huv
      · rw [hfuv] at hu'
        exact absurd (hu'.2.2 huW) (fun h => hvW (hv'.2.1 h))
      · rw [← hfuv] at hv'
        exact absurd (hv'.2.2 hvW) (fun h => huW (hu'.2.1 h))
      · simp only [huW, hvW, ite_false] at hfuv
        exact absurd (hNinj u (mem_erase.2 ⟨h1.1, hu⟩) v (mem_erase.2 ⟨h2.1, hv⟩) hfuv) huv

/-- If a path edge `by` leaving a minimal tight set has disjoint lists, then the other edge `bz`
at `b` is good. -/
theorem side [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (k : ℕ)
    (hC : (nb L S).card = 2 * k) (hL : ∀ v ∈ S, k ≤ (L v).card) (hH : HallProper S L)
    (W : Finset ℕ) (hW : MinTight S L W) (b y z : ℕ) (hbS : b ∈ S) (hbW : b ∉ W)
    (hyW : y ∈ W) (hzS : z ∈ S) (hzW : z ∉ W) (hbz : b + 1 = z ∨ z + 1 = b)
    (hdisj : Disjoint (L b) (L y)) : Col S L := by
  obtain ⟨hWS, _, _, hWt, _⟩ := hW
  have hyS := hWS hyW
  have hunion : L b ∪ L y = nb L S := by
    apply eq_of_subset_of_card_le
    · exact union_subset (subset_biUnion_of_mem L hbS) (subset_biUnion_of_mem L hyS)
    · rw [card_union_of_disjoint hdisj, hC]
      have := hL b hbS
      have := hL y hyS
      omega
  obtain ⟨N, hNL, hNinj⟩ := pm_erase S L hH b hbS
  have hout := pm_outside S L W hWt b hbW hWS N hNL hNinj
  have hz' : z ∈ S.erase b := mem_erase.2 ⟨by omega, hzS⟩
  have hNz : N z ∈ L b := by
    have h1 : N z ∈ nb L S := mem_biUnion.2 ⟨z, hzS, hNL z hz'⟩
    rw [← hunion] at h1
    rcases mem_union.1 h1 with h | h
    · exact h
    · exact absurd (mem_biUnion.2 ⟨y, hyW, h⟩) (hout z hz' hzW)
  refine ⟨fun v => if v = b then N z else N v, ?_, ?_⟩
  · intro v hv
    by_cases h : v = b
    · simp only [h, ite_true]; exact hNz
    · simp only [h, ite_false]; exact hNL v (mem_erase.2 ⟨h, hv⟩)
  · intro u hu v hv huv hfuv
    by_cases h1 : u = b <;> by_cases h2 : v = b
    · exact absurd (h1.trans h2.symm) huv
    · simp only [h1, h2, ite_true, ite_false] at hfuv
      have := hNinj z hz' v (mem_erase.2 ⟨h2, hv⟩) hfuv
      omega
    · simp only [h1, h2, ite_true, ite_false] at hfuv
      have := hNinj z hz' u (mem_erase.2 ⟨h1, hu⟩) hfuv.symm
      omega
    · simp only [h1, h2, ite_false] at hfuv
      exact absurd (hNinj u (mem_erase.2 ⟨h1, hu⟩) v (mem_erase.2 ⟨h2, hv⟩) hfuv) huv

/-- With no good edge, every path edge meets a minimal tight set. -/
theorem walk [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (k : ℕ)
    (hC : (nb L S).card = 2 * k) (hL : ∀ v ∈ S, k ≤ (L v).card) (hH : HallProper S L)
    (hconv : ∀ u ∈ S, ∀ w ∈ S, ∀ x, u ≤ x → x ≤ w → x ∈ S) (hnc : ¬ Col S L)
    (W : Finset ℕ) (hW : MinTight S L W) :
    ∀ u, u ∈ S → u + 1 ∈ S → u ∈ W ∨ u + 1 ∈ W := by
  intro u hu hu1
  by_contra hcon
  push Not at hcon
  obtain ⟨huW, hu1W⟩ := hcon
  have hWS := hW.1
  obtain ⟨w, hw⟩ := hW.2.2.1
  have hwS := hWS hw
  have hwu : w ≠ u := fun h => huW (h ▸ hw)
  have hwu1 : w ≠ u + 1 := fun h => hu1W (h ▸ hw)
  rcases lt_or_gt_of_ne hwu with hlt | hgt
  · -- the nearest vertex of `W` below the edge
    have hT : (W.filter (· < u)).Nonempty := ⟨w, mem_filter.2 ⟨hw, hlt⟩⟩
    obtain ⟨y, hy⟩ : ∃ y, y = (W.filter (· < u)).max' hT := ⟨_, rfl⟩
    have hyT : y ∈ W.filter (· < u) := hy ▸ max'_mem _ hT
    have hyW := (mem_filter.1 hyT).1
    have hyu := (mem_filter.1 hyT).2
    have hyS := hWS hyW
    have habove : ∀ x ∈ W, x < u → x ≤ y := fun x hx hxu =>
      hy ▸ le_max' _ x (mem_filter.2 ⟨hx, hxu⟩)
    have hbS : y + 1 ∈ S := hconv y hyS u hu (y + 1) (by omega) (by omega)
    have hbW : y + 1 ∉ W := by
      intro hb
      by_cases hbu : y + 1 < u
      · have := habove _ hb hbu; omega
      · have : y + 1 = u := by omega
        exact huW (this ▸ hb)
    by_cases hint : (L (y + 1) ∩ L y).Nonempty
    · obtain ⟨c, hc⟩ := hint
      rw [mem_inter] at hc
      exact hnc (cross S L hH W hW (y + 1) y hbS hbW hyW (by omega) c hc.1 hc.2)
    · rw [not_nonempty_iff_eq_empty] at hint
      have hdisj : Disjoint (L (y + 1)) (L y) := disjoint_iff_inter_eq_empty.2 hint
      have hzS : y + 2 ∈ S := hconv y hyS (u + 1) hu1 (y + 2) (by omega) (by omega)
      have hzW : y + 2 ∉ W := by
        intro hz
        by_cases hzu : y + 2 < u
        · have := habove _ hz hzu; omega
        · rcases (show y + 2 = u ∨ y + 2 = u + 1 by omega) with h | h
          · exact huW (h ▸ hz)
          · exact hu1W (h ▸ hz)
      exact hnc (side S L k hC hL hH W hW (y + 1) y (y + 2) hbS hbW hyW hzS hzW
        (by omega) hdisj)
  · -- the nearest vertex of `W` above the edge
    have hgt' : u + 1 < w := by omega
    have hT : (W.filter (fun x => u + 1 < x)).Nonempty := ⟨w, mem_filter.2 ⟨hw, hgt'⟩⟩
    obtain ⟨y, hy⟩ : ∃ y, y = (W.filter (fun x => u + 1 < x)).min' hT := ⟨_, rfl⟩
    have hyT : y ∈ W.filter (fun x => u + 1 < x) := hy ▸ min'_mem _ hT
    have hyW := (mem_filter.1 hyT).1
    have hyu := (mem_filter.1 hyT).2
    have hyS := hWS hyW
    have hbelow : ∀ x ∈ W, u + 1 < x → y ≤ x := fun x hx hxu =>
      hy ▸ min'_le _ x (mem_filter.2 ⟨hx, hxu⟩)
    have hbS : y - 1 ∈ S := hconv (u + 1) hu1 y hyS (y - 1) (by omega) (by omega)
    have hbW : y - 1 ∉ W := by
      intro hb
      by_cases hbu : u + 1 < y - 1
      · have := hbelow _ hb hbu; omega
      · have : y - 1 = u + 1 := by omega
        exact hu1W (this ▸ hb)
    by_cases hint : (L (y - 1) ∩ L y).Nonempty
    · obtain ⟨c, hc⟩ := hint
      rw [mem_inter] at hc
      exact hnc (cross S L hH W hW (y - 1) y hbS hbW hyW (by omega) c hc.1 hc.2)
    · rw [not_nonempty_iff_eq_empty] at hint
      have hdisj : Disjoint (L (y - 1)) (L y) := disjoint_iff_inter_eq_empty.2 hint
      have hzS : y - 2 ∈ S := hconv u hu y hyS (y - 2) (by omega) (by omega)
      have hzW : y - 2 ∉ W := by
        intro hz
        by_cases hzu : u + 1 < y - 2
        · have := hbelow _ hz hzu; omega
        · rcases (show y - 2 = u ∨ y - 2 = u + 1 by omega) with h | h
          · exact huW (h ▸ hz)
          · exact hu1W (h ▸ hz)
      exact hnc (side S L k hC hL hH W hW (y - 1) y (y - 2) hbS hbW hyW hzS hzW
        (by omega) hdisj)

/-- With no good edge, consecutive lists are disjoint. -/
theorem consec_disjoint [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (k : ℕ)
    (hS : S.card = 2 * k + 1) (hk : 1 ≤ k) (hC : (nb L S).card = 2 * k)
    (hL : ∀ v ∈ S, k ≤ (L v).card) (hH : HallProper S L)
    (hconv : ∀ u ∈ S, ∀ w ∈ S, ∀ x, u ≤ x → x ≤ w → x ∈ S) (hnc : ¬ Col S L) :
    ∀ u, u ∈ S → u + 1 ∈ S → Disjoint (L u) (L (u + 1)) := by
  intro u hu hu1
  obtain ⟨W, hW, huW⟩ := exists_mintight S L k hS hk hC u hu
  have hu1W : u + 1 ∈ W := (walk S L k hC hL hH hconv hnc W hW u hu hu1).resolve_left huW
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  rintro ⟨c, hc⟩
  rw [mem_inter] at hc
  exact hnc (cross S L hH W hW u (u + 1) hu huW hu1W (Or.inl rfl) c hc.1 hc.2)

/-- The key lemma: a path of `2k+1` vertices with lists of size `k` drawn from `2k` colours and
Hall's condition on every proper subset is colourable unless its outer lists coincide. -/
theorem star [Inhabited α] (S : Finset ℕ) (L : ℕ → Finset α) (k : ℕ)
    (hS : S.card = 2 * k + 1) (hk : 1 ≤ k) (hC : (nb L S).card = 2 * k)
    (hL : ∀ v ∈ S, k ≤ (L v).card) (hH : HallProper S L)
    (hconv : ∀ u ∈ S, ∀ w ∈ S, ∀ x, u ≤ x → x ≤ w → x ∈ S) (hnc : ¬ Col S L) :
    ∀ u ∈ ev S, ∀ v ∈ ev S, L u = L v ∧ (L u).card = k := by
  have hdisj := consec_disjoint S L k hS hk hC hL hH hconv hnc
  have hcomp : ∀ u, u ∈ S → u + 1 ∈ S →
      L u = nb L S \ L (u + 1) ∧ L (u + 1) = nb L S \ L u ∧ (L u).card = k ∧
        (L (u + 1)).card = k := by
    intro u hu hu1
    have hd := hdisj u hu hu1
    have h1 := hL u hu
    have h2 := hL (u + 1) hu1
    have hsub1 : L u ⊆ nb L S := subset_biUnion_of_mem L hu
    have hsub2 : L (u + 1) ⊆ nb L S := subset_biUnion_of_mem L hu1
    have hun := card_le_card (union_subset hsub1 hsub2)
    rw [card_union_of_disjoint hd] at hun
    have hc1 : (L u).card = k := by omega
    have hc2 : (L (u + 1)).card = k := by omega
    refine ⟨?_, ?_, hc1, hc2⟩
    · apply eq_of_subset_of_card_le
      · intro c hc
        exact mem_sdiff.2 ⟨hsub1 hc, fun h => disjoint_left.1 hd hc h⟩
      · rw [card_sdiff_of_subset hsub2]; omega
    · apply eq_of_subset_of_card_le
      · intro c hc
        exact mem_sdiff.2 ⟨hsub2 hc, fun h => disjoint_left.1 hd h hc⟩
      · rw [card_sdiff_of_subset hsub1]; omega
  have hstep : ∀ u, u ∈ S → u + 2 ∈ S → L (u + 2) = L u := by
    intro u hu hu2
    have hu1 : u + 1 ∈ S := hconv u hu (u + 2) hu2 (u + 1) (by omega) (by omega)
    rw [(hcomp (u + 1) hu1 hu2).2.1, (hcomp u hu hu1).1]
  have hchain : ∀ u ∈ S, ∀ d, u + 2 * d ∈ S → L (u + 2 * d) = L u := by
    intro u hu d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have h1 : u + 2 * d ∈ S := hconv u hu _ hd _ (by omega) (by omega)
      have := hstep (u + 2 * d) h1 (by rw [show u + 2 * d + 2 = u + 2 * (d + 1) by ring]; exact hd)
      rw [show u + 2 * (d + 1) = u + 2 * d + 2 by ring, this, ih h1]
  have hcardk : ∀ u ∈ S, (L u).card = k := by
    intro u hu
    obtain ⟨w, hw, hwu⟩ := exists_mem_ne (show 1 < S.card by omega) u
    rcases lt_or_gt_of_ne hwu with h | h
    · have : u - 1 ∈ S := hconv w hw u hu (u - 1) (by omega) (by omega)
      have := (hcomp (u - 1) this (by rw [Nat.sub_add_cancel (by omega)]; exact hu)).2.2.2
      rwa [Nat.sub_add_cancel (by omega)] at this
    · exact (hcomp u hu (hconv u hu w hw (u + 1) (by omega) (by omega))).2.2.1
  intro u hu v hv
  have hu' := mem_ev.1 hu
  have hv' := mem_ev.1 hv
  refine ⟨?_, hcardk u hu'.1⟩
  rcases le_total u v with h | h
  · have := hchain u hu'.1 ((v - u) / 2) (by rw [show u + 2 * ((v - u) / 2) = v by omega]; exact hv'.1)
    rw [show u + 2 * ((v - u) / 2) = v by omega] at this
    exact this.symm
  · have := hchain v hv'.1 ((u - v) / 2) (by rw [show v + 2 * ((u - v) / 2) = u by omega]; exact hu'.1)
    rw [show v + 2 * ((u - v) / 2) = u by omega] at this
    exact this



end OddAntihole
