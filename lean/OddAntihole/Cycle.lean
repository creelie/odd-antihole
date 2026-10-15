import OddAntihole.PathTheorem

/-!
# The odd cycle

On the complement of the cycle of length `2m + 1`, `m ≥ 2`, lists of size `m` from which no
colouring exists are all equal.
-/

open Finset

namespace OddAntihole

variable {α : Type*} [DecidableEq α]

/-- Successor on the cycle `0, 1, …, n - 1`. -/
def nxt (n v : ℕ) : ℕ := if v + 1 < n then v + 1 else 0

/-- The vertex `r` steps after `i` on the cycle of length `n`. -/
def pos (n i r : ℕ) : ℕ := if i + r < n then i + r else i + r - n

/-- Adjacency in the cycle of length `n`. -/
def cadj (n u v : ℕ) : Prop :=
  u + 1 = v ∨ v + 1 = u ∨ (u = 0 ∧ v + 1 = n) ∨ (v = 0 ∧ u + 1 = n)

/-- `CCol n L`: the complement of the cycle of length `n` has an `L`-colouring. -/
def CCol (n : ℕ) (L : ℕ → Finset α) : Prop :=
  ∃ f : ℕ → α, (∀ v < n, f v ∈ L v) ∧ ∀ u < n, ∀ v < n, u ≠ v → f u = f v → cadj n u v

theorem cadj_symm {n u v : ℕ} (h : cadj n u v) : cadj n v u := by
  unfold cadj at *; omega

theorem cadj_nxt (n v : ℕ) (_hn : 2 ≤ n) (hv : v < n) : cadj n v (nxt n v) := by
  unfold cadj nxt; split_ifs <;> omega

theorem cadj_pos (n i r : ℕ) (_hn : 2 ≤ n) (hi : i < n) (hr : r + 1 < n) :
    cadj n (pos n i r) (pos n i (r + 1)) := by
  unfold cadj pos; split_ifs <;> omega

theorem pos_lt (n i r : ℕ) (hi : i < n) (hr : r < n) : pos n i r < n := by
  unfold pos; split_ifs <;> omega

/-- An independent set of the cycle of length `2m+1` has at most `m` vertices. -/
theorem indep_le (m : ℕ) (I : Finset ℕ) (hI : I ⊆ range (2 * m + 1))
    (h : ∀ v ∈ I, nxt (2 * m + 1) v ∉ I) : I.card ≤ m := by
  have hinj : Set.InjOn (nxt (2 * m + 1)) I := by
    intro u hu v hv huv
    have hu' := mem_range.1 (hI hu)
    have hv' := mem_range.1 (hI hv)
    unfold nxt at huv
    split_ifs at huv <;> omega
  have h1 := card_image_of_injOn hinj
  have hd : Disjoint I (I.image (nxt (2 * m + 1))) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
    exact h y hy hx
  have hsub : I ∪ I.image (nxt (2 * m + 1)) ⊆ range (2 * m + 1) := by
    refine union_subset hI ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    have := mem_range.1 (hI hy)
    rw [mem_range]
    unfold nxt
    split_ifs <;> omega
  have h2 := card_le_card hsub
  rw [card_union_of_disjoint hd, card_range, h1] at h2
  omega

/-- If consecutive lists on the odd cycle are disjoint, Hall's condition holds and the
complement of the cycle is colourable. -/
theorem claim1 [Inhabited α] (m : ℕ) (hm : 1 ≤ m) (L : ℕ → Finset α)
    (hL : ∀ v < 2 * m + 1, m ≤ (L v).card)
    (hd : ∀ v < 2 * m + 1, Disjoint (L v) (L (nxt (2 * m + 1) v))) : CCol (2 * m + 1) L := by
  obtain ⟨f, hf, hinj⟩ := hall_sdr (range (2 * m + 1)) L (fun W hW => by
    refine card_le_of_bounded W L m (by omega) (fun v hv => hL v (mem_range.1 (hW hv))) ?_
    intro c
    apply indep_le m _ ((filter_subset _ _).trans hW)
    intro v hv hv'
    rw [mem_filter] at hv hv'
    exact disjoint_left.1 (hd v (mem_range.1 (hW hv.1))) hv.2 hv'.2)
  exact ⟨f, fun v hv => hf v (mem_range.2 hv), fun u hu v hv huv hfe =>
    absurd (hinj u (mem_range.2 hu) v (mem_range.2 hv) hfe) huv⟩

/-- The lists of the path that remains after deleting `i` and its successor, with the colour
`c` removed. -/
def eraseShift (n i : ℕ) (L : ℕ → Finset α) (c : α) (j : ℕ) : Finset α :=
  (L (pos n i (j + 2))).erase c

/-- The position on that path of a vertex of the cycle. -/
def back (n i v : ℕ) : ℕ := if i + 2 ≤ v then v - i - 2 else v + n - i - 2

/-- If two consecutive vertices `i`, `i + 1` share a colour `c`, every second vertex after them
has the same list, and that list contains `c`. -/
theorem claim2 [Inhabited α] (m : ℕ) (hm : 2 ≤ m) (L : ℕ → Finset α)
    (hL : ∀ v < 2 * m + 1, m ≤ (L v).card) (hnc : ¬ CCol (2 * m + 1) L)
    (i : ℕ) (hi : i < 2 * m + 1) (c : α) (hc1 : c ∈ L i) (hc2 : c ∈ L (nxt (2 * m + 1) i)) :
    ∀ r, 2 ≤ r → r ≤ 2 * m → r % 2 = 0 →
      c ∈ L (pos (2 * m + 1) i r) ∧ L (pos (2 * m + 1) i r) = L (pos (2 * m + 1) i 2) := by
  have hG : Good (range (2 * m - 1)) := by
    intro v hv hodd
    rw [mem_range] at hv
    exact ⟨mem_range.2 (by omega), mem_range.2 (by omega)⟩
  have hevm : (ev (range (2 * m - 1))).card ≤ m := by
    have hs : ev (range (2 * m - 1)) ⊆ (range m).image (fun j => 2 * j) := by
      intro v hv
      rw [mem_ev, mem_range] at hv
      rw [mem_image]
      exact ⟨v / 2, mem_range.2 (by omega), by omega⟩
    exact (card_le_card hs).trans (card_image_le.trans (card_range m).le)
  have hback : ∀ v < 2 * m + 1, v ≠ i → v ≠ nxt (2 * m + 1) i →
      back (2 * m + 1) i v ∈ range (2 * m - 1) ∧ pos (2 * m + 1) i (back (2 * m + 1) i v + 2) = v := by
    intro v hv hvi hvn
    unfold nxt at hvn
    rw [mem_range]
    unfold back pos
    constructor <;> split_ifs at hvn ⊢ <;> omega
  have hcol : ¬ Col (range (2 * m - 1)) (eraseShift (2 * m + 1) i L c) := by
    rintro ⟨g, hg, hginj⟩
    apply hnc
    refine ⟨fun v => if v = i ∨ v = nxt (2 * m + 1) i then c else g (back (2 * m + 1) i v),
      ?_, ?_⟩
    · intro v hv
      by_cases h : v = i ∨ v = nxt (2 * m + 1) i
      · dsimp only
        rw [if_pos h]
        rcases h with h | h
        · rw [h]; exact hc1
        · rw [h]; exact hc2
      · dsimp only
        rw [if_neg h]
        push Not at h
        obtain ⟨hb, hp⟩ := hback v hv h.1 h.2
        have := hg _ hb
        unfold eraseShift at this
        rw [hp] at this
        exact mem_of_mem_erase this
    · intro u hu v hv huv hfe
      by_cases hu' : u = i ∨ u = nxt (2 * m + 1) i
      · by_cases hv' : v = i ∨ v = nxt (2 * m + 1) i
        · rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
          · exact absurd (h1.trans h2.symm) huv
          · rw [h1, h2]; exact cadj_nxt _ i (by omega) hi
          · rw [h1, h2]; exact cadj_symm (cadj_nxt _ i (by omega) hi)
          · exact absurd (h1.trans h2.symm) huv
        · dsimp only at hfe
          rw [if_pos hu', if_neg hv'] at hfe
          push Not at hv'
          obtain ⟨hb, -⟩ := hback v hv hv'.1 hv'.2
          have := hg _ hb
          unfold eraseShift at this
          exact absurd hfe.symm (ne_of_mem_erase this)
      · by_cases hv' : v = i ∨ v = nxt (2 * m + 1) i
        · dsimp only at hfe
          rw [if_neg hu', if_pos hv'] at hfe
          push Not at hu'
          obtain ⟨hb, -⟩ := hback u hu hu'.1 hu'.2
          have := hg _ hb
          unfold eraseShift at this
          exact absurd hfe (ne_of_mem_erase this)
        · dsimp only at hfe
          rw [if_neg hu', if_neg hv'] at hfe
          push Not at hu' hv'
          obtain ⟨hbu, hpu⟩ := hback u hu hu'.1 hu'.2
          obtain ⟨hbv, hpv⟩ := hback v hv hv'.1 hv'.2
          have hne : back (2 * m + 1) i u ≠ back (2 * m + 1) i v := by
            intro h
            apply huv
            rw [← hpu, ← hpv, h]
          have hbu' := mem_range.1 hbu
          have hbv' := mem_range.1 hbv
          rcases hginj _ hbu _ hbv hne hfe with h | h
          · have := cadj_pos (2 * m + 1) i (back (2 * m + 1) i u + 2) (by omega) hi (by omega)
            rw [show back (2 * m + 1) i u + 2 + 1 = back (2 * m + 1) i v + 2 by omega, hpu,
              hpv] at this
            exact this
          · have := cadj_pos (2 * m + 1) i (back (2 * m + 1) i v + 2) (by omega) hi (by omega)
            rw [show back (2 * m + 1) i v + 2 + 1 = back (2 * m + 1) i u + 2 by omega, hpu,
              hpv] at this
            exact cadj_symm this
  have hLge : ∀ v ∈ range (2 * m - 1),
      (ev (range (2 * m - 1))).card - 1 ≤ (eraseShift (2 * m + 1) i L c v).card := by
    intro v hv
    unfold eraseShift
    have h1 := pred_card_le_card_erase (s := L (pos (2 * m + 1) i (v + 2))) (a := c)
    have h2 := hL (pos (2 * m + 1) i (v + 2)) (pos_lt _ _ _ hi (by rw [mem_range] at hv; omega))
    omega
  have GP := gpath (range (2 * m - 1)) hG (eraseShift (2 * m + 1) i L c) hLge hcol
  have hmem : ∀ x ∈ ev (range (2 * m - 1)), c ∈ L (pos (2 * m + 1) i (x + 2)) := by
    intro x hx
    by_contra hcx
    have hx' := (GP x hx x hx).2
    unfold eraseShift at hx'
    rw [erase_eq_of_notMem hcx] at hx'
    have hx2 := hx
    rw [mem_ev, mem_range] at hx2
    have := hL (pos (2 * m + 1) i (x + 2)) (pos_lt _ _ _ hi (by omega))
    omega
  intro r hr2 hrm hre
  have hu : r - 2 ∈ ev (range (2 * m - 1)) := mem_ev.2 ⟨mem_range.2 (by omega), by omega⟩
  have h0 : 0 ∈ ev (range (2 * m - 1)) := mem_ev.2 ⟨mem_range.2 (by omega), by omega⟩
  have e := (GP _ hu 0 h0).1
  unfold eraseShift at e
  have hcu := hmem _ hu
  have hc0 := hmem 0 h0
  rw [show r - 2 + 2 = r by omega] at e hcu
  rw [zero_add] at e hc0
  exact ⟨hcu, (insert_erase hcu).symm.trans ((congrArg (insert c) e).trans (insert_erase hc0))⟩

/-- The cycle theorem: on the complement of an odd cycle of length `2m+1`, `m ≥ 2`, lists of
size at least `m` give a colouring unless all lists are equal. -/
theorem cycle_main [Inhabited α] (m : ℕ) (hm : 2 ≤ m) (L : ℕ → Finset α)
    (hL : ∀ v < 2 * m + 1, m ≤ (L v).card) (hnc : ¬ CCol (2 * m + 1) L) :
    ∀ u < 2 * m + 1, ∀ v < 2 * m + 1, L u = L v := by
  have hex : ∃ i < 2 * m + 1, ¬ Disjoint (L i) (L (nxt (2 * m + 1) i)) := by
    by_contra h
    push Not at h
    exact hnc (claim1 m (by omega) L hL h)
  obtain ⟨i, hi, hd⟩ := hex
  obtain ⟨c, hc1, hc2⟩ := not_disjoint_iff.1 hd
  obtain ⟨i1, hi1⟩ : ∃ i1, i1 = pos (2 * m + 1) i (2 * m) := ⟨_, rfl⟩
  have hi1lt : i1 < 2 * m + 1 := by rw [hi1]; exact pos_lt _ _ _ hi (by omega)
  have ia : nxt (2 * m + 1) i1 = i := by rw [hi1]; unfold nxt pos; split_ifs <;> omega
  have ib : ∀ r, r < 2 * m → pos (2 * m + 1) i1 (r + 1) = pos (2 * m + 1) i r := by
    intro r hr; rw [hi1]; unfold pos; split_ifs <;> omega
  have ic : pos (2 * m + 1) i 1 = nxt (2 * m + 1) i := by unfold pos nxt; split_ifs <;> omega
  have id : nxt (2 * m + 1) (nxt (2 * m + 1) i) = pos (2 * m + 1) i 2 := by
    unfold pos nxt; split_ifs <;> omega
  have ie1 : pos (2 * m + 1) (nxt (2 * m + 1) i) (2 * m) = i := by
    unfold pos nxt; split_ifs <;> omega
  have ie2 : pos (2 * m + 1) (nxt (2 * m + 1) i) 2 = pos (2 * m + 1) i 3 := by
    unfold pos nxt; split_ifs <;> omega
  have i_f : nxt (2 * m + 1) (pos (2 * m + 1) i 2) = pos (2 * m + 1) i 3 := by
    unfold pos nxt; split_ifs <;> omega
  have ig1 : pos (2 * m + 1) (pos (2 * m + 1) i 2) (2 * m) = nxt (2 * m + 1) i := by
    unfold pos nxt; split_ifs <;> omega
  have ig2 : pos (2 * m + 1) (pos (2 * m + 1) i 2) 2 = pos (2 * m + 1) i 4 := by
    unfold pos; split_ifs <;> omega
  have hnxtlt : nxt (2 * m + 1) i < 2 * m + 1 := by unfold nxt; split_ifs <;> omega
  have hp2lt : pos (2 * m + 1) i 2 < 2 * m + 1 := pos_lt _ _ _ hi (by omega)
  have e2 : pos (2 * m + 1) i1 2 = nxt (2 * m + 1) i := (ib 1 (by omega)).trans ic
  have e4 : pos (2 * m + 1) i1 4 = pos (2 * m + 1) i 3 := ib 3 (by omega)
  have A := claim2 m hm L hL hnc i hi c hc1 hc2
  have B := claim2 m hm L hL hnc i1 hi1lt c
    (by rw [hi1]; exact (A (2 * m) (by omega) le_rfl (by omega)).1) (by rw [ia]; exact hc1)
  have A2 := A 2 le_rfl (by omega) rfl
  have A4 := A 4 (by omega) (by omega) rfl
  have B4 := B 4 (by omega) (by omega) rfl
  rw [e4] at B4
  have C := claim2 m hm L hL hnc (nxt (2 * m + 1) i) hnxtlt c hc2 (by rw [id]; exact A2.1)
  have C2m := (C (2 * m) (by omega) le_rfl (by omega)).2
  rw [ie1, ie2] at C2m
  have D := claim2 m hm L hL hnc (pos (2 * m + 1) i 2) hp2lt c A2.1 (by rw [i_f]; exact B4.1)
  have D2m := (D (2 * m) (by omega) le_rfl (by omega)).2
  rw [ig1, ig2] at D2m
  -- the two classes of lists agree with `L i`
  have hodd : L (pos (2 * m + 1) i1 2) = L i := (C2m.trans B4.2).symm
  have heven : L (pos (2 * m + 1) i 2) = L i :=
    A4.2.symm.trans (D2m.symm.trans ((congrArg L e2).symm.trans hodd))
  have hall : ∀ v < 2 * m + 1, L v = L i := by
    intro v hv
    obtain ⟨r, hr, hrv⟩ : ∃ r, r < 2 * m + 1 ∧ pos (2 * m + 1) i r = v :=
      ⟨if i ≤ v then v - i else v + (2 * m + 1) - i, by split_ifs <;> omega,
        by unfold pos; split_ifs <;> omega⟩
    rw [← hrv]
    by_cases hr0 : r = 0
    · rw [hr0, show pos (2 * m + 1) i 0 = i by unfold pos; split_ifs <;> omega]
    · by_cases hre : r % 2 = 0
      · exact (A r (by omega) (by omega) hre).2.trans heven
      · rw [← ib r (by omega)]
        exact (B (r + 1) (by omega) (by omega) (by omega)).2.trans hodd
  exact fun u hu v hv => (hall u hu).trans (hall v hv).symm


end OddAntihole
