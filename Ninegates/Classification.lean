/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.Elimination

/-!

# Classification of full waits

The main theorem of our project.
-/

@[expose] public section

namespace Mahjong.Hand

open Counterexample

theorem fullWait_classification (n : Nat) (hn : 2 ≤ n) (c : Hand n)
    (hc : IsFullWait c) : IsEightFamily c := by
  classical
  by_contra hfamily
  let hex : ∃ m, 2 ≤ m ∧ ∃ d : Hand m, IsCE d :=
    ⟨n, hn, c, ⟨hc, hfamily⟩⟩
  let m := Nat.find hex
  obtain ⟨hm, d, hd⟩ := Nat.find_spec hex
  have hmin : ∀ k, 2 ≤ k → k < m → ¬ HasCE k := by
    intro k hk hkm hcounterexample
    have hspec := Nat.find_min' hex ⟨hk, hcounterexample⟩
    omega
  have hdmem := mem_candidates_of_minimal hm hd hmin
  have hm' : m ≤ 7 := (mem_candidates_iff.mp hdmem).2.1
  exact candidates_no_CE m hm hm' d hdmem hd

theorem isFullWait_iff_eightFamily (n : Nat) (hn : 2 ≤ n) (c : Hand n) :
    IsFullWait c ↔ IsEightFamily c := by
  constructor
  · exact fullWait_classification n hn c
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Standard.A.isFullWait n (by omega)
    · exact Standard.B.isFullWait n hn
    · exact Standard.B'.isFullWait n hn
    · exact Standard.C.isFullWait n hn
    · exact Standard.C'.isFullWait n hn
    · exact Standard.D.isFullWait n hn
    · exact Standard.D'.isFullWait n hn
    · exact Standard.E.isFullWait n hn

theorem orderOne_fullWait_classification (c : Hand 1) (hc : IsFullWait c) :
    IsOrderOneFamily c := by
  have hmem : c ∈ Candidates 1 := by
    apply mem_candidates_iff.mpr
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro i
      exact interior_positive c hc ⟨i.val + 1, by omega⟩
        ⟨by simp, by simp⟩
    · exact IsFullWait.size (by omega) hc
    · omega
  exact orderOne_fullWait_classification_of_candidates c hmem hc

theorem orderOne_isFullWait_iff_isOrderOneFamily (c : Hand 1) :
    IsFullWait c ↔ IsOrderOneFamily c := by
  constructor
  · exact orderOne_fullWait_classification c
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Standard.One.a.isFullWait
    · exact Standard.One.b.isFullWait
    · exact Standard.One.c.isFullWait
    · exact Standard.One.c'.isFullWait
    · exact Standard.One.d.isFullWait
    · exact Standard.One.d'.isFullWait

theorem liveFullWait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsLiveFullWait) : c = Standard.A n := by
  have hfull := (isLiveFullWait_iff_le_three.mp hc).1
  have hfamily := fullWait_classification n hn c hfull
  rcases hfamily with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact False.elim ((Standard.B.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.B'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.C.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.C'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.D.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.D'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.E.not_isLiveFullWait n hn) hc)

end Mahjong.Hand
