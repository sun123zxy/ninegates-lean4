import Ninegates.Wait.Decide
import Ninegates.Winning.Decidable

/-!
Correctness specifications and optimized `Decidable` instances for waits.
-/

namespace Mahjong.Hand

namespace IsWaitingTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsWaitingTile.decide c i = true ↔ IsWaitingTile c i := by
  simp [IsWaitingTile.decide, IsWaitingTile, Winning.Decidable.decide_spec]

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWaitingTile c i) :=
  decidable_of_iff (IsWaitingTile.decide c i = true) (decide_spec c i)

end IsWaitingTile.Decidable

namespace IsLiveWaitingTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsLiveWaitingTile.decide c i = true ↔ IsLiveWaitingTile c i := by
  simp only [IsLiveWaitingTile.decide, IsWaitingTile.decide, Bool.and_eq_true,
    Winning.Decidable.decide_spec, decide_eq_true_eq]
  rfl

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsLiveWaitingTile c i) :=
  decidable_of_iff (IsLiveWaitingTile.decide c i = true) (decide_spec c i)

end IsLiveWaitingTile.Decidable

namespace IsFullWait.Decidable

open Winning.Decidable

@[simp, grind =]
private lemma vector_set_get_eq {α : Type} {m : Nat} (v : Vector α m) (i : Fin m)
    (x : α) : (v.set i.val x).get i = x := by
  change (v.toArray.set i.val x)[i.val] = x
  simp

@[simp, grind =]
private lemma vector_set_get_ne {α : Type} {m : Nat} (v : Vector α m) (i j : Fin m)
    (x : α) (h : i ≠ j) : (v.set i.val x).get j = v.get j := by
  change (v.toArray.set i.val x)[j.val] = v.toArray[j.val]
  simp only [Array.getElem_set]
  split
  · exact (h (Fin.ext ‹_›)).elim
  · rfl

@[simp, grind =]
private lemma finRange_append_last (k : Nat) :
    List.finRange (k + 1) =
      (List.finRange k).map Fin.castSucc ++ [(⟨k, by omega⟩ : Fin (k + 1))] := by
  apply List.ext_getElem
  · simp
  · intros; simp [List.getElem_finRange]; grind

private def prefixIndices (m k : Nat) (hk : k ≤ m) : List (Fin m) :=
  (List.finRange k).map (fun a => ⟨a.val, by omega⟩)

private def prefixUpdate (m : Nat) (f : Fin m → Nat)
    (v : Vector StateSet (m + 1)) (i : Fin m) : Vector StateSet (m + 1) :=
  v.set (i.val + 1) (stepSet (f i) (v.get ⟨i.val, by omega⟩)) (by omega)

private def prefixFold (m : Nat) (f : Fin m → Nat) (k : Nat) (hk : k ≤ m) :
    Vector StateSet (m + 1) :=
  (prefixIndices m k hk).foldl (prefixUpdate m f)
    ((Vector.replicate (m + 1) emptyStateSet).set 0
      (emptyStateSet.insert State.init) (by omega))

private def prefixSem (m : Nat) (f : Fin m → Nat) (j : Nat) : StateSet :=
  reachable ((∅ : StateSet).insert State.init)
    ((List.ofFn f).take j)

@[simp, grind =]
private lemma prefixIndices_succ (m k : Nat) (hk : k + 1 ≤ m) :
    prefixIndices m (k + 1) hk = prefixIndices m k (by omega) ++
      [⟨k, by omega⟩] := by
  simp [prefixIndices]

@[simp, grind =]
private lemma prefixFold_succ (m : Nat) (f : Fin m → Nat) (k : Nat)
    (hk : k + 1 ≤ m) :
    prefixFold m f (k + 1) hk =
      prefixUpdate m f (prefixFold m f k (by omega)) ⟨k, by omega⟩ := by
  simp [prefixFold, List.foldl_append]

@[grind =]
private lemma prefixFold_get : ∀ (m : Nat) (f : Fin m → Nat) (k : Nat) (hk : k ≤ m),
    ∀ j (hj : j ≤ k),
      (prefixFold m f k hk).get ⟨j, by omega⟩ = prefixSem m f j := by
  intro m f k
  induction k with
  | zero =>
      intro hk j hj
      have hj0 : j = 0 := by omega
      subst j
      change ((Vector.replicate (m + 1) emptyStateSet).set 0
          (emptyStateSet.insert State.init) (by omega)).get ⟨0, by omega⟩ = _
      simpa [prefixSem, reachable] using
        (vector_set_get_eq (Vector.replicate (m + 1) emptyStateSet)
          (⟨0, by omega⟩ : Fin (m + 1)) (emptyStateSet.insert State.init))
  | succ k ih =>
      intro hk j hj
      by_cases hlast : j = k + 1
      · subst j
        rw [prefixFold_succ m f k hk]
        have hp := ih (by omega) k (by omega)
        let z : Fin (m + 1) := ⟨k + 1, by omega⟩
        have hz0 := vector_set_get_eq (prefixFold m f k (by omega)) z
          (stepSet (f ⟨k, by omega⟩)
            ((prefixFold m f k (by omega)).get ⟨k, by omega⟩))
        have hlen : (List.ofFn f).length = m := by simp
        have hsem : prefixSem m f (k + 1) =
            stepSet (f ⟨k, by omega⟩) (prefixSem m f k) := by
          unfold prefixSem
          rw [← List.take_concat_get' (List.ofFn f) k
            (by simpa [hlen] using (show k < m from by omega)),
            Winning.Decidable.reachable_append]
          simp [reachable, List.getElem_ofFn]
        have hz : (prefixUpdate m f (prefixFold m f k (by omega)) ⟨k, by omega⟩).get z =
            stepSet (f ⟨k, by omega⟩) (prefixSem m f k) := by
          unfold prefixUpdate
          simpa [z, hp] using hz0
        exact hz.trans hsem.symm
      · have hjk : j ≤ k := by omega
        rw [prefixFold_succ m f k hk]
        let z : Fin (m + 1) := ⟨k + 1, by omega⟩
        let q : Fin (m + 1) := ⟨j, by omega⟩
        have hz := vector_set_get_ne (prefixFold m f k (by omega)) z q
          (stepSet (f ⟨k, by omega⟩)
            ((prefixFold m f k (by omega)).get ⟨k, by omega⟩)) (by
              intro heq
              apply hlast
              simpa [z, q] using (congrArg Fin.val heq).symm)
        simpa [prefixUpdate, z, q] using (hz.trans (ih (by omega) j hjk))

@[grind =]
private lemma buildPrefix_eq_prefixFold (count : Array Nat) :
    buildPrefix count = prefixFold count.size
      (fun i => count[i.val]'i.isLt) count.size le_rfl := by
  simp [buildPrefix, prefixFold, prefixIndices, List.forIn_pure_yield_eq_foldl]
  congr 1

private lemma mem_fold_insert_if (xs : List Winning.Decidable.State)
    (p : Winning.Decidable.State → Bool) (acc : Winning.Decidable.StateSet)
    (q : Winning.Decidable.State) :
    q ∈ xs.foldl (fun good x => if p x then good.insert x else good) acc ↔
      q ∈ acc ∨ ∃ x ∈ xs, p x = true ∧ q = x := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp; grind

@[grind =]
private lemma nonempty_iff_exists (s : Winning.Decidable.StateSet) :
    s.isEmpty = false ↔ ∃ q, q ∈ s := by
  rw [Std.ExtHashSet.isEmpty_eq_false_iff]
  constructor
  · intro hs
    by_contra hn
    push Not at hn
    apply hs
    ext; grind
  · grind

private def predecessor (x : Nat) (states : Winning.Decidable.StateSet) :
    Winning.Decidable.StateSet :=
  Winning.Decidable.State.all.foldl (fun good q =>
    if !(Winning.Decidable.step x q ∩ states).isEmpty then good.insert q else good)
    Winning.Decidable.emptyStateSet

@[grind =]
private lemma predecessor_spec (x : Nat) (states : Winning.Decidable.StateSet)
    (q : Winning.Decidable.State) :
    q ∈ predecessor x states ↔
      ∃ t, t ∈ Winning.Decidable.step x q ∧ t ∈ states := by
  unfold predecessor
  rw [mem_fold_insert_if]
  simp only [Winning.Decidable.emptyStateSet,
    Std.ExtHashSet.emptyWithCapacity_eq, Winning.Decidable.state_all]
  constructor
  · rintro (h | ⟨s, hs, hcond, hq⟩)
    · simp at h
    · subst q
      have hcond' : (Winning.Decidable.step x s ∩ states).isEmpty = false := by
        simpa [Bool.not_eq_true_eq_eq_false] using hcond
      obtain ⟨t, ht⟩ := (nonempty_iff_exists _).mp hcond'
      exact ⟨t, (Std.ExtHashSet.mem_inter_iff.mp ht).1,
        (Std.ExtHashSet.mem_inter_iff.mp ht).2⟩
  · rintro ⟨t, ht, hts⟩
    right
    refine ⟨q, by trivial, ?_, rfl⟩
    have hne : (Winning.Decidable.step x q ∩ states).isEmpty = false :=
      (nonempty_iff_exists _).mpr ⟨t, (Std.ExtHashSet.mem_inter_iff).mpr ⟨ht, hts⟩⟩
    simpa [Bool.not_eq_true_eq_eq_false] using hne

private def suffixIndices (m k : Nat) (hk : k ≤ m) : List (Fin m) :=
  (List.finRange k).map (fun a => ⟨m - 1 - a.val, by omega⟩)

private def suffixUpdate (m : Nat) (f : Fin m → Nat)
    (v : Vector Winning.Decidable.StateSet (m + 1)) (i : Fin m) :
    Vector Winning.Decidable.StateSet (m + 1) :=
  v.set i.val (predecessor (f i) (v.get ⟨i.val + 1, by omega⟩)) (by omega)

private def suffixFold (m : Nat) (f : Fin m → Nat) (k : Nat) (hk : k ≤ m) :
    Vector Winning.Decidable.StateSet (m + 1) :=
  (suffixIndices m k hk).foldl (suffixUpdate m f)
    ((Vector.replicate (m + 1) Winning.Decidable.emptyStateSet).set m
      (Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final) (by omega))

private def suffixSemList : List Nat → Winning.Decidable.StateSet
  | [] => Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final
  | x :: xs => predecessor x (suffixSemList xs)

private def suffixSem (m : Nat) (f : Fin m → Nat) (j : Nat) :
    Winning.Decidable.StateSet := suffixSemList ((List.ofFn f).drop j)

@[simp, grind =]
private lemma suffixIndices_succ (m k : Nat) (hk : k + 1 ≤ m) :
    suffixIndices m (k + 1) hk = suffixIndices m k (by omega) ++
      [⟨m - 1 - k, by omega⟩] := by
  simp [suffixIndices]

@[simp, grind =]
private lemma suffixSem_succ (m : Nat) (f : Fin m → Nat) (j : Nat) (hj : j < m) :
    suffixSem m f j = predecessor (f ⟨j, hj⟩) (suffixSem m f (j + 1)) := by
  unfold suffixSem
  rw [← List.cons_getElem_drop_succ (l := List.ofFn f) (n := j)
    (h := by simp_all)]
  simp [List.getElem_ofFn]
  rfl

@[grind =]
private lemma suffixSemList_spec (xs : List Nat) (q : Winning.Decidable.State) :
    q ∈ suffixSemList xs ↔
      ∃ choices,
        Winning.Decidable.replayChoices q xs choices = some Winning.Decidable.State.final := by
  induction xs generalizing q with
  | nil =>
      change q ∈ Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final ↔ _
      simp; grind
  | cons x xs ih =>
    simp only [suffixSemList, predecessor_spec, Winning.Decidable.replayChoices_exists_cons_iff]
    grind

@[grind =]
private lemma suffixSemList_reachable (xs : List Nat) (q : Winning.Decidable.State) :
      q ∈ suffixSemList xs ↔
      Winning.Decidable.State.final ∈
        Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert q) xs := by
  rw [suffixSemList_spec, Winning.Decidable.mem_reachable]
  grind

@[simp, grind =]
private lemma suffixFold_succ (m : Nat) (f : Fin m → Nat) (k : Nat)
    (hk : k + 1 ≤ m) :
    suffixFold m f (k + 1) hk =
      suffixUpdate m f (suffixFold m f k (by omega)) ⟨m - 1 - k, by omega⟩ := by
  simp [suffixFold, List.foldl_append]

@[grind =]
private lemma suffixFold_get : ∀ (m : Nat) (f : Fin m → Nat) (k : Nat) (hk : k ≤ m),
    ∀ j (_hjlo : m - k ≤ j) (hjhi : j ≤ m),
      (suffixFold m f k hk).get ⟨j, by omega⟩ = suffixSem m f j := by
  intro m f k
  induction k with
  | zero =>
      intro hk j hjlo hjhi
      have hj : j = m := by omega
      subst j
      change ((Vector.replicate (m + 1) Winning.Decidable.emptyStateSet).set m
          (Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final) (by omega)).get
          ⟨m, by omega⟩ = _
      have hlast := vector_set_get_eq (Vector.replicate (m + 1)
        Winning.Decidable.emptyStateSet) (⟨m, by omega⟩ : Fin (m + 1))
        (Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final)
      have hdrop : (List.ofFn f).drop m = [] := by simp
      simpa [suffixSem, suffixSemList, hdrop] using hlast
  | succ k ih =>
      intro hk j hjlo hjhi
      let i : Nat := m - 1 - k
      by_cases hlast : j = i
      · subst j
        rw [suffixFold_succ m f k hk]
        let z : Fin (m + 1) := ⟨i, by omega⟩
        have hz0 := vector_set_get_eq (suffixFold m f k (by omega)) z
          (predecessor (f ⟨i, by omega⟩)
            ((suffixFold m f k (by omega)).get ⟨i + 1, by omega⟩))
        have hprev := ih (by omega) (i + 1) (by omega) (by omega)
        have hz : (suffixUpdate m f (suffixFold m f k (by omega)) ⟨i, by omega⟩).get z =
            predecessor (f ⟨i, by omega⟩) (suffixSem m f (i + 1)) := by
          unfold suffixUpdate
          simpa [z, i, hprev] using hz0
        exact hz.trans (suffixSem_succ m f i (by omega)).symm
      · have hj : i < j := by omega
        rw [suffixFold_succ m f k hk]
        let z : Fin (m + 1) := ⟨i, by omega⟩
        let q : Fin (m + 1) := ⟨j, by omega⟩
        have hz := vector_set_get_ne (suffixFold m f k (by omega)) z q
          (predecessor (f ⟨i, by omega⟩)
            ((suffixFold m f k (by omega)).get ⟨i + 1, by omega⟩)) (by
              intro heq
              apply hlast
              simpa [z, q, i] using (congrArg Fin.val heq).symm)
        simpa [suffixUpdate, z, q] using (hz.trans (ih (by omega) j (by omega) hjhi))

private lemma buildSuffix_inner (x : Nat) (states : Winning.Decidable.StateSet) :
    Id.run (do
      let mut good : Winning.Decidable.StateSet := Winning.Decidable.emptyStateSet
      for q in Winning.Decidable.State.all do
        if !(Winning.Decidable.step x q ∩ states).isEmpty then
          good := good.insert q
      return good) = predecessor x states := by
  simp only [Id.run_bind, Id.run_pure]
  let g : Winning.Decidable.State → Winning.Decidable.StateSet →
      Winning.Decidable.StateSet := fun q good =>
    if !(Winning.Decidable.step x q ∩ states).isEmpty then good.insert q else good
  have h := List.forIn_pure_yield_eq_foldl (m := Id)
    (l := Winning.Decidable.State.all) (f := g) Winning.Decidable.emptyStateSet
  have h' := congrArg Id.run h
  dsimp [g, predecessor] at h' ⊢
  convert h' using 1
  congr 2
  funext q good
  grind

private def suffixDoInner (count : Array Nat)
    (v : Vector Winning.Decidable.StateSet (count.size + 1)) (k : Fin count.size) :
    Id Winning.Decidable.StateSet := do
  let i := count.size - 1 - k.val
  let mut good : Winning.Decidable.StateSet := Winning.Decidable.emptyStateSet
  for q in Winning.Decidable.State.all do
    if !(Winning.Decidable.step (count[i]'(by omega)) q ∩
        (v.get ⟨i + 1, by omega⟩)).isEmpty then
      good := good.insert q
  return good

private def suffixDoUpdate (count : Array Nat)
    (v : Vector Winning.Decidable.StateSet (count.size + 1)) (k : Fin count.size) :
    Id (Vector Winning.Decidable.StateSet (count.size + 1)) := do
  let i := count.size - 1 - k.val
  let good ← suffixDoInner count v k
  return v.set i good (by omega)

@[grind =]
private lemma suffixDoInner_eq (count : Array Nat)
    (v : Vector Winning.Decidable.StateSet (count.size + 1)) (k : Fin count.size) :
    suffixDoInner count v k = predecessor (count[count.size - 1 - k.val]'(by omega))
      (v.get ⟨count.size - 1 - k.val + 1, by omega⟩) := by
  unfold suffixDoInner
  exact buildSuffix_inner _ _

private lemma foldlM_id {α β : Type} (f : β → α → Id β) (b : β) (xs : List α) :
    (List.foldlM f b xs).run = List.foldl (fun b a => (f b a).run) b xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    simp [List.foldlM, List.foldl, ih]

private def updateAt (xs : List Nat) (i : Nat) (hi : i < xs.length) : List Nat :=
  xs.set i (xs.get ⟨i, hi⟩ + 1)

@[grind =]
private lemma list_ofFn_add_single (c : Hand n) (i : Fin (3 * n)) :
    List.ofFn (c + single i) = updateAt (List.ofFn c) i.val (by simp) := by
  apply List.ext_getElem
  · simp only [updateAt, List.length_set, List.length_ofFn]
  · intros; simp [updateAt]; grind

@[grind =]
private lemma updateAt_eq_take (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    updateAt xs i hi = xs.take i ++ [xs.get ⟨i, hi⟩ + 1] ++ xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [updateAt]
      | succ i =>
          simp only [updateAt, List.set_cons_succ, List.get_cons_succ,
            List.take_succ_cons, List.drop_succ_cons]
          have hi' : i < xs.length := by simpa using hi
          exact congrArg (fun ys => x :: ys) (ih (i := i) hi')

private lemma fold_set_get {α : Type} : ∀ (N m : Nat) (hm : m ≤ N) (v : Vector α N)
    (f : Fin m → α) (j : Fin m),
    ((List.finRange m).foldl (fun v i => v.set i.val (f i) (by omega)) v).get
      ⟨j.val, by omega⟩ = f j := by
  intro N m
  induction m with
  | zero => intro hm v f j; exact Fin.elim0 j
  | succ m ih =>
      intro hm v f j
      rw [finRange_append_last, List.foldl_append, List.foldl_map]
      simp only [List.foldl_cons, List.foldl_nil]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · grind
      · let v' := (List.finRange m).foldl
          (fun v i => v.set i.val (f i.castSucc) (by omega)) v
        have hv := ih (hm := by omega) v (fun i => f i.castSucc) j
        have hjlt : j.val < m := j.isLt
        have hset := vector_set_get_ne v' (⟨m, by omega⟩ : Fin N)
          ⟨j.val, by omega⟩ (f ⟨m, by omega⟩) (by
            apply Fin.ne_of_val_ne
            change m ≠ j.val
            omega)
        simpa [v'] using (hset.trans hv)

@[grind =]
private lemma buildSuffix_eq_suffixFold (count : Array Nat) :
    buildSuffix count = suffixFold count.size
      (fun i => count[i.val]'i.isLt) count.size le_rfl := by
  unfold buildSuffix
  simp only [Id.run_bind, Id.run_pure]
  let init : Vector Winning.Decidable.StateSet (count.size + 1) :=
    (Vector.replicate (count.size + 1) Winning.Decidable.emptyStateSet).set count.size
      (Winning.Decidable.emptyStateSet.insert Winning.Decidable.State.final) (by omega)
  let f : Fin count.size →
      Vector Winning.Decidable.StateSet (count.size + 1) → Id Winning.Decidable.StateSet :=
    fun k v => suffixDoInner count v k
  let g : Fin count.size →
      Vector Winning.Decidable.StateSet (count.size + 1) → Winning.Decidable.StateSet →
        Vector Winning.Decidable.StateSet (count.size + 1) :=
    fun k v good => v.set (count.size - 1 - k.val) good (by omega)
  have h := List.forIn_yield_eq_foldlM (m := Id) (l := List.finRange count.size)
    (f := f) (g := g) init
  have h' := congrArg Id.run h
  convert h' using 1
  · congr 2
  · rw [foldlM_id, suffixFold, suffixIndices, List.foldl_map]
    simp [suffixUpdate, init, f, g, suffixDoInner_eq]
    rfl

@[simp, grind =]
theorem waitingTiles_size (count : Array Nat) :
    (waitingTiles count).size = count.size := by
  simp [waitingTiles]

@[grind =]
private lemma waitingTiles_get (count : Array Nat) (j : Fin count.size) :
    (waitingTiles count)[j.val]'(by simp) =
      waitsOn count (buildPrefix count) (buildSuffix count) j := by
  simp only [waitingTiles, Id.run_bind, Id.run_pure,
    List.forIn_pure_yield_eq_foldl]
  exact fold_set_get count.size count.size le_rfl
    (Vector.replicate count.size false)
    (waitsOn count (buildPrefix count) (buildSuffix count)) j

@[grind =]
private lemma reachable_append_mem_iff (states : Winning.Decidable.StateSet)
    (xs : List Nat) (ys : List Nat) (t : Winning.Decidable.State) :
  t ∈ Winning.Decidable.reachable states (xs ++ ys) ↔
      ∃ q, q ∈ Winning.Decidable.reachable states xs ∧
        t ∈ Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert q) ys := by
  rw [Winning.Decidable.reachable_append, Winning.Decidable.mem_reachable]
  grind

@[grind =]
private lemma reachable_from_set_iff (states : Winning.Decidable.StateSet)
    (xs : List Nat) (t : Winning.Decidable.State) :
    t ∈ Winning.Decidable.reachable states xs ↔
      ∃ q, q ∈ states ∧
        t ∈ Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert q) xs := by
  rw [Winning.Decidable.mem_reachable]
  grind

@[grind =]
private lemma reachable_singleton_cons_iff (q : Winning.Decidable.State) (x : Nat)
    (xs : List Nat) (t : Winning.Decidable.State) :
  t ∈ Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert q) (x :: xs) ↔
      ∃ u, u ∈ Winning.Decidable.step x q ∧
        t ∈ Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert u) xs := by
  rw [Winning.Decidable.reachable, reachable_from_set_iff]
  grind

@[grind =]
private lemma waitsOn_reachable (count : Array Nat) (j : Fin count.size) :
    waitsOn count (buildPrefix count) (buildSuffix count) j = true ↔
      Winning.Decidable.State.final ∈
        Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert
          Winning.Decidable.State.init)
          ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).take j.val ++
            [count[j.val]'j.isLt + 1] ++
            (List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).drop (j.val + 1)) := by
  rw [buildPrefix_eq_prefixFold, buildSuffix_eq_suffixFold]
  have hp := prefixFold_get count.size (fun i : Fin count.size => count[i.val]'i.isLt)
    count.size le_rfl j.val (by omega)
  have hs := suffixFold_get count.size (fun i : Fin count.size => count[i.val]'i.isLt)
    count.size le_rfl (j.val + 1) (by omega) (by omega)
  unfold waitsOn
  simp only [Bool.not_eq_true_eq_eq_false]
  rw [nonempty_iff_exists]
  constructor
  · rintro ⟨t, ht⟩
    rcases Std.ExtHashSet.mem_inter_iff.mp ht with ⟨htstep, htsuff⟩
    rw [Winning.Decidable.mem_stepSet] at htstep
    obtain ⟨q, hq, htq⟩ := htstep
    have hq' : q ∈ Winning.Decidable.reachable
        ((∅ : Winning.Decidable.StateSet).insert Winning.Decidable.State.init)
        ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).take j.val) := by
      simpa [prefixSem, hp] using hq
    have htsuff' : Winning.Decidable.State.final ∈
        Winning.Decidable.reachable ((∅ : Winning.Decidable.StateSet).insert t)
          ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).drop (j.val + 1)) := by
      apply (suffixSemList_reachable _ t).mp
      simpa [suffixSem, hs] using htsuff
    grind
  · rintro h
    have hsplit := (reachable_append_mem_iff
      ((∅ : Winning.Decidable.StateSet).insert Winning.Decidable.State.init)
      ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).take j.val)
      ([count[j.val]'j.isLt + 1] ++
        ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).drop (j.val + 1)))
      Winning.Decidable.State.final).mp (by simpa [List.append_assoc] using h)
    obtain ⟨q, hq, hrest⟩ := hsplit
    obtain ⟨t, htq, htsuff⟩ := (reachable_singleton_cons_iff q (count[j.val]'j.isLt + 1)
      ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).drop (j.val + 1))
      Winning.Decidable.State.final).mp hrest
    apply Exists.intro t
    apply Std.ExtHashSet.mem_inter_iff.mpr
    constructor
    · rw [Winning.Decidable.mem_stepSet]
      exact ⟨q, by simpa [hp, prefixSem] using hq, htq⟩
    · simpa [suffixSem, hs] using
        ((suffixSemList_reachable
          ((List.ofFn (fun i : Fin count.size => count[i.val]'i.isLt)).drop (j.val + 1)) t).mpr
          htsuff)

theorem waitingTiles_spec (c : Hand n) (hc : Hand.size c = 3 * n + 4) (i : Fin (3 * n)) :
    (waitingTiles (Array.ofFn c))[i.val]'(by simp) = true ↔
      IsWaitingTile c i := by
  let j : Fin (Array.ofFn c).size := ⟨i.val, by simp⟩
  rw [show (waitingTiles (Array.ofFn c))[i.val]'(by simp) =
      waitsOn (Array.ofFn c) (buildPrefix (Array.ofFn c)) (buildSuffix (Array.ofFn c)) j by
    simpa [j] using waitingTiles_get (Array.ofFn c) j]
  rw [waitsOn_reachable]
  change _ ↔ Winning (c + single i)
  let xs := List.ofFn c
  have hlist : List.ofFn (c + single i) =
      xs.take i.val ++ [xs.get ⟨i.val, by simp [xs]⟩ + 1] ++ xs.drop (i.val + 1) := by
    rw [list_ofFn_add_single, updateAt_eq_take]
  have hsize : Hand.size (c + single i) = 3 * n + 5 := by
    rw [map_add, size_single, hc]
  have hcanon :
      (List.take j.val (List.ofFn (fun k : Fin (Array.ofFn c).size =>
        (Array.ofFn c)[k.val]'k.isLt)) ++
        [(Array.ofFn c)[j.val]'j.isLt + 1] ++
        List.drop (j.val + 1) (List.ofFn (fun k : Fin (Array.ofFn c).size =>
          (Array.ofFn c)[k.val]'k.isLt))) = List.ofFn (c + single i) := by
    simpa [j, xs] using hlist.symm
  constructor
  · intro h
    apply Winning.Decidable.dpWinning_to_winning
    use hsize; grind
  · intro h
    obtain ⟨_hsize', choices, hchoices⟩ :=
      Winning.Decidable.winning_to_dpWinning (c := c + single i) h
    grind

end IsFullWait.Decidable

namespace IsWait.Decidable

theorem decide_spec (c : Hand n) :
    IsWait.decide c = true ↔ IsWait c := by
  simp only [IsWait.decide, Bool.and_eq_true, Array.any_eq_true, IsWait]
  constructor
  · rintro ⟨hsize, ⟨j, hj, h⟩⟩
    have hcsize : Hand.size c = 3 * n + 4 := by simpa using hsize
    let i : Fin (3 * n) := ⟨j, by simpa using hj⟩
    exact ⟨i, IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp h⟩
  · rintro ⟨i, hi⟩
    have hcsize := IsWait.size ⟨i, hi⟩
    refine ⟨by simpa using hcsize, i.val, ?_, ?_⟩
    · simp
    · exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mpr hi

instance (c : Hand n) : Decidable (IsWait c) :=
  decidable_of_iff (IsWait.decide c = true) (decide_spec c)

end IsWait.Decidable

namespace IsLiveWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveWait.decide c = true ↔ IsLiveWait c := by
  simp only [IsLiveWait.decide, Bool.and_eq_true, Array.all_eq_true,
    Array.any_eq_true]
  constructor
  · rintro ⟨⟨hsize, hvalid⟩, ⟨j, hj, hRaw⟩⟩
    have hcsize : Hand.size c = 3 * n + 4 := by simpa using hsize
    simp only [id_eq, Array.getElem_zipWith hj, Array.getElem_map] at hRaw
    rcases Bool.and_eq_true_iff.mp hRaw with ⟨hwaitRaw, hcountRaw⟩
    let i : Fin (3 * n) :=
      ⟨j, by simpa [Array.size_zipWith, Array.size_map] using hj⟩
    have hwait : (IsFullWait.Decidable.waitingTiles (Array.ofFn c))[i.val]'(by simp) = true := by
      simpa [i] using hwaitRaw
    have hcount : c i ≤ 3 := by
      simpa [i, Array.getElem_map] using hcountRaw
    have hvc : Valid c := by
      intro k
      simpa using hvalid k.val (by simp)
    exact ⟨i, isLiveWaitingTile_iff.mpr
      ⟨IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp hwait, hvc, hcount⟩⟩
  · rintro ⟨i, hi⟩
    rcases isLiveWaitingTile_iff.mp hi with ⟨hw, hvalid, hcount⟩
    have hcsize := IsLiveWait.size ⟨i, hi⟩
    refine ⟨⟨by simpa using hcsize, ?_⟩, ?_⟩
    · intro j hj
      simpa using hvalid ⟨j, by simpa using hj⟩
    · refine ⟨i.val, ?_, ?_⟩
      · simp [Array.size_zipWith]
      · have hwait := IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mpr hw
        simp_all

instance (c : Hand n) : Decidable (IsLiveWait c) :=
  decidable_of_iff (IsLiveWait.decide c = true) (decide_spec c)

end IsLiveWait.Decidable

namespace IsFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsFullWait.decide c = true ↔ IsFullWait c := by
  cases n with
  | zero =>
    have hc : c = 0 := by ext i; exact Fin.elim0 i
    subst c
    have hwt : IsFullWait.Decidable.waitingTiles (Array.ofFn (0 : Hand 0)) = #[] := by
      rfl
    simp_all [IsFullWait.decide, IsFullWait]
  | succ n =>
    simp only [IsFullWait.decide, Bool.and_eq_true, Bool.or_eq_true,
      Array.all_eq_true, IsFullWait]
    constructor
    · rintro ⟨hsize, hwait⟩ i
      have hcsize : Hand.size c = 3 * (n + 1) + 4 := by
        simpa using hsize.resolve_left (by simp)
      exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp (hwait i.val (by simp))
    · intro h
      have hcsize := IsFullWait.size (Nat.succ_pos n) h
      refine ⟨Or.inr (by simpa using hcsize), ?_⟩
      intro i hi
      let j : Fin (3 * (n + 1)) := ⟨i, by simpa using hi⟩
      exact IsFullWait.Decidable.waitingTiles_spec c hcsize j |>.mpr (h j)

instance (c : Hand n) : Decidable (IsFullWait c) :=
  decidable_of_iff (IsFullWait.decide c = true) (decide_spec c)

end IsFullWait.Decidable

namespace IsLiveFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveFullWait.decide c = true ↔ IsLiveFullWait c := by
  cases n with
  | zero =>
    have hc : c = 0 := by ext i; exact Fin.elim0 i
    subst c
    have hwt : IsFullWait.Decidable.waitingTiles (Array.ofFn (0 : Hand 0)) = #[] := by
      rfl
    simp only [IsLiveFullWait.decide]
    rw [hwt]
    simp [IsLiveFullWait]
  | succ n =>
    simp only [IsLiveFullWait.decide, Bool.and_eq_true, Array.all_eq_true,
      Bool.or_eq_true, IsLiveFullWait]
    constructor
    · rintro ⟨⟨hsize, hwait⟩, hcount⟩
      have hcsize : Hand.size c = 3 * (n + 1) + 4 := by
        simpa using hsize.resolve_left (by simp)
      apply isLiveFullWait_iff_le_three.mpr
      refine ⟨?_, ?_⟩
      · intro i
        exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp (hwait i.val (by simp))
      · intro i
        simpa using hcount i.val (by simp)
    · intro h
      rcases isLiveFullWait_iff_le_three.mp h with ⟨hfull, hcount⟩
      have hcsize := IsLiveFullWait.size (Nat.succ_pos n) h
      refine ⟨⟨Or.inr (by simpa using hcsize), ?_⟩, ?_⟩
      · intro i hi
        let j : Fin (3 * (n + 1)) := ⟨i, by simpa using hi⟩
        exact IsFullWait.Decidable.waitingTiles_spec c hcsize j |>.mpr (hfull j)
      · intro i hi
        simpa using hcount ⟨i, by simpa using hi⟩

instance (c : Hand n) : Decidable (IsLiveFullWait c) :=
  decidable_of_iff (IsLiveFullWait.decide c = true) (decide_spec c)

end IsLiveFullWait.Decidable

end Mahjong.Hand
