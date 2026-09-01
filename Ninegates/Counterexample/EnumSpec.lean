import Ninegates.Counterexample.Enum
import Ninegates.Counterexample.Reduction
import Ninegates.Wait.Decidable
import Mathlib.Data.List.GetD

/-!
# Specifications for the finite counterexample enumeration

The executable enumeration lives in `Counterexample.Enum`.  This file records
the mathematical contract that connects its output to minimal live
full-wait counterexamples.
-/

namespace Mahjong.Hand.Counterexample

lemma ofFn_getD {xs : List Nat} :
    List.ofFn (fun i : Fin xs.length => xs.getD i.val 0) = xs := by
  simpa only [List.getD_eq_get, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := xs))

lemma sum_getD (xs : List Nat) :
    (∑ i : Fin xs.length, xs.getD i.val 0) = xs.sum := by
  rw [← List.sum_ofFn, ofFn_getD]

lemma sum_fin_boundaries {n : Nat} (hn : 2 ≤ n) (f : Fin (3 * n) → Nat) :
    (∑ i : Fin (3 * n), f i) =
      f ⟨0, by omega⟩ +
        (∑ i : Fin (3 * n - 2), f ⟨i.val + 1, by omega⟩) +
      f ⟨3 * n - 1, by omega⟩ := by
  have hsumFin (g : Fin ((3 * n - 2) + 2) → Nat) :
      (∑ i, g i) =
        g 0 + (∑ i : Fin (3 * n - 2), g i.castSucc.succ) +
          g (Fin.last (3 * n - 2 + 1)) := by
    grind [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  let e : Fin ((3 * n - 2) + 2) ≃ Fin (3 * n) := finCongr (by omega)
  have he0 : e 0 = ⟨0, by omega⟩ := by simp [Fin.ext_iff, e]
  have heMid (i : Fin (3 * n - 2)) :
      e i.castSucc.succ = ⟨i.val + 1, by omega⟩ := by
    simp [Fin.ext_iff, e]
  have heLast :
      e (Fin.last (3 * n - 2 + 1)) = ⟨3 * n - 1, by omega⟩ := by
    simp [Fin.ext_iff, e]
    omega
  grind [Equiv.sum_comp e f]

def BoundedBy : List Nat → List Nat → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | bound :: bounds, value :: values =>
      value ≤ bound ∧ BoundedBy bounds values

lemma BoundedBy.length_eq {bounds values : List Nat} (h : BoundedBy bounds values) :
    values.length = bounds.length := by
  induction bounds generalizing values with
  | nil => cases values <;> simp [BoundedBy] at h ⊢
  | cons bound bounds ih =>
      cases values with
      | nil => simp [BoundedBy] at h
      | cons value values =>
          simp only [List.length_cons]
          rw [ih h.2]

lemma BoundedBy.getD_le {bounds values : List Nat} (h : BoundedBy bounds values)
    (i : Nat) : values.getD i 0 ≤ bounds.getD i 0 := by
  induction bounds generalizing values i with
  | nil =>
      cases values with
      | nil => simp
      | cons value values => simp only [BoundedBy] at h
  | cons bound bounds ih =>
      cases values with
      | nil => simp only [BoundedBy] at h
      | cons value values =>
          cases i with
          | zero => simp only [BoundedBy, List.getD_cons_zero] at h ⊢; omega
          | succ i =>
              simp only [List.getD_cons_succ]
              exact ih h.2 i

lemma boundedBy_replicate_iff {bound n : Nat} {values : List Nat} :
    BoundedBy (List.replicate n bound) values ↔
      values.length = n ∧ ∀ value ∈ values, value ≤ bound := by
  induction n generalizing values with
  | zero =>
      cases values <;> simp [BoundedBy]
  | succ n ih =>
      cases values with
      | nil => simp [List.replicate_succ, BoundedBy]
      | cons value values =>
          simp only [List.replicate_succ, BoundedBy, ih, List.length_cons,
            List.mem_cons]
          grind

lemma boundedBy_replicate_append_singleton_iff
    {bound last : Nat} {values : List Nat} {lastValue : Nat} :
    BoundedBy (List.replicate values.length bound ++ [last])
        (values ++ [lastValue]) ↔
      (∀ value ∈ values, value ≤ bound) ∧ lastValue ≤ last := by
  induction values with
  | nil => simp [BoundedBy]
  | cons value values ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        BoundedBy, List.mem_cons, ih]
      grind

lemma list_split_boundaries {xs : List Nat} {m : Nat}
    (h : xs.length = m + 2) :
    ∃ left interior right,
      xs = left :: interior ++ [right] ∧ interior.length = m := by
  induction m generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at h
      | cons left xs =>
          cases xs with
          | nil => simp at h
          | cons right xs =>
              cases xs with
              | nil => exact ⟨left, [], right, by simp⟩
              | cons x xs => simp at h
  | succ m ih =>
      cases xs with
      | nil => simp at h
      | cons left xs =>
          have hxs : xs.length = m + 2 := by
            simp only [List.length_cons] at h
            omega
          obtain ⟨first, interior, right, rfl, hlen⟩ := ih hxs
          refine ⟨left, first :: interior, right, ?_, ?_⟩
          · simp
          · simp [hlen]

lemma mem_boundedLists_iff {bounds values : List Nat} {total : Nat} :
    values ∈ boundedLists bounds total ↔
      BoundedBy bounds values ∧ values.sum = total := by
  induction bounds generalizing total values with
  | nil =>
      cases total <;> cases values <;> simp [boundedLists, BoundedBy]
  | cons bound bounds ih =>
      cases values with
      | nil => simp [boundedLists, BoundedBy]
      | cons value values =>
          simp only [boundedLists, List.bind_eq_flatMap, List.mem_flatMap,
            List.mem_range, List.mem_pure, BoundedBy, List.sum_cons, ih]
          grind

def positiveEntries : List Nat → List Nat
  | [] => []
  | 0 :: xs => positiveEntries xs
  | x :: xs => x :: positiveEntries xs

def zeroGaps : List Nat → List Nat
  | [] => [0]
  | 0 :: xs =>
      match zeroGaps xs with
      | gap :: gaps => (gap + 1) :: gaps
      | [] => []
  | _ :: xs => 0 :: zeroGaps xs

def NoTripleZeros : List Nat → Prop
  | a :: b :: c :: rest =>
      ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧ NoTripleZeros (b :: c :: rest)
  | _ => True

lemma mem_positiveEntries_iff {x : Nat} {xs : List Nat} :
    x ∈ positiveEntries xs ↔ x ∈ xs ∧ x ≠ 0 := by
  induction xs with
  | nil => simp [positiveEntries]
  | cons y ys ih =>
      cases y with
      | zero =>
          simp only [positiveEntries, List.mem_cons, ih]
          grind
      | succ y =>
          simp only [positiveEntries, List.mem_cons, ih]
          grind

lemma zeroGaps_ne_nil (xs : List Nat) : zeroGaps xs ≠ [] := by
  induction xs with
  | nil => simp [zeroGaps]
  | cons x xs ih =>
      cases x with
      | zero =>
          simp only [zeroGaps]
          cases h : zeroGaps xs with
          | nil => exact (ih h).elim
          | cons gap gaps => simp
      | succ x => simp [zeroGaps]

lemma placePositives_succ_gap (gap : Nat) (gaps values : List Nat) :
    placePositives ((gap + 1) :: gaps) values =
      0 :: placePositives (gap :: gaps) values := by
  cases values with
  | nil => simp [placePositives, List.bind_eq_flatMap, List.replicate_succ]
  | cons x values => simp [placePositives, List.replicate_succ]

lemma placePositives_zeroGaps (xs : List Nat) :
    placePositives (zeroGaps xs) (positiveEntries xs) = xs := by
  induction xs with
  | nil => simp [zeroGaps, positiveEntries, placePositives, List.bind_eq_flatMap]
  | cons x xs ih =>
      cases x with
      | zero =>
          simp only [zeroGaps, positiveEntries]
          cases h : zeroGaps xs with
          | nil => exact (zeroGaps_ne_nil xs h).elim
          | cons gap gaps =>
              rw [placePositives_succ_gap]
              rw [h] at ih
              exact congrArg (List.cons 0) ih
      | succ x =>
          simp only [zeroGaps, positiveEntries, placePositives, List.replicate_zero,
            List.nil_append]
          exact congrArg (List.cons (x + 1)) ih

lemma length_zeroGaps (xs : List Nat) :
    (zeroGaps xs).length = (positiveEntries xs).length + 1 := by
  induction xs with
  | nil => simp [zeroGaps, positiveEntries]
  | cons x xs ih =>
      cases x with
      | zero =>
          simp only [zeroGaps, positiveEntries]
          cases h : zeroGaps xs with
          | nil => exact (zeroGaps_ne_nil xs h).elim
          | cons gap gaps =>
              rw [h] at ih
              simp only [List.length_cons] at ih ⊢
              exact ih
      | succ x =>
          simp only [zeroGaps, positiveEntries, List.length_cons]
          omega

lemma zeroGaps_replicate_zero (gap : Nat) :
    zeroGaps (List.replicate gap 0) = [gap] := by
  induction gap with
  | zero => simp [zeroGaps]
  | succ gap ih => simp only [List.replicate_succ, zeroGaps, ih]

lemma positiveEntries_replicate_zero (gap : Nat) :
    positiveEntries (List.replicate gap 0) = [] := by
  induction gap with
  | zero => simp [positiveEntries]
  | succ gap ih => simp [List.replicate_succ, positiveEntries, ih]

lemma zeroGaps_replicate_zero_cons (gap x : Nat) (xs : List Nat) (_hx : x ≠ 0) :
    zeroGaps (List.replicate gap 0 ++ x :: xs) = gap :: zeroGaps xs := by
  induction gap with
  | zero => simp [zeroGaps]
  | succ gap ih =>
      simp only [List.replicate_succ, List.cons_append, zeroGaps]
      rw [ih]

lemma positiveEntries_replicate_zero_cons
    (gap x : Nat) (xs : List Nat) (_hx : x ≠ 0) :
    positiveEntries (List.replicate gap 0 ++ x :: xs) =
      x :: positiveEntries xs := by
  induction gap with
  | zero => simp [positiveEntries]
  | succ gap ih => simp [List.replicate_succ, positiveEntries, ih]

lemma zeroGaps_placePositives {gaps values : List Nat}
    (hlen : gaps.length = values.length + 1)
    (hvalues : ∀ value ∈ values, value ≠ 0) :
    zeroGaps (placePositives gaps values) = gaps := by
  induction values generalizing gaps with
  | nil =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          cases gaps with
          | nil =>
              simp [placePositives, List.bind_eq_flatMap, zeroGaps_replicate_zero]
          | cons gap' gaps => simp at hlen
  | cons value values ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have hvalue : value ≠ 0 := hvalues value (by simp)
          have hlen' : gaps.length = values.length + 1 := by
            simp only [List.length_cons] at hlen
            omega
          simp only [placePositives]
          rw [zeroGaps_replicate_zero_cons _ _ _ hvalue]
          rw [ih hlen' (by
            intro x hx
            exact hvalues x (by simp [hx]))]

lemma positiveEntries_placePositives {gaps values : List Nat}
    (hlen : gaps.length = values.length + 1)
    (hvalues : ∀ value ∈ values, value ≠ 0) :
    positiveEntries (placePositives gaps values) = values := by
  induction values generalizing gaps with
  | nil =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          cases gaps with
          | nil =>
              simp [placePositives, List.bind_eq_flatMap,
                positiveEntries_replicate_zero]
          | cons gap' gaps => simp at hlen
  | cons value values ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have hvalue : value ≠ 0 := hvalues value (by simp)
          have hlen' : gaps.length = values.length + 1 := by
            simp only [List.length_cons] at hlen
            omega
          simp only [placePositives]
          rw [positiveEntries_replicate_zero_cons _ _ _ hvalue]
          rw [ih hlen' (by
            intro x hx
            exact hvalues x (by simp [hx]))]

lemma noTripleZeros_tail {x : Nat} {xs : List Nat}
    (h : NoTripleZeros (x :: xs)) : NoTripleZeros xs := by
  cases xs with
  | nil => simp [NoTripleZeros]
  | cons y ys =>
      cases ys with
      | nil => simp [NoTripleZeros]
      | cons z zs => exact h.2

lemma noTripleZeros_iff_getD (xs : List Nat) :
    NoTripleZeros xs ↔
      ∀ i, i + 2 < xs.length →
        ¬(xs.getD i 0 = 0 ∧ xs.getD (i + 1) 0 = 0 ∧
          xs.getD (i + 2) 0 = 0) := by
  induction xs with
  | nil => simp [NoTripleZeros]
  | cons x xs ih =>
      constructor
      · intro h i hi
        cases i with
        | zero =>
            cases xs with
            | nil => simp at hi
            | cons y ys =>
                cases ys with
                | nil => simp at hi
                | cons z zs =>
                    have hz :
                        ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
                          NoTripleZeros (y :: z :: zs) := by
                      simpa [NoTripleZeros] using h
                    exact hz.1
        | succ i =>
            have hrec := ih.mp (noTripleZeros_tail h) i (by
              simp at hi ⊢
              omega)
            simpa [Nat.add_assoc] using hrec
      · intro h
        cases xs with
        | nil => trivial
        | cons y ys =>
            cases ys with
            | nil => trivial
            | cons z zs =>
                constructor
                · have hzero := h 0 (by simp)
                  simpa using hzero
                · apply ih.mpr
                  intro i hi
                  have hsucc := h (i + 1) (by
                    simp at hi ⊢
                    omega)
                  simpa [Nat.add_assoc] using hsucc

lemma zeroGaps_tail_le {x k : Nat} {xs : List Nat}
    (h : ∀ gap ∈ zeroGaps (x :: xs), gap ≤ k) :
    ∀ gap ∈ zeroGaps xs, gap ≤ k := by
  cases x with
  | zero =>
      obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil (zeroGaps_ne_nil xs)
      have ha_bound : a + 1 ≤ k := by
        exact h (a + 1) (by simp [zeroGaps, ha])
      intro q hq
      rw [ha] at hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · omega
      · exact h q (by simp [zeroGaps, ha, hq])
  | succ x =>
      intro gap hgap
      exact h gap (by simp [zeroGaps, hgap])

lemma noTripleZeros_of_zeroGaps_le_two (xs : List Nat)
    (h : ∀ gap ∈ zeroGaps xs, gap ≤ 2) : NoTripleZeros xs := by
  induction xs with
  | nil => simp [NoTripleZeros]
  | cons x xs ih =>
      cases xs with
      | nil => simp [NoTripleZeros]
      | cons y ys =>
          cases ys with
          | nil => simp [NoTripleZeros]
          | cons z zs =>
              simp only [NoTripleZeros]
              constructor
              · rintro ⟨rfl, rfl, rfl⟩
                obtain ⟨a, as, ha⟩ :=
                  List.exists_cons_of_ne_nil (zeroGaps_ne_nil zs)
                have ha_bound : a + 3 ≤ 2 := by
                  exact h (a + 3) (by simp [zeroGaps, ha])
                omega
              · exact ih (zeroGaps_tail_le h)

lemma zeroGaps_le_two_of_noTripleZeros (xs : List Nat)
    (h : NoTripleZeros xs) : ∀ gap ∈ zeroGaps xs, gap ≤ 2 := by
  induction xs with
  | nil => simp [zeroGaps]
  | cons x xs ih =>
      have htail := ih (noTripleZeros_tail h)
      cases x with
      | succ x =>
          intro gap hgap
          simp only [zeroGaps, List.mem_cons] at hgap
          rcases hgap with rfl | hgap
          · omega
          · exact htail gap hgap
      | zero =>
          cases xs with
          | nil => simp [zeroGaps]
          | cons y ys =>
              cases y with
              | succ y =>
                  intro gap hgap
                  simp only [zeroGaps, List.mem_cons] at hgap
                  rcases hgap with rfl | hgap
                  · omega
                  · exact htail gap (by simp [zeroGaps, hgap])
              | zero =>
                  cases ys with
                  | nil => simp [zeroGaps]
                  | cons z zs =>
                      cases z with
                      | zero => exact False.elim (h.1 ⟨rfl, rfl, rfl⟩)
                      | succ z =>
                          intro gap hgap
                          simp only [zeroGaps, List.mem_cons] at hgap
                          rcases hgap with rfl | hgap
                          · omega
                          · exact htail gap (by simp [zeroGaps, hgap])

lemma length_placePositives_empty (gaps : List Nat) :
    (placePositives gaps []).length = gaps.sum := by
  induction gaps with
  | nil => simp [placePositives]
  | cons gap gaps ih =>
      simp [placePositives, List.bind_eq_flatMap]

lemma sum_flatMap_replicate_zero (gaps : List Nat) :
    (gaps.flatMap (fun gap => List.replicate gap 0)).sum = 0 := by
  induction gaps with
  | nil => simp
  | cons gap gaps ih => simp [ih]

lemma sum_placePositives_empty (gaps : List Nat) :
    (placePositives gaps []).sum = 0 := by
  simpa [placePositives, List.bind_eq_flatMap] using sum_flatMap_replicate_zero gaps

lemma length_placePositives_of_nonempty {gaps : List Nat} {x : Nat}
    {values : List Nat} (h : (x :: values).length ≤ gaps.length) :
    (placePositives gaps (x :: values)).length = gaps.sum + (x :: values).length := by
  induction gaps generalizing x values with
  | nil => simp at h
  | cons gap gaps ih =>
      simp only [placePositives, List.length_append, List.length_replicate,
        List.length_cons, List.sum_cons]
      by_cases hvalues : values = []
      · simp [hvalues, placePositives, List.bind_eq_flatMap]
        omega
      · cases values with
        | nil => simp_all
        | cons y values =>
            have h' : (y :: values).length ≤ gaps.length := by
              change values.length + 2 ≤ gaps.length + 1 at h
              change values.length + 1 ≤ gaps.length
              omega
            simp only [List.length_cons] at ⊢
            rw [ih (x := y) (values := values) h']
            simp only [List.length_cons]
            omega

lemma length_placePositives {gaps values : List Nat}
    (h : values.length ≤ gaps.length) :
    (placePositives gaps values).length = gaps.sum + values.length := by
  cases values with
  | nil => simpa using length_placePositives_empty gaps
  | cons x values => exact length_placePositives_of_nonempty h

lemma sum_placePositives_of_nonempty {gaps : List Nat} {x : Nat}
    {values : List Nat} (h : (x :: values).length ≤ gaps.length) :
    (placePositives gaps (x :: values)).sum = x + values.sum := by
  induction gaps generalizing x values with
  | nil => simp at h
  | cons gap gaps ih =>
      simp only [placePositives, List.sum_append, List.sum_replicate,
        List.sum_cons]
      by_cases hvalues : values = []
      · simp only [placePositives, List.bind_eq_flatMap, hvalues, nsmul_zero,
          zero_add, Nat.add_left_cancel_iff]
        exact sum_flatMap_replicate_zero gaps
      · cases values with
        | nil => simp_all
        | cons y values =>
            have h' : (y :: values).length ≤ gaps.length := by
              change values.length + 2 ≤ gaps.length + 1 at h
              change values.length + 1 ≤ gaps.length
              omega
            rw [ih (x := y) (values := values) h']
            simp only [List.sum_cons]
            simp

lemma sum_placePositives {gaps values : List Nat}
    (h : values.length ≤ gaps.length) :
    (placePositives gaps values).sum = values.sum := by
  cases values with
  | nil => exact sum_placePositives_empty gaps
  | cons x values =>
      simpa only [List.sum_cons] using
        sum_placePositives_of_nonempty h

lemma sum_positiveEntries (xs : List Nat) :
    (positiveEntries xs).sum = xs.sum := by
  have h := sum_placePositives
    (gaps := zeroGaps xs) (values := positiveEntries xs) (by
      rw [length_zeroGaps]
      omega)
  rw [placePositives_zeroGaps] at h
  exact h.symm

lemma sum_zeroGaps_add_length_positiveEntries (xs : List Nat) :
    (zeroGaps xs).sum + (positiveEntries xs).length = xs.length := by
  have h := length_placePositives
    (gaps := zeroGaps xs) (values := positiveEntries xs) (by
      rw [length_zeroGaps]
      omega)
  rw [placePositives_zeroGaps] at h
  exact h.symm

lemma sum_map_pred_add_length {values : List Nat}
    (h : ∀ value ∈ values, 1 ≤ value) :
    (values.map (fun value => value - 1)).sum + values.length = values.sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hvalue := h value (by simp)
      have htail : ∀ x ∈ values, 1 ≤ x := by
        intro x hx
        exact h x (by simp [hx])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ih' := ih htail
      omega

lemma map_succ_map_pred {values : List Nat}
    (h : ∀ value ∈ values, 1 ≤ value) :
    (values.map (fun value => value - 1)).map (fun value => value + 1) = values := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hvalue := h value (by simp)
      have htail : ∀ x ∈ values, 1 ≤ x := by
        intro x hx
        exact h x (by simp [hx])
      simp only [List.map_cons]
      rw [ih htail]
      congr 1
      omega

lemma sum_map_succ (values : List Nat) :
    (values.map (fun value => value + 1)).sum = values.sum + values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

lemma length_largeCandidateExcesses {n : Nat} {excess : List Nat} (hn : 3 ≤ n)
    (h : excess ∈ largeCandidateExcesses n) : excess.length = 3 * n := by
  simp only [largeCandidateExcesses, List.cons_append, List.pure_def,
    List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ⟨left, hleft, right, hright, count, hcount, hif,
    positiveExcess, hpositive, gaps, hgaps, rfl⟩
  have hpositive' := (mem_boundedLists_iff.mp hpositive).1.length_eq
  have hgaps' := (mem_boundedLists_iff.mp hgaps).1.length_eq
  have hgaps_sum := (mem_boundedLists_iff.mp hgaps).2
  simp only [List.length_replicate] at hpositive' hgaps'
  have hplace := length_placePositives
    (gaps := gaps) (values := positiveExcess.map (fun excess => excess + 1)) (by
      simp only [List.length_map]
      omega)
  simp only [List.length_cons, List.length_append, List.length_map,
    List.length_nil, Nat.zero_add] at hplace ⊢
  rw [hplace]
  rw [hgaps_sum, hpositive']
  omega

lemma sum_largeCandidateExcesses {n : Nat} {excess : List Nat}
    (h : excess ∈ largeCandidateExcesses n) : excess.sum = 6 := by
  simp only [largeCandidateExcesses, List.cons_append, List.pure_def,
    List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ⟨left, hleft, right, hright, count, hcount, hif,
    positiveExcess, hpositive, gaps, hgaps, rfl⟩
  have hpositive' := (mem_boundedLists_iff.mp hpositive).2
  have hpositiveLen := (mem_boundedLists_iff.mp hpositive).1.length_eq
  have hgaps' := (mem_boundedLists_iff.mp hgaps).1.length_eq
  simp only [List.length_replicate] at hpositiveLen hgaps'
  have hplace := sum_placePositives
    (gaps := gaps) (values := positiveExcess.map (fun excess => excess + 1)) (by
      simp only [List.length_map]
      omega)
  simp only [List.sum_cons, List.sum_append] at ⊢
  rw [hplace, sum_map_succ, hpositive', hpositiveLen]
  simp only [List.sum_nil]
  omega

def IsCandidateExcess (n : Nat) (excess : List Nat) : Prop :=
  ∃ left interior right,
    excess = left :: interior ++ [right] ∧
    interior.length = 3 * n - 2 ∧
    left ≤ 3 ∧ right ≤ 3 ∧
    (∀ value ∈ interior, value ≤ 2) ∧
    excess.sum = 6 ∧
    (n = 2 ∨ NoTripleZeros interior)

lemma mem_orderTwoCandidateExcesses_iff {excess : List Nat} :
    excess ∈ boundedLists (3 :: List.replicate 4 2 ++ [3]) 6 ↔
      IsCandidateExcess 2 excess := by
  constructor
  · intro h
    rcases mem_boundedLists_iff.mp h with ⟨hbound, hsum⟩
    have hlength := hbound.length_eq
    simp only [List.length_cons, List.length_append, List.length_replicate] at hlength
    obtain ⟨left, interior, right, rfl, hlen⟩ :=
      list_split_boundaries (m := 4) (by omega)
    have htail := hbound.2
    rw [← hlen] at htail
    have htail := boundedBy_replicate_append_singleton_iff.mp htail
    exact ⟨left, interior, right, rfl, by omega, hbound.1, htail.2,
      htail.1, hsum, Or.inl rfl⟩
  · rintro ⟨left, interior, right, rfl, hlen, hleft, hright,
      hvalues, hsum, _⟩
    apply mem_boundedLists_iff.mpr
    refine ⟨?_, hsum⟩
    refine ⟨hleft, ?_⟩
    have hlen' : interior.length = 4 := by omega
    rw [← hlen']
    exact boundedBy_replicate_append_singleton_iff.mpr ⟨hvalues, hright⟩

lemma largeCandidateExcesses_sound {n : Nat} {excess : List Nat} (hn : 3 ≤ n)
    (h : excess ∈ largeCandidateExcesses n) : IsCandidateExcess n excess := by
  have hsum := sum_largeCandidateExcesses h
  simp only [largeCandidateExcesses, List.cons_append, List.pure_def,
    List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ⟨left, hleft, right, hright, count, hcount, hif,
    positiveExcess, hpositive, gaps, hgaps, rfl⟩
  have hpositiveBound := boundedBy_replicate_iff.mp
    (mem_boundedLists_iff.mp hpositive).1
  have hpositiveSum := (mem_boundedLists_iff.mp hpositive).2
  have hgapBound := boundedBy_replicate_iff.mp
    (mem_boundedLists_iff.mp hgaps).1
  have hgapSum := (mem_boundedLists_iff.mp hgaps).2
  let positives := positiveExcess.map (fun value => value + 1)
  let interior := placePositives gaps positives
  have hpositive : ∀ value ∈ positives, value ≠ 0 := by
    intro value hvalue
    simp only [positives, List.mem_map] at hvalue
    grind
  have hlen : interior.length = 3 * n - 2 := by
    have hplace := length_placePositives
      (gaps := gaps) (values := positives) (by
        simp only [positives, List.length_map]
        omega)
    rw [hplace, hgapSum]
    simp only [positives, List.length_map]
    omega
  have hvalues : ∀ value ∈ interior, value ≤ 2 := by
    intro value hvalue
    by_cases hzero : value = 0
    · omega
    · have hmem : value ∈ positiveEntries interior :=
        mem_positiveEntries_iff.mpr ⟨hvalue, hzero⟩
      have hentries := positiveEntries_placePositives
        (gaps := gaps) (values := positives) (by
          simp only [positives, List.length_map]
          omega) hpositive
      rw [hentries] at hmem
      simp only [positives, List.mem_map] at hmem
      rcases hmem with ⟨source, hsource, rfl⟩
      have := hpositiveBound.2 source hsource
      omega
  have htriple : NoTripleZeros interior := by
    apply noTripleZeros_of_zeroGaps_le_two
    have hzgaps := zeroGaps_placePositives
      (gaps := gaps) (values := positives) (by
        simp only [positives, List.length_map]
        omega) hpositive
    intro gap hgap
    rw [hzgaps] at hgap
    exact hgapBound.2 gap hgap
  refine ⟨left, interior, right, ?_, hlen, by omega, by omega,
    hvalues, ?_, Or.inr htriple⟩
  · rfl
  · exact hsum

lemma largeCandidateExcesses_complete {n : Nat} {excess : List Nat} (hn : 3 ≤ n)
    (h : IsCandidateExcess n excess) : excess ∈ largeCandidateExcesses n := by
  rcases h with ⟨left, interior, right, rfl, hlen, hleft, hright,
    hvalues, hsum, hncase⟩
  have htriple : NoTripleZeros interior := hncase.resolve_left (by omega)
  let positives := positiveEntries interior
  let positiveExcess := positives.map (fun value => value - 1)
  let gaps := zeroGaps interior
  let count := positives.length
  have hpositive : ∀ value ∈ positives, 1 ≤ value ∧ value ≤ 2 := by
    intro value hvalue
    have hmem := mem_positiveEntries_iff.mp hvalue
    exact ⟨Nat.one_le_iff_ne_zero.mpr hmem.2, hvalues value hmem.1⟩
  have hpositiveSum : positives.sum = interior.sum := by
    exact sum_positiveEntries interior
  have hcountLe : count ≤ positives.sum := by
    exact List.length_le_sum_of_one_le positives (fun value hvalue =>
      (hpositive value hvalue).1)
  have htotal : left + interior.sum + right = 6 := by
    simpa only [List.sum_cons, List.sum_append, List.sum_singleton,
      List.sum_nil, Nat.add_zero] using hsum
  have hif : left + right + count ≤ 6 := by omega
  have hcount : count < 7 := by omega
  have hpositiveMem : positiveExcess ∈
      boundedLists (List.replicate count 1) (6 - left - right - count) := by
    apply mem_boundedLists_iff.mpr
    constructor
    · apply boundedBy_replicate_iff.mpr
      constructor
      · simp [positiveExcess, count]
      · intro value hvalue
        simp only [positiveExcess, List.mem_map] at hvalue
        rcases hvalue with ⟨source, hsource, rfl⟩
        have := hpositive source hsource
        omega
    · have hpred := sum_map_pred_add_length
        (values := positives) (fun value hvalue => (hpositive value hvalue).1)
      simp only [positiveExcess, count]
      omega
  have hgapMem : gaps ∈
      boundedLists (List.replicate (count + 1) 2) (3 * n - 2 - count) := by
    apply mem_boundedLists_iff.mpr
    constructor
    · apply boundedBy_replicate_iff.mpr
      constructor
      · exact length_zeroGaps interior
      · exact zeroGaps_le_two_of_noTripleZeros interior htriple
    · have hgapSum := sum_zeroGaps_add_length_positiveEntries interior
      change gaps.sum + count = interior.length at hgapSum
      rw [hlen] at hgapSum
      omega
  have hmap : positiveExcess.map (fun value => value + 1) = positives := by
    exact map_succ_map_pred (fun value hvalue => (hpositive value hvalue).1)
  have hreconstruct : placePositives gaps positives = interior := by
    exact placePositives_zeroGaps interior
  simp only [largeCandidateExcesses, List.cons_append, List.pure_def,
    List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_ite_nil_right, List.mem_cons, List.cons.injEq,
    List.append_singleton_inj, List.not_mem_nil, or_false, existsAndEq,
    and_true, exists_and_left, true_and]
  refine ⟨by omega, by omega, count, hcount, hif,
    positiveExcess, hpositiveMem, gaps, hgapMem, ?_⟩
  rw [hmap, hreconstruct]

lemma mem_minimalCandidateExcesses_iff {n : Nat} {excess : List Nat} :
    excess ∈ MinimalCandidateExcesses n ↔
      2 ≤ n ∧ n ≤ 7 ∧ IsCandidateExcess n excess := by
  by_cases hn2 : n = 2
  · subst n
    simpa [MinimalCandidateExcesses] using
      (mem_orderTwoCandidateExcesses_iff (excess := excess))
  · by_cases hn3 : 3 ≤ n
    · by_cases hn7 : n ≤ 7
      · constructor
        · intro h
          have hlarge : excess ∈ largeCandidateExcesses n := by
            simpa [MinimalCandidateExcesses, hn2, hn3, hn7] using h
          exact ⟨by omega, hn7, largeCandidateExcesses_sound hn3 hlarge⟩
        · rintro ⟨_, _, hcandidate⟩
          have hlarge := largeCandidateExcesses_complete hn3 hcandidate
          simpa [MinimalCandidateExcesses, hn2, hn3, hn7] using hlarge
      · simp [MinimalCandidateExcesses, hn2, hn3, hn7]
    · have hnlow : ¬2 ≤ n := by omega
      simp [MinimalCandidateExcesses, hn2, hn3, hnlow]

@[simp]
lemma handOfExcess_interior (n : Nat) (excess : List Nat)
    (i : Fin (3 * n - 2)) :
    handOfExcess n excess ⟨i.val + 1, by omega⟩ = excess.getD (i.val + 1) 0 + 1 := by
  simp only [handOfExcess_apply]
  split <;> omega

@[simp]
lemma handOfExcess_left_boundary (n : Nat) (hn : 0 < n) (excess : List Nat) :
    handOfExcess n excess ⟨0, by omega⟩ = excess.getD 0 0 := by
  simp only [handOfExcess_apply]
  simp

@[simp]
lemma handOfExcess_right_boundary (n : Nat) (hn : 0 < n) (excess : List Nat) :
    handOfExcess n excess ⟨3 * n - 1, by omega⟩ = excess.getD (3 * n - 1) 0 := by
  simp only [handOfExcess_apply]
  simp

lemma size_handOfExcess {n : Nat} {excess : List Nat} (hn : 2 ≤ n)
    (hlength : excess.length = 3 * n) :
    Hand.size (handOfExcess n excess) = excess.sum + (3 * n - 2) := by
  obtain ⟨left, interior, right, rfl, hlen⟩ :=
    list_split_boundaries (xs := excess) (m := 3 * n - 2) (by omega)
  have hsumGetD :
      (∑ i : Fin (3 * n - 2), interior.getD i.val 0) = interior.sum := by
    let e : Fin (3 * n - 2) ≃ Fin interior.length := finCongr hlen.symm
    calc
      _ = ∑ i : Fin interior.length, interior.getD i.val 0 := by
        apply Fintype.sum_equiv e
        intro i
        simp [e]
      _ = interior.sum := sum_getD interior
  have hgetD (i : Fin (3 * n - 2)) :
      (left :: interior ++ [right]).getD (i.val + 1) 0 =
        interior.getD i.val 0 := by
    exact List.getD_append interior [right] 0 i.val (by omega)
  have hrightGetD :
      (left :: interior ++ [right]).getD (3 * n - 1) 0 = right := by
    have hlast : 3 * n - 1 = (3 * n - 2) + 1 := by omega
    rw [hlast]
    change (interior ++ [right]).getD (3 * n - 2) 0 = right
    rw [List.getD_append_right]
    · simp [hlen]
    · omega
  have hinterior :
      (∑ i : Fin (3 * n - 2),
        handOfExcess n (left :: interior ++ [right])
          ⟨i.val + 1, by omega⟩) =
        interior.sum + (3 * n - 2) := by
    simp only [handOfExcess_apply]
    have hnotBoundary (i : Fin (3 * n - 2)) :
        ¬(i.val + 1 = 0 ∨ i.val + 1 = 3 * n - 1) := by omega
    simp only [hnotBoundary, ite_false, hgetD]
    rw [Finset.sum_add_distrib, hsumGetD]
    simp
  rw [Hand.size_eq_sum, sum_fin_boundaries hn, hinterior]
  simp only [handOfExcess_apply]
  rw [hrightGetD]
  simp
  omega

lemma size_handOfExcess_of_candidate {n : Nat} {excess : List Nat} (hn : 2 ≤ n)
    (h : IsCandidateExcess n excess) :
    Hand.size (handOfExcess n excess) = 3 * n + 4 := by
  rcases h with ⟨left, interior, right, rfl, hlen, _, _, _, hsum, _⟩
  have hlength : (left :: interior ++ [right]).length = 3 * n := by
    simp [hlen]
    omega
  rw [size_handOfExcess hn hlength]
  simp at hsum ⊢
  omega

def excessOf (n : Nat) (c : Hand n) : List Nat :=
  List.ofFn (fun i : Fin (3 * n) =>
    c i - if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else 1)

lemma excessOf_getD (n : Nat) (c : Hand n) (i : Fin (3 * n)) :
    (excessOf n c).getD i.val 0 =
      c i - if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else 1 := by
  unfold excessOf
  rw [List.getD_eq_getElem]
  · simp
  · simp

lemma handOfExcess_excessOf {n : Nat} {c : Hand n}
    (hc : ∀ i : Fin (3 * n - 2), 1 ≤ c ⟨i.val + 1, by omega⟩) :
    handOfExcess n (excessOf n c) = c := by
  ext i
  simp only [handOfExcess_apply, excessOf_getD]
  by_cases hi : i.val = 0 ∨ i.val = 3 * n - 1
  · simp only [hi, ite_true, Nat.sub_zero, Nat.add_zero]
  · simp only [hi, ite_false]
    rcases lt_or_ge i.val 1 with hi0 | hi1
    · omega
    · by_cases hilast : i.val = 3 * n - 1
      · exact False.elim (hi (Or.inr hilast))
      · have hpos : 1 ≤ c i := by
          have hpos' := hc ⟨i.val - 1, by omega⟩
          convert hpos' using 1
          congr 1
          apply Fin.ext
          change i.val = (i.val - 1) + 1
          omega
        omega

/-- An interior run of three ordinary entries. -/
def NoInteriorTripleOnes {n : Nat} (c : Hand n) : Prop :=
  ∀ i : Fin (3 * n - 4),
    ¬ (c ⟨i.val + 1, by omega⟩ = 1 ∧
      c ⟨i.val + 2, by omega⟩ = 1 ∧
      c ⟨i.val + 3, by omega⟩ = 1)

lemma noInteriorTripleOnes_handOfExcess_iff
    {n left right : Nat} {interior : List Nat} (hn : 2 ≤ n)
    (hlen : interior.length = 3 * n - 2) :
    NoInteriorTripleOnes (handOfExcess n (left :: interior ++ [right])) ↔
      NoTripleZeros interior := by
  have hvalue (i : Nat) (hi : i < interior.length) :
      handOfExcess n (left :: interior ++ [right]) ⟨i + 1, by omega⟩ =
        interior.getD i 0 + 1 := by
    let j : Fin (3 * n - 2) := ⟨i, by omega⟩
    have hgetD :
        (left :: interior ++ [right]).getD (i + 1) 0 = interior.getD i 0 :=
      List.getD_append interior [right] 0 i hi
    simpa only [j, hgetD] using
      (handOfExcess_interior n (left :: interior ++ [right]) j)
  constructor
  · intro h
    apply (noTripleZeros_iff_getD interior).mpr
    intro i hi hzeros
    let j : Fin (3 * n - 4) := ⟨i, by omega⟩
    apply h j
    have hi₀ : i < interior.length := by omega
    have hi₁ : i + 1 < interior.length := by omega
    have hi₂ : i + 2 < interior.length := by omega
    grind [hvalue i hi₀, hvalue (i + 1) hi₁, hvalue (i + 2) hi₂]
  · intro h i hones
    have hzeros := (noTripleZeros_iff_getD interior).mp h i.val (by omega)
    apply hzeros
    have hi₀ : i.val < interior.length := by omega
    have hi₁ : i.val + 1 < interior.length := by omega
    have hi₂ : i.val + 2 < interior.length := by omega
    grind [hvalue i.val hi₀, hvalue (i.val + 1) hi₁,
      hvalue (i.val + 2) hi₂]

/-- The numerical conditions satisfied by a minimal live counterexample in the
small range. -/
def IsMinimalCandidate {n : Nat} (c : Hand n) : Prop :=
  2 ≤ n ∧ n ≤ 7 ∧
    (∀ i, c i ≤ 3) ∧
    (∀ i : Fin (3 * n - 2), 1 ≤ c ⟨i.val + 1, by omega⟩) ∧
    Hand.size c = 3 * n + 4 ∧
    (n = 2 ∨ NoInteriorTripleOnes c)

lemma IsCandidateExcess.isMinimalCandidate_handOfExcess
    {n : Nat} {excess : List Nat} (hn : 2 ≤ n) (hn' : n ≤ 7)
    (h : IsCandidateExcess n excess) :
    IsMinimalCandidate (handOfExcess n excess) := by
  have hsize := size_handOfExcess_of_candidate hn h
  rcases h with ⟨left, interior, right, rfl, hlen, hleft, hright,
    hvalues, _, hncase⟩
  have hrightGetD :
      (left :: interior ++ [right]).getD (3 * n - 1) 0 = right := by
    have hlast : 3 * n - 1 = (3 * n - 2) + 1 := by omega
    rw [hlast]
    change (interior ++ [right]).getD (3 * n - 2) 0 = right
    rw [List.getD_append_right]
    · simp [hlen]
    · omega
  have hleftValue :
      handOfExcess n (left :: interior ++ [right]) ⟨0, by omega⟩ = left := by
    rw [handOfExcess_left_boundary n (by omega)]
    simp
  have hrightValue :
      handOfExcess n (left :: interior ++ [right])
        ⟨3 * n - 1, by omega⟩ = right := by
    rw [handOfExcess_right_boundary n (by omega), hrightGetD]
  have hle : ∀ i, handOfExcess n (left :: interior ++ [right]) i ≤ 3 := by
    intro i
    by_cases hzero : i.val = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hzero
      calc
        _ = handOfExcess n (left :: interior ++ [right]) ⟨0, by omega⟩ :=
          congrArg _ hi
        _ = left := hleftValue
        _ ≤ 3 := hleft
    by_cases hlast : i.val = 3 * n - 1
    · have hi : i = ⟨3 * n - 1, by omega⟩ := Fin.ext hlast
      calc
        _ = handOfExcess n (left :: interior ++ [right])
            ⟨3 * n - 1, by omega⟩ := congrArg _ hi
        _ = right := hrightValue
        _ ≤ 3 := hright
    · have hj : i.val - 1 < interior.length := by omega
      have hgetD :
          (left :: interior ++ [right]).getD i.val 0 =
            interior.getD (i.val - 1) 0 := by
        have hi : i.val = (i.val - 1) + 1 := by omega
        rw [hi]
        exact List.getD_append interior [right] 0 (i.val - 1) hj
      have hvalue : interior.getD (i.val - 1) 0 ≤ 2 := by
        rw [List.getD_eq_getElem]
        · exact hvalues _ (List.getElem_mem hj)
        · exact hj
      simp only [handOfExcess_apply, hzero, hlast, false_or, ite_false]
      rw [hgetD]
      omega
  have hpositive :
      ∀ i : Fin (3 * n - 2),
        1 ≤ handOfExcess n (left :: interior ++ [right])
          ⟨i.val + 1, by omega⟩ := by
    intro i
    simp only [handOfExcess_interior]
    omega
  refine ⟨hn, hn', hle, hpositive, hsize, ?_⟩
  rcases hncase with rfl | htriple
  · exact Or.inl rfl
  · exact Or.inr (noInteriorTripleOnes_handOfExcess_iff hn hlen |>.mpr htriple)

lemma IsMinimalCandidate.isCandidateExcess_excessOf
    {n : Nat} {c : Hand n} (h : IsMinimalCandidate c) :
    IsCandidateExcess n (excessOf n c) := by
  rcases h with ⟨hn, _, hle, hpositive, hsize, hncase⟩
  have hlength : (excessOf n c).length = 3 * n := by
    simp [excessOf]
  obtain ⟨left, interior, right, hexcess, hlen⟩ :=
    list_split_boundaries (xs := excessOf n c) (m := 3 * n - 2) (by omega)
  have hrecover := handOfExcess_excessOf hpositive
  rw [hexcess] at hrecover
  have hrightGetD :
      (left :: interior ++ [right]).getD (3 * n - 1) 0 = right := by
    have hlast : 3 * n - 1 = (3 * n - 2) + 1 := by omega
    rw [hlast]
    change (interior ++ [right]).getD (3 * n - 2) 0 = right
    rw [List.getD_append_right]
    · simp [hlen]
    · omega
  have hleftValue :
      handOfExcess n (left :: interior ++ [right]) ⟨0, by omega⟩ = left := by
    rw [handOfExcess_left_boundary n (by omega)]
    simp
  have hrightValue :
      handOfExcess n (left :: interior ++ [right])
        ⟨3 * n - 1, by omega⟩ = right := by
    rw [handOfExcess_right_boundary n (by omega), hrightGetD]
  have hvalue (i : Nat) (hi : i < interior.length) :
      handOfExcess n (left :: interior ++ [right]) ⟨i + 1, by omega⟩ =
        interior.getD i 0 + 1 := by
    let j : Fin (3 * n - 2) := ⟨i, by omega⟩
    have hgetD :
        (left :: interior ++ [right]).getD (i + 1) 0 = interior.getD i 0 :=
      List.getD_append interior [right] 0 i hi
    simpa only [j, hgetD] using
      (handOfExcess_interior n (left :: interior ++ [right]) j)
  have hleft : left ≤ 3 := by
    calc
      left = handOfExcess n (left :: interior ++ [right]) ⟨0, by omega⟩ :=
        hleftValue.symm
      _ = c ⟨0, by omega⟩ := congrArg (fun d : Hand n => d _) hrecover
      _ ≤ 3 := hle _
  have hright : right ≤ 3 := by
    calc
      right = handOfExcess n (left :: interior ++ [right])
          ⟨3 * n - 1, by omega⟩ := hrightValue.symm
      _ = c ⟨3 * n - 1, by omega⟩ := congrArg (fun d : Hand n => d _) hrecover
      _ ≤ 3 := hle _
  have hvalues : ∀ value ∈ interior, value ≤ 2 := by
    intro value hmem
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, rfl⟩
    have hc := hle ⟨i + 1, by omega⟩
    rw [← hrecover, hvalue i hi] at hc
    rw [List.getD_eq_getElem] at hc
    · omega
    · exact hi
  have hsizeExcess := size_handOfExcess hn hlength
  rw [handOfExcess_excessOf hpositive, hsize] at hsizeExcess
  have hsum : (excessOf n c).sum = 6 := by omega
  refine ⟨left, interior, right, hexcess, hlen, hleft, hright,
    hvalues, hsum, ?_⟩
  rcases hncase with hn2 | htriple
  · exact Or.inl hn2
  · apply Or.inr
    apply (noInteriorTripleOnes_handOfExcess_iff
      (left := left) (right := right) hn hlen).mp
    exact hrecover.symm ▸ htriple

/-- The enumeration contains exactly the hands satisfying its numerical
conditions. -/
theorem mem_minimalCandidates_iff {n : Nat} {c : Hand n} :
    c ∈ MinimalCandidates n ↔ IsMinimalCandidate c := by
  simp only [MinimalCandidates, List.mem_map]
  constructor
  · rintro ⟨excess, hmem, rfl⟩
    rcases mem_minimalCandidateExcesses_iff.mp hmem with
      ⟨hn, hn', hcandidate⟩
    exact hcandidate.isMinimalCandidate_handOfExcess hn hn'
  · intro h
    rcases h with ⟨hn, hn', hle, hpositive, hsize, hncase⟩
    have hminimal : IsMinimalCandidate c :=
      ⟨hn, hn', hle, hpositive, hsize, hncase⟩
    have hcandidate := hminimal.isCandidateExcess_excessOf
    refine ⟨excessOf n c, mem_minimalCandidateExcesses_iff.mpr
      ⟨hn, hn', hcandidate⟩, ?_⟩
    exact handOfExcess_excessOf hpositive

/-- Every minimal live counterexample occurs in the finite enumeration. -/
theorem mem_minimalCandidates_of_minimal
    {n : Nat} {c : Hand n} (hn : 2 ≤ n) (hc : IsLiveCE c)
    (hmin : ∀ m, 2 ≤ m → m < n → ¬ HasLiveCE m) :
    c ∈ MinimalCandidates n := by
  apply mem_minimalCandidates_iff.mpr
  have hfull := isLiveFullWait_iff_le_three.mp hc.1 |>.1
  have hn' : n ≤ 7 := by
    by_contra hn'
    obtain ⟨m, hm, hm', hcounterexample⟩ := liveFullWait_reduction hn hc
    exact hmin m hm (by omega) hcounterexample
  have hle : ∀ i, c i ≤ 3 := hc.1.le_three
  have hpositive :
      ∀ i : Fin (3 * n - 2), 1 ≤ c ⟨i.val + 1, by omega⟩ := by
    intro i
    exact interior_positive hn c hfull ⟨i.val + 1, by omega⟩
      ⟨by simp, by simp; omega⟩
  have hsize := IsLiveFullWait.size (by omega) hc.1
  refine ⟨hn, hn', hle, hpositive, hsize, ?_⟩
  by_cases hn2 : n = 2
  · exact Or.inl hn2
  · apply Or.inr
    intro i hones
    cases n with
    | zero => omega
    | succ m =>
        let k : Fin (3 * m) := ⟨i.val + 1, by omega⟩
        have hk : 0 < k.val := by simp [k]
        have hseq : HasSeqAt c k := by
          simpa only [k] using hones
        obtain ⟨d, k, hk, hcd⟩ := hseq.exists_insertSeqAt hk
        have hd := Counterexample.IsLiveCE_of_insertSeqAt k hk (hcd ▸ hc)
        exact hmin m (by omega) (by omega) ⟨d, hd⟩

open Winning.Decidable

/-- The successors of one winning-hand automaton state, represented as a list
so that closed computations can be checked by kernel reduction. -/
def listNextStates (x : Nat) (q : State) : List State :=
  [false, true].filterMap (fun takePair => nextState q takePair x)

/-- Advance a list representation of a winning-hand automaton state set. -/
def listStepStates (x : Nat) (states : List State) : List State :=
  (states.flatMap (listNextStates x)).eraseDups

/-- Run the winning-hand automaton using transparent lists of states. -/
def listReachable : List State → List Nat → List State
  | states, [] => states
  | states, x :: xs => listReachable (listStepStates x states) xs

@[simp]
lemma mem_listNextStates {x : Nat} {q t : State} :
    t ∈ listNextStates x q ↔
      ∃ takePair, nextState q takePair x = some t := by
  simp [listNextStates]

@[simp]
lemma mem_listStepStates {x : Nat} {states : List State} {t : State} :
    t ∈ listStepStates x states ↔
      ∃ q ∈ states, t ∈ Winning.Decidable.step x q := by
  simp only [listStepStates, List.mem_eraseDups, List.mem_flatMap,
    mem_listNextStates, Winning.Decidable.mem_step]
  grind

lemma mem_listReachable (states : List State) (xs : List Nat) (t : State) :
    t ∈ listReachable states xs ↔
      ∃ s ∈ states, ∃ choices, replayChoices s xs choices = some t := by
  induction xs generalizing states with
  | nil =>
      simp [listReachable, replayChoices_exists_nil_iff]
  | cons x xs ih =>
      simp only [listReachable, ih, mem_listStepStates,
        replayChoices_exists_cons_iff]
      grind

/-- A transparent list-based winning-hand checker used for kernel certificates. -/
def listWinning (c : Hand n) : Bool :=
  Hand.size c == 3 * n + 5 &&
    (listReachable [State.init] (List.ofFn c)).contains State.final

lemma listWinning_spec (c : Hand n) :
    listWinning c = true ↔ Winning c := by
  rw [← Winning.Decidable.decide_spec, Winning.Decidable.decide_dp]
  simp only [listWinning, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem, mem_listReachable, List.mem_singleton,
    exists_eq_left, Winning.Decidable.DPWinning]

/-- Transparently check whether a hand is the standard live full wait. -/
def isStandardLiveFullWait (c : Hand n) : Bool :=
  (List.finRange (3 * n)).all fun i =>
    c i == if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1

lemma isStandardLiveFullWait_spec (c : Hand n) :
    isStandardLiveFullWait c = true ↔ c = standardLiveFullWait n := by
  simp only [isStandardLiveFullWait, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext i
    simpa only [standardLiveFullWait_apply] using h i (by simp)
  · rintro rfl i _
    simp only [standardLiveFullWait_apply]

/-- A candidate passes when it has a non-winning tile or is the standard hand. -/
def minimalCandidatePasses (n : Nat) (c : Hand n) : Bool :=
  (List.finRange (3 * n)).any (fun i => !listWinning (c + single i)) ||
    isStandardLiveFullWait c

lemma minimalCandidatePasses_spec {n : Nat} {c : Hand n}
    (hle : ∀ i, c i ≤ 3) :
    minimalCandidatePasses n c = true ↔ ¬ IsLiveCE c := by
  constructor
  · intro h hc
    rcases Bool.or_eq_true_iff.mp h with hnonwinning | heq
    · obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hnonwinning
      rw [Bool.not_eq_true_eq_eq_false] at hi
      have hwinning := (isLiveFullWait_iff_le_three.mp hc.1).1 i
      have htrue := listWinning_spec (c + single i) |>.mpr hwinning
      rw [htrue] at hi
      contradiction
    · have heq' := isStandardLiveFullWait_spec c |>.mp heq
      exact hc.2 heq'
  · intro hnce
    by_cases heq : c = standardLiveFullWait n
    · apply Bool.or_eq_true_iff.mpr
      right
      exact isStandardLiveFullWait_spec c |>.mpr heq
    · apply Bool.or_eq_true_iff.mpr
      left
      apply List.any_eq_true.mpr
      have hnfull : ¬ IsFullWait c := by
        intro hfull
        exact hnce ⟨isLiveFullWait_iff_le_three.mpr ⟨hfull, hle⟩, heq⟩
      simp only [IsFullWait] at hnfull
      push Not at hnfull
      obtain ⟨i, hi⟩ := hnfull
      refine ⟨i, by simp, ?_⟩
      rw [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
      intro htrue
      exact hi (listWinning_spec (c + single i) |>.mp htrue)

/-
No enumerated small candidate is a live counterexample.
Replace `native_decide` with `rfl` for a axiom-free, but slower proof.
-/
-- set_option maxRecDepth 100000 in
-- set_option maxHeartbeats 2000000 in
theorem minimalCandidates_no_liveCE (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    ∀ c ∈ MinimalCandidates n, ¬ IsLiveCE c := by
  have hcertificate :
      (MinimalCandidates n).all (minimalCandidatePasses n) = true := by
    interval_cases n <;> native_decide
  intro c hc
  have hle := (mem_minimalCandidates_iff.mp hc).2.2.1
  exact minimalCandidatePasses_spec hle |>.mp
    (List.all_eq_true.mp hcertificate c hc)

end Mahjong.Hand.Counterexample
