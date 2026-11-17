/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Segment
public import Ninegates.Hand.Parity

/-! The paper's even and odd lower-bound families, expressed uniformly in n.
The odd family has one extra initial three before the alternating five/four part. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

def hand (n : ℕ) : VirtualHand n := fun i ↦
  if i.val = 0 then 2 else if i.val = 1 then 4 else if i.val = 2 then 6
  else if i.val = 3 then 3 else if 3 * n - 2 ≤ i.val then 2
  else if n % 2 = 1 ∧ i.val = 4 then 3 else if (i.val + n) % 2 = 0 then 5 else 4

@[grind =]
lemma hand_apply {n : ℕ} (i : Rank n) : hand n i =
    if i.val = 0 then 2 else if i.val = 1 then 4 else if i.val = 2 then 6
    else if i.val = 3 then 3 else if 3 * n - 2 ≤ i.val then 2
    else if n % 2 = 1 ∧ i.val = 4 then 3 else if (i.val + n) % 2 = 0 then 5 else 4 := rfl

def even (a : ℕ) : VirtualHand (2 * a + 2) := hand (2 * a + 2)
def odd (a : ℕ) : VirtualHand (2 * a + 3) := hand (2 * a + 3)

def meldCount (n : ℕ) : ℕ := 9 * n / 2 - 3

lemma nonnegative_hand (n : ℕ) : Nonnegative (hand n) := by
  intro i
  change 0 ≤ hand n i
  unfold hand
  split_ifs <;> norm_num

end Mahjong.VirtualHand.AlternatingWait
