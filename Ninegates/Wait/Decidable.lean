import Ninegates.Wait.Decide
import Ninegates.Winning.Decidable

/-!
Correctness specifications and optimized `Decidable` instances for waits.
-/

namespace Mahjong.Hand

namespace IsWinningTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsWinningTile.decide c i = true ↔ IsWinningTile c i := by
  sorry

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWinningTile c i) :=
  decidable_of_iff (IsWinningTile.decide c i = true) (decide_spec c i)

end IsWinningTile.Decidable

namespace IsLiveWinningTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsLiveWinningTile.decide c i = true ↔ IsLiveWinningTile c i := by
  sorry

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsLiveWinningTile c i) :=
  decidable_of_iff (IsLiveWinningTile.decide c i = true) (decide_spec c i)

end IsLiveWinningTile.Decidable

namespace IsWait.Decidable

theorem decide_spec (c : Hand n) :
    IsWait.decide c = true ↔ IsWait c := by
  sorry

instance (c : Hand n) : Decidable (IsWait c) :=
  decidable_of_iff (IsWait.decide c = true) (decide_spec c)

end IsWait.Decidable

namespace IsLiveWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveWait.decide c = true ↔ IsLiveWait c := by
  sorry

instance (c : Hand n) : Decidable (IsLiveWait c) :=
  decidable_of_iff (IsLiveWait.decide c = true) (decide_spec c)

end IsLiveWait.Decidable

namespace IsFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsFullWait.decide c = true ↔ IsFullWait c := by
  sorry

instance (c : Hand n) : Decidable (IsFullWait c) :=
  decidable_of_iff (IsFullWait.decide c = true) (decide_spec c)

end IsFullWait.Decidable

namespace IsLiveFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveFullWait.decide c = true ↔ IsLiveFullWait c := by
  sorry

instance (c : Hand n) : Decidable (IsLiveFullWait c) :=
  decidable_of_iff (IsLiveFullWait.decide c = true) (decide_spec c)

end IsLiveFullWait.Decidable

end Mahjong.Hand
