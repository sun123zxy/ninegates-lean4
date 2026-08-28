import Ninegates.Wait.Decide

namespace Mahjong.Hand

namespace IsWinningTile.Decidable

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWinningTile c i) := by
  sorry

end IsWinningTile.Decidable

namespace IsWait.Decidable

instance (c : Hand n) : Decidable (IsWait c) := by
  sorry -- by some sort of inferInstance directly from Decidable (IsWinningTile c i)

end IsWait.Decidable

namespace IsFullWait.Decidable

instance (c : Hand n) : Decidable (IsFullWait c) := by
  sorry

end IsFullWait.Decidable

end Mahjong.Hand
