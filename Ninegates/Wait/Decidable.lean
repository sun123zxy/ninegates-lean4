import Ninegates.Wait.Decide

namespace Mahjong.Hand

namespace IsLiveWinningTile.Decidable

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsLiveWinningTile c i) := by
  sorry

end IsLiveWinningTile.Decidable

namespace IsLiveWait.Decidable

instance (c : Hand n) : Decidable (IsLiveWait c) := by
  sorry -- by some sort of inferInstance directly from Decidable (IsLiveWinningTile c i)

end IsLiveWait.Decidable

namespace IsLiveFullWait.Decidable

instance (c : Hand n) : Decidable (IsLiveFullWait c) := by
  sorry

end IsLiveFullWait.Decidable

end Mahjong.Hand
