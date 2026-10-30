import LambdaCantor.RationalPowers.LargeExponentRawFull12Context005Cell
import LambdaCantor.RationalPowers.LargeExponentRawLogCore
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def largeExponentRawFull12Context005Table001Sources : Array RawPhase.Geometry := #[
  ⟨9,188,15300⟩,
  ⟨9,186,18216⟩]

def largeExponentRawFull12Context005Table001Caches : Array RawPhase.Cache := #[
  ⟨⟨-282387079596083138841255,-282387079596083138841254⟩,⟨-276549338036997296704343,-276549338036997296704342⟩,⟨-76693068123714647942530854,-76693068123714647942530853⟩,⟨-76707117411712133480858854,-76707117411712133480858853⟩⟩,
  ⟨⟨-294156300908139698280286,-294156300908139698280285⟩,⟨-288255955924027997360926,-288255955924027997360925⟩,⟨-117659357511497357201639183,-117659357511497357201639182⟩,⟨-117673405815358046690929424,-117673405815358046690929423⟩⟩]

theorem largeExponentRawFull12Context005Table001RawLog_checked : RawLog.tableCheck largeExponentRawFull12Context005Cell largeExponentRawFull12Context005Table001Sources largeExponentRawFull12Context005Table001Caches = true := by native_decide

end LambdaCantor.RationalPowers
