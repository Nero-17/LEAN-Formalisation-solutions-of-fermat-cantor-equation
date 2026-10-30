import LambdaCantor.RationalPowers.SharedLogData.Rows00
import LambdaCantor.RationalPowers.SharedLogData.Rows01
import LambdaCantor.RationalPowers.SharedLogData.Rows02
import LambdaCantor.RationalPowers.SharedLogData.Rows03
import LambdaCantor.RationalPowers.SharedLogData.Rows04
import LambdaCantor.RationalPowers.SharedLogData.Rows05
import LambdaCantor.RationalPowers.SharedLogData.Rows06
import LambdaCantor.RationalPowers.SharedLogData.Rows07
import LambdaCantor.RationalPowers.SharedLogData.Rows08
import LambdaCantor.RationalPowers.SharedLogData.Rows09
import LambdaCantor.RationalPowers.SharedLogData.Rows10
import LambdaCantor.RationalPowers.SharedLogData.Rows11
import LambdaCantor.RationalPowers.SharedLogData.Rows12
import LambdaCantor.RationalPowers.SharedLogData.Rows13
import LambdaCantor.RationalPowers.SharedLogData.Rows14
import LambdaCantor.RationalPowers.SharedLogData.Rows15
import LambdaCantor.RationalPowers.SharedLogData.Rows16
import LambdaCantor.RationalPowers.SharedLogData.Rows17
import LambdaCantor.RationalPowers.SharedLogData.Rows18
import LambdaCantor.RationalPowers.SharedLogData.Rows19
import LambdaCantor.RationalPowers.SharedLogData.Rows20
import LambdaCantor.RationalPowers.SharedLogData.Rows21
import LambdaCantor.RationalPowers.SharedLogData.Rows22
import LambdaCantor.RationalPowers.SharedLogData.Rows23
import LambdaCantor.RationalPowers.SharedLogData.Rows24
import LambdaCantor.RationalPowers.SharedLogData.Rows25
import LambdaCantor.RationalPowers.SharedLogData.Rows26
import LambdaCantor.RationalPowers.SharedLogData.Rows27
import LambdaCantor.RationalPowers.SharedLogData.Rows28
import LambdaCantor.RationalPowers.SharedLogData.Rows29
import LambdaCantor.RationalPowers.SharedLogData.Rows30
import LambdaCantor.RationalPowers.SharedLogData.Rows31
import LambdaCantor.RationalPowers.SharedLogData.Rows32
import LambdaCantor.RationalPowers.SharedLogData.Rows33
import LambdaCantor.RationalPowers.SharedLogData.Rows34
import LambdaCantor.RationalPowers.SharedLogData.Rows35
import LambdaCantor.RationalPowers.SharedLogData.Rows36
import LambdaCantor.RationalPowers.IdentifierLookup
import Init.Data.Array.QSort
import Lean.Elab.Tactic.Decide

#check (True.intro : True)

namespace LambdaCantor.RationalPowers

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedFullSourceBlocks : Array SharedSourceBlock := #[
  sharedSourceBlock00,
  sharedSourceBlock01,
  sharedSourceBlock02,
  sharedSourceBlock03,
  sharedSourceBlock04,
  sharedSourceBlock05,
  sharedSourceBlock06,
  sharedSourceBlock07,
  sharedSourceBlock08,
  sharedSourceBlock09,
  sharedSourceBlock10,
  sharedSourceBlock11,
  sharedSourceBlock12,
  sharedSourceBlock13,
  sharedSourceBlock14,
  sharedSourceBlock15,
  sharedSourceBlock16,
  sharedSourceBlock17,
  sharedSourceBlock18,
  sharedSourceBlock19,
  sharedSourceBlock20,
  sharedSourceBlock21,
  sharedSourceBlock22,
  sharedSourceBlock23,
  sharedSourceBlock24,
  sharedSourceBlock25,
  sharedSourceBlock26,
  sharedSourceBlock27,
  sharedSourceBlock28,
  sharedSourceBlock29,
  sharedSourceBlock30,
  sharedSourceBlock31,
  sharedSourceBlock32,
  sharedSourceBlock33,
  sharedSourceBlock34,
  sharedSourceBlock35,
  sharedSourceBlock36]

#check sharedFullSourceBlocks

theorem sharedFullSourceBlocks_accepted : ordinaryCatalogueAccepted sharedFullSourceBlocks = true := by
  simp only [ordinaryCatalogueAccepted, sharedFullSourceBlocks, List.all_toArray, List.all_cons, List.all_nil,
    sharedSourceBlock00_accepted,
    sharedSourceBlock01_accepted,
    sharedSourceBlock02_accepted,
    sharedSourceBlock03_accepted,
    sharedSourceBlock04_accepted,
    sharedSourceBlock05_accepted,
    sharedSourceBlock06_accepted,
    sharedSourceBlock07_accepted,
    sharedSourceBlock08_accepted,
    sharedSourceBlock09_accepted,
    sharedSourceBlock10_accepted,
    sharedSourceBlock11_accepted,
    sharedSourceBlock12_accepted,
    sharedSourceBlock13_accepted,
    sharedSourceBlock14_accepted,
    sharedSourceBlock15_accepted,
    sharedSourceBlock16_accepted,
    sharedSourceBlock17_accepted,
    sharedSourceBlock18_accepted,
    sharedSourceBlock19_accepted,
    sharedSourceBlock20_accepted,
    sharedSourceBlock21_accepted,
    sharedSourceBlock22_accepted,
    sharedSourceBlock23_accepted,
    sharedSourceBlock24_accepted,
    sharedSourceBlock25_accepted,
    sharedSourceBlock26_accepted,
    sharedSourceBlock27_accepted,
    sharedSourceBlock28_accepted,
    sharedSourceBlock29_accepted,
    sharedSourceBlock30_accepted,
    sharedSourceBlock31_accepted,
    sharedSourceBlock32_accepted,
    sharedSourceBlock33_accepted,
    sharedSourceBlock34_accepted,
    sharedSourceBlock35_accepted,
    sharedSourceBlock36_accepted,
    Bool.and_self]

#check sharedFullSourceBlocks_accepted

theorem sharedFullSourceBlocks_row_count : sharedFullSourceBlocks.foldl (fun count block => count+block.rows.size) 0 = 295480 := by
  native_decide

#check sharedFullSourceBlocks_row_count

/-- The full identifier table stores only module/row references, sorted once in native code. -/
def sharedFullOrdinaryEntries : Array (IdentifierEntry OrdinaryReference) :=
  (sharedLogRows00.mapIdx (fun index row => (⟨row.lowIndex,⟨0,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows01.mapIdx (fun index row => (⟨row.lowIndex,⟨1,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows02.mapIdx (fun index row => (⟨row.lowIndex,⟨2,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows03.mapIdx (fun index row => (⟨row.lowIndex,⟨3,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows04.mapIdx (fun index row => (⟨row.lowIndex,⟨4,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows05.mapIdx (fun index row => (⟨row.lowIndex,⟨5,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows06.mapIdx (fun index row => (⟨row.lowIndex,⟨6,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows07.mapIdx (fun index row => (⟨row.lowIndex,⟨7,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows08.mapIdx (fun index row => (⟨row.lowIndex,⟨8,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows09.mapIdx (fun index row => (⟨row.lowIndex,⟨9,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows10.mapIdx (fun index row => (⟨row.lowIndex,⟨10,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows11.mapIdx (fun index row => (⟨row.lowIndex,⟨11,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows12.mapIdx (fun index row => (⟨row.lowIndex,⟨12,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows13.mapIdx (fun index row => (⟨row.lowIndex,⟨13,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows14.mapIdx (fun index row => (⟨row.lowIndex,⟨14,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows15.mapIdx (fun index row => (⟨row.lowIndex,⟨15,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows16.mapIdx (fun index row => (⟨row.lowIndex,⟨16,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows17.mapIdx (fun index row => (⟨row.lowIndex,⟨17,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows18.mapIdx (fun index row => (⟨row.lowIndex,⟨18,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows19.mapIdx (fun index row => (⟨row.lowIndex,⟨19,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows20.mapIdx (fun index row => (⟨row.lowIndex,⟨20,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows21.mapIdx (fun index row => (⟨row.lowIndex,⟨21,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows22.mapIdx (fun index row => (⟨row.lowIndex,⟨22,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows23.mapIdx (fun index row => (⟨row.lowIndex,⟨23,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows24.mapIdx (fun index row => (⟨row.lowIndex,⟨24,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows25.mapIdx (fun index row => (⟨row.lowIndex,⟨25,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows26.mapIdx (fun index row => (⟨row.lowIndex,⟨26,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows27.mapIdx (fun index row => (⟨row.lowIndex,⟨27,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows28.mapIdx (fun index row => (⟨row.lowIndex,⟨28,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows29.mapIdx (fun index row => (⟨row.lowIndex,⟨29,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows30.mapIdx (fun index row => (⟨row.lowIndex,⟨30,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows31.mapIdx (fun index row => (⟨row.lowIndex,⟨31,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows32.mapIdx (fun index row => (⟨row.lowIndex,⟨32,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows33.mapIdx (fun index row => (⟨row.lowIndex,⟨33,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows34.mapIdx (fun index row => (⟨row.lowIndex,⟨34,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows35.mapIdx (fun index row => (⟨row.lowIndex,⟨35,index⟩⟩ : IdentifierEntry OrdinaryReference)) ++
    sharedLogRows36.mapIdx (fun index row => (⟨row.lowIndex,⟨36,index⟩⟩ : IdentifierEntry OrdinaryReference))).qsort (fun first second => decide (first.identifier < second.identifier))

#check sharedFullOrdinaryEntries

end LambdaCantor.RationalPowers
