/-
G2-coulomb: the per-representative kernel checks (core Lean, so that the data modules stay light).
-/
import GW.Endpoint.Coulomb.GeomData

namespace GW.Endpoint.Coulomb

def dFace : QT × Int × Int := (.leaf 3 0, 0, 0)

/-- The check of outer face `i` of the representative `key` (`f` = quadtree and enclosure). -/
def faceChkC (key : Int × Int × Int) (k : Nat) (f : QT × Int × Int) (i : Nat) : Bool :=
  decide (alN Dvc (cellTs.getD i dflt) key = 0) ||
    (decide (detN Dvc (cellTs.getD i dflt) key ≠ 0) &&
      decide (treeChk (qcOf Bint Dvc (cellTs.getD i dflt) key) k f.1 0 0 0 false = some f.2))

def fLoC (key : Int × Int × Int) (i : Nat) (lo hi : Int) : Int :=
  if alN Dvc (cellTs.getD i dflt) key = 0 then 0 else tLo Dvc (cellTs.getD i dflt) key lo hi
def fHiC (key : Int × Int × Int) (i : Nat) (lo hi : Int) : Int :=
  if alN Dvc (cellTs.getD i dflt) key = 0 then 0 else tHi Dvc (cellTs.getD i dflt) key lo hi

def sumLoC (key : Int × Int × Int) (fs : List (QT × Int × Int)) : Int :=
  ((List.range 72).map fun i => fLoC key i (fs.getD i dFace).2.1 (fs.getD i dFace).2.2).sum
def sumHiC (key : Int × Int × Int) (fs : List (QT × Int × Int)) : Int :=
  ((List.range 72).map fun i => fHiC key i (fs.getD i dFace).2.1 (fs.getD i dFace).2.2).sum

end GW.Endpoint.Coulomb
