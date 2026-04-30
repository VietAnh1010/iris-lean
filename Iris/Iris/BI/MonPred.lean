/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viet Anh Nguyen
-/
module

public import Iris.BI.BI
public import Iris.BI.Updates
public import Iris.BI.DerivedLaws
import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.BI
open Iris.Std OFE COFE

structure BiIndex where
  type : Type _
  inhabited : Inhabited type
  rel : Relation type
  rel_preorder : Preorder rel

instance : CoeSort BiIndex (Type _) := ⟨BiIndex.type⟩
instance {I : BiIndex} : Inhabited I := I.inhabited
instance {I : BiIndex} : Preorder I.rel := I.rel_preorder

class BiIndexBottom where

structure MonPred (I : BiIndex) (PROP : Type _) [BI PROP] where
  holds : I → PROP
  mono : ∀ {i j : I}, I.rel i j → holds i ⊢ holds j

instance {I : BiIndex} {PROP : Type _} [BI PROP] : CoeFun (MonPred I PROP) (fun _ => I → PROP) where
  coe x := x.holds

section cofe

variable {I : BiIndex} {PROP : Type _} [BI PROP]

instance : OFE (MonPred I PROP) where
  Equiv P Q := ∀ (i : I), P i ≡ Q i
  Dist n P Q := ∀ (i : I), P i ≡{n}≡ Q i
  dist_eqv := {
    refl _ _ := .rfl
    symm h i := (h i).symm
    trans h₁ h₂ i := (h₁ i).trans (h₂ i)
  }
  equiv_dist := ⟨fun h _ i => (h i).dist, fun h i => equiv_dist.mpr (fun n => h n i)⟩
  dist_lt h hlt i := (h i).lt hlt

def MonPred.proj (i : I) : MonPred I PROP -n> PROP where
  f P := P i
  ne := ⟨fun {_ _ _} h => h i⟩

instance : COFE (MonPred I PROP) where
  compl c := {
    holds i := compl (c.map (MonPred.proj i))
    mono {i₁ i₂} h := sorry
  }
  conv_compl := sorry

end cofe

namespace MonPred

variable {I : BiIndex} {PROP : Type _} [BI PROP]

section bidefs

protected def Entails (P Q : MonPred I PROP) : Prop := ∀ i, P i ⊢ Q i

protected def upclosed (Ψ : I → PROP) : MonPred I PROP where
  holds i := iprop(∀ j, ⌜I.rel i j⌝ → Ψ j)
  mono h_rel := forall_mono fun _ => imp_mono (pure_mono (trans h_rel)) .rfl

protected def embed (P : PROP) : MonPred I PROP where
  holds _ := P
  mono _ := .rfl

protected def emp : MonPred I PROP where
  holds _ := emp
  mono _ := .rfl

protected def pure (p : Prop) : MonPred I PROP where
  holds _ := iprop(⌜p⌝)
  mono _ := .rfl

protected def objectively (P : I → PROP) : MonPred I PROP where
  holds _ := iprop(∀ i, P i)
  mono _ := .rfl

protected def subjectively (P : I → PROP) : MonPred I PROP where
  holds _ := iprop(∃ i, P i)
  mono _ := .rfl

protected def and (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∧ Q i)
  mono h_rel := and_mono (P.mono h_rel) (Q.mono h_rel)

protected def or (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∨ Q i)
  mono h_rel := or_mono (P.mono h_rel) (Q.mono h_rel)

protected def imp (P Q : MonPred I PROP) : MonPred I PROP :=
  MonPred.upclosed fun i => iprop(P i → Q i)

-- def sForall

-- def sExists

protected def sep (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∗ Q i)
  mono h_rel := sep_mono (P.mono h_rel) (Q.mono h_rel)

protected def wand (P Q : MonPred I PROP) : MonPred I PROP :=
  MonPred.upclosed fun i => iprop(P i -∗ Q i)

protected def persistently (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(<pers> P i)
  mono h_rel := persistently_mono (P.mono h_rel)

-- in is a Lean keyword
protected def in' (i : I) : MonPred I PROP where
  holds i' := iprop(⌜I.rel i i'⌝)
  mono h_rel := pure_mono fun h_rel' => trans h_rel' h_rel

protected def later (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(▷ P i)
  mono h_rel := later_mono (P.mono h_rel)

protected def bupd [BIUpdate PROP] (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(|==> P i)
  mono h_rel := BIUpdate.mono (P.mono h_rel)

-- def fupd

protected def siPure [Sbi PROP] (Pi : SiProp) : MonPred I PROP where
  holds _ := iprop(<si_pure> Pi)
  mono _ := .rfl

def siEmpValid [Sbi PROP] (P : MonPred I PROP) : SiProp :=
  iprop(<si_emp_valid> ∀ i, P i)

instance : BIBase (MonPred I PROP) where
  Entails := MonPred.Entails
  emp := MonPred.emp
  pure := MonPred.pure
  and := MonPred.and
  or := MonPred.or
  imp := MonPred.imp
  sForall := sorry
  sExists := sorry
  sep := MonPred.sep
  wand := MonPred.wand
  persistently := MonPred.persistently
  later := MonPred.later

instance : BI (MonPred I PROP) where
  entails_preorder := sorry
  equiv_iff := sorry -- todo: remove this once we fill in the details
  and_ne := sorry
  or_ne := sorry
  imp_ne := sorry
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := sorry
  wand_ne := sorry
  persistently_ne := sorry
  later_ne := sorry
  pure_intro := sorry
  pure_elim' := sorry
  and_elim_l := sorry
  and_elim_r := sorry
  and_intro := sorry
  or_intro_l := sorry
  or_intro_r := sorry
  or_elim := sorry
  imp_intro := sorry
  imp_elim := sorry
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := sorry
  emp_sep := sorry
  sep_symm := sorry
  sep_assoc_l := sorry
  wand_intro := sorry
  wand_elim := sorry
  persistently_mono := sorry
  persistently_idem_2 := sorry
  persistently_emp_2 := sorry
  persistently_and_2 := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l := sorry
  persistently_and_l := sorry
  later_mono := sorry
  later_intro := sorry
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := sorry
  later_persistently := sorry
  later_false_em := sorry

-- BI Persistently instance
-- BI Later instance
-- BI Embed instance (what is this?)

-- SBI instance
-- BIBUpd instance
-- BIFUpd instance
-- BI Lob instance
-- BIPositive instance
-- BIAffine instance
-- BIPersistentlyForall instance
-- BIPureForall instance
-- BILaterContractive instance
-- BIEmbedEmp instance
-- BIEmbedLater instance
-- BIBUpdFUpd instance
-- BIEmbedBUpd instance
-- BIEmbedFUpd instance
-- SbiEmpValidExist instance
-- BiEmbedSbi instance
-- BiBUpdSbi instance
-- BiFUpdSbi instance
-- class Objective (for what?)
-- bi_facts
-- <obj> and <surj> notations

end bidefs

end MonPred
