/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viet Anh Nguyen
-/
module

public import Iris.BI.BI
public import Iris.BI.Updates
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
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

def Entails (P Q : MonPred I PROP) : Prop := ∀ i, P i ⊢ Q i

def upclosed (Ψ : I → PROP) : MonPred I PROP where
  holds i := iprop(∀ j, ⌜I.rel i j⌝ → Ψ j)
  mono h_rel := forall_mono fun _ => imp_mono (pure_mono (trans h_rel)) .rfl

def embed (P : PROP) : MonPred I PROP where
  holds _ := P
  mono _ := .rfl

def emp : MonPred I PROP where
  holds _ := iprop(emp)
  mono _ := .rfl

def pure (φ : Prop) : MonPred I PROP where
  holds _ := iprop(⌜φ⌝)
  mono _ := .rfl

def objectively (Ψ : I → PROP) : MonPred I PROP where
  holds _ := iprop(∀ i, Ψ i)
  mono _ := .rfl

def subjectively (Ψ : I → PROP) : MonPred I PROP where
  holds _ := iprop(∃ i, Ψ i)
  mono _ := .rfl

def and (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∧ Q i)
  mono h_rel := and_mono (P.mono h_rel) (Q.mono h_rel)

def or (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∨ Q i)
  mono h_rel := or_mono (P.mono h_rel) (Q.mono h_rel)

def imp (P Q : MonPred I PROP) : MonPred I PROP :=
  MonPred.upclosed fun i => iprop(P i → Q i)

def sForall (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := iprop(∀ P, ⌜Ψ P⌝ → P i)
  mono h_rel := forall_mono fun P => imp_mono_r (P.mono h_rel)

def sExists (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := iprop(∃ P, ⌜Ψ P⌝ ∧ P i)
  mono h_rel := exists_mono fun P => and_mono_r (P.mono h_rel)

def sep (P Q : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(P i ∗ Q i)
  mono h_rel := sep_mono (P.mono h_rel) (Q.mono h_rel)

def wand (P Q : MonPred I PROP) : MonPred I PROP :=
  MonPred.upclosed fun i => iprop(P i -∗ Q i)

def persistently (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(<pers> P i)
  mono h_rel := persistently_mono (P.mono h_rel)

-- in is a Lean keyword
def in' (i : I) : MonPred I PROP where
  holds i' := iprop(⌜I.rel i i'⌝)
  mono h_rel := pure_mono fun h_rel' => trans h_rel' h_rel

def later (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(▷ P i)
  mono h_rel := later_mono (P.mono h_rel)

def bupd [BIUpdate PROP] (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(|==> P i)
  mono h_rel := BIUpdate.mono (P.mono h_rel)

-- def fupd

def siPure [Sbi PROP] (Pi : SiProp) : MonPred I PROP where
  holds _ := iprop(<si_pure> Pi)
  mono _ := .rfl

def siEmpValid [Sbi PROP] (P : MonPred I PROP) : SiProp :=
  iprop(<si_emp_valid> ∀ i, P i)

instance [BIUpdate PROP] : BUpd (MonPred I PROP) := ⟨MonPred.bupd⟩

instance [Sbi PROP] : SiPure (MonPred I PROP) := ⟨MonPred.siPure⟩

instance [Sbi PROP] : SiEmpValid (MonPred I PROP) := ⟨MonPred.siEmpValid⟩

instance [BIUpdate PROP] : NonExpansive BUpd.bupd (α := MonPred I PROP) :=
  sorry

instance : BIBase (MonPred I PROP) where
  Entails := MonPred.Entails
  emp := MonPred.emp
  pure := MonPred.pure
  and := MonPred.and
  or := MonPred.or
  imp := MonPred.imp
  sForall := MonPred.sForall
  sExists := MonPred.sExists
  sep := MonPred.sep
  wand := MonPred.wand
  persistently := MonPred.persistently
  later := MonPred.later

instance : Preorder BIBase.Entails (α := MonPred I PROP) where
  refl _ := .rfl
  trans h₁ h₂ i := (h₁ i).trans (h₂ i)

instance : BI (MonPred I PROP) where
  entails_preorder := inferInstance
  equiv_iff {P Q} := by
    constructor
    · intro h; exact ⟨fun i => (equiv_iff.mp (h i)).mp, fun i => (equiv_iff.mp (h i)).mpr⟩
    · intro h; exact fun i => equiv_iff.mpr ⟨h.mp i, h.mpr i⟩
  and_ne := ⟨fun n _ _ h₁ _ _ h₂ i => and_ne.ne (h₁ i) (h₂ i)⟩
  or_ne := ⟨fun n _ _ h₁ _ _ h₂ i => or_ne.ne (h₁ i) (h₂ i)⟩
  imp_ne := by
    refine ⟨fun n _ _ h₁ _ _ h₂ i => ?_⟩
    refine forall_ne fun j => ?_
    refine imp_ne.ne .rfl ?_
    exact imp_ne.ne (h₁ j) (h₂ j)
  sForall_ne {n Ψ₁ Ψ₂} h i := by
    obtain ⟨h₁, h₂⟩ := h
    sorry
  sExists_ne {n Ψ₁ Ψ₂} h i := by
    obtain ⟨h₁, h₂⟩ := h
    sorry
  sep_ne := ⟨fun n _ _ h₁ _ _ h₂ i => sep_ne.ne (h₁ i) (h₂ i)⟩
  wand_ne := by
    refine ⟨fun n _ _ h₁ _ _ h₂ i => ?_⟩
    refine forall_ne fun j => ?_
    refine imp_ne.ne .rfl ?_
    exact wand_ne.ne (h₁ j) (h₂ j)
  persistently_ne := ⟨fun n _ _ h i => persistently_ne.ne (h i)⟩
  later_ne := ⟨fun n _ _ h i => later_ne.ne (h i)⟩
  pure_intro φ _ := pure_intro φ
  pure_elim' h i := pure_elim' fun hφ => pure_elim' fun _ => h hφ i
  and_elim_l i := and_elim_l
  and_elim_r i := and_elim_r
  and_intro h₁ h₂ i := and_intro (h₁ i) (h₂ i)
  or_intro_l i := or_intro_l
  or_intro_r i := or_intro_r
  or_elim h₁ h₂ i := or_elim (h₁ i) (h₂ i)
  imp_intro {P Q R} h i := by
    refine forall_intro fun j => ?_
    refine imp_intro ?_
    refine pure_elim_r fun h_rel => ?_
    refine (P.mono h_rel).trans ?_
    exact imp_intro (h j)
  imp_elim h i := by
    refine imp_elim ?_
    refine (h i).trans ?_
    refine (forall_elim i).trans ?_
    exact pure_imp_elim refl
  sForall_intro h i := forall_intro fun P => imp_intro <| pure_elim_r fun hP => h P hP i
  sForall_elim {Ψ P} h i := (forall_elim P).trans (pure_imp_elim h)
  sExists_intro {Ψ P} h i := exists_intro' P <| and_intro (pure_intro h) .rfl
  sExists_elim h i := exists_elim fun Q => pure_elim_l fun hQ => h Q hQ i
  sep_mono h₁ h₂ i := sep_mono (h₁ i) (h₂ i)
  emp_sep := ⟨fun i => emp_sep.mp, fun i => emp_sep.mpr⟩
  sep_symm i := sep_symm
  sep_assoc_l i := sep_assoc_l
  wand_intro {P Q R} h i := by
    refine forall_intro fun j => ?_
    refine imp_intro ?_
    refine pure_elim_r fun h_rel => ?_
    refine (P.mono h_rel).trans ?_
    exact wand_intro (h j)
  wand_elim h i := by
    refine wand_elim ?_
    refine (h i).trans ?_
    refine (forall_elim i).trans ?_
    exact pure_imp_elim refl
  persistently_mono h i := persistently_mono (h i)
  persistently_idem_2 i := persistently_idem_2
  persistently_emp_2 i := persistently_emp_2
  persistently_and_2 i := persistently_and_2
  persistently_sExists_1 {Ψ} i := by
    refine persistently_exists.mp.trans ?_
    refine exists_elim fun P => ?_
    refine persistently_and.mp.trans ?_
    refine exists_intro' iprop(⌜Ψ P⌝ ∧ <pers> P) ?_
    refine and_intro (pure_intro ⟨_, rfl⟩) ?_
    exact and_intro (and_elim_l.trans persistently_pure.mp) and_elim_r
  persistently_absorb_l i := persistently_absorb_l
  persistently_and_l i := persistently_and_l
  later_mono h i := later_mono (h i)
  later_intro i := later_intro
  later_sForall_2 {Ψ} i := by
    refine .trans ?_ later_forall.mpr
    refine forall_intro fun P => ?_
    refine (forall_elim (iprop(⌜Ψ P⌝ → ▷ P))).trans ?_
    simp
    sorry
  later_sExists_false := sorry
  later_sep := ⟨fun i => later_sep.mp, fun i => later_sep.mpr⟩
  later_persistently := ⟨fun i => later_persistently.mp, fun i => later_persistently.mpr⟩
  later_false_em {P} i := by
    refine later_false_em.trans ?_
    refine or_elim or_intro_l (or_intro_r' ?_)
    refine forall_intro fun j => ?_
    refine imp_intro ?_
    refine pure_elim_r fun h_rel => ?_
    exact imp_mono_r (P.mono h_rel)

-- BI Persistently instance
-- BI Later instance
-- proven inside BI

-- BI Embed instance (what is this?)

-- SBI instance

instance : Sbi (MonPred I PROP) := sorry

-- BIBUpd instance

instance [BIUpdate PROP] : BIUpdate (MonPred I PROP) where
  intro := sorry
  mono := sorry
  trans := sorry
  frame_r := sorry

-- BIFUpd instance
-- BI Lob instance

instance : BILoeb (MonPred I PROP) := sorry

-- BIPositive instance

-- BIAffine instance

instance : BIAffine (MonPred I PROP) := sorry

-- BIPersistentlyForall instance

instance : BIPersistentlyForall (MonPred I PROP) where
  persistently_sForall_2 := sorry

-- BIPureForall instance
-- can always be proven using classical logic, so no need for such instance

-- BILaterContractive instance

instance : BILaterContractive (MonPred I PROP) where
  toContractive := sorry

-- BIEmbedEmp instance

-- BIEmbedLater instance

-- BIBUpdFUpd instance
-- BIEmbedBUpd instance
-- BIEmbedFUpd instance

-- SbiEmpValidExist instance

instance [Sbi PROP] : SbiEmpValidExist (MonPred I PROP) where
  siEmpValid_sExists_1 := sorry

-- BiEmbedSbi instance

-- BiBUpdSbi instance

instance [BIUpdate PROP] : BIBUpdateSbi (MonPred I PROP) where
  bupd_si_pure := sorry

-- BiFUpdSbi instance

-- class Objective (for what?)
-- bi_facts
-- <obj> and <surj> notations

end bidefs

end MonPred
