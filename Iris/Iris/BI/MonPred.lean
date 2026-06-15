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

namespace Iris
open BI Std OFE COFE Sbi

@[rocq_alias biIndex]
structure BIIndex where
  type : Type _
  inhabited : Inhabited type
  rel : Relation type
  rel_preorder : Preorder rel

instance : CoeSort BIIndex (Type _) := ⟨BIIndex.type⟩
instance {I : BIIndex} : Inhabited I := I.inhabited
instance {I : BIIndex} : Preorder I.rel := I.rel_preorder


-- Change: `bot` is a field of this class, in Rocq it is a parameter of this class
@[rocq_alias BiIndexBottom]
class BIIndexBottom (I : BIIndex) where
  bot : I
  bot_le (i : I) : I.rel bot i

structure MonPred (I : BIIndex) (PROP : Type _) [BI PROP] where
  holds : I → PROP
  mono : ∀ {i j : I}, I.rel i j → holds i ⊢ holds j

instance {I : BIIndex} {PROP : Type _} [BI PROP] : CoeFun (MonPred I PROP) (fun _ => I → PROP) where
  coe x := x.holds

section cofe

variable {I : BIIndex} {PROP : Type _} [BI PROP]

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

@[rocq_alias monPred_cofe]
instance : COFE (MonPred I PROP) where
  compl c := {
    holds i := compl (c.map (MonPred.proj i))
    -- Monotonicity at the limit. We cannot use `LimitPreserving` over `MonPred I PROP` (its COFE
    -- is exactly what we are defining), so we work in the function space `I → PROP`, which is
    -- already a COFE. There, `LimitPreserving.entails` says `· i₁ ⊢ · i₂` survives limits; each
    -- `c n` satisfies it by `(c n).mono`, and the two function-space limits are definitionally the
    -- projected PROP limits above.
    mono {i₁ i₂} h :=
      let c' : Chain (I → PROP) := ⟨fun n => (c n).holds, fun hle j => c.cauchy hle j⟩
      LimitPreserving.entails (applyHom i₁) (applyHom i₂) c' fun n => (c n).mono h
  }
  conv_compl _ := conv_compl

end cofe

namespace MonPred

variable {I : BIIndex} {PROP : Type _} [BI PROP]

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

-- `<obj> Ψ`: `Ψ` holds at *every* index
def objectively (Ψ : I → PROP) : MonPred I PROP where
  holds _ := iprop(∀ i, Ψ i)
  mono _ := .rfl

-- `<subj> Ψ`: `Ψ` holds at *some* index
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
  holds i := BI.sForall fun p => ∃ P, Ψ P ∧ P i = p
  mono h_rel := by
    refine sForall_intro ?_
    rintro _ ⟨P, hP, rfl⟩
    exact (sForall_elim ⟨P, hP, rfl⟩).trans (P.mono h_rel)

def sExists (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := BI.sExists fun p => ∃ P, Ψ P ∧ P i = p
  mono h_rel := by
    refine sExists_elim ?_
    rintro _ ⟨P, hP, rfl⟩
    exact (P.mono h_rel).trans (sExists_intro ⟨P, hP, rfl⟩)

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

def fupd [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(|={E1,E2}=> P i)
  mono h_rel := BIFUpdate.mono (P.mono h_rel)

def siPure [Sbi PROP] (Pi : SiProp) : MonPred I PROP where
  holds _ := iprop(<si_pure> Pi)
  mono _ := .rfl

def siEmpValid [Sbi PROP] (P : MonPred I PROP) : SiProp :=
  iprop(<si_emp_valid> ∀ i, P i)

end bidefs

syntax:max "<obj> " term:40 : term
syntax:max "<subj> " term:40 : term

macro_rules
  | `(iprop(<obj> $P))  => ``(MonPred.objectively (iprop($P) : MonPred _ _))
  | `(iprop(<subj> $P)) => ``(MonPred.subjectively (iprop($P) : MonPred _ _))

delab_rule MonPred.objectively
  | `($_ $P) => do ``(iprop(<obj> $(← unpackIprop P)))
delab_rule MonPred.subjectively
  | `($_ $P) => do ``(iprop(<subj> $(← unpackIprop P)))

instance [BIUpdate PROP] : BUpd (MonPred I PROP) := ⟨MonPred.bupd⟩

instance [BIFUpdate PROP] : FUpd (MonPred I PROP) := ⟨MonPred.fupd⟩

instance [Sbi PROP] : SiPure (MonPred I PROP) := ⟨MonPred.siPure⟩

instance [Sbi PROP] : SiEmpValid (MonPred I PROP) := ⟨MonPred.siEmpValid⟩

instance [BIUpdate PROP] : NonExpansive BUpd.bupd (α := MonPred I PROP) :=
  ⟨fun {_ _ _} h i => BIUpdate.bupd_ne.ne (h i)⟩

instance [BIFUpdate PROP] {E1 E2 : CoPset} : NonExpansive (FUpd.fupd E1 E2) (α := MonPred I PROP) :=
  ⟨fun {_ _ _} h i => BIFUpdate.ne.ne (h i)⟩

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

@[rocq_alias monPredI]
instance : BI (MonPred I PROP) where
  entails_preorder := inferInstance
  equiv_iff {P Q} := by
    constructor
    · exact fun h => ⟨fun i => (equiv_iff.mp (h i)).mp, fun i => (equiv_iff.mp (h i)).mpr⟩
    · exact fun h i => equiv_iff.mpr ⟨h.mp i, h.mpr i⟩
  and_ne := ⟨fun n _ _ h₁ _ _ h₂ i => and_ne.ne (h₁ i) (h₂ i)⟩
  or_ne := ⟨fun n _ _ h₁ _ _ h₂ i => or_ne.ne (h₁ i) (h₂ i)⟩
  imp_ne := by
    refine ⟨fun n _ _ h₁ _ _ h₂ i => ?_⟩
    refine forall_ne fun j => ?_
    refine imp_ne.ne .rfl ?_
    exact imp_ne.ne (h₁ j) (h₂ j)
  sForall_ne {n Ψ₁ Ψ₂} h i := by
    obtain ⟨h₁, h₂⟩ := h
    refine sForall_ne ⟨?_, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨Q, hQ, hPQ⟩ := h₁ P hP
      exact ⟨Q i, ⟨Q, hQ, rfl⟩, hPQ i⟩
    · rintro _ ⟨Q, hQ, rfl⟩
      obtain ⟨P, hP, hPQ⟩ := h₂ Q hQ
      exact ⟨P i, ⟨P, hP, rfl⟩, hPQ i⟩
  sExists_ne {n Ψ₁ Ψ₂} h i := by
    obtain ⟨h₁, h₂⟩ := h
    refine sExists_ne ⟨?_, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨Q, hQ, hPQ⟩ := h₁ P hP
      exact ⟨Q i, ⟨Q, hQ, rfl⟩, hPQ i⟩
    · rintro _ ⟨Q, hQ, rfl⟩
      obtain ⟨P, hP, hPQ⟩ := h₂ Q hQ
      exact ⟨P i, ⟨P, hP, rfl⟩, hPQ i⟩
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
  sForall_intro {P Ψ} h i := by
    refine sForall_intro ?_
    rintro _ ⟨Q, hQ, rfl⟩
    exact h Q hQ i
  sForall_elim {Ψ P} h i := sForall_elim ⟨P, h, rfl⟩
  sExists_intro {Ψ P} h i := sExists_intro ⟨P, h, rfl⟩
  sExists_elim h i := by
    refine sExists_elim ?_
    rintro _ ⟨Q, hQ, rfl⟩
    exact h Q hQ i
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
    refine persistently_sExists_1.trans ?_
    refine exists_elim fun p => ?_
    refine pure_elim_l ?_
    rintro ⟨P, hP, rfl⟩
    refine (and_intro (pure_intro hP) .rfl).trans ?_
    refine sExists_intro ?_; dsimp
    exact ⟨iprop(⌜Ψ P⌝ ∧ <pers> P), ⟨P, rfl⟩, rfl⟩
  persistently_absorb_l i := persistently_absorb_l
  persistently_and_l i := persistently_and_l
  later_mono h i := later_mono (h i)
  later_intro i := later_intro
  later_sForall_2 {Ψ} i := by
    refine .trans ?_ later_sForall_2
    refine forall_intro fun p => ?_
    refine imp_intro ?_
    refine pure_elim_r ?_
    rintro ⟨P, hP, rfl⟩
    refine (sForall_elim ⟨iprop(⌜Ψ P⌝ → ▷ P), ⟨P, rfl⟩, rfl⟩).trans ?_
    refine (forall_elim i).trans ?_; dsimp
    refine (pure_imp_elim refl).trans ?_
    exact pure_imp_elim hP
  later_sExists_false {Ψ} i := by
    refine later_sExists_false.trans ?_
    refine or_mono .rfl ?_
    refine exists_elim fun p => ?_
    refine pure_elim_l ?_
    rintro ⟨P, hP, rfl⟩
    refine (and_intro (pure_intro hP) .rfl).trans ?_
    refine sExists_intro ?_; dsimp
    exact ⟨iprop(⌜Ψ P⌝ ∧ ▷ P), ⟨P, rfl⟩, rfl⟩
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

-- sForall can also be defined in an alternative (but equivalent way), however
-- this is harder to work with
def sForall' (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := iprop(∀ P, ⌜Ψ P⌝ → P i)
  mono h_rel := forall_mono fun P => imp_mono_r (P.mono h_rel)

-- Ditto for sExists
def sExists' (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := iprop(∃ P, ⌜Ψ P⌝ ∧ P i)
  mono h_rel := exists_mono fun P => and_mono_r (P.mono h_rel)

theorem sForall_sForall' {Ψ : MonPred I PROP → Prop} : sForall Ψ ⊣⊢ sForall' Ψ := by
  constructor
  · intros i
    refine forall_intro fun P => ?_
    refine imp_intro ?_
    refine pure_elim_r fun hP => ?_
    exact sForall_elim ⟨P, hP, rfl⟩
  · intro i
    refine sForall_intro ?_
    rintro _ ⟨P, hP, rfl⟩
    refine (forall_elim P).trans ?_
    exact pure_imp_elim hP

theorem sExists_sExists' {Ψ : MonPred I PROP → Prop} : sExists Ψ ⊣⊢ sExists' Ψ := by
  constructor
  · intros i
    refine sExists_elim ?_
    rintro _ ⟨P, hP, rfl⟩
    refine exists_intro' P ?_
    exact and_intro (pure_intro hP) .rfl
  · intros i
    refine exists_elim fun P => ?_
    refine pure_elim_l fun hP => ?_
    exact sExists_intro ⟨P, hP, rfl⟩

@[rocq_alias monPred_at_forall]
theorem forall_at {α} {Ψ : α → MonPred I PROP} i : iprop(∀ x, Ψ x) i ⊣⊢ ∀ x, Ψ x i := by
  constructor
  · refine (sForall_sForall'.mp i).trans ?_
    refine forall_intro fun x => ?_
    refine (forall_elim (Ψ x)).trans ?_; dsimp
    exact pure_imp_elim ⟨x, rfl⟩
  · refine .trans ?_ (sForall_sForall'.mpr i)
    refine forall_intro fun P => ?_; dsimp
    refine imp_intro ?_
    refine pure_elim_r ?_
    rintro ⟨x, rfl⟩
    exact forall_elim x

@[rocq_alias monPred_at_exists]
theorem exists_at {α} {Ψ : α → MonPred I PROP} i : iprop(∃ x, Ψ x) i ⊣⊢ ∃ x, Ψ x i := by
  constructor
  · refine (sExists_sExists'.mp i).trans ?_
    refine exists_elim fun P => ?_; dsimp
    refine pure_elim_l ?_
    rintro ⟨x, rfl⟩
    exact exists_intro' x .rfl
  · refine .trans ?_ (sExists_sExists'.mpr i)
    refine exists_elim fun x => ?_
    refine exists_intro' (Ψ x) ?_; dsimp
    exact and_intro (pure_intro ⟨x, rfl⟩) .rfl

-- Embed instances (DEFERRED — not ported). `MonPred.embed` exists as a plain `def` (above), but the
-- generic `Embed`/`BiEmbed` typeclass hierarchy that Rocq's `embedding.v` provides does not exist in
-- iris-lean, so none of the embed instances below are ported:
--   BiEmbed · BiEmbedEmp · BiEmbedLater · BiEmbedBUpd · BiEmbedFUpd · BiEmbedSbi · embed_objective
-- See `MonPred-porting-notes.md` § "Decision (session 3): do NOT port the generic BiEmbed infra".

-- BIBUpd instance
@[rocq_alias monPred_bi_bupd]
instance [BIUpdate PROP] : BIUpdate (MonPred I PROP) where
  intro _ := BIUpdate.intro
  mono h i := BIUpdate.mono (h i)
  trans _ := BIUpdate.trans
  frame_r _ := BIUpdate.frame_r

-- BIFUpd instance
@[rocq_alias monPred_bi_fupd]
instance [BIFUpdate PROP] : BIFUpdate (MonPred I PROP) where
  subset h _ := BIFUpdate.subset h
  except0 _ := BIFUpdate.except0
  mono h i := BIFUpdate.mono (h i)
  trans _ := BIFUpdate.trans
  mask_frame_r' h i := by
    refine .trans ?_ (BIFUpdate.mask_frame_r' h)
    refine BIFUpdate.mono ?_
    refine (forall_elim i).trans ?_; dsimp
    exact pure_imp_elim refl
  frame_r _ := BIFUpdate.frame_r

-- BiLöb instance
@[rocq_alias monPred_bi_löb]
instance [BILoeb PROP] : BILoeb (MonPred I PROP) where
  loeb_weak h i := BILoeb.loeb_weak (h i)

-- BiPositive instance
@[rocq_alias monPred_bi_positive]
instance [BIPositive PROP] : BIPositive (MonPred I PROP) where
  affinely_sep_l _ := BIPositive.affinely_sep_l

-- BiAffine instance
@[rocq_alias monPred_bi_affine]
instance [BIAffine PROP] : BIAffine (MonPred I PROP) where
  affine _ := ⟨fun _ => Affine.affine⟩

-- BiPersistentlyForall instance
@[rocq_alias monPred_bi_persistently_forall]
instance [BIPersistentlyForall PROP] : BIPersistentlyForall (MonPred I PROP) where
  persistently_sForall_2 Ψ i := by
    refine .trans ?_ (BIPersistentlyForall.persistently_sForall_2 (fun p => ∃ P, Ψ P ∧ P i = p))
    refine forall_intro fun p => ?_
    refine imp_intro ?_
    refine pure_elim_r ?_
    rintro ⟨P, hP, rfl⟩
    have entails : (∀ p, ⌜Ψ p⌝ → <pers> p) ⊢ <pers> P := (forall_elim P).trans (pure_imp_elim hP)
    exact entails i

-- BiPureForall instance
-- can always be proven using classical logic, so no need for such instance

-- BiLaterContractive instance
@[rocq_alias monPred_bi_later_contractive]
instance [BILaterContractive PROP] : BILaterContractive (MonPred I PROP) where
  distLater_dist h i := BILaterContractive.toContractive.distLater_dist fun m hlt => h m hlt i

-- BiBUpdFUpd instance
@[rocq_alias monPred_bi_bupd_fupd]
instance [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] : BIUpdateFUpdate (MonPred I PROP) where
  fupd_of_bupd _ := BIUpdateFUpdate.fupd_of_bupd

-- SbiEmpValidExist instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiBUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiFUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

section modalities
variable {P Q : MonPred I PROP}

/-! ### The `<obj>` modality -/

@[rocq_alias monPred_objectively_mono]
theorem objectively_mono (h : P ⊢ Q) : <obj> P ⊢ <obj> Q :=
  fun _ => forall_mono h

@[rocq_alias monPred_objectively_elim]
theorem objectively_elim : <obj> P ⊢ P := forall_elim

@[rocq_alias monPred_objectively_idemp]
theorem objectively_idemp : <obj> <obj> P ⊣⊢ <obj> P :=
  ⟨objectively_elim, fun _ => forall_intro fun _ => .rfl⟩

@[rocq_alias monPred_objectively_forall]
theorem objectively_forall {α} {Ψ : α → MonPred I PROP} :
    <obj> (∀ x, Ψ x) ⊣⊢ ∀ x, <obj> Ψ x := by
  constructor
  · exact forall_intro fun x => objectively_mono (forall_elim x)
  · intro i
    refine forall_intro fun j => ?_
    refine .trans ?_ (forall_at j).mpr
    refine forall_intro fun x => ?_
    refine (forall_at i).mp.trans ?_
    refine (forall_elim x).trans ?_
    exact forall_elim j

@[rocq_alias monPred_objectively_exist]
theorem objectively_exists {α : Sort _} {Ψ : α → MonPred I PROP} :
    (∃ x, <obj> Ψ x) ⊢ <obj> (∃ x, Ψ x) :=
  exists_elim fun x => objectively_mono (exists_intro x)

@[rocq_alias monPred_objectively_and]
theorem objectively_and : <obj> (P ∧ Q) ⊣⊢ <obj> P ∧ <obj> Q := by
  constructor
  · exact and_intro (objectively_mono and_elim_l) (objectively_mono and_elim_r)
  · exact fun _ => forall_intro fun i => and_mono (forall_elim i) (forall_elim i)

@[rocq_alias monPred_objectively_or]
theorem objectively_or : <obj> P ∨ <obj> Q ⊢ <obj> (P ∨ Q) :=
  or_elim (objectively_mono or_intro_l) (objectively_mono or_intro_r)

theorem objectively_sep_mp [BIIndexBottom I] : <obj> (P ∗ Q) ⊢ <obj> P ∗ <obj> Q := by
  intros _
  refine (forall_elim BIIndexBottom.bot).trans ?_
  refine sep_mono ?_ ?_
  · exact forall_intro fun i => P.mono (BIIndexBottom.bot_le i)
  · exact forall_intro fun i => Q.mono (BIIndexBottom.bot_le i)

@[rocq_alias monPred_objectively_sep_2]
theorem objectively_sep_mpr : <obj> P ∗ <obj> Q ⊢ <obj> (P ∗ Q) :=
  fun _ => forall_intro fun i => sep_mono (forall_elim i) (forall_elim i)

@[rocq_alias monPred_objectively_sep]
theorem objectively_sep [BIIndexBottom I] : <obj> (P ∗ Q) ⊣⊢ <obj> P ∗ <obj> Q :=
  ⟨objectively_sep_mp, objectively_sep_mpr⟩

@[rocq_alias monPred_objectively_emp]
theorem objectively_emp : <obj> emp ⊣⊢@{MonPred I PROP} emp :=
  ⟨objectively_elim, fun _ => forall_intro fun _ => .rfl⟩

@[rocq_alias monPred_objectively_pure]
theorem objectively_pure {φ : Prop} : <obj> ⌜φ⌝ ⊣⊢@{MonPred I PROP} ⌜φ⌝ :=
  ⟨objectively_elim, fun _ => forall_intro fun _ => .rfl⟩

/-! ### The `<subj>` modality -/

@[rocq_alias monPred_subjectively_mono]
theorem subjectively_mono (h : P ⊢ Q) : <subj> P ⊢ <subj> Q :=
  fun _ => exists_mono h

@[rocq_alias monPred_subjectively_intro]
theorem subjectively_intro : P ⊢ <subj> P := exists_intro

@[rocq_alias monPred_subjectively_forall]
theorem subjectively_forall {α : Sort _} (Ψ : α → MonPred I PROP) :
    <subj> (∀ x, Ψ x) ⊢ ∀ x, <subj> Ψ x :=
  forall_intro fun x => subjectively_mono (forall_elim x)

@[rocq_alias monPred_subjectively_exists]
theorem subjectively_exists {α : Sort _} (Ψ : α → MonPred I PROP) :
    <subj> (∃ x, Ψ x) ⊣⊢ ∃ x, <subj> Ψ x := by
  constructor
  · intro i
    refine exists_elim fun j => ?_
    refine (exists_at j).mp.trans ?_
    refine exists_elim fun x => ?_
    refine .trans ?_ (exists_at i).mpr
    refine exists_intro' x ?_
    refine exists_intro j
  · exact exists_elim fun x => subjectively_mono (exists_intro x)

@[rocq_alias monPred_subjectively_and]
theorem subjectively_and : <subj> (P ∧ Q) ⊢ <subj> P ∧ <subj> Q :=
  and_intro (subjectively_mono and_elim_l) (subjectively_mono and_elim_r)

@[rocq_alias monPred_subjectively_or]
theorem subjectively_or : <subj> (P ∨ Q) ⊣⊢ <subj> P ∨ <subj> Q := by
  constructor
  · exact fun _ => exists_elim fun i => or_mono (exists_intro i) (exists_intro i)
  · exact or_elim (subjectively_mono or_intro_l) (subjectively_mono or_intro_r)

@[rocq_alias monPred_subjectively_sep]
theorem subjectively_sep : <subj> (P ∗ Q) ⊢ <subj> P ∗ <subj> Q :=
  fun _ => exists_elim fun i => sep_mono (exists_intro i) (exists_intro i)

@[rocq_alias monPred_subjectively_idemp]
theorem subjectively_idemp : <subj> <subj> P ⊣⊢ <subj> P :=
  ⟨fun _ => exists_elim fun _ => .rfl, subjectively_intro⟩

/-! ### `Objective` predicates -/

-- `Objective P`: `P` does not depend on the index, i.e. `P i ⊢ P j` for all `i j`.
@[rocq_alias Objective]
class Objective (P : MonPred I PROP) : Prop where
  holds (i j : I) : P i ⊢ P j

@[rocq_alias objective_objectively]
theorem objective_objectively (P : MonPred I PROP) [Objective P] : P ⊢ <obj> P :=
  fun i => forall_intro (Objective.holds i)

@[rocq_alias objective_subjectively]
theorem objective_subjectively (P : MonPred I PROP) [Objective P] : <subj> P ⊢ P :=
  fun i => exists_elim fun j => Objective.holds j i

@[rocq_alias pure_objective]
instance pure_objective {φ : Prop} : Objective (iprop(⌜φ⌝ : MonPred I PROP)) :=
  ⟨fun _ _ => .rfl⟩

@[rocq_alias emp_objective]
instance emp_objective : Objective (iprop(emp) : MonPred I PROP) :=
  ⟨fun _ _ => .rfl⟩

@[rocq_alias objectively_objective]
instance objectively_objective : Objective iprop(<obj> P) :=
  ⟨fun _ _ => .rfl⟩

@[rocq_alias subjectively_objective]
instance subjectively_objective : Objective iprop(<subj> P) :=
  ⟨fun _ _ => .rfl⟩

@[rocq_alias and_objective]
instance and_objective [Objective P] [Objective Q] : Objective iprop(P ∧ Q) :=
  ⟨fun i j => and_mono (Objective.holds i j) (Objective.holds i j)⟩

@[rocq_alias or_objective]
instance or_objective [Objective P] [Objective Q] : Objective iprop(P ∨ Q) :=
  ⟨fun i j => or_mono (Objective.holds i j) (Objective.holds i j)⟩

@[rocq_alias sep_objective]
instance sep_objective [Objective P] [Objective Q] : Objective iprop(P ∗ Q) :=
  ⟨fun i j => sep_mono (Objective.holds i j) (Objective.holds i j)⟩

@[rocq_alias persistently_objective]
instance persistently_objective [Objective P] : Objective iprop(<pers> P) :=
  ⟨fun i j => persistently_mono (Objective.holds i j)⟩

@[rocq_alias forall_objective]
instance forall_objective {α : Sort _} {Ψ : α → MonPred I PROP} [∀ x, Objective (Ψ x)] :
    Objective iprop(∀ x, Ψ x) := by
  constructor
  intro i j
  refine (forall_at i).mp.trans ?_
  refine .trans ?_ (forall_at j).mpr
  refine forall_mono fun x => ?_
  exact Objective.holds i j

@[rocq_alias exists_objective]
instance exists_objective {α : Sort _} {Ψ : α → MonPred I PROP} [∀ x, Objective (Ψ x)] :
    Objective iprop(∃ x, Ψ x) := by
  constructor
  intro i j
  refine (exists_at i).mp.trans ?_
  refine .trans ?_ (exists_at j).mpr
  refine exists_mono fun x => ?_
  exact Objective.holds i j

@[rocq_alias impl_objective]
instance imp_objective [Objective P] [Objective Q] : Objective iprop(P → Q) := by
  constructor
  intro i j
  refine forall_intro fun k => ?_; dsimp
  refine imp_intro ?_
  refine and_elim_l.trans ?_ -- ignore pure hypothesis
  refine (forall_elim i).trans ?_
  refine (pure_imp_elim refl).trans ?_
  exact imp_mono (Objective.holds k i) (Objective.holds i k)

@[rocq_alias wand_objective]
instance wand_objective [Objective P] [Objective Q] : Objective iprop(P -∗ Q) := by
  constructor
  intro i j
  refine forall_intro fun k => ?_; dsimp
  refine imp_intro ?_
  refine and_elim_l.trans ?_ -- ignore pure hypothesis
  refine (forall_elim i).trans ?_
  refine (pure_imp_elim refl).trans ?_; dsimp
  exact wand_mono (Objective.holds k i) (Objective.holds i k)

@[rocq_alias later_objective]
instance later_objective [Objective P] : Objective iprop(▷ P) :=
  ⟨fun i j => later_mono (Objective.holds i j)⟩

@[rocq_alias except0_objective]
instance except0_objective [Objective P] : Objective iprop(◇ P) :=
  ⟨fun i j => except0_mono (Objective.holds i j)⟩

@[rocq_alias laterN_objective]
instance laterN_objective [Objective P] {n : Nat} : Objective iprop(▷^[n] P) := by
  induction n with
  | zero => exact inferInstanceAs (Objective P)
  | succ n' ih => exact later_objective

@[rocq_alias bupd_objective]
instance bupd_objective [BIUpdate PROP] [Objective P] : Objective iprop(|==> P) :=
  ⟨fun i j => BIUpdate.mono (Objective.holds i j)⟩

@[rocq_alias fupd_objective]
instance fupd_objective [BIFUpdate PROP] {E1 E2 : CoPset} [Objective P] :
    Objective iprop(|={E1,E2}=> P) :=
  ⟨fun i j => BIFUpdate.mono (Objective.holds i j)⟩

end modalities

/-! ### Lifting `Persistent`/`Absorbing`/`Affine` -/

@[rocq_alias monPred_persistent]
theorem lift_persistent {P : MonPred I PROP} (h : ∀ i, Persistent (P i)) : Persistent P :=
  ⟨fun i => (h i).persistent⟩

@[rocq_alias monPred_absorbing]
theorem lift_absorbing {P : MonPred I PROP} (h : ∀ i, Absorbing (P i)) : Absorbing P :=
  ⟨fun i => (h i).absorbing⟩

@[rocq_alias monPred_affine]
theorem lift_affine {P : MonPred I PROP} (h : ∀ i, Affine (P i)) : Affine P :=
  ⟨fun i => (h i).affine⟩

@[rocq_alias monPred_at_persistent]
instance at_persistent {P : MonPred I PROP} [Persistent P] (i : I) : Persistent (P i) :=
  ⟨Persistent.persistent (P := P) i⟩

@[rocq_alias monPred_at_absorbing]
instance at_absorbing {P : MonPred I PROP} [Absorbing P] (i : I) : Absorbing (P i) :=
  ⟨Absorbing.absorbing (P := P) i⟩

@[rocq_alias monPred_at_affine]
instance at_affine {P : MonPred I PROP} [Affine P] (i : I) : Affine (P i) :=
  ⟨Affine.affine (P := P) i⟩

/-! ### `Persistent`/`Absorbing`/`Affine` for `<obj>`/`<subj>` -/

@[rocq_alias monPred_objectively_persistent]
instance objectively_persistent {P : MonPred I PROP} [BIPersistentlyForall PROP] [Persistent P] :
    Persistent iprop(<obj> P) :=
  ⟨fun _ => (forall_mono fun _ => Persistent.persistent).trans persistently_forall.mpr⟩

@[rocq_alias monPred_objectively_absorbing]
instance objectively_absorbing {P : MonPred I PROP} [Absorbing P] : Absorbing iprop(<obj> P) :=
  ⟨fun _ => absorbingly_forall_1.trans (forall_mono fun _ => Absorbing.absorbing)⟩

@[rocq_alias monPred_objectively_affine]
instance objectively_affine {P : MonPred I PROP} [Affine P] : Affine iprop(<obj> P) :=
  ⟨fun i => (forall_elim i).trans Affine.affine⟩

@[rocq_alias monPred_subjectively_persistent]
instance subjectively_persistent {P : MonPred I PROP} [Persistent P] : Persistent iprop(<subj> P) :=
  ⟨fun _ => (exists_mono fun _ => Persistent.persistent).trans persistently_exists.mpr⟩

@[rocq_alias monPred_subjectively_absorbing]
instance subjectively_absorbing {P : MonPred I PROP} [Absorbing P] : Absorbing iprop(<subj> P) :=
  ⟨fun _ => absorbingly_exists.mp.trans (exists_mono fun _ => Absorbing.absorbing)⟩

@[rocq_alias monPred_subjectively_affine]
instance subjectively_affine {P : MonPred I PROP} [Affine P] : Affine iprop(<subj> P) :=
  ⟨fun _ => exists_elim fun _ => Affine.affine⟩

end MonPred

-- The `Sbi`-dependent instances live here, in a scope with *only* `[Sbi PROP]` (and no independent
-- `[BI PROP]`). This is essential: under the namespace-level `variable [BI PROP]` above, `MonPred I
-- PROP` would carry a second `BI PROP` distinct from `Sbi.toBI`, so lemmas like `forall_mono` would
-- synthesize the section `BI` while the PROP-level `Sbi` laws live over `Sbi.toBI` - an instance
-- diamond.
namespace MonPred

variable {I : BIIndex} {PROP : Type _} [Sbi PROP]

-- Sbi instance
@[rocq_alias monPred_sbi]
instance : Sbi (MonPred I PROP) where
  siPure_ne := ⟨fun {_ _ _} h _ => siPure_ne.ne h⟩
  siEmpValid_ne := ⟨fun {_ _ _} h => siEmpValid_ne.ne (forall_ne h)⟩
  siPure_mono h i := siPure_mono h
  siEmpValid_mono h := siEmpValid_mono (forall_mono h)
  siEmpValid_siPure {Pi} := by
    constructor
    · exact (siEmpValid_mono (forall_elim default)).trans siEmpValid_siPure.mp
    · exact siEmpValid_siPure.mpr.trans (siEmpValid_mono (forall_intro fun _ => .rfl))
  siPure_siEmpValid i := siPure_siEmpValid.trans (persistently_mono (forall_elim i))
  siPure_imp_mpr i := by
    refine (forall_elim i).trans ?_; dsimp
    exact (pure_imp_elim refl).trans siPure_imp_mpr
  siPure_sForall_mpr {Ψ} i := by
    refine .trans ?_ siPure_sForall_mpr
    refine forall_intro fun Pi => ?_
    refine imp_intro ?_
    refine pure_elim_r fun hPi => ?_
    have entails : (∀ Pi, ⌜Ψ Pi⌝ → <si_pure> Pi) ⊢@{MonPred I PROP} <si_pure> Pi :=
      (forall_elim Pi).trans (pure_imp_elim hPi)
    exact entails i
  persistently_imp_siPure {Pi P} i := by
    refine (forall_elim i).trans ?_; dsimp
    refine (pure_imp_elim refl).trans ?_
    refine persistently_imp_siPure.trans ?_
    refine persistently_mono ?_
    refine forall_intro fun j => ?_; dsimp
    refine imp_intro ?_
    refine pure_elim_r fun h_rel => ?_
    exact imp_mono_r (P.mono h_rel)
  siPure_later := ⟨fun _ => siPure_later.mp, fun _ => siPure_later.mpr⟩
  siPure_absorbing {Pi} := ⟨fun _ => (siPure_absorbing Pi).absorbing⟩
  siEmpValid_later_mp := (siEmpValid_mono later_forall.mpr).trans siEmpValid_later_mp
  siEmpValid_affinely_mpr := by
    refine siEmpValid_affinely_mpr.trans ?_
    refine siEmpValid_mono ?_
    refine forall_intro fun i => ?_
    exact affinely_mono (forall_elim i)
  prop_ext_siEmpValid {P Q} := by
    refine .trans ?_ (SiProp.fun_ext_internalEq P Q)
    refine forall_intro fun i => ?_
    refine .trans ?_ prop_ext_siEmpValid
    refine siEmpValid_mono ?_
    refine (forall_elim i).trans (and_mono ?_ ?_)
    · exact (forall_elim i).trans (pure_imp_elim refl)
    · exact (forall_elim i).trans (pure_imp_elim refl)

@[rocq_alias si_pure_objective]
instance si_pure_objective {Pi : SiProp} : Objective (iprop(<si_pure> Pi) : MonPred I PROP) :=
  ⟨fun _ _ => .rfl⟩

@[rocq_alias plainly_objective]
instance plainly_objective {P : MonPred I PROP} : Objective iprop(■ P) := ⟨fun _ _ => .rfl⟩

@[rocq_alias monPred_sbi_emp_valid_exist]
instance [SbiEmpValidExist PROP] [BIIndexBottom I] : SbiEmpValidExist (MonPred I PROP) where
  siEmpValid_sExists_1 Ψ := by
    refine (siEmpValid_mono (forall_elim BIIndexBottom.bot)).trans ?_
    refine (SbiEmpValidExist.siEmpValid_sExists_1 _).trans ?_
    refine exists_elim fun p => ?_
    refine pure_elim_l ?_
    rintro ⟨P, hP, rfl⟩
    refine exists_intro' P ?_
    refine and_intro (pure_intro hP) ?_
    refine siEmpValid_mono ?_
    exact forall_intro fun i => P.mono (BIIndexBottom.bot_le i)

@[rocq_alias monPred_bi_bupd_sbi]
instance [BIUpdate PROP] [BIBUpdateSbi PROP] : BIBUpdateSbi (MonPred I PROP) where
  bupd_si_pure Pi _ := BIBUpdateSbi.bupd_si_pure Pi

-- `BIFUpdatePlainly` for `MonPred`. This mirrors Rocq's `monPred_bi_fupd_sbi`. The key fact is that
-- `MonPred`'s plainly is *objective*: `(■ P).holds i = <si_pure> <si_emp_valid> (∀ j, P j) = ■ (∀ j,
-- P j)` (definitionally), constant in `i`. So at each index `i` we feed the *objective body* `∀ j, P
-- j` to the PROP-level law — which itself strips the `■` — then reindex the result at `i` via
-- `forall_elim i` under `fupd`/`▷`/`◇`. (The PROP laws do the plainly-elimination internally, so —
-- unlike the older speculative note suggested — no `BIIndexBottom`/affineness side condition is
-- needed here.)
instance [BIFUpdate PROP] [BIFUpdatePlainly PROP] : BIFUpdatePlainly (MonPred I PROP) where
  fupd_plainly_keep_l E E' P R i := by
    -- Peel the *upclosed* wand at `i` (`forall_elim i` + `pure_imp_elim refl`); the explicit type
    -- on `hw` records that `(|={E,E'}=> ■ P).holds i` is `|={E,E'}=> ■ (∀ j, P j)`.
    have hw : (iprop(R -∗ |={E,E'}=> ■ P)).holds i ⊢ iprop(R.holds i -∗ |={E,E'}=> ■ (∀ j, P j)) :=
      (forall_elim i).trans (pure_imp_elim refl)
    refine (sep_mono_l hw).trans ?_
    refine (BIFUpdatePlainly.fupd_plainly_keep_l E E' (iprop(∀ j, P j)) (R.holds i)).trans ?_
    exact BIFUpdate.mono (sep_mono_l (forall_elim i))
  fupd_plainly_later E P i :=
    (BIFUpdatePlainly.fupd_plainly_later E (iprop(∀ j, P j))).trans
      (BIFUpdate.mono (later_mono (except0_mono (forall_elim i))))
  fupd_plainly_sForall_2 E Φ i :=
    (BIFUpdate.mono (plainly_mono (forall_elim i))).trans
      (BIFUpdatePlainly.fupd_plainly_sForall_2 E (fun p => ∃ Q, Φ Q ∧ Q.holds i = p))

end MonPred
