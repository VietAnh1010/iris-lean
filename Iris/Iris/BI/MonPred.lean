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

structure BIIndex where
  type : Type _
  inhabited : Inhabited type
  rel : Relation type
  rel_preorder : Preorder rel

instance : CoeSort BIIndex (Type _) := ⟨BIIndex.type⟩
instance {I : BIIndex} : Inhabited I := I.inhabited
instance {I : BIIndex} : Preorder I.rel := I.rel_preorder

/-- `BIIndexBottom I` provides a least element `bot` of the index relation: it sits below every
index. Mirrors Rocq's `BiIndexBottom {I} (bot : I) := bi_index_bot i : bot ⊑ i`; we bundle `bot` as
a field (keyed on `I`) so that `[BIIndexBottom I]` determines it during instance synthesis. -/
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

/-- `<obj> Ψ`: force `Ψ` at *every* index. `holds _ = ∀ i, Ψ i` (constant in the index),
so the result is objective. Mirrors Rocq's `monPred_objectively`. -/
def objectively (Ψ : I → PROP) : MonPred I PROP where
  holds _ := iprop(∀ i, Ψ i)
  mono _ := .rfl

/-- `<subj> Ψ`: force `Ψ` at *some* index. `holds _ = ∃ i, Ψ i` (constant in the index),
so the result is objective. Mirrors Rocq's `monPred_subjectively`. -/
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

-- sForall can also be defined in an alternative (but equivalent way), however
-- this is harder to work with
def sForall' (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
  holds i := iprop(∀ P, ⌜Ψ P⌝ → P i)
  mono h_rel := forall_mono fun P => imp_mono_r (P.mono h_rel)

-- Ditto for sExists
def sExists' (Ψ : MonPred I PROP -> Prop) : MonPred I PROP where
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

def fupd [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(|={E1,E2}=> P i)
  mono h_rel := BIFUpdate.mono (P.mono h_rel)

def siPure [Sbi PROP] (Pi : SiProp) : MonPred I PROP where
  holds _ := iprop(<si_pure> Pi)
  mono _ := .rfl

def siEmpValid [Sbi PROP] (P : MonPred I PROP) : SiProp :=
  iprop(<si_emp_valid> ∀ i, P i)

end bidefs

instance [BIUpdate PROP] : BUpd (MonPred I PROP) := ⟨MonPred.bupd⟩

instance [BIFUpdate PROP] : FUpd (MonPred I PROP) := ⟨MonPred.fupd⟩

instance [Sbi PROP] : SiPure (MonPred I PROP) := ⟨MonPred.siPure⟩

instance [Sbi PROP] : SiEmpValid (MonPred I PROP) := ⟨MonPred.siEmpValid⟩

instance [BIUpdate PROP] : NonExpansive BUpd.bupd (α := MonPred I PROP) :=
  ⟨fun {_ _ _} h i => BIUpdate.bupd_ne.ne (h i)⟩

instance [BIFUpdate PROP] {E1 E2 : CoPset} :
    NonExpansive (FUpd.fupd E1 E2 (PROP := MonPred I PROP)) :=
  ⟨fun {_ _ _} h i => BIFUpdate.ne.ne (h i)⟩

-- With the value-indexed definition of `sForall`/`sExists`, projecting at an index `i` is now
-- *definitionally* the corresponding PROP-level quantifier, so these bridge lemmas are `.rfl`. They
-- are kept as named lemmas so the call sites below (and the BI instance) keep reading clearly.
theorem sForall_at (Ψ : MonPred I PROP → Prop) i :
    sForall Ψ i ⊣⊢ BI.sForall fun p => ∃ P, Ψ P ∧ P i = p := .rfl

theorem sExists_at (Ψ : MonPred I PROP → Prop) i :
    sExists Ψ i ⊣⊢ BI.sExists fun p => ∃ P, Ψ P ∧ P i = p := .rfl

-- Bridges from the value-indexed `holds i` to the natural pointwise form. These are PROP-level (they
-- do not use the `MonPred` BI instance) and are used to reprove the BI quantifier laws below.
theorem sForall_holds (Ψ : MonPred I PROP → Prop) i :
    (sForall Ψ).holds i ⊣⊢ ∀ P, ⌜Ψ P⌝ → P i := by
  constructor
  · exact forall_intro fun P => imp_intro <| pure_elim_r fun hP => sForall_elim ⟨P, hP, rfl⟩
  · refine sForall_intro ?_
    rintro _ ⟨P, hP, rfl⟩
    exact (forall_elim P).trans (pure_imp_elim hP)

theorem sExists_holds (Ψ : MonPred I PROP → Prop) i :
    (sExists Ψ).holds i ⊣⊢ ∃ P, ⌜Ψ P⌝ ∧ P i := by
  constructor
  · refine sExists_elim ?_
    rintro _ ⟨P, hP, rfl⟩
    exact exists_intro' P (and_intro (pure_intro hP) .rfl)
  · exact exists_elim fun P => pure_elim_l fun hP => sExists_intro ⟨P, hP, rfl⟩

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

-- Pointwise projection of the `∀`/`∃` binders (Rocq's `monPred_at_forall`/`monPred_at_exist`).
theorem forall_at {α : Sort _} (Φ : α → MonPred I PROP) i :
    iprop(∀ x, Φ x).holds i ⊣⊢ ∀ x, (Φ x).holds i := by
  refine (sForall_holds _ i).trans ⟨?_, ?_⟩
  · refine forall_intro fun x => ?_
    exact (forall_elim (Φ x)).trans (pure_imp_elim ⟨x, rfl⟩)
  · refine forall_intro fun _ => imp_intro <| pure_elim_r ?_
    rintro ⟨x, rfl⟩
    exact forall_elim x

theorem exists_at {α : Sort _} (Φ : α → MonPred I PROP) i :
    iprop(∃ x, Φ x).holds i ⊣⊢ ∃ x, (Φ x).holds i := by
  refine (sExists_holds _ i).trans ⟨?_, ?_⟩
  · refine exists_elim fun _ => pure_elim_l ?_
    rintro ⟨x, rfl⟩
    exact exists_intro' x .rfl
  · refine exists_elim fun x => ?_
    exact exists_intro' (Φ x) (and_intro (pure_intro ⟨x, rfl⟩) .rfl)

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

-- BI Embed instance (what is this?)

-- SBI instance

-- The SBI structure for `MonPred` mirrors Rocq's `monPred_sbi_mixin`. The two operations are
-- pointwise/objective:
--   `(siPure Pi) i = <si_pure> Pi`   (constant in `i`)
--   `siEmpValid P  = <si_emp_valid> (∀ i, P i)`   (validity of the *objective* `∀ i, P i`)
-- Most fields therefore discharge at each index `i` by the corresponding PROP-level law, after
-- unfolding the (definitionally pointwise) connectives. `siEmpValid_forall` / `later_forall`
-- turn the `∀ i` underneath `<si_emp_valid>` into a MonPred-level `∀`.
-- SBI instance: see the dedicated `namespace MonPred` block after `end MonPred` below. It must
-- live outside the namespace-level `variable [BI PROP]` so that `MonPred I PROP`'s `BI` resolves
-- to `Sbi.toBI` rather than an independent section `BI PROP` (an instance diamond otherwise).

-- BIBUpd instance
instance [BIUpdate PROP] : BIUpdate (MonPred I PROP) where
  intro _ := BIUpdate.intro
  mono h i := BIUpdate.mono (h i)
  trans _ := BIUpdate.trans
  frame_r _ := BIUpdate.frame_r

-- BIFUpd instance
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

-- BI Lob instance
instance [BILoeb PROP] : BILoeb (MonPred I PROP) where
  loeb_weak h i := BILoeb.loeb_weak (h i)

-- BIPositive instance
instance [BIPositive PROP] : BIPositive (MonPred I PROP) where
  affinely_sep_l _ := BIPositive.affinely_sep_l

-- BIAffine instance
instance [BIAffine PROP] : BIAffine (MonPred I PROP) where
  affine _ := ⟨fun _ => Affine.affine⟩

-- BIPersistentlyForall instance
instance [BIPersistentlyForall PROP] : BIPersistentlyForall (MonPred I PROP) where
  persistently_sForall_2 Ψ i := by
    refine .trans ?_ (persistently_mono (sForall_at Ψ i).mpr)
    refine .trans ?_ (BIPersistentlyForall.persistently_sForall_2 (fun q => ∃ P, Ψ P ∧ P i = q))
    refine forall_intro fun q => imp_intro <| pure_elim_r ?_
    rintro ⟨P, hP, rfl⟩
    exact (show (∀ p, ⌜Ψ p⌝ → <pers> p) ⊢ <pers> P from
      (forall_elim P).trans (pure_imp_elim hP)) i

-- BIPureForall instance
-- can always be proven using classical logic, so no need for such instance

-- BILaterContractive instance
instance [BILaterContractive PROP] : BILaterContractive (MonPred I PROP) where
  distLater_dist h i := BILaterContractive.toContractive.distLater_dist fun m hlt => h m hlt i

-- BIEmbedEmp instance

-- BIEmbedLater instance

-- BIBUpdFUpd instance
instance [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] :
    BIUpdateFUpdate (MonPred I PROP) where
  fupd_of_bupd _ := BIUpdateFUpdate.fupd_of_bupd

-- BIEmbedBUpd instance
-- BIEmbedFUpd instance

-- SbiEmpValidExist instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiEmbedSbi instance

-- BiBUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiFUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

/-! ## Objective predicates and the `<obj>` / `<subj>` modalities

Mirrors Rocq's `Objective`, `monPred_objectively`, `monPred_subjectively` theory (`bi_facts`).
`<obj> P` forces `P` at *every* index (`holds _ = ∀ i, P i`); `<subj> P` at *some* index
(`holds _ = ∃ i, P i`). An `Objective P` predicate does not depend on the index. -/

/-- `Objective P`: the predicate does not depend on the index, i.e. `P i ⊢ P j` for all `i j`.
Mirrors Rocq's `Objective`. -/
class Objective (P : MonPred I PROP) : Prop where
  objective_at (i j : I) : P i ⊢ P j

export Objective (objective_at)

@[inherit_doc objectively] syntax:max "<obj> " term:40 : term
@[inherit_doc subjectively] syntax:max "<subj> " term:40 : term

-- `objectively`/`subjectively` take a raw `I → PROP`; we elaborate the body at `MonPred _ _`
-- (so inner connectives like `∧`/`∗` resolve via the `MonPred` BI) and let the `CoeFun`
-- coercion turn it into the `I → PROP` argument.
macro_rules
  | `(iprop(<obj> $P))  => ``(MonPred.objectively (iprop($P) : MonPred _ _))
  | `(iprop(<subj> $P)) => ``(MonPred.subjectively (iprop($P) : MonPred _ _))

delab_rule MonPred.objectively
  | `($_ $P) => do ``(iprop(<obj> $(← unpackIprop P)))
delab_rule MonPred.subjectively
  | `($_ $P) => do ``(iprop(<subj> $(← unpackIprop P)))

section objectively
variable {P Q : MonPred I PROP}

theorem objectively_mono (h : P ⊢ Q) : iprop(<obj> P) ⊢ iprop(<obj> Q) :=
  fun _ => forall_mono fun j => h j

theorem objectively_elim : iprop(<obj> P) ⊢ P := fun i => forall_elim i

theorem objectively_idemp : iprop(<obj> <obj> P) ⊣⊢ iprop(<obj> P) :=
  ⟨fun i => forall_elim i, fun _ => forall_intro fun _ => .rfl⟩

theorem objectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    iprop(<obj> (∀ x, Φ x)) ⊣⊢ iprop(∀ x, <obj> (Φ x)) :=
  ⟨fun i => (forall_intro fun x => forall_intro fun k =>
      ((forall_elim k).trans (forall_at Φ k).mp).trans (forall_elim x)).trans
        (forall_at (fun x => iprop(<obj> (Φ x))) i).mpr,
   fun i => forall_intro fun k => (forall_intro fun x =>
      ((forall_at (fun x => iprop(<obj> (Φ x))) i).mp.trans (forall_elim x)).trans
        (forall_elim k)).trans (forall_at Φ k).mpr⟩

theorem objectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    iprop(∃ x, <obj> (Φ x)) ⊢ iprop(<obj> (∃ x, Φ x)) :=
  fun i => (exists_at (fun x => iprop(<obj> (Φ x))) i).mp.trans
    (exists_elim fun x => forall_intro fun k =>
      (forall_elim k).trans ((exists_intro x).trans (exists_at Φ k).mpr))

theorem objectively_and : iprop(<obj> (P ∧ Q)) ⊣⊢ iprop(<obj> P ∧ <obj> Q) :=
  ⟨fun _ => and_intro (forall_mono fun _ => and_elim_l) (forall_mono fun _ => and_elim_r),
   fun _ => forall_intro fun k =>
     and_intro (and_elim_l.trans (forall_elim k)) (and_elim_r.trans (forall_elim k))⟩

theorem objectively_or : iprop(<obj> P ∨ <obj> Q) ⊢ iprop(<obj> (P ∨ Q)) :=
  fun _ => or_elim (forall_mono fun _ => or_intro_l) (forall_mono fun _ => or_intro_r)

theorem objectively_sep_2 : iprop(<obj> P ∗ <obj> Q) ⊢ iprop(<obj> (P ∗ Q)) :=
  fun _ => forall_intro fun k => sep_mono (forall_elim k) (forall_elim k)

theorem objectively_sep [BIIndexBottom I] : iprop(<obj> (P ∗ Q)) ⊣⊢ iprop(<obj> P ∗ <obj> Q) :=
  ⟨fun _ => (forall_elim BIIndexBottom.bot).trans
     (sep_mono (forall_intro fun j => P.mono (BIIndexBottom.bot_le j))
       (forall_intro fun j => Q.mono (BIIndexBottom.bot_le j))),
   objectively_sep_2⟩

theorem objectively_emp : iprop(<obj> (emp : MonPred I PROP)) ⊣⊢ iprop(emp) :=
  ⟨fun i => forall_elim i, fun _ => forall_intro fun _ => .rfl⟩

theorem objectively_pure {φ : Prop} : iprop(<obj> (⌜φ⌝ : MonPred I PROP)) ⊣⊢ iprop(⌜φ⌝) :=
  ⟨fun i => forall_elim i, fun _ => forall_intro fun _ => .rfl⟩

/-! ### The `<subj>` modality -/

theorem subjectively_mono (h : P ⊢ Q) : iprop(<subj> P) ⊢ iprop(<subj> Q) :=
  fun _ => exists_mono fun j => h j

theorem subjectively_intro : P ⊢ iprop(<subj> P) := fun i => exists_intro i

theorem subjectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    iprop(<subj> (∀ x, Φ x)) ⊢ iprop(∀ x, <subj> (Φ x)) :=
  fun i => (forall_intro fun x => exists_elim fun k =>
    ((forall_at Φ k).mp.trans (forall_elim x)).trans (exists_intro k)).trans
      (forall_at (fun x => iprop(<subj> (Φ x))) i).mpr

theorem subjectively_and : iprop(<subj> (P ∧ Q)) ⊢ iprop(<subj> P ∧ <subj> Q) :=
  fun _ => and_intro (exists_mono fun _ => and_elim_l) (exists_mono fun _ => and_elim_r)

theorem subjectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    iprop(<subj> (∃ x, Φ x)) ⊣⊢ iprop(∃ x, <subj> (Φ x)) :=
  ⟨fun i => (exists_elim fun k => (exists_at Φ k).mp.trans (exists_elim fun x =>
      exists_intro' x (exists_intro k))).trans
        (exists_at (fun x => iprop(<subj> (Φ x))) i).mpr,
   fun i => (exists_at (fun x => iprop(<subj> (Φ x))) i).mp.trans
      (exists_elim fun x => exists_elim fun k =>
        ((exists_intro x).trans (exists_at Φ k).mpr).trans (exists_intro k))⟩

theorem subjectively_or : iprop(<subj> (P ∨ Q)) ⊣⊢ iprop(<subj> P ∨ <subj> Q) :=
  ⟨fun _ => exists_elim fun k => or_mono (exists_intro k) (exists_intro k),
   fun _ => or_elim (exists_mono fun _ => or_intro_l) (exists_mono fun _ => or_intro_r)⟩

theorem subjectively_sep : iprop(<subj> (P ∗ Q)) ⊢ iprop(<subj> P ∗ <subj> Q) :=
  fun _ => exists_elim fun k => sep_mono (exists_intro k) (exists_intro k)

theorem subjectively_idemp : iprop(<subj> <subj> P) ⊣⊢ iprop(<subj> P) :=
  ⟨fun _ => exists_elim fun _ => .rfl, fun i => exists_intro i⟩

/-! ### `Objective` predicates: `<obj>`/`<subj>` collapse, and closure instances -/

theorem objective_objectively (P : MonPred I PROP) [Objective P] : P ⊢ iprop(<obj> P) :=
  fun i => forall_intro fun k => objective_at i k

theorem objective_subjectively (P : MonPred I PROP) [Objective P] : iprop(<subj> P) ⊢ P :=
  fun i => exists_elim fun k => objective_at k i

instance pure_objective {φ : Prop} : Objective (iprop(⌜φ⌝) : MonPred I PROP) := ⟨fun _ _ => .rfl⟩
instance emp_objective : Objective (iprop(emp) : MonPred I PROP) := ⟨fun _ _ => .rfl⟩
instance objectively_objective : Objective iprop(<obj> P) := ⟨fun _ _ => .rfl⟩
instance subjectively_objective : Objective iprop(<subj> P) := ⟨fun _ _ => .rfl⟩

instance and_objective [Objective P] [Objective Q] : Objective iprop(P ∧ Q) :=
  ⟨fun i j => and_mono (objective_at i j) (objective_at i j)⟩
instance or_objective [Objective P] [Objective Q] : Objective iprop(P ∨ Q) :=
  ⟨fun i j => or_mono (objective_at i j) (objective_at i j)⟩
instance sep_objective [Objective P] [Objective Q] : Objective iprop(P ∗ Q) :=
  ⟨fun i j => sep_mono (objective_at i j) (objective_at i j)⟩
instance persistently_objective [Objective P] : Objective iprop(<pers> P) :=
  ⟨fun i j => persistently_mono (objective_at i j)⟩

instance forall_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective iprop(∀ x, Φ x) :=
  ⟨fun i j => ((forall_at Φ i).mp.trans (forall_mono fun _ => objective_at i j)).trans
    (forall_at Φ j).mpr⟩
instance exists_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective iprop(∃ x, Φ x) :=
  ⟨fun i j => ((exists_at Φ i).mp.trans (exists_mono fun _ => objective_at i j)).trans
    (exists_at Φ j).mpr⟩

instance impl_objective [Objective P] [Objective Q] : Objective iprop(P → Q) := ⟨by
  intro i j
  refine forall_intro fun k => imp_intro <| and_elim_l.trans ?_
  refine (forall_elim i).trans ?_
  refine (pure_imp_elim (refl : I.rel i i)).trans ?_
  exact imp_mono (objective_at k i) (objective_at i k)⟩
instance wand_objective [Objective P] [Objective Q] : Objective iprop(P -∗ Q) := ⟨by
  intro i j
  refine forall_intro fun k => imp_intro <| and_elim_l.trans ?_
  refine (forall_elim i).trans ?_
  refine (pure_imp_elim (refl : I.rel i i)).trans ?_
  exact wand_mono (objective_at k i) (objective_at i k)⟩

-- The pointwise modalities lift objectivity directly (`(▷ P).holds i = ▷ (P i)`, etc.).
instance later_objective [Objective P] : Objective iprop(▷ P) :=
  ⟨fun i j => later_mono (objective_at i j)⟩
instance except0_objective [Objective P] : Objective iprop(◇ P) :=
  ⟨fun i j => except0_mono (objective_at i j)⟩
instance laterN_objective [Objective P] {n : Nat} : Objective iprop(▷^[n] P) := by
  induction n with
  | zero => exact inferInstanceAs (Objective P)
  | succ n ih => exact later_objective (P := iprop(▷^[n] P))
instance bupd_objective [BIUpdate PROP] [Objective P] : Objective iprop(|==> P) :=
  ⟨fun i j => BIUpdate.mono (objective_at i j)⟩
instance fupd_objective [BIFUpdate PROP] {E1 E2 : CoPset} [Objective P] :
    Objective iprop(|={E1,E2}=> P) :=
  ⟨fun i j => BIFUpdate.mono (objective_at i j)⟩

end objectively

/-! ### Lifting `Persistent`/`Absorbing`/`Affine` through the (pointwise) index

`<pers>`, `<absorb>`, `emp` are all pointwise on `MonPred`, so each of these classes holds for `P`
iff it holds at every index. Mirrors Rocq's `monPred_persistent`/`absorbing`/`affine` and the
`monPred_at_*` reverse projections. -/

theorem monPred_persistent {P : MonPred I PROP} (h : ∀ i, Persistent (P i)) : Persistent P :=
  ⟨fun i => (h i).persistent⟩
theorem monPred_absorbing {P : MonPred I PROP} (h : ∀ i, Absorbing (P i)) : Absorbing P :=
  ⟨fun i => (h i).absorbing⟩
theorem monPred_affine {P : MonPred I PROP} (h : ∀ i, Affine (P i)) : Affine P :=
  ⟨fun i => (h i).affine⟩

instance monPred_at_persistent {P : MonPred I PROP} [Persistent P] (i : I) : Persistent (P i) :=
  ⟨(Persistent.persistent (P := P)) i⟩
instance monPred_at_absorbing {P : MonPred I PROP} [Absorbing P] (i : I) : Absorbing (P i) :=
  ⟨(Absorbing.absorbing (P := P)) i⟩
instance monPred_at_affine {P : MonPred I PROP} [Affine P] (i : I) : Affine (P i) :=
  ⟨(Affine.affine (P := P)) i⟩

/-! ### `Persistent`/`Absorbing`/`Affine` for `<obj>`/`<subj>`

At index `i`, `<obj> P` is `∀ j, P j` and `<subj> P` is `∃ j, P j` (constant in `i`), so these reduce
to the corresponding PROP-level quantifier facts. `<obj>` persistence needs `BiPersistentlyForall`
(to push `<pers>` through `∀`), exactly as in Rocq. -/

instance objectively_persistent {P : MonPred I PROP} [BIPersistentlyForall PROP] [Persistent P] :
    Persistent iprop(<obj> P) :=
  ⟨fun _ => (forall_mono fun j => Persistent.persistent (P := P j)).trans persistently_forall.mpr⟩
instance objectively_absorbing {P : MonPred I PROP} [Absorbing P] : Absorbing iprop(<obj> P) :=
  ⟨fun _ => absorbingly_forall_1.trans (forall_mono fun j => Absorbing.absorbing (P := P j))⟩
instance objectively_affine {P : MonPred I PROP} [Affine P] : Affine iprop(<obj> P) :=
  ⟨fun i => (forall_elim i).trans (Affine.affine (P := P i))⟩

instance subjectively_persistent {P : MonPred I PROP} [Persistent P] : Persistent iprop(<subj> P) :=
  ⟨fun _ => (exists_mono fun j => Persistent.persistent (P := P j)).trans persistently_exists.mpr⟩
instance subjectively_absorbing {P : MonPred I PROP} [Absorbing P] : Absorbing iprop(<subj> P) :=
  ⟨fun _ => absorbingly_exists.1.trans (exists_mono fun j => Absorbing.absorbing (P := P j))⟩
instance subjectively_affine {P : MonPred I PROP} [Affine P] : Affine iprop(<subj> P) :=
  ⟨fun _ => exists_elim fun j => Affine.affine (P := P j)⟩

end MonPred

namespace MonPred

-- The `Sbi`-dependent instances live here, in a scope with *only* `[Sbi PROP]` (and no independent
-- `[BI PROP]`). This is essential: under the namespace-level `variable [BI PROP]` above, `MonPred I
-- PROP` would carry a second `BI PROP` distinct from `Sbi.toBI`, so lemmas like `forall_mono` would
-- synthesize the section `BI` while the PROP-level `Sbi` laws live over `Sbi.toBI` — an instance
-- diamond. With only `[Sbi PROP]` in scope, `MonPred I PROP`'s `BI` resolves to `Sbi.toBI` and the
-- pointwise/objective field proofs line up. Each field mirrors Rocq's `monPred_sbi_mixin`:
--   `(siPure Pi) i = <si_pure> Pi`   (constant in `i`)
--   `siEmpValid P  = <si_emp_valid> (∀ i, P i)`   (validity of the *objective* `∀ i, P i`).
variable {I : BIIndex} {PROP : Type _} [Sbi PROP]

-- Internal equality of `MonPred`s is pointwise: `MonPred`'s `Dist` is `∀ i, P i ≡{n}≡ Q i`, which is
-- exactly the function `Dist` on `holds`. So `fun_ext_internalEq` (on `holds`) plus the
-- definitional `Dist` match (`internalEq_entails`) give the `∀ i`-introduction direction we need for
-- `prop_ext_siEmpValid`. Mirrors the `sig_equivI`/`discrete_fun_equivI` step in Rocq's
-- `monPred_sbi_prop_ext_mixin`.
theorem internalEq_2 {P Q : MonPred I PROP} :
    iprop(∀ i, SiProp.internalEq (P i) (Q i)) ⊢ SiProp.internalEq P Q :=
  (SiProp.fun_ext_internalEq P.holds Q.holds).trans
    ((SiProp.internalEq_entails P.holds Q.holds P Q).mpr fun _ h => h)

instance : Sbi (MonPred I PROP) where
  siPure_ne := ⟨fun {_ _ _} h _ => Sbi.siPure_ne.ne h⟩
  siEmpValid_ne := ⟨fun {_ _ _} h => Sbi.siEmpValid_ne.ne (forall_ne fun i => h i)⟩
  siPure_mono H _ := Sbi.siPure_mono H
  siEmpValid_mono H := Sbi.siEmpValid_mono (forall_mono fun i => H i)
  siEmpValid_siPure :=
    ⟨(Sbi.siEmpValid_mono (forall_elim default)).trans Sbi.siEmpValid_siPure.mp,
     Sbi.siEmpValid_siPure.mpr.trans (Sbi.siEmpValid_mono (forall_intro fun _ => .rfl))⟩
  siPure_siEmpValid i := Sbi.siPure_siEmpValid.trans (persistently_mono (forall_elim i))
  siPure_imp_mpr i := (forall_elim i).trans ((pure_imp_elim refl).trans Sbi.siPure_imp_mpr)
  siPure_sForall_mpr := by
    intro Ψi i
    -- Project at `i`, peel the upclosed `→` at its own index, then apply the PROP-level law.
    refine ((forall_at _ i).mp.trans (forall_mono fun _ => ?_)).trans Sbi.siPure_sForall_mpr
    refine (forall_elim i).trans ?_
    exact pure_imp_elim refl
  persistently_imp_siPure := by
    intro Pi Q i
    -- Peel the upclosed `→` at `i` (`Q` is recovered at other indices `j ⊒ i` by monotonicity),
    -- apply the PROP-level law, then rebuild the upclosed `∀ j` under `<pers>`.
    refine (forall_elim i).trans ?_
    refine (pure_imp_elim refl).trans ?_
    refine Sbi.persistently_imp_siPure.trans (persistently_mono ?_)
    refine forall_intro fun j => imp_intro' <| pure_elim_l fun hr => ?_
    exact imp_mono_r (Q.mono hr)
  siPure_later := ⟨fun _ => Sbi.siPure_later.mp, fun _ => Sbi.siPure_later.mpr⟩
  siPure_absorbing _ := ⟨fun i => (Sbi.siPure_absorbing _).absorbing⟩
  siEmpValid_later_mp := (Sbi.siEmpValid_mono later_forall.mpr).trans Sbi.siEmpValid_later_mp
  siEmpValid_affinely_mpr :=
    Sbi.siEmpValid_affinely_mpr.trans
      (Sbi.siEmpValid_mono (forall_intro fun j => and_mono_r (forall_elim j)))
  prop_ext_siEmpValid := by
    intro P Q
    -- Reduce target `internalEq P Q` to `∀ j, internalEq (P j) (Q j)` (`internalEq_2`); at each `j`
    -- peel the upclosed wands of `P ∗-∗ Q` down to `P j ∗-∗ Q j` and apply the PROP-level law.
    refine (forall_intro fun j => ?_).trans internalEq_2
    refine (siEmpValid_mono ?_).trans Sbi.prop_ext_siEmpValid
    refine (forall_elim j).trans (and_mono ?_ ?_)
    · refine (forall_elim j).trans ?_
      exact pure_imp_elim refl
    · refine (forall_elim j).trans ?_
      exact pure_imp_elim refl

-- `<si_pure> Pi` and `■ P` are *objective for any argument*: `(<si_pure> Pi).holds i = <si_pure> Pi`
-- and `(■ P).holds i = <si_pure> (<si_emp_valid> (∀ j, P j))` are both constant in `i` (no `[Objective
-- P]` hypothesis needed). Mirrors Rocq's `si_pure_objective`, `plainly_objective`.
instance si_pure_objective (Pi : SiProp) : Objective (iprop(<si_pure> Pi) : MonPred I PROP) :=
  ⟨fun _ _ => .rfl⟩
instance plainly_objective (P : MonPred I PROP) : Objective iprop(■ P) := ⟨fun _ _ => .rfl⟩

-- Mirrors Rocq's `monPred_sbi_emp_valid_exist`, which needs a bottom index `bot`: instantiate the
-- objective `∀ i` at `bot`, apply PROP's `siEmpValid_sExists_1`, then transport the witness `q = P
-- bot` back to `<si_emp_valid> P` using `P bot ⊢ ∀ i, P i` (from `bot ≤ i`).
instance [SbiEmpValidExist PROP] [BIIndexBottom I] : SbiEmpValidExist (MonPred I PROP) where
  siEmpValid_sExists_1 Ψ := by
    refine ((siEmpValid_mono (forall_elim BIIndexBottom.bot)).trans
      ((siEmpValid_mono (sExists_at Ψ BIIndexBottom.bot).mp).trans
        (SbiEmpValidExist.siEmpValid_sExists_1 _))).trans ?_
    exact exists_elim fun p => pure_elim_l fun ⟨P, hP, hbot⟩ =>
      exists_intro' P (and_intro (pure_intro hP)
        (hbot ▸ siEmpValid_mono (forall_intro fun i => P.mono (BIIndexBottom.bot_le i))))

instance [BIUpdate PROP] [BIBUpdateSbi PROP] : BIBUpdateSbi (MonPred I PROP) where
  bupd_si_pure Pi := fun _ => BIBUpdateSbi.bupd_si_pure Pi

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
