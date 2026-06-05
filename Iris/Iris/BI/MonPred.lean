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
export BIIndexBottom (bot_le)

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

def fupd [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) : MonPred I PROP where
  holds i := iprop(|={E1,E2}=> P i)
  mono h_rel := BIFUpdate.mono (P.mono h_rel)

def siPure [Sbi PROP] (Pi : SiProp) : MonPred I PROP where
  holds _ := iprop(<si_pure> Pi)
  mono _ := .rfl

def siEmpValid [Sbi PROP] (P : MonPred I PROP) : SiProp :=
  iprop(<si_emp_valid> ∀ i, P i)

instance [BIUpdate PROP] : BUpd (MonPred I PROP) := ⟨MonPred.bupd⟩

instance [BIFUpdate PROP] : FUpd (MonPred I PROP) := ⟨MonPred.fupd⟩

instance [Sbi PROP] : SiPure (MonPred I PROP) := ⟨MonPred.siPure⟩

instance [Sbi PROP] : SiEmpValid (MonPred I PROP) := ⟨MonPred.siEmpValid⟩

instance [BIUpdate PROP] : NonExpansive BUpd.bupd (α := MonPred I PROP) :=
  ⟨fun {_ _ _} h i => BIUpdate.bupd_ne.ne (h i)⟩

instance [BIFUpdate PROP] {E1 E2 : CoPset} :
    NonExpansive (FUpd.fupd E1 E2 (PROP := MonPred I PROP)) :=
  ⟨fun {_ _ _} h i => BIFUpdate.ne.ne (h i)⟩

theorem sForall_at (Ψ : MonPred I PROP → Prop) i :
    sForall Ψ i ⊣⊢ BI.sForall fun p => ∃ P, Ψ P ∧ P i = p := by
  constructor
  · refine sForall_intro ?_
    rintro _ ⟨P, hP, rfl⟩
    refine (forall_elim P).trans ?_
    exact pure_imp_elim hP
  · refine forall_intro fun P => ?_
    refine imp_intro ?_
    refine pure_elim_r fun hP => ?_
    exact sForall_elim ⟨P, hP, rfl⟩

theorem sExists_at (Ψ : MonPred I PROP → Prop) i :
    sExists Ψ i ⊣⊢ BI.sExists fun p => ∃ P, Ψ P ∧ P i = p := by
  constructor
  · refine exists_elim fun P => ?_
    refine pure_elim_l fun hP => ?_
    exact sExists_intro ⟨P, hP, rfl⟩
  · refine sExists_elim ?_
    rintro _ ⟨P, hP, rfl⟩
    refine exists_intro' P ?_
    exact and_intro (pure_intro hP) .rfl

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
    refine (equiv_iff.mpr (sForall_at Ψ₁ i)).dist.trans ?_
    refine .trans ?_ (equiv_iff.mpr (sForall_at Ψ₂ i)).symm.dist
    refine sForall_ne ⟨?_, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨Q, hQ, hPQ⟩ := h₁ P hP
      exact ⟨Q i, ⟨Q, hQ, rfl⟩, hPQ i⟩
    · rintro _ ⟨Q, hQ, rfl⟩
      obtain ⟨P, hP, hPQ⟩ := h₂ Q hQ
      exact ⟨P i, ⟨P, hP, rfl⟩, hPQ i⟩
  sExists_ne {n Ψ₁ Ψ₂} h i := by
    obtain ⟨h₁, h₂⟩ := h
    refine (equiv_iff.mpr (sExists_at Ψ₁ i)).dist.trans ?_
    refine .trans ?_ (equiv_iff.mpr (sExists_at Ψ₂ i)).symm.dist
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
    refine (forall_elim iprop(⌜Ψ P⌝ → ▷ P)).trans ?_; dsimp
    refine (pure_imp_elim ⟨P, rfl⟩).trans ?_
    refine (forall_elim i).trans ?_; dsimp
    refine (pure_imp_elim refl).trans ?_; dsimp
    -- Key step: `(⌜Ψ P⌝ → ▷ P i) ⊢ ▷ (⌜Ψ P⌝ → P i)`. A pure implication `⌜φ⌝ → R`
    -- is equivalent to the BI-forall `∀ _ : φ, R` indexed by proofs of `φ`.
    refine .trans (forall_intro pure_imp_elim) ?_
    refine later_forall_2.trans ?_
    refine later_mono ?_
    refine imp_intro ?_
    exact pure_elim_r forall_elim
  later_sExists_false {Ψ} i := by
    refine (later_mono (sExists_at Ψ i).mp).trans ?_
    refine later_sExists_false.trans ?_
    refine or_mono .rfl ?_
    refine exists_elim fun p => ?_
    refine pure_elim_l ?_
    rintro ⟨P, hP, rfl⟩
    refine exists_intro' iprop(⌜Ψ P⌝ ∧ ▷ P) ?_; dsimp
    refine and_intro (pure_intro ⟨P, rfl⟩) ?_
    exact and_intro (pure_intro hP) .rfl
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
  intro := fun _ => BIUpdate.intro
  mono H := fun i => BIUpdate.mono (H i)
  trans := fun _ => BIUpdate.trans
  frame_r := fun _ => BIUpdate.frame_r

-- BIFUpd instance

instance [BIFUpdate PROP] : BIFUpdate (MonPred I PROP) where
  subset h := fun _ => BIFUpdate.subset h
  except0 := fun _ => BIFUpdate.except0
  mono H := fun i => BIFUpdate.mono (H i)
  trans := fun _ => BIFUpdate.trans
  mask_frame_r' h := fun i =>
    (BIFUpdate.mono (PROP := PROP) ((forall_elim i).trans (pure_imp_elim refl))).trans
      (BIFUpdate.mask_frame_r' h)
  frame_r := fun _ => BIFUpdate.frame_r

-- BI Lob instance

instance [BILoeb PROP] : BILoeb (MonPred I PROP) where
  loeb_weak h := fun i => BILoeb.loeb_weak (h i)

-- BIPositive instance

instance [BIPositive PROP] : BIPositive (MonPred I PROP) where
  affinely_sep_l := fun _ => BIPositive.affinely_sep_l

-- BIAffine instance

instance [BIAffine PROP] : BIAffine (MonPred I PROP) where
  affine _ := ⟨fun _ => Affine.affine⟩

-- BIPersistentlyForall instance

instance [BIPersistentlyForall PROP] : BIPersistentlyForall (MonPred I PROP) where
  persistently_sForall_2 Ψ := by
    refine fun i => .trans ?_ (persistently_mono (sForall_at Ψ i).mpr)
    refine .trans ?_ (BIPersistentlyForall.persistently_sForall_2 (fun q => ∃ P, Ψ P ∧ P i = q))
    refine forall_intro fun q => imp_intro <| pure_elim_r ?_
    rintro ⟨P, hP, rfl⟩
    exact (show (∀ p, ⌜Ψ p⌝ → <pers> p) ⊢ <pers> P from
      (forall_elim P).trans (pure_imp_elim hP)) i

-- BIPureForall instance
-- can always be proven using classical logic, so no need for such instance

-- BILaterContractive instance

instance [BILaterContractive PROP] : BILaterContractive (MonPred I PROP) where
  distLater_dist h i :=
    (BILaterContractive.toContractive (PROP := PROP)).distLater_dist fun m hm => h m hm i

-- BIEmbedEmp instance

-- BIEmbedLater instance

-- BIBUpdFUpd instance

instance [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] :
    BIUpdateFUpdate (MonPred I PROP) where
  fupd_of_bupd := fun _ => BIUpdateFUpdate.fupd_of_bupd

-- BIEmbedBUpd instance
-- BIEmbedFUpd instance

-- SbiEmpValidExist instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiEmbedSbi instance

-- BiBUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- BiFUpdSbi instance: see the `[Sbi PROP]` block after `end MonPred` below.

-- class Objective (for what?)
-- bi_facts
-- <obj> and <surj> notations

end bidefs

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
  siPure_sForall_mpr := sorry
  persistently_imp_siPure := sorry
  siPure_later := ⟨fun _ => Sbi.siPure_later.mp, fun _ => Sbi.siPure_later.mpr⟩
  siPure_absorbing _ := ⟨fun i => (Sbi.siPure_absorbing _).absorbing⟩
  siEmpValid_later_mp := (Sbi.siEmpValid_mono later_forall.mpr).trans Sbi.siEmpValid_later_mp
  siEmpValid_affinely_mpr :=
    Sbi.siEmpValid_affinely_mpr.trans
      (Sbi.siEmpValid_mono (forall_intro fun j => and_mono_r (forall_elim j)))
  prop_ext_siEmpValid := sorry

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
        (hbot ▸ siEmpValid_mono (forall_intro fun i => P.mono (bot_le i))))

instance [BIUpdate PROP] [BIBUpdateSbi PROP] : BIBUpdateSbi (MonPred I PROP) where
  bupd_si_pure Pi := fun _ => BIBUpdateSbi.bupd_si_pure Pi

-- NO `BIFUpdatePlainly` instance for `MonPred`. Standard Rocq Iris (`iris/bi/monpred.v`) gives
-- MonPred no `BiFUpdPlainly` instance either, and the laws genuinely fail in the general case:
--
--   * MonPred's plainly is *objective*: `■ P = <si_pure> <si_emp_valid> P`, so at every index
--     `(■ P).holds i = ■_PROP (∀ j, P j)` — it discards the index and asserts the validity of the
--     all-index conjunction `∀ j, P j`.
--   * MonPred's `fupd` is *index-local*: `(|={E1,E2}=> P).holds i = |={E1,E2}=> P.holds i`, so a
--     fupd at index `i` can only ever see index `i`.
--
-- A law like `fupd_plainly_sForall_2 : (|={E}=> ■ sForall Φ) ⊢ |={E}=> sForall Φ` reduces, at index
-- `i`, to recovering the *local* `(sForall Φ) i` from `■_PROP (∀ j, (sForall Φ) j)`. That fails on
-- two counts: (1) stripping the `■` needs `[Absorbing _]` (`plainly_elim` is not general), and
-- (2) the objective `∀ j` that `si_emp_valid` inserts sits between the plainly and the connective,
-- so PROP's own `BIFUpdatePlainly` laws (which expect `■ sForall …`) no longer match. Intuitively a
-- single index's fupd can neither *produce* the all-index witness `■ P` demands nor *consume* it down
-- to one index. Recovering an instance would require a strictly weaker statement with extra
-- hypotheses (e.g. `[BIAffine PROP]` for absorbingness, and/or `[BIIndexBottom I]`).

end MonPred
