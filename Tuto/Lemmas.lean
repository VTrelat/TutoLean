import LeanSearchClient
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Tuto.Extra

variable {α : Type}

namespace Lst

@[simp] theorem append_is_append {u : Lst α} {v : Lst α} : (u ++ v) = u.append v := rfl

theorem concat_eq_append (v : Lst α) (a : α) : concat v a = v ++ (cons a nil) := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    rw [concat, ih]
    congr

theorem append_assoc (u v w : Lst α) : u ++ (v ++ w) = u ++ v ++ w  := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    dsimp at ih ⊢
    rw [ih]

@[simp] theorem append_nil (v : Lst α) : v ++ nil (α := α) = v := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    dsimp at ih ⊢
    rw [ih]

theorem rev_append {u : Lst α} {v : Lst α} : (u ++ v).rev = v.rev ++ u.rev := by
  induction u with
  | nil =>
    dsimp only [rev, append]
    rw [append_nil v.rev]
    dsimp
  | cons x u ih =>
    dsimp at ih ⊢
    rw [ih, concat_eq_append, concat_eq_append]
    dsimp [← append_is_append]
    rw [← append_assoc]

theorem rev_rev {v : Lst α} : v.rev.rev = v := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    rw [rev, concat_eq_append, rev_append, ih, rev, concat_eq_append]
    dsimp

@[simp]
theorem mem_cons {xs : Lst α} {x y : α} : y ∈ xs.cons x ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [instMembership, or_false]
  | cons c cs ih =>
    dsimp [instMembership]
    constructor <;>
    · rintro (rfl | rfl | h)
      · left; rfl
      · right; left; rfl
      · right; right; exact h

theorem toSet_mem_iff {xs : Lst α} {x : α} : x ∈ xs ↔ x ∈ xs.toSet := by
  constructor
  · intro mem_xs
    induction xs with
    | nil => dsimp [Lst.instMembership] at mem_xs
    | cons c cs ih =>
      rw [toSet, Set.mem_union]
      rcases mem_cons.mp mem_xs with rfl | h
      · left
        rfl
      · right
        exact ih h
  · intro mem_set
    induction xs with
    | nil => nomatch mem_set
    | cons c cs ih =>
      rw [toSet, Set.mem_union] at mem_set
      rcases mem_set with rfl | h
      · left; rfl
      · right; exact ih h
end Lst

namespace Vec

@[simp]
theorem mem_cons {n : Nat} {v : Vec α n} {x y : α} : y ∈ v.cons x ↔ x = y ∨ y ∈ v := by
  induction v with
  | nil => simp [instMembership, or_false]
  | cons c cs ih =>
    dsimp [instMembership]
    constructor <;>
    · rintro (rfl | rfl | h)
      · left; rfl
      · right; left; rfl
      · right; right; exact h

theorem toSet_mem_iff {n : Nat} {v : Vec α n} {x : α} : x ∈ v ↔ x ∈ v.toSet := by
  constructor
  · intro mem_v
    induction v with
    | nil => nomatch mem_v
    | cons c cs ih =>
      rw [toSet, Set.mem_union]
      rcases mem_cons.mp mem_v with rfl | h
      · left; rfl
      · right; exact ih h
  · intro mem_set
    induction v with
    | nil => nomatch mem_set
    | cons c cs ih =>
      rw [toSet, Set.mem_union] at mem_set
      rcases mem_set with rfl | h
      · left; rfl
      · right; exact ih h
end Vec

theorem Vec.toLst_size {α : Type} {n : Nat} (v : Vec α n) : v.toLst.size = n := by
  induction v with
  | nil => rfl
  | @cons n x xs ih =>
    rw [Vec.toLst, Lst.size, ih, Nat.add_comm]

theorem Lst.toVec_toLst {α : Type} (v : Lst α) : v.toVec.toLst = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => rw [toVec, Vec.ofLst, Vec.toLst, ih]

theorem Vec.toLst_toVec {α : Type} {n : Nat} (v : Vec α n) : v.toLst.toVec = Vec.toLst_size _ ▸ v := by
  induction v with
  | nil => rfl
  | @cons n x xs ih =>
    unfold Lst.toVec at ih
    rw [Eq.rec_eq_cast, eq_cast_iff_heq, Lst.toVec, Vec.toLst, Vec.ofLst, ih]
    push_cast
    congr
    · apply toLst_size
    · apply eqRec_heq

theorem Vec_Lst_ext_iff {α : Type} {n : Nat} (v : Vec α n) (l : Lst α) : (∀ x, x ∈ v ↔ x ∈ l) ↔ v.toSet = l.toSet := by
  constructor
  · intro h
    ext1 z
    rw [← Vec.toSet_mem_iff, ← Lst.toSet_mem_iff, h]
  · intro h x
    rw [Vec.toSet_mem_iff, Lst.toSet_mem_iff, h]
