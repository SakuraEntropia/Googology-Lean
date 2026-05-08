import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Classical

/-!
# Definition of TREE(3)

This file formalizes the definition of the TREE function, based on finite labeled trees and the homeomorphic embedding relation.
The label set is {0,1,2} (i.e., Fin 3).
Kruskal's tree theorem guarantees that for a given number of labels, the lengths of all valid sequences have a maximum,
and we define TREE(n) as that maximum.

Note: Since the numerical value of TREE(3) is astronomically large and cannot be computed in Lean, only its qualitative definition is given.
-/

/-- A finite labeled tree. The label type is `Label`. -/
inductive LabeledTree (Label : Type) : Type
  | node : Label → List (LabeledTree Label) → LabeledTree Label

/-- The size of a tree (total number of nodes). -/
def LabeledTree.size {Label : Type} : LabeledTree Label → ℕ
  | .node _ children => 1 + (children.map size).sum

/-- Specialization to trees with label set Fin k. -/
abbrev Tree (k : ℕ) := LabeledTree (Fin k)

/-- Homeomorphic embedding relation between trees (embedding as subtrees preserving tree structure, ignoring child order).
    Definition follows the standard recursion: there exists an injection from the children of `s` to the children of `t`
    such that corresponding children also satisfy the embedding, and the root labels are equal. -/
inductive HomeomorphicEmbedding {Label : Type} : LabeledTree Label → LabeledTree Label → Prop
  /-- Identity embedding -/
  | refl (t : LabeledTree Label) : HomeomorphicEmbedding t t
  /-- Node embedding: root labels are equal, and there exists an injective mapping of children. -/
  | node {x y : Label} {cx cy : List (LabeledTree Label)} (hx : x = y)
      (f : ℕ → ℕ) (inj : Function.Injective f)
      (hf : ∀ i (h : i < cy.length),
        let ch := cy.get ⟨i, h⟩
        HomeomorphicEmbedding ch (cx.get ⟨f i, _⟩)) :
      HomeomorphicEmbedding (LabeledTree.node x cx) (LabeledTree.node y cy)

-- Auxiliary lemma: in the `node` constructor, we need to prove that `f i` is within bounds of `cx`.
-- A more rigorous version is provided below:
/-- Rigorous definition of homeomorphic embedding. -/
inductive HomeomorphicEmbedding' {Label : Type} : LabeledTree Label → LabeledTree Label → Prop
  | refl (t : LabeledTree Label) : HomeomorphicEmbedding' t t
  | node {x y : Label} {cx cy : List (LabeledTree Label)} (hx : x = y)
      (f : ℕ → ℕ) (inj : Function.Injective f)
      (h_dom : ∀ i (h : i < cy.length), f i < cx.length)
      (h_emb : ∀ i (h : i < cy.length),
        HomeomorphicEmbedding' (cy.get ⟨i, h⟩) (cx.get ⟨f i, h_dom i h⟩)) :
      HomeomorphicEmbedding' (LabeledTree.node x cx) (LabeledTree.node y cy)

-- Use the rigorous version
attribute [instance] HomeomorphicEmbedding'

/-- Validity of a sequence:
    * The i-th tree has size ≤ i+1
    * For any i < j, the i-th tree cannot be homeomorphically embedded into the j-th tree -/
def valid_TREE_sequence {k : ℕ} (seq : List (Tree k)) : Prop :=
  (∀ i (h : i < seq.length), (seq.get ⟨i, h⟩).size ≤ i + 1) ∧
  (∀ i j (hi : i < seq.length) (hj : j < seq.length),
    i < j → ¬ HomeomorphicEmbedding (seq.get ⟨i, hi⟩) (seq.get ⟨j, hj⟩))

/-- Kruskal's tree theorem (finite label case):
    For any finite label set, there is a uniform bound on the length of all sequences satisfying the above conditions.
    We introduce it as an axiom because its proof is beyond the scope of this file. -/
axiom kruskal_theorem (k : ℕ) : ∃ B : ℕ, ∀ (seq : List (Tree k)), valid_TREE_sequence seq → seq.length ≤ B

/-- The set of lengths of all valid sequences. -/
def len_set (k : ℕ) : Set ℕ :=
  { len | ∃ seq : List (Tree k), valid_TREE_sequence seq ∧ seq.length = len }

/-- By Kruskal's theorem, this set is bounded above. -/
theorem len_set_bdd_above (k : ℕ) : BddAbove (len_set k) := by
  rcases kruskal_theorem k with ⟨B, hB⟩
  exact ⟨B, fun l hl => by
    rcases hl with ⟨seq, hvalid, rfl⟩
    exact hB seq hvalid⟩

/-- `len_set k` is nonempty (it contains 0 from the empty sequence, which is trivially valid). -/
theorem len_set_nonempty (k : ℕ) : (len_set k).Nonempty :=
  ⟨0, [], by
    constructor
    · simp [valid_TREE_sequence]
    · rfl⟩

/-- TREE(k) is defined as the maximum length among all valid sequences. -/
noncomputable def TREE (k : ℕ) : ℕ :=
  Nat.findGreatest (fun l => l ∈ len_set k) (Classical.choose (kruskal_theorem k))

/-- Finally, TREE(3). -/
noncomputable def TREE3 : ℕ := TREE 3

-- Type-checking examples (no computation)
#check @TREE3
#check valid_TREE_sequence (fun (k : ℕ) => (k : ℕ))

-- To test, uncomment the next line; it proves that the empty sequence is valid:
-- example : valid_TREE_sequence (List.nil) := ⟨by simp, by simp⟩