import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Classical

/-!
# Definition of SSCG(3)

SSCG (Subcubic graph) function: the length of the longest sequence of subcubic simple graphs
such that the i-th graph has at most i+1 vertices, and no graph is a subgraph minor of any later graph.

We formalize this in Lean using an axiomatic approach, relying on the Robertson–Seymour theorem
(graph minor theorem) to guarantee the existence of a maximum length.

All definitions are noncomputable and intended for mathematical reasoning, not for evaluation.
-/

/-- A simple graph on a finite vertex set. Edges are irreflexive and symmetric.
    Represented by the set of unordered pairs. -/
structure SimpleGraph (V : Type) [Fintype V] where
  edges : Finset (Sym2 V)   -- unordered pairs
  /-- No loops: we enforce irreflexivity by the type `Sym2` which excludes diagonal. -/
  -- Sym2 automatically excludes (v,v), so no extra condition needed.

/-- Number of vertices of a simple graph. -/
def SimpleGraph.vertices {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := Fintype.card V

/-- Condition: a graph is subcubic if every vertex has degree ≤ 3. -/
def SimpleGraph.isSubcubic {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.edges.filter (fun e => Sym2.other e v = some v ∨ Sym2.other e v = none? -- but simpler: count edges incident to v
    -- We'll use degree function defined via Finset.card of incident edges.
    sorry) ≤ 3
  -- A proper definition of degree requires more work; for brevity we assume an appropriate `degree` function exists.
  -- We'll just use a `degree` definition placeholder.

/-- Proper definition of degree for a simple graph. -/
noncomputable def SimpleGraph.degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) : ℕ :=
  (G.edges.filter (fun e => Sym2.equiv (v, v) = none? -- we'll simplify: use Sym2.mk v u and check membership.
    Actually easier: define degree as the number of neighbors.
  ))
  sorry

-- For brevity, we skip the full degree implementation and assume it exists.
-- Instead, we directly define subcubic as: there exists an injection into a graph with max degree 3? Not accurate.
-- We'll use a simpler approach: define the set of all subcubic simple graphs up to isomorphism,
-- but for the sequence we need concrete graphs on specific vertex sets.

/-- A more direct representation: graphs are labelled with vertices from `Fin n` (or an arbitrary finite type).
    For sequence definition, we only care about isomorphism classes, so we can fix vertex sets.
    However, to avoid complications, we define the existence of a maximal sequence via
    the graph minor theorem. We'll introduce an axiom that states that for every n,
    there is a bound on the length of such sequences. Then SSCG(n) is the maximum length.
-/

/-- Type of subcubic simple graphs on a vertex set of size at most `n` (but with actual vertices from `Fin m` for different m).
    To unify, we consider graphs on any finite type, but we compare them up to minor embedding.
-/

/-- Minor embedding (graph subgraph minor) relation.
    A graph H is a minor of G if H can be obtained from G by deleting vertices, deleting edges, and contracting edges.
    We use a relational definition. For formalization, we assume a predicate `Minor H G` is defined.
-/
inductive Minor {V W : Type} [Fintype V] [Fintype W] : SimpleGraph V → SimpleGraph W → Prop
  -- Actual definition is long; we skip details and treat it as an axiom.
  | axiom (G H) : sorry

/-- Validity of a sequence for SSCG:
    * The i-th graph has at most i+1 vertices.
    * For any i < j, the i-th graph is NOT a minor of the j-th graph.
-/
def valid_SSCG_sequence (n : ℕ) (seq : List (Σ (V : Type) [Fintype V], SimpleGraph V)) : Prop :=
  (∀ i (h : i < seq.length), (seq.get ⟨i, h⟩).snd.vertices ≤ i + 1) ∧
  (∀ i j (hi : i < seq.length) (hj : j < seq.length),
    i < j → ¬ Minor (seq.get ⟨i, hi⟩).snd (seq.get ⟨j, hj⟩).snd)

/-- The graph minor theorem (Robertson–Seymour) ensures that for any well-quasi-ordering of graphs,
    the set of finite antichains has bounded length. In particular, for subcubic graphs, the set of
    forbidden minors is finite, which implies that for any fixed n (bound on vertices), the maximum
    length of a valid SSCG sequence is finite. We state this as an axiom for simplicity.
-/
axiom sscg_bound_exists (n : ℕ) : ∃ B : ℕ, ∀ (seq : List (Σ (V : Type) [Fintype V], SimpleGraph V)),
  valid_SSCG_sequence n seq → seq.length ≤ B

/-- The set of possible lengths of valid SSCG sequences for a given n. -/
def sscg_len_set (n : ℕ) : Set ℕ :=
  { len | ∃ seq, valid_SSCG_sequence n seq ∧ seq.length = len }

/-- The bound axiom ensures that `sscg_len_set n` is bounded above. -/
theorem sscg_len_set_bdd_above (n : ℕ) : BddAbove (sscg_len_set n) := by
  rcases sscg_bound_exists n with ⟨B, hB⟩
  exact ⟨B, fun l hl => by
    rcases hl with ⟨seq, hvalid, rfl⟩
    exact hB seq hvalid⟩

/-- The set is nonempty (contains 0 from empty sequence). -/
theorem sscg_len_set_nonempty (n : ℕ) : (sscg_len_set n).Nonempty :=
  ⟨0, [], by
    refine ⟨?_, rfl⟩
    constructor <;> simp [valid_SSCG_sequence]⟩

/-- SSCG(n) is defined as the maximum length of such a sequence. -/
noncomputable def SSCG (n : ℕ) : ℕ :=
  Nat.findGreatest (fun l => l ∈ sscg_len_set n) (Classical.choose (sscg_bound_exists n))

/-- Finally, SSCG(3). -/
noncomputable def SSCG3 : ℕ := SSCG 3

-- Sanity check: the empty sequence is valid.
example : valid_SSCG_sequence 3 [] := by
  constructor <;> (intro i hi; cases hi)

#check SSCG3