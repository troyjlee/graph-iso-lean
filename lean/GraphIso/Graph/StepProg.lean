module

public import GraphIso.Graph.Ind
public import GraphIso.Luks.MaxBlocksProg

/-!
# Programs of one layer step: the layer string

Programs of the cost language computing the functional models of
`GraphIso/Graph/StepModel.lean`, with their exact results and cost bounds, for graph data of
maximum degree at most three (`∀ u, (nbrs G u).length ≤ 3`):

* `nbLProg`: the neighbours of level `r` (`nbL`), at cost at most `21`;
* `memProg`, `seteqProg`, `adjProg`, `edge3Prog`: membership, set equality, adjacency and the
  edge test of a triple;
* `xTripProg`: the layer string of a triple (`xTrip`), at cost at most `101 m + 27` for `m`
  points of level `r + 1`;
* `subsProg ℓ`: the canonical triples `subsL ℓ`, by three nested folds;
  `ptsProg`: the subsets as triples of points (`ptrips`);
* `xArrProg`: the layer-string array (`xArr`).

The programs make no backend calls; each is well-formed (`wf_*`).
-/

@[expose] public section

namespace GraphIso

namespace Cost.Ty

/-- Graph data: adjacency lists. -/
abbrev graph : Ty := .array (.list .nat)
/-- Triples of points. -/
abbrev trip : Ty := .prod .nat (.prod .nat .nat)

end Cost.Ty

namespace Graph

open Equiv Cost Programs Sims

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The point `u` has level `r`. -/
def levEqProg (lev : var (.array .nat)) (r u : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet lev u) fun lu => .op2 .natEq lu r

/-- The neighbours of `w` of level `r`. -/
def nbLProg (G : var Ty.graph) (lev : var (.array .nat)) (r w : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet G w) fun ns => Luks.filterList ns fun u => levEqProg lev r u

/-- Membership in a list. -/
def memProg (l : var (.list .nat)) (x : var .nat) : Prog S rec var .bool :=
  anyList l fun y => .op2 .natEq y x

/-- Two lists with the same elements. -/
def seteqProg (l₁ l₂ : var (.list .nat)) : Prog S rec var .bool :=
  .bind (allList l₁ fun x => memProg l₂ x) fun b₁ =>
  .bind (allList l₂ fun x => memProg l₁ x) fun b₂ => .op2 .and b₁ b₂

/-- Adjacency. -/
def adjProg (G : var Ty.graph) (u v : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet G u) fun ns => memProg ns v

/-- The edge test of a triple. -/
def edge3Prog (G : var Ty.graph) (x y z : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .natEq x y) fun e =>
  .ite e
    (.bind (.op2 .natEq x z) fun exz => .bind (.op1 .not exz) fun nxz =>
      .bind (adjProg G x z) fun a => .op2 .and nxz a)
    (.bind (.op2 .natEq z x) fun ezx => .bind (.op2 .natEq z y) fun ezy =>
      .bind (.op2 .or ezx ezy) fun o => .bind (adjProg G x y) fun a => .op2 .and o a)

/-- The neighbours of level `r` of `w` are the elements of `T`. -/
def nbEqProg (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat) (T : var (.list .nat))
    (w : var .nat) : Prog S rec var .bool :=
  .bind (nbLProg G lev r w) fun nw => seteqProg nw T

/-- The layer string of the triple `(x, y, z)`; `New` lists the points of level `r + 1`. -/
def xTripProg (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (New : var (.list .nat)) (x y z : var .nat) : Prog S rec var .nat :=
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons z nl) fun l₁ => .bind (.op2 .cons y l₁) fun l₂ =>
  .bind (.op2 .cons x l₂) fun T =>
  .bind (Luks.filterList New fun w => nbEqProg G lev r T w) fun cl =>
  .bind (.op1 .length cl) fun c =>
  .bind (edge3Prog G x y z) fun e =>
  .ite e (.bind (.op0 (.natLit 4)) fun four => .op2 .add c four) (.ret c)

/-- Cons the triple `(x, y, z)`. -/
def consTripProg (x y z : var .nat) (acc : var (.list Ty.trip)) :
    Prog S rec var (.list Ty.trip) :=
  .bind (.op2 .pair y z) fun yz => .bind (.op2 .pair x yz) fun t => .op2 .cons t acc

/-- The triple `(i, j, k)` is canonical. -/
def canonicalProg (i j k : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .natLt j i) fun l₁ => .bind (.op1 .not l₁) fun le₁ =>
  .bind (.op2 .natLt k j) fun l₂ => .bind (.op1 .not l₂) fun le₂ =>
  .bind (.op2 .natEq j k) fun e₁ => .bind (.op1 .not e₁) fun ne₁ =>
  .bind (.op2 .natEq i j) fun e₂ => .bind (.op2 .or ne₁ e₂) fun imp =>
  .bind (.op2 .and le₁ le₂) fun c => .op2 .and c imp

/-- Cons the triple `(i, j, k)` if it is canonical. -/
def consSubProg (i j k : var .nat) (acc : var (.list Ty.trip)) :
    Prog S rec var (.list Ty.trip) :=
  .bind (canonicalProg i j k) fun c => .ite c (consTripProg i j k acc) (.ret acc)

/-- The canonical triples of `0, …, ℓ − 1`, in lexicographic order. -/
def subsProg (ℓ : var .nat) : Prog S rec var (.list Ty.trip) :=
  .bind (.op1 .range ℓ) fun rl => .bind (.op1 .reverse rl) fun rr => .bind (.op0 .nil) fun nl =>
  .foldList rr nl fun acc i => .foldList rr acc fun acc j => .foldList rr acc fun acc k =>
    consSubProg i j k acc

/-- Read the three entries of a triple through an array. -/
def tmapProg (A : var (.array .nat)) (t : var Ty.trip) : Prog S rec var Ty.trip :=
  .bind (.op1 .fst t) fun i => .bind (.op1 .snd t) fun jk =>
  .bind (.op1 .fst jk) fun j => .bind (.op1 .snd jk) fun k =>
  .bind (.op2 .arrayGet A i) fun x => .bind (.op2 .arrayGet A j) fun y =>
  .bind (.op2 .arrayGet A k) fun z => .bind (.op2 .pair y z) fun yz => .op2 .pair x yz

/-- The subsets as triples of points: the canonical triples `S` read through `Lr`. -/
def ptsProg (LA : var (.array .nat)) (Sb : var (.list Ty.trip)) :
    Prog S rec var (.list Ty.trip) :=
  mapList Sb fun t => tmapProg LA t

/-- The layer string of a triple given as a value. -/
def xTripOfProg (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (New : var (.list .nat)) (p : var Ty.trip) : Prog S rec var .nat :=
  .bind (.op1 .fst p) fun x => .bind (.op1 .snd p) fun yz =>
  .bind (.op1 .fst yz) fun y => .bind (.op1 .snd yz) fun z => xTripProg G lev r New x y z

/-- The layer-string array: `0` on the `N` graph points, then the triples `P`. -/
def xArrProg (G : var Ty.graph) (lev : var (.array .nat)) (N r : var .nat)
    (New : var (.list .nat)) (P : var (.list Ty.trip)) : Prog S rec var Ty.str :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk N z) fun za =>
  .bind (.op1 .arrayToList za) fun zl =>
  .bind (mapList P fun p => xTripOfProg G lev r New p) fun xs =>
  .bind (.op2 .append zl xs) fun l => .op1 .arrayOfList l

end Prog

/-! ### Models of the folds -/

theorem foldl_cons_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (acc : List β),
      l.reverse.foldl (fun acc x => f x :: acc) acc = l.map f ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.reverse_cons, List.foldl_append, foldl_cons_map f l]
    rfl

theorem foldl_append_flatMap {α β : Type} (f : α → List β) (g : List β → α → List β)
    (hg : ∀ acc x, g acc x = f x ++ acc) :
    ∀ (l : List α) (acc : List β), l.reverse.foldl g acc = l.flatMap f ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.reverse_cons, List.foldl_append, foldl_append_flatMap f g hg l]
    simp [hg, List.flatMap_cons, List.append_assoc]

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem foldl_cons_filter {α β : Type} (f : α → β) (q : β → Bool) :
    ∀ (l : List α) (acc : List β),
      l.reverse.foldl (fun acc x => if q (f x) then f x :: acc else acc) acc =
        (l.map f).filter q ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.reverse_cons, List.foldl_append, foldl_cons_filter f q l]
    by_cases h : q (f x) <;> simp [h]

/-- The canonicity test, as computed. -/
def canonB (t : ℕ × ℕ × ℕ) : Bool :=
  (!decide (t.2.1 < t.1) && !decide (t.2.2 < t.2.1)) && (!(t.2.1 == t.2.2) || (t.1 == t.2.1))

theorem canonB_eq (t : ℕ × ℕ × ℕ) : canonB t = decide (Canonical t) := by
  obtain ⟨i, j, k⟩ := t
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [canonB, Canonical, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_true, beq_eq_false_iff_ne, beq_iff_eq, not_lt]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, h₂, fun e => h₃.resolve_left (not_not.2 e)⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨h₁, h₂⟩, (em (j = k)).elim (fun e => Or.inr (h₃ e)) Or.inl⟩

/-- The value of the nested folds of `subsProg`. -/
theorem subs_fold (ℓ : ℕ) :
    (List.range ℓ).reverse.foldl (fun acc i => (List.range ℓ).reverse.foldl (fun acc j =>
      (List.range ℓ).reverse.foldl (fun acc k =>
        if canonB (i, j, k) then (i, j, k) :: acc else acc) acc) acc) [] = subsL ℓ := by
  have h₃ : ∀ (i j : ℕ) (acc : List (ℕ × ℕ × ℕ)),
      (List.range ℓ).reverse.foldl (fun acc k =>
        if canonB (i, j, k) then (i, j, k) :: acc else acc) acc =
      ((List.range ℓ).map fun k => (i, j, k)).filter canonB ++ acc := fun i j acc =>
    foldl_cons_filter (fun k => (i, j, k)) canonB _ acc
  have h₂ : ∀ (i : ℕ) (acc : List (ℕ × ℕ × ℕ)), (List.range ℓ).reverse.foldl (fun acc j =>
      (List.range ℓ).reverse.foldl (fun acc k =>
        if canonB (i, j, k) then (i, j, k) :: acc else acc) acc) acc =
      ((List.range ℓ).flatMap fun j => ((List.range ℓ).map fun k => (i, j, k)).filter canonB) ++
        acc := fun i acc =>
    foldl_append_flatMap _ _ (fun acc j => h₃ i j acc) _ acc
  rw [foldl_append_flatMap _ _ (fun acc i => h₂ i acc) _ [], List.append_nil]
  unfold subsL tripsL
  rw [List.filter_flatMap]
  refine flatMap_congr_mem fun i _ => ?_
  rw [List.filter_flatMap]
  refine flatMap_congr_mem fun j _ => ?_
  congr 1
  funext t
  exact canonB_eq t

theorem ptrips_eq_map (Lr : List ℕ) :
    ptrips Lr = (subsL Lr.length).map (tmap (get Lr.toArray)) := by
  unfold ptrips
  congr 1
  funext t
  simp only [tmap, get_toArray]

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.caseOption_eq_none {a' t : Ty} {o : (Ty.option a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = none) (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_none h

theorem RunsWithin.caseOption_eq_some {a' t : Ty} {o : (Ty.option a').denote} {v : a'.denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = some v) (h : RunsWithin X body (q v) r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_some h

theorem RunsWithin.levEqProg (lev : Array ℕ) (r u : ℕ) :
    RunsWithin X body (Graph.levEqProg lev r u) (get lev u == r) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl

theorem RunsWithin.nbLProg (G : GraphData) (lev : Array ℕ) (r w : ℕ) :
    RunsWithin X body (Graph.nbLProg G lev r w) (nbL G lev r w)
      (6 * (nbrs G w).length + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Luks.RunsWithin.filterList (a' := .nat) fun u _ => RunsWithin.levEqProg lev r u
  case hc =>
    simp only [Prim.cost]
    change 1 + ((nbrs G w).length * (2 + 4) + 2) ≤ _
    omega

theorem length_nbL_le (G : GraphData) (lev : Array ℕ) (r w : ℕ) :
    (nbL G lev r w).length ≤ (nbrs G w).length :=
  List.length_filter_le _ _

theorem RunsWithin.memProg (l : List ℕ) (x : ℕ) :
    RunsWithin X body (Graph.memProg l x) (l.any fun y => y == x) (3 * l.length + 1) :=
  (RunsWithin.anyList_le (c := 1) fun y _ => RunsWithin.prim_le rfl le_rfl).mono
    (by omega)

theorem RunsWithin.seteqProg (l₁ l₂ : List ℕ) :
    RunsWithin X body (Graph.seteqProg l₁ l₂) (seteqB l₁ l₂)
      (l₁.length * (3 * l₂.length + 3) + l₂.length * (3 * l₁.length + 3) + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.allList_le fun x _ => RunsWithin.memProg l₂ x)
    run_step (RunsWithin.allList_le fun x _ => RunsWithin.memProg l₁ x)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    ring_nf
    omega

theorem RunsWithin.adjProg (G : GraphData) (u v : ℕ) :
    RunsWithin X body (Graph.adjProg G u v) (adjB G u v) (3 * (nbrs G u).length + 2) :=
  (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.memProg _ v)).mono (by
    simp only [Prim.cost]
    change 1 + (3 * (nbrs G u).length + 1) ≤ _
    omega)

theorem RunsWithin.edge3Prog {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3) (x y z : ℕ) :
    RunsWithin X body (Graph.edge3Prog G x y z) (edge3B G x y z) 17 := by
  have hx := hG3 x
  by_cases hxy : x = y
  · subst hxy
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simp [Prim.eval]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.adjProg G x z)
      exact RunsWithin.prim_le (by simp [Prim.eval, edge3B]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (by simp [Prim.eval, hxy]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.adjProg G x y)
      exact RunsWithin.prim_le (by simp [Prim.eval, edge3B, hxy]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega

theorem RunsWithin.nbEqProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) {T : List ℕ} (hT : T.length ≤ 3) (w : ℕ) :
    RunsWithin X body (Graph.nbEqProg G lev r T w) (seteqB (nbL G lev r w) T) 96 := by
  have h₁ := hG3 w
  have h₂ := length_nbL_le G lev r w
  refine RunsWithin.bind_le (RunsWithin.nbLProg G lev r w) (RunsWithin.seteqProg _ T) ?_
  nlinarith

theorem RunsWithin.xTripProg {N : ℕ} {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r x y z : ℕ) (hm : (levList lev N (r + 1)).length ≤ N) :
    RunsWithin X body (Graph.xTripProg G lev r (levList lev N (r + 1)) x y z)
      (xTrip G lev N r x y z) (101 * N + 27) := by
  have hfilt := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := levList lev N (r + 1)) fun w _ => RunsWithin.nbEqProg hG3 lev r (T := [x, y, z])
      (by simp) w
  cases he : edge3B G x y z
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfilt
      run_step (RunsWithin.prim_le (c := N + 1) rfl (by
        simp only [Prim.cost, Args.head_cons]
        exact Nat.succ_le_succ ((List.length_filter_le _ _).trans hm)))
      run_step (RunsWithin.edge3Prog hG3 x y z)
      rw [he]
      run_with RunsWithin.ite_neg rfl _
      exact (RunsWithin.ret _).of_eq (by simp [xTrip, Prim.eval, he])
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfilt
      run_step (RunsWithin.prim_le (c := N + 1) rfl (by
        simp only [Prim.cost, Args.head_cons]
        exact Nat.succ_le_succ ((List.length_filter_le _ _).trans hm)))
      run_step (RunsWithin.edge3Prog hG3 x y z)
      rw [he]
      run_with RunsWithin.ite_pos rfl _
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [xTrip, Prim.eval, he]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega

theorem RunsWithin.consTripProg (x y z : ℕ) (acc : List (ℕ × ℕ × ℕ)) :
    RunsWithin X body (Graph.consTripProg x y z acc) ((x, y, z) :: acc) 3 :=
  RunsWithin.bind_le (RunsWithin.prim _ _)
    (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl) le_rfl

theorem RunsWithin.canonicalProg (i j k : ℕ) :
    RunsWithin X body (Graph.canonicalProg i j k) (canonB (i, j, k)) 10 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.consSubProg (i j k : ℕ) (acc : List (ℕ × ℕ × ℕ)) :
    RunsWithin X body (Graph.consSubProg i j k acc)
      (if canonB (i, j, k) then (i, j, k) :: acc else acc) 14 := by
  cases hc : canonB (i, j, k)
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.canonicalProg i j k)
      rw [hc]
      run_with RunsWithin.ite_neg rfl _
      exact (RunsWithin.ret _).of_eq (by simp)
    case hc =>
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.canonicalProg i j k)
      rw [hc]
      run_with RunsWithin.ite_pos rfl _
      exact (RunsWithin.consTripProg i j k acc).of_eq (by simp)
    case hc =>
      omega

theorem RunsWithin.subsProg (ℓ : ℕ) :
    RunsWithin X body (Graph.subsProg ℓ) (subsL ℓ) (ℓ * (ℓ * (15 * ℓ + 1) + 1) + 2 * ℓ + 3) := by
  have h₃ : ∀ (i j : ℕ) (acc : List (ℕ × ℕ × ℕ)), RunsWithin X body
      (.foldList (a := .nat) (b := .list Ty.trip) (List.range ℓ).reverse acc fun acc k =>
        Graph.consSubProg i j k acc)
      ((List.range ℓ).reverse.foldl (fun acc k =>
        if canonB (i, j, k) then (i, j, k) :: acc else acc) acc) (ℓ * 15) := by
    intro i j acc
    have := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list Ty.trip)
      (cf := fun _ => 14) (F := fun acc k => if canonB (i, j, k) then (i, j, k) :: acc else acc)
      (List.range ℓ).reverse acc fun acc k _ => RunsWithin.consSubProg i j k acc
    rw [sum_map_const, List.length_reverse, List.length_range] at this
    exact this
  have h₂ : ∀ (i : ℕ) (acc : List (ℕ × ℕ × ℕ)), RunsWithin X body
      (.foldList (a := .nat) (b := .list Ty.trip) (List.range ℓ).reverse acc fun acc j =>
        .foldList (a := .nat) (List.range ℓ).reverse acc fun acc k => Graph.consSubProg i j k acc)
      ((List.range ℓ).reverse.foldl (fun acc j => (List.range ℓ).reverse.foldl (fun acc k =>
        if canonB (i, j, k) then (i, j, k) :: acc else acc) acc) acc) (ℓ * (ℓ * 15 + 1)) := by
    intro i acc
    have := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list Ty.trip)
      (cf := fun _ => ℓ * 15) (List.range ℓ).reverse acc fun acc j _ => h₃ i j acc
    rw [sum_map_const, List.length_reverse, List.length_range] at this
    exact this
  have h₁ := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list Ty.trip)
    (cf := fun _ => ℓ * (ℓ * 15 + 1)) (List.range ℓ).reverse [] fun acc i _ => h₂ i acc
  rw [sum_map_const, List.length_reverse, List.length_range, subs_fold] at h₁
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact h₁
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range]
    ring_nf
    omega

theorem RunsWithin.tmapProg (A : Array ℕ) (t : ℕ × ℕ × ℕ) :
    RunsWithin X body (Graph.tmapProg A t) (tmap (get A) t) 9 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.ptsProg (Lr : List ℕ) :
    RunsWithin X body (Graph.ptsProg Lr.toArray (subsL Lr.length)) (ptrips Lr)
      (12 * nsub Lr + 2) := by
  rw [ptrips_eq_map]
  exact (RunsWithin.mapList_le fun t _ => RunsWithin.tmapProg Lr.toArray t).mono
    (by simp only [nsub]; omega)

theorem RunsWithin.xTripOfProg {N : ℕ} {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) (hm : (levList lev N (r + 1)).length ≤ N) (p : ℕ × ℕ × ℕ) :
    RunsWithin X body (Graph.xTripOfProg G lev r (levList lev N (r + 1)) p)
      (xTrip G lev N r p.1 p.2.1 p.2.2) (101 * N + 31) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.xTripProg hG3 lev r _ _ _ hm
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.xArrProg {N : ℕ} {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) (hm : (levList lev N (r + 1)).length ≤ N) (Lr : List ℕ) :
    RunsWithin X body (Graph.xArrProg G lev N r (levList lev N (r + 1)) (ptrips Lr))
      (xArr G lev N r Lr) ((ptrips Lr).length * (101 * N + 35) + 4 * N + 7) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun p _ => RunsWithin.xTripOfProg hG3 lev r hm p)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, xArr]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList, Array.size_replicate]
    ring_nf
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_filterList {a' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {p₁ : var₁ a' → Prog S rec var₁ .bool} {p₂ : var₂ a' → Prog S rec var₂ .bool}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (Luks.filterList xs₁ p₁) (Luks.filterList xs₂ p₂) := by
  unfold Luks.filterList
  refine .bind (.prim _ .nil) fun n₁ n₂ => .bind (.foldList (by simp [hxs]) (List.Mem.head _)
    fun acc₁ acc₂ x₁ x₂ => .bind (hp _ (fun y hy => by simp [hy]) _ _ (by simp))
      fun c₁ c₂ => ?_) fun ra₁ ra₂ => ?_
  · prog_wf
  · prog_wf

theorem wf_levEqProg {l₁ : var₁ (.array .nat)} {l₂ : var₂ (.array .nat)} {r₁ u₁ : var₁ .nat}
    {r₂ u₂ : var₂ .nat} (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (levEqProg l₁ r₁ u₁) (levEqProg l₂ r₂ u₂) := by
  unfold levEqProg
  prog_wf

theorem wf_nbLProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {r₁ w₁ : var₁ .nat} {r₂ w₂ : var₂ .nat}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hw : ⟨.nat, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbLProg G₁ l₁ r₁ w₁) (nbLProg G₂ l₂ r₂ w₂) := by
  unfold nbLProg
  refine .bind (.prim _ (.cons hG (.cons hw .nil))) fun ns₁ ns₂ =>
    wf_filterList (List.Mem.head _) fun Γ' hΓ u₁ u₂ hu =>
      wf_levEqProg (hΓ (by simp [hl])) (hΓ (by simp [hr])) hu

theorem wf_seteqProg {a₁ b₁ : var₁ (.list .nat)} {a₂ b₂ : var₂ (.list .nat)}
    (ha : ⟨.list .nat, a₁, a₂⟩ ∈ Γ) (hb : ⟨.list .nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (seteqProg a₁ b₁) (seteqProg a₂ b₂) := by
  unfold seteqProg memProg allList anyList
  prog_wf

theorem wf_nbEqProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {r₁ w₁ : var₁ .nat} {r₂ w₂ : var₂ .nat}
    {T₁ : var₁ (.list .nat)} {T₂ : var₂ (.list .nat)}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hT : ⟨.list .nat, T₁, T₂⟩ ∈ Γ) (hw : ⟨.nat, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbEqProg G₁ l₁ r₁ T₁ w₁) (nbEqProg G₂ l₂ r₂ T₂ w₂) :=
  .bind (wf_nbLProg hG hl hr hw) fun _ _ => wf_seteqProg (List.Mem.head _) (by simp [hT])

theorem wf_edge3Prog {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {x₁ y₁ z₁ : var₁ .nat}
    {x₂ y₂ z₂ : var₂ .nat} (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ)
    (hy : ⟨.nat, y₁, y₂⟩ ∈ Γ) (hz : ⟨.nat, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (edge3Prog G₁ x₁ y₁ z₁) (edge3Prog G₂ x₂ y₂ z₂) := by
  unfold edge3Prog adjProg memProg anyList
  prog_wf

theorem wf_xTripProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {r₁ x₁ y₁ z₁ : var₁ .nat} {r₂ x₂ y₂ z₂ : var₂ .nat}
    {m₁ : var₁ (.list .nat)} {m₂ : var₂ (.list .nat)}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hy : ⟨.nat, y₁, y₂⟩ ∈ Γ)
    (hz : ⟨.nat, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (xTripProg G₁ l₁ r₁ m₁ x₁ y₁ z₁)
      (xTripProg G₂ l₂ r₂ m₂ x₂ y₂ z₂) := by
  unfold xTripProg
  refine .bind (.prim _ .nil) fun n₁ n₂ => .bind (.prim _ (.cons (by simp [hz]) (.cons
    (List.Mem.head _) .nil))) fun c₁ c₂ => .bind (.prim _ (.cons (by simp [hy]) (.cons
    (List.Mem.head _) .nil))) fun d₁ d₂ => .bind (.prim _ (.cons (by simp [hx]) (.cons
    (List.Mem.head _) .nil))) fun T₁ T₂ => .bind (wf_filterList (by simp [hm])
      fun Γ' hΓ w₁ w₂ hw => wf_nbEqProg (hΓ (by simp [hG])) (hΓ (by simp [hl]))
        (hΓ (by simp [hr])) (hΓ (List.Mem.head _)) hw) fun cl₁ cl₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k₁ k₂ =>
    .bind (wf_edge3Prog (by simp [hG]) (by simp [hx]) (by simp [hy]) (by simp [hz]))
      fun e₁ e₂ => ?_
  prog_wf

theorem wf_subsProg {l₁ : var₁ .nat} {l₂ : var₂ .nat} (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (subsProg l₁) (subsProg l₂) := by
  unfold subsProg consSubProg canonicalProg consTripProg
  prog_wf

theorem wf_ptsProg {A₁ : var₁ (.array .nat)} {A₂ : var₂ (.array .nat)}
    {S₁ : var₁ (.list Ty.trip)} {S₂ : var₂ (.list Ty.trip)} (hA : ⟨.array .nat, A₁, A₂⟩ ∈ Γ)
    (hS : ⟨.list Ty.trip, S₁, S₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ptsProg A₁ S₁) (ptsProg A₂ S₂) := by
  unfold ptsProg tmapProg mapList
  prog_wf

theorem wf_xArrProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {m₁ : var₁ (.list .nat)} {m₂ : var₂ (.list .nat)} {P₁ : var₁ (.list Ty.trip)}
    {P₂ : var₂ (.list Ty.trip)} (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ)
    (hP : ⟨.list Ty.trip, P₁, P₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (xArrProg G₁ l₁ N₁ r₁ m₁ P₁)
      (xArrProg G₂ l₂ N₂ r₂ m₂ P₂) := by
  unfold xArrProg
  refine .bind (.prim _ .nil) fun z₁ z₂ => .bind (.prim _ (.cons (by simp [hN]) (.cons
    (List.Mem.head _) .nil))) fun a₁ a₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil))
    fun zl₁ zl₂ => .bind (wf_mapList (by simp [hP]) fun Γ' hΓ p₁ p₂ hp => ?_) fun xs₁ xs₂ => ?_
  · have hsub : ∀ e, e ∈ Γ → e ∈ Γ' := fun e he => hΓ (by simp [he])
    unfold xTripOfProg
    exact .bind (.prim _ (.cons hp .nil)) fun x₁ x₂ => .bind (.prim _ (.cons (by simp [hp])
      .nil)) fun yz₁ yz₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun y₁ y₂ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun z₁ z₂ =>
      wf_xTripProg (by simp [hsub _ hG]) (by simp [hsub _ hl]) (by simp [hsub _ hr])
        (by simp [hsub _ hm]) (by simp) (by simp) (by simp)
  · prog_wf

end Wf

end Graph

end GraphIso
