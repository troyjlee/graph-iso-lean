# Lean development plan, milestone 17: graph isomorphism on Turing machines

Prepared 26 October 2026. This continues `PLAN-16.md` (milestone 16 is complete, `289e203`). The
conventions and standards of `PLAN.md` and `lean/docs/` remain in force.

## Goal

The cost bounds of milestones 1–16 are stated for the project's explicit program semantics
(`GraphIso.Cost`: unit-cost naturals, copying charged by length). `PLAN.md` (§ Cost model) left a
simulation into a standard machine model as a separate obligation. This milestone discharges it
with mathlib's Turing machines (`Turing.FinTM2`, `Turing.TM2ComputableInTime`):

1. **Every closed well-formed program runs on a Turing machine** in time polynomial in its
   charged local cost, the length of its input and the length of its output, of a degree
   independent of the program. (The first version of this statement omitted the output's
   length; with a degree independent of the program it cannot be omitted, see §10.3. The
   amendment was confirmed by the user on 27 October 2026.)
2. **Graph isomorphism in quasipolynomial time on a Turing machine:** for pairs of simple graphs
   encoded as strings of length `L`, a `FinTM2` decides isomorphism in at most
   `2^{c (λ(L) + 1)⁸}` steps (`λ = Nat.log 2`), as a `TM2ComputableInTime` structure, and a second
   machine outputs the coset of all isomorphisms.

## 1. The route

- **Machine model.** Mathlib's `FinTM2` has finitely many stacks, a finite set of labels and a
  finite local state; one step executes one statement of a label. Mathlib requires only the input
  alphabet to be finite; every alphabet constructed here is finite. A run counts in
  `TM2OutputsInTime` only if it halts with the output on the output stack, every other stack
  empty and the local state reset.
- **Structured stack programs** (`GraphIso.TM`). Writing machines label by label is impractical.
  Programs are written in a small structured language over the machine's stacks (push, pop and
  peek through finitely many registers; sequence, conditional, while, and calls of finitely many
  possibly recursive procedures), with a big-step semantics that counts steps. One generic
  theorem compiles a program to a `FinTM2` whose labels are the finitely many continuations
  reachable in the program and whose return addresses live on an extra stack, and bounds its
  running time by the counted steps.
- **Sharing forces a heap.** In the cost model, `pair x x` costs one unit and doubles the size of
  the value as a tree, so values written out as trees can be exponentially larger than the cost.
  The machine therefore keeps values in an append-only heap of cells with binary addresses
  (`nat`, `bool`, `unit`, `pair`, `none`, `some`, `nil`, `cons`, arrays of addresses). Each
  primitive allocates at most a number of cells proportional to its charge.
- **Numbers stay small.** The only arithmetic primitives are `add` and `sub`, plus `length`,
  `range` and `arraySize`. Every number in the heap is below `2^{K + W}` for `W` the heap size in
  words and `K` the largest literal's length. So unit-cost naturals cost a polynomial factor, and
  no analysis of particular programs is needed.
- **Compilation, not interpretation.** A well-formed PHOAS program, instantiated with de Bruijn
  levels as variables, is compiled construct by construct to stack-program code. Recursion
  (`recur`) becomes a procedure call, `loop` and `foldList` become while loops, and environments
  are stacks of addresses. Correctness is proved against `eval` by induction along the relation
  `Prog.Wf` between the value and the level instantiation. This makes formal the "standard
  correspondence with first-order syntax" that `GraphIso.Cost.WellFormed` describes informally.
- **Time.** Uncharged constructs (`ret`, `bind`) run at most `|P|` times per charged event
  (`|P|` = program size). Each construct takes polynomially many steps in the size of the
  machine's stacks, and that size is polynomial in the input length and the cost. Writing the
  output takes time polynomial in its length and the heap's size. So the running time is
  `C_P (cost + |input| + |output| + 1)^d`, with `C_P` depending on the program and `d` fixed
  (§10.3: with `d` fixed, the output's length cannot be dropped).
- **Graph isomorphism.** Instantiate with `qpSolver 192 181` and `giEntry` (milestone 16). The
  input is the serialization of `(n, adjacency lists of G, adjacency lists of H)`; its length
  `L` is at least `n`. With `gi_simpleGraph_final`, the time is `2^{c (λ(L) + 1)⁸}`.

**What is not claimed.** Mathlib's `TM2` is a multi-stack Turing machine; its polynomial
equivalence with single-tape machines is classical and not formalized here. *(Later, milestone 18,
`PLAN-18.md`: stage 18e formalizes the transfer of every `FinTM2` with finite stack alphabets to
a finite single-tape machine with quadratic overhead, input preparation and output cleanup
included (`compile_outputs`), and stage 18f runs the two GI machines of this milestone on
single-tape machines (`gi_tm0`, `gi_coset_tm0`, and in the number of vertices
`gi_tm0_vertices`, `gi_coset_tm0_vertices`). This milestone's own scope is as stated here.)* The decision
function `isoDecide` is defined by brute force over permutations (it is a specification, not
the algorithm), with `isoDecide_iff : isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`.

## 2. Stages

Each stage is its own lean-loop, in `GraphIso/TM/` (namespace `GraphIso.TM`, mathlib imports
only until 17b; from 17c on also the cost language's types). Criteria for 17b–17h are written
before each stage starts.

- **17a: stack programs and Turing machines** (§3): the language, its semantics, the generic
  compilation to `FinTM2`, and the computability builder.
- **17b: numbers and lists on stacks.** Binary naturals (least significant bit first, with
  terminators), moving, copying and erasing stack segments, increment and decrement, `add`,
  truncated `sub`, equality and `<`, with exact semantics and step bounds.
- **17c: the heap** (§6). Cells, the append-only heap stack with binary addresses, allocation and
  lookup, the representation relation for values of every `Ty`, and its monotonicity under
  allocation.
- **17d: input and output** (§7). The serialization `ser t` of values, loading a serialized
  input into the heap, and writing a heap value to the output.
- **17e: the compiler** (§8). Level instantiation, environments and frames, the compiler for
  every control construct with the primitives given by a specification, and the simulation
  theorem against `eval` via `Prog.Wf`, with the heap size invariant and step bounds.
- **17f: the primitives.** Code for the 27 primitives meeting the specification of 17e.
- **17g: the simulation on Turing machines.** The main program (load the input, run the
  compiled entry, write the output, clear the stacks), `outputsInTime`, and the running time
  `(κ_P (cost + |input| + |output| + 1))^120` (§10).
- **17h: graph isomorphism on Turing machines.** `GraphPair`, the encoding, `isoDecide` and
  `isoDecide_iff`, a decision entry returning a Boolean, `gi_tm` (decision,
  `TM2ComputableInTime`) and `gi_coset_tm` (the coset), each in time `2^{c (λ(L) + 1)⁸}`.

## 3. Stage 17a: completion criteria (stack programs and Turing machines)

Files `GraphIso/TM/Code.lean` and `GraphIso/TM/Machine.lean` (mathlib only), checks
`GraphIsoChecks/TMCode.lean`.

1. **The language** (`Code.lean`), over stack names `K` (finite, decidable equality), a finite
   alphabet `Γ` and `R` registers holding `Option Γ`:
   - actions: push a constant, push a register's symbol, pop into a register, peek into a
     register, set a register;
   - conditions on registers;
   - code: `skip`, an action, sequence, `ite`, `while`, `call p` for procedure names `p` in a
     finite type;
   - code has decidable equality (actions and conditions are data, interpreted by fixed
     functions). A program is a body for each procedure and a main procedure.
2. **Semantics:** a big-step relation `Exec` between configurations (registers and stacks) with a
   step count: one step for an action, a `skip`, a test of `ite` or `while`, and a `seq`; two
   steps for a call and its return. It is deterministic in the result and the count.
3. **Compilation** (`Machine.lean`): `Program.toFinTM2` is a `FinTM2` with:
   - the program's stacks plus a return stack;
   - labels the continuations (lists of code) reachable from the procedure bodies, as a subtype
     of an explicitly computed `Finset`, closed under every transition;
   - local state the registers and a return slot;
   - designated input and output stacks with alphabet `Γ`.
4. **Simulation:** if `Exec` runs `main` from a configuration to another in `n` steps, the machine
   goes from the corresponding configuration to the corresponding one in exactly `n` steps
   (labels as continuations, the return stack unchanged). Corollaries:
   - **`outputsInTime`:** if `main` maps the input on the input stack (other stacks empty,
     registers empty) to the output on the output stack (other stacks empty, registers empty)
     in `n` steps, then `TM2OutputsInTime` holds with `n + 1` steps;
   - **`computableInTime`:** if that holds for every `a` with output `eb (f a)` within
     `T (ea a).length` steps, a `TM2ComputableInTime ea eb f` with time `T + 1`.
5. **Checks:** a concrete program, with an exact `Exec` and the resulting
   `TM2ComputableInTime`, for a nontrivial function. For example, list reversal over a two-letter
   alphabet in time linear in the length, using a recursive call. Also a kernel-checked run of the
   compiled machine's `step` on a tiny input, against `haltList`, and a negative control (fewer
   steps do not reach the halting configuration).
6. **Audit and docs**, as before. The targets are `outputsInTime` and `computableInTime`.

**Not in this stage:** arithmetic, the heap, input and output, and the compiler (17b–17e).

## 4. Design notes

- **Labels as continuations.** A label is the list of code fragments still to run in the current
  procedure: `seq a b :: k` goes to `a :: b :: k`; `while c a :: k` goes to `a :: while c a :: k`
  or to `k`; `call p :: k` pushes `k` and goes to `[body p]`; `[]` pops a return address (or
  halts). The reachable set is finite: by induction on code, every successor of a label in
  `reach c k` is in `reach c k` or is `k`.
- **Halting convention.** Mathlib's halting configuration has every stack but the output empty
  and the local state equal to the initial one. Programs therefore erase their working stacks
  and clear their registers before returning from `main`, and the return slot is empty after
  the final pop.
- **Why not mathlib's `PartrecToTM2`.** It compiles partial recursive codes to `TM2` without
  time bounds, over lists of naturals. A compiler from this project's language to it, plus a time
  analysis of its proofs, would be more work than the direct route.

## 5. Stage 17b: completion criteria (numbers and arithmetic on stacks)

Files `GraphIso/TM/Sat.lean`, `GraphIso/TM/Bits.lean`, `GraphIso/TM/Num.lean` and
`GraphIso/TM/Arith.lean` (mathlib and stage 17a only), checks `GraphIsoChecks/TMArith.lean`.

1. **Specifications** (`Sat.lean`): `Sat prog x c t Q` holds when the code `x` runs (`Exec`) from
   `c` within `t` steps to a configuration satisfying `Q`. There is a rule for each construct.
   - Loops take an invariant indexed by the number of remaining iterations.
   - Budget forms of sequencing give the second part the steps the first leaves.
2. **The alphabet and bit lists** (`Bits.lean`):
   - `Sym` is finite (a `Fintype`). It has bits, an end mark, cell tags for stage 17c and four
     markers.
   - A number is a list of bits, least significant first and of any length, with value `ofBits`.
   - The serial processor `zipL f` reads two bit lists (missing bits read as `false`). It gives
     the output bits, of length `max`, and the final carry. Each mode has a lemma about values:
     - adder: the output with the final carry appended has value `ofBits xs + ofBits ys`;
     - subtractor: the borrow is set exactly when `ofBits xs < ofBits ys`, and otherwise the
       output has value `ofBits xs - ofBits ys`;
     - comparator: the final carry is set exactly when the values differ.
3. **Routines** (`Num.lean`, `Arith.lean`) work over any stack names with `4` registers.
   - Each routine starts and ends with empty registers.
   - It names its stacks, requires them distinct where needed, and leaves every other stack
     unchanged.
   - Its specification is a `Sat` with an explicit step bound, linear in the lengths of the bit
     lists involved.
   - The routines:
     - for numbers: moving (`moveBits`, `moveBits2`), copying (`copyNum`), dropping (`dropNum`)
       and pushing constants (`pushNum`);
     - for segments: moving and dropping up to a given symbol (`moveSeg`, `dropSeg`), and
       emptying a stack (`erase`);
     - the bit processor `zipNum f`, which carries out `zipL f` on two numbers;
     - `addNum`, `subNum` (truncated), `ltNum`, `eqNum`, `incNum` and `decNum`.
   - Results are stated through `ofBits` for inputs of any length; there is no canonical form.
4. **Checks**:
   - kernel runs on concrete numbers, with the exact final stacks, registers and step counts,
     including a step bound attained exactly, equality of non-canonical bit lists, and
     truncated subtraction;
   - a specification applied to a concrete input;
   - a negative control: by determinism, a run with fewer steps is impossible.
5. **Audit and docs**, as before. The targets are `addNum_sat`, `subNum_sat`, `ltNum_sat` and
   `eqNum_sat`.

**Not in this stage:** cells and the heap (17c).

## 6. Stage 17c: completion criteria (the heap)

Files `GraphIso/TM/Heap.lean`, `GraphIso/TM/Lookup.lean`, `GraphIso/TM/Alloc.lean` and
`GraphIso/TM/Rep.lean` (mathlib, stages 17a–17b, and `GraphIso.Cost.Program` for `Ty`), checks
`GraphIsoChecks/TMHeap.lean`.

1. **The simulator's stacks** `Stk` (a `Fintype`): input, output, heap, scan, allocation
   counter, work, pointer, environment, loop, and five temporaries.
2. **Cells and heaps** (`Heap.lean`):
   - a cell has an address (a number), a tag and a list of fields (numbers: addresses of other
     cells, or the bits of a natural);
   - on a stack a cell is `mk 1`, the address, the tag, the fields and `mk 0`;
   - a heap is a list of cells, oldest first, stored with the newest cell on top;
   - `HeapWF h`: the cell at index `i` has an address of value `i`.
3. **Routines**, as in 17b: empty registers at both ends, every stack not named is unchanged,
   and an explicit step bound.
   - `moveSeg2` moves a segment onto two stacks.
   - **Lookup** (`lookup_sat`). Assume a well-formed heap `h` on `heap`, `scan` empty, and a
     pointer `p` on `ptr` with `ofBits p < h.length`. Then `lookup` pushes a copy of the cell
     `h[ofBits p]` onto `work` and consumes the pointer. It restores `heap` and `scan` and
     leaves every other stack unchanged. Its bound is at most `50 (N + |p| + 3)²`, where `N` is
     the heap's length in symbols.
   - **Allocation** (`alloc_sat`). `HeapAt h c` says the configuration holds `h`: well formed,
     on `heap`, `scan` empty, and a counter on `cnt` of value `h.length` and length at most
     `h.length + 1`. From `HeapAt h`, with fields `fs` on `work` above a marker `mk 2`,
     `alloc t` appends a cell `⟨l, t, fs⟩` with `ofBits l = h.length`, so that
     `HeapAt (h ++ [_])` holds. It replaces the fields and the marker by the address `l` and
     leaves every other stack unchanged. Its bound is quadratic in the fields' length plus
     linear in `h.length`.
4. **Representation** (`Rep.lean`). `Rep h t v p` says that the cell at index `p`, with the
   cells it points to, represents the value `v : t.denote`. It covers every `Ty`:
   - the unit, Booleans (two tags), `none` and `nil` are cells without fields;
   - a natural is a cell whose one field is its bits;
   - a pair is a cell with two pointers, `some` a cell with one, and `cons` a cell with two
     (head and tail);
   - an array is a cell with one pointer per element.

   Fields are read through `ofBits`, so pointers need not be canonical. Representations are
   kept when cells are appended (`Rep.mono`), and they point into the heap (`Rep.lt`).
5. **Checks**:
   - kernel runs of `lookup` and `alloc` on a concrete heap, with the exact final stacks,
     registers and step counts, including a non-canonical pointer;
   - the specifications on concrete inputs;
   - representations, including after an allocation;
   - negative controls: a wrong value, a wrong type, and a heap that is not well formed.
6. **Audit and docs**, as before. The targets are `lookup_sat`, `alloc_sat` and `Rep.mono`.

**Not in this stage:** serializing values, loading the input and writing the output (now
stage 17d), and the compiler (now 17e).

## 7. Stage 17d: completion criteria (input and output)

Files `GraphIso/TM/Ser.lean`, `GraphIso/TM/Load.lean` and `GraphIso/TM/Write.lean` (mathlib,
stages 17a–17c), the rule `Sat.loop_list` in `GraphIso/TM/Sat.lean`, checks
`GraphIsoChecks/TMIO.lean`.

1. **Serialization** (`Ser.lean`). `ser t v` is a list of symbols for every `Ty`, a prefix code:
   - the unit is empty, a Boolean is a tag, a natural is its canonical bits `toBits n` and the
     end mark (`ofBits (toBits n) = n`);
   - a pair is its two components; an option is the tag `none`, or `some` and its value;
   - a list is its elements, each after the tag `cons`, then the tag `nil`;
   - an array is the same for its elements in reverse order (the loader then pushes their
     pointers in the order of the cell's fields).
2. **Loops over lists** (`Sat.loop_list`): an invariant indexed by the items still to process,
   with a budget per item, for loops whose iterations cost different amounts.
3. **Loading** (`load_sat`). Assume `HeapAt h`, empty registers, `ser t v` on top of `inp`, and
   `h.length + cellsB t v ≤ U`, where `cellsB t v` bounds the number of cells. Then `load t`
   ends with empty registers and:
   - reads `ser t v` from `inp`;
   - appends cells `h'` with `HeapAt (h ++ h')`, at most `cellsB t v` of them;
   - pushes a pointer `l` of length at most `U` onto `work`, with `Rep (h ++ h') t v (ofBits l)`;
   - leaves every other stack unchanged;
   - runs within `ldB t v U` steps.
4. **Writing** (`write_sat`). Assume a well-formed heap `h` on `heap`, `scan` empty, empty
   registers, and a pointer `p` on `ptr` with `Rep h t v (ofBits p)` and `|p| ≤ N`, where `N`
   is the heap's length in symbols. Then `write t` ends with empty registers and:
   - pushes `ser t v` onto `out`;
   - consumes the pointer and leaves every other stack unchanged;
   - writes naturals canonically, whatever the length of their bit lists;
   - runs within `wrB t v N` steps.
5. **Polynomial bounds**, where `L = (ser t v).length` and `wt t` is a weight of the type:
   - `cellsB t v ≤ wt t * (L + 1)`;
   - `ldB t v U ≤ wt t * (L + 1) * PL U` for `L ≤ U`, with `PL` a fixed polynomial;
   - `wrB t v N ≤ wt t * (L + 1) * visB N`, with `visB N` the cost of visiting one cell
     (quadratic in `N` plus a lookup).
6. **Checks**:
   - kernel runs of `load` and `write` on concrete values with lists, arrays, options, pairs and
     non-canonical naturals, with exact final stacks and step counts;
   - a round trip (load, then write the loaded value);
   - the specifications on concrete inputs;
   - negative controls.
7. **Audit and docs**, as before. The targets are `load_sat` and `write_sat`.

**Not in this stage:** the compiler and the simulation theorem (17e).

## 8. Stage 17e: completion criteria (the compiler: environments and control)

Files `GraphIso/TM/Env.lean` and `GraphIso/TM/Compile.lean` (stages 17a–17d and the cost
language's `Program`, `Evaluation` and `WellFormed`), checks `GraphIsoChecks/TMCompile.lean`.
The primitives are a parameter here, given by a specification; their code is stage 17f.

1. **Environments** (`Env.lean`). The stack `env` holds the pointers of the variables in scope,
   newest on top; a frame of depth `d` is its top `d` entries, and level `k < d` is the entry
   `d - 1 - k` from the top. Routines, as in 17b (empty registers at both ends, every stack not
   named unchanged, an explicit step bound):
   - move the pointer on top of `work` onto `env`, and drop the top entry of `env`;
   - copy the entry at offset `j` onto a stack, restoring `env`, within `(2 j + 1)` times a
     linear function of the longest entry's length.
2. **The size invariant** `HeapBnd B F h`: the cell at index `i` has an address of at most
   `B + i` bits, at most `F` fields, and fields of at most `B + i` bits. Every heap satisfies it
   for `B` and `F` at least its length in symbols (so a loaded input does, with no analysis of
   the loader). Under `HeapBnd`, the heap's length in symbols is at most an explicit polynomial
   in `h.length`, `B` and `F`. Pointers (frame entries, arguments, results) have at most
   `B + h.length` bits.
3. **The compiler** `comp pc pb d p`. Programs are over the empty signature, instantiated with
   de Bruijn levels (`Lv t = ℕ`); `d` is the depth of the frame, `pc` gives code for each
   primitive and `pb` is the procedure that runs the compiled body. The code pushes the pointer
   of the program's value onto `work`:
   - `ret`: copy the variable's entry; `bind`: run, move the pointer onto `env`, run the
     continuation at depth `d + 1`, drop the entry; `prim`: copy the arguments' pointers onto
     `work`, then run `pc p`;
   - `ite`, `caseOption`, `caseList`: fetch the cell, branch on its tag, bind its fields as new
     levels;
   - `foldList` and `loop`: while loops, the remaining list and the accumulator, or the state,
     kept on `env` and `work`;
   - `recur`: move the argument's pointer onto `env` (a new frame of depth `1`), call `pb`, drop
     the entry.

   `psize d p` is a size of the program (each primitive weighted by `pw p`, which is at least
   the length of a literal's bits and the number of cells of a default value).
4. **The primitive specification** `PrimSpec prog pc B F K Q`. For every primitive `p` with
   `pw p ≤ K`, arguments `xs` with `p.cost xs ≤ F`, a heap `h` with `HeapAt h` and
   `HeapBnd B F h`, empty registers, and pointers on `work` (the last argument on top) of at most
   `B + h.length` bits representing `xs`, the code `pc p` ends with empty registers and:
   - appends cells `h'` with `HeapAt (h ++ h')` and `HeapBnd B F (h ++ h')`, at most
     `K * p.cost xs` of them;
   - replaces the arguments' pointers by a pointer `l` of at most `B + (h ++ h').length` bits
     with `Rep (h ++ h') t (p.eval xs) (ofBits l)`;
   - leaves every other stack except `heap` and `cnt` unchanged;
   - runs within `p.cost xs * Q N` steps, `N` the final heap's length in symbols.
5. **The simulation theorem** `comp_sat`. Let `Pr` be a well-formed procedure over the empty
   signature whose compiled body (depth `1`) is the body of `pb`. Assume `PrimSpec`, `Q`
   monotone with `ctrlB D (B + N) ≤ Q N` (the control overhead of one construct), `K ≤ B`, and
   `K` and `D` large enough for the procedure body (`psize` plus constants). Let
   `Prog.Wf true Γ p₁ p₂` relate a program at `Ty.denote` to one at levels, with
   `eval O (Pr.proc Ty.denote) fuel p₁ = some (v, tr)` and `localCost tr ≤ F`. Assume
   `HeapAt h` and `HeapBnd B F h`, empty registers, and a frame of depth `d` representing `Γ`
   (each `⟨t, x, k⟩ ∈ Γ` has `k < d` and its entry represents `x`, with at most `B + h.length`
   bits), and `psize`-bounds for `p₂` against `K` and `D`. Then
   `comp pc pb d p₂` ends with empty registers and:
   - appends cells `h'`, at most `K * localCost tr`, with `HeapAt` and `HeapBnd B F` kept;
   - pushes a pointer of at most `B + (h ++ h').length` bits representing `v` onto `work`;
   - leaves every other stack except `heap` and `cnt` unchanged (`env` in particular);
   - runs within `(psize d p₂ + K * localCost tr) * Q N` steps, `N` the final heap's length in
     symbols.
6. **Checks**:
   - kernel runs of compiled programs exercising every control construct (a fold, a loop, case
     analysis on options and lists, a branch, a recursive procedure), with code for the few
     primitives they use, exact final stacks and step counts;
   - the size invariant and the environment routines on concrete inputs;
   - negative controls.
7. **Audit and docs**, as before. The target is `comp_sat`.

**Not in this stage:** the code of the primitives meeting the specification (17f); the main
program (loading the input, running the compiled entry, writing the output, clearing the
stacks), the Turing machine and the polynomial time bound (17g); graph isomorphism (17h).

## 9. Stage 17f: completion criteria (the primitives)

Files `GraphIso/TM/PrimLib.lean` (routines) and `GraphIso/TM/Prims.lean`, checks
`GraphIsoChecks/TMPrims.lean`.

1. **Routines** (`PrimLib.lean`), as in 17b–17e (empty registers at the start, every stack not
   named unchanged, an explicit step bound; empty registers at the end, except where the result
   is a register for the caller to test: `openTop` leaves the fetched cell's tag in register
   `1`, and the tests of the loops in `Prims.lean` leave their result for the loop's condition;
   the code of every complete primitive ends with empty registers, item 3):
   - allocating one cell, keeping `HeapBnd`;
   - fetching the cell, or the bits of the natural, of the pointer on top of `work`;
   - moving or counting the numbers above a marker;
   - walking a list (pushing the pointers of its elements onto a stack), and building a list
     from pointers on a stack, keeping `HeapBnd`.
2. **Code for every primitive** `primCode : PrimCode P` (the 27 constructors of `Prim`). The
   arguments' pointers are on `work` (the last on top) and are replaced by the result's
   pointer:
   - `unit`, `boolLit`, `none`, `nil`, `pair`, `some`, `cons`: one cell; `natLit k`: one cell
     with the bits of `k`;
   - `fst`, `snd`, `and`, `or`: an existing pointer (a field or an argument), no new cell;
     `not`: one cell;
   - `add`, `sub`, `natEq`, `natLt`: the 17b arithmetic on the arguments' bits, one cell;
   - lists: `append` (a cons cell per element of the first list), `reverse` (a cons cell per
     element, and `nil`), `length` (a count, one cell), `range k` (a natural and a cons cell
     per number, and `nil`);
   - arrays: `arrayMk k v` (one cell with `k` fields), `arraySize` (a count), `arrayGet` (a
     field, or new cells for the default value), `arrayUpdate` (the writes applied in order to
     the fields, then one cell), `arrayOfList` (one cell), `arrayToList` (a cons cell per
     element, and `nil`).
3. **`primCode_spec`**: `PrimSpec prog primCode B F K Q` for every program `prog`, under
   `F + 1 ≤ B` (counts of at most `F` elements fit the field bound), `2 ≤ F` (cells with two
   fields) and `primB (B + N) ≤ Q N` for every `N`, with `primB` an explicit polynomial: it
   covers a few lookups, the allocation of a cell of at most `M` symbols, and a scan over the
   fields of a cell (at most `F ≤ M` of them, each of at most `M` bits). The code does its
   lookups before it allocates, so its step bounds are fixed in advance.
4. **Checks**:
   - kernel runs of each primitive's code on concrete heaps, with exact results and step
     counts;
   - `primCode_spec` instantiated, and the 17e simulation theorem discharged on a concrete
     program with `primCode`, replacing `copy_spec`, whose `PrimSpec` premise for `pcDemo`
     cannot hold (finding F1 of the 17e audit);
   - negative controls.
5. **Audit and docs**, as before. The target is `primCode_spec`.

**Not in this stage:** the main program, the Turing machine and the polynomial time bound
(17g); graph isomorphism (17h).

## 10. Stage 17g: completion criteria (the simulation on Turing machines)

Files `GraphIso/TM/Main.lean`, checks `GraphIsoChecks/TMMain.lean`.

1. **Stack growth.** If `Exec prog x c c' n`, every stack of `c'` has at most `n` more symbols
   than in `c` (each step pushes at most one symbol). With it, the heap loaded from an input of
   length `L` has at most as many symbols as the loading took steps, a polynomial in `L`.
2. **The main program** `mainProg Pr E`, for a well-formed procedure `Pr : WfProc
   Signature.empty a b` and an entry `E : (var : Ty → Type) → var a' → Prog Signature.empty
   (a, b) var c` (procedures `Bool`; `true` runs the compiled procedure body
   `comp primCode true 1 (Pr.proc Lv 0)`). `main` initializes the allocation counter, loads the
   input (`load a'`), binds it at level `0`, runs `comp primCode true 1 (E Lv 0)`, drops the
   level, makes the result's pointer canonical (`toBits` of its value), writes the result
   (`write c`), and erases `heap` and `cnt`.
3. **The run** (`main_exec`). Assume `E` well formed:
   `Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁) (E Lv x₂)` for all `x₁`, `x₂`. For every input
   `x` with `Runs O (Pr.proc Ty.denote) (E Ty.denote x) v tr`, `main` runs from
   `inCfg .inp (ser a' x)` to `inCfg .out (ser c v)` (every other stack empty, registers empty)
   in at most `(κ (localCost tr + (ser a' x).length + (ser c v).length + 1)) ^ 120` steps, with
   `κ = 4096 (wt a' + wt c + K + D + psize 1 (E Lv 0) + 1)` explicit in the sizes of `Pr` and
   `E` (`K = psize 1 (Pr.proc Lv 0) + psize 1 (E Lv 0) + 1`, `D = 1 + 3 (…)`) and the weights
   of `a'` and `c`. A sharper bound `mainT` comes first, then the closed form (`mainT_le`).

   The output's length appears because values share cells: at a cost of about `m`, a program
   can build a list of `m` copies of one list of `m` numbers, which the machine writes out in at
   least `m²` symbols (lists nested `d` deep: `m^d`). So no bound
   `C_P (cost + |input| + 1)^d` with `d` independent of the program holds, and the Goal's
   statement 1 and §1 ("Time") are amended to include the output's length. Graph isomorphism
   (the Goal's statement 2) is unaffected: the decision's output is a Boolean, and the coset's
   is polynomial in `n` (17h).
4. **On Turing machines.** With 17a's `outputsInTime` and `stepsOf`: `TM2OutputsInTime
   (toFinTM2 (mainProg Pr E) .inp .out) (ser a' x) (some (ser c v)) (T + 1)` for the bound `T`
   of item 3 (`main_tm`).
5. **Checks**:
   - kernel runs of `main` on concrete programs from `inCfg .inp`: the output, every other
     stack including `heap` and `cnt` empty, registers empty, exact step counts; one with
     sharing (an output four times as long as the input, for two units of cost);
   - `canonPtr` on a pointer with a high zero bit;
   - the example of item 3 evaluated in the cost model: its local cost and the length of its
     output's serialization, for a concrete `m`;
   - `main_exec` and `main_tm` instantiated on a concrete program and input, with the time
     bound evaluated and the machine's step count computed;
   - negative controls.
6. **Audit and docs**, as before. The targets are `main_exec` and `main_tm`.

**Not in this stage:** graph isomorphism (17h).

## 11. Stage 17h: completion criteria (graph isomorphism on Turing machines)

Files `GraphIso/TM/GI.lean`, checks `GraphIsoChecks/TMGI.lean`.

1. **Graph pairs and the specification.** `GraphPair`: `n` and simple graphs `G`, `H` on
   `Fin n` with decidable adjacency. Its encoding `GraphPair.enc p = ser Ty.giInput (n,
   GraphData.ofSimpleGraph G, GraphData.ofSimpleGraph H)`, over the machine's alphabet, with
   `n ≤ (enc p).length`. `isoDecide p`: brute force over the permutations of `Fin n` (a
   specification, not the algorithm), with `isoDecide_iff : isoDecide p = true ↔
   Nonempty (p.G ≃g p.H)`.
2. **The entries.** `giCosetEntry`: milestone 16's entry `(giEntry Ty.unit var x).subst ssImpl`;
   `giDecEntry`: the same, then `true` exactly when its result is `some`. Both well formed
   (`Prog.Wf`, from `giEntry_wf` and `Prog.Wf.subst`). The programs: `giDecProg` and
   `giCosetProg`, `mainProg (qpSolver 192 181) _` (17g).
3. **The output's length.** For `r` with valid data and at most `4 gN(n)²` generators (as
   `GICosetOK` gives), `(ser Ty.giCoset r).length ≤ 16 (n + 1)^6`.
4. **Decision** (`gi_tm`): there are `c` and a `TM2ComputableInTime GraphPair.enc (ser .bool)
   isoDecide` whose machine is `toFinTM2 giDecProg .inp .out` and whose time on inputs of length
   `L` is at most `2^{c (λ(L) + 1)⁸}`; and on every pair `p` that machine outputs
   `ser .bool (isoDecide p)` on `enc p` within `2^{c (λ(L) + 1)⁸}` steps (so the statement does
   not depend on the alphabet equivalences inside the `TM2ComputableInTime` structure). From
   milestone 16 (`gi_simpleGraph_final`, `giSolve_final`: local cost at most
   `2^{c₀ (λ(n) + 1)⁸}`) and `main_exec` (17g), with `n ≤ L` and an output of length `1`.
5. **The coset** (`gi_coset_tm`): there is `c` such that for every pair `p`, with `L` the length
   of its encoding, some `r` has `TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) (enc p)
   (some (ser Ty.giCoset r)) (2^{c (λ(L) + 1)⁸})`, `r = none ↔ IsEmpty (G ≃g H)`, and for
   `r = some (τ, hs)` valid data with the coset `τ • ⟨hs⟩` exactly the set of the permutations
   underlying the isomorphisms `G ≃g H` (as in `gi_simpleGraph_final`).
6. **Checks**:
   - `isoDecide` on concrete pairs, isomorphic and not, with `isoDecide_iff` turning them into
     statements about `≃g`;
   - the encoding of a concrete pair, and its length against `n`;
   - the output-length bound at concrete permutation data;
   - `gi_tm` and `gi_coset_tm` instantiated on concrete pairs: the decision machine outputs
     the encoding of `true` on the isomorphic pair and of `false` on the other, and the coset
     machine outputs `some` on the isomorphic pair and `none` on the other;
   - the coset entry evaluated by the kernel in the cost model on graphs with at most two
     vertices: its answer and its local cost (the machines themselves are not run on graphs);
   - negative controls.
7. **Audit and docs**, as before. The targets are `gi_tm` and `gi_coset_tm`.

**What remains outside the milestone** (as in §1): the polynomial equivalence of `TM2` with
single-tape machines. *(Done later, in milestone 18: `PLAN-18.md` §§6–7.)*

## References

- Mathlib, `Mathlib/Computability/TuringMachine/StackTuringMachine.lean` and `Computable.lean`.
- A. Chlipala, *Parametric higher-order abstract syntax for mechanized semantics*, ICFP 2008 (the
  relational well-formedness used to pass from PHOAS to first-order syntax).
- S. A. Cook and R. A. Reckhow, *Time bounded random access machines*, JCSS 7 (1973) (unit-cost
  machines with addition and subtraction simulate in polynomial time).
