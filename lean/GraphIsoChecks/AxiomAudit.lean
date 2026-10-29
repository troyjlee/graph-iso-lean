module

import all GraphIso
import all GraphIso.Align.AlignProg
import all GraphIso.Align.Interface
import all GraphIso.Align.JohnOps
import all GraphIso.Align.PartOps
import all GraphIso.Align.SetOps
import all GraphIso.Align.Trim
import all GraphIso.AltQuot.Affected
import all GraphIso.AltQuot.Alternating
import all GraphIso.AltQuot.Interfaces
import all GraphIso.AltQuot.Subdirect
import all GraphIso.AltQuot.Subsets
import all GraphIso.AltQuot.Unaffected
import all GraphIso.Case2b.Case2bProg
import all GraphIso.Case2b.ChoiceProg
import all GraphIso.Case2b.Link
import all GraphIso.Case2b.OutOps
import all GraphIso.Case2b.Pipeline
import all GraphIso.Case2b.PipelineProg
import all GraphIso.Case2b.Tree
import all GraphIso.Case3.Case3Prog
import all GraphIso.Case3.Colouring
import all GraphIso.Case3.Link
import all GraphIso.Case3.Model
import all GraphIso.Case3.Pipeline
import all GraphIso.Case3.PipelineProg
import all GraphIso.CertProg.Affected
import all GraphIso.CertProg.Cert
import all GraphIso.CertProg.CertIso
import all GraphIso.CertProg.Kernel
import all GraphIso.CertProg.PairBeard
import all GraphIso.CertProg.Setting
import all GraphIso.CertProg.Step
import all GraphIso.CertProg.TestSets
import all GraphIso.CertProg.Transporter
import all GraphIso.Certificates.Aggregate
import all GraphIso.Certificates.Basic
import all GraphIso.Certificates.Beard
import all GraphIso.Certificates.Cases
import all GraphIso.Certificates.Local
import all GraphIso.Certificates.Relabel
import all GraphIso.Coherent.Basic
import all GraphIso.Coherent.BipGraph
import all GraphIso.Coherent.Classical
import all GraphIso.Coherent.Design
import all GraphIso.Coherent.DesignArray
import all GraphIso.Coherent.DesignProg
import all GraphIso.Coherent.Fisher
import all GraphIso.Coherent.LargeClique
import all GraphIso.Coherent.ListProg
import all GraphIso.Coherent.RCW
import all GraphIso.Coherent.Skeleton
import all GraphIso.Coherent.Tuples
import all GraphIso.Coherent.TuplesProg
import all GraphIso.Coherent.WL
import all GraphIso.Coherent.WLArray
import all GraphIso.Coherent.WLOn
import all GraphIso.Coherent.WLProg
import all GraphIso.Cost.BackendRefinement
import all GraphIso.Cost.Evaluation
import all GraphIso.Cost.Local
import all GraphIso.Cost.Program
import all GraphIso.Cost.Spec
import all GraphIso.Cost.WellFormed
import all GraphIso.Giant.Aggregate
import all GraphIso.Giant.Case1
import all GraphIso.Giant.Case2a
import all GraphIso.Giant.FullGroup
import all GraphIso.Graph.Algorithm
import all GraphIso.Graph.All
import all GraphIso.Graph.Basic
import all GraphIso.Graph.CompProg
import all GraphIso.Graph.Components
import all GraphIso.Graph.Domain
import all GraphIso.Graph.EdgeProg
import all GraphIso.Graph.Entry
import all GraphIso.Graph.Ind
import all GraphIso.Graph.IndProg
import all GraphIso.Graph.Layers
import all GraphIso.Graph.Levels
import all GraphIso.Graph.LevelsProg
import all GraphIso.Graph.Lift
import all GraphIso.Graph.LiftProg
import all GraphIso.Graph.Perms
import all GraphIso.Graph.SimpleGraph
import all GraphIso.Graph.Step
import all GraphIso.Graph.StepModel
import all GraphIso.Graph.StepProg
import all GraphIso.Graph.Subsets
import all GraphIso.Graph.Swap
import all GraphIso.Graph.Twins
import all GraphIso.Graph.TwoGroup
import all GraphIso.Graph.Validate
import all GraphIso.GroupOps.Enumeration
import all GraphIso.GroupOps.EnumerationProg
import all GraphIso.GroupOps.Interface
import all GraphIso.Groups.BoundedLinear
import all GraphIso.Groups.Coprime
import all GraphIso.Groups.FactorAction
import all GraphIso.Groups.LinearPGroup
import all GraphIso.Groups.MinimalNormal
import all GraphIso.Groups.NoAbelian
import all GraphIso.Groups.PCore
import all GraphIso.Groups.PrimitiveBounded
import all GraphIso.Groups.PrimitiveSolvable
import all GraphIso.Groups.Radical
import all GraphIso.Groups.Sections
import all GraphIso.Groups.SolvableLinear
import all GraphIso.Groups.Subdirect
import all GraphIso.Luks.Basic
import all GraphIso.Luks.Bounded
import all GraphIso.Luks.Closure
import all GraphIso.Luks.Correctness
import all GraphIso.Luks.Cost
import all GraphIso.Luks.Entry
import all GraphIso.Luks.MaxBlocks
import all GraphIso.Luks.MaxBlocksProg
import all GraphIso.Luks.Nilpotent
import all GraphIso.Luks.Primitive
import all GraphIso.Luks.Solvable
import all GraphIso.Luks.Strategy
import all GraphIso.Main.CJohnOps
import all GraphIso.Main.Derive
import all GraphIso.Main.DeriveModel
import all GraphIso.Main.DynSeq
import all GraphIso.Main.Frame
import all GraphIso.Main.Free
import all GraphIso.Main.Full
import all GraphIso.Main.FullCase
import all GraphIso.Main.FullPot
import all GraphIso.Main.FullProg
import all GraphIso.Main.FullSharp
import all GraphIso.Main.FullStep
import all GraphIso.Main.GraphEntry
import all GraphIso.Main.GraphEntryProg
import all GraphIso.Main.GraphQP
import all GraphIso.Main.Growth
import all GraphIso.Main.GrowthCosts
import all GraphIso.Main.HInst
import all GraphIso.Main.M2bLoop
import all GraphIso.Main.M4Bridge
import all GraphIso.Main.M4Step
import all GraphIso.Main.M4Struct
import all GraphIso.Main.M5Align
import all GraphIso.Main.M5CJData
import all GraphIso.Main.M5CJLeaf
import all GraphIso.Main.M5CJProg
import all GraphIso.Main.M5CJWf
import all GraphIso.Main.M5Case2bCJ
import all GraphIso.Main.M5Case3CJ
import all GraphIso.Main.M5Cases
import all GraphIso.Main.M5CasesNs
import all GraphIso.Main.M5Cert
import all GraphIso.Main.M5Core
import all GraphIso.Main.M5Restrict
import all GraphIso.Main.M5Step
import all GraphIso.Main.M5StepCJ
import all GraphIso.Main.M5StepNs
import all GraphIso.Main.Mini
import all GraphIso.Main.PotQ
import all GraphIso.Main.PotThr
import all GraphIso.Main.PotWork
import all GraphIso.Main.QPBound
import all GraphIso.Main.QPJ
import all GraphIso.Main.RD
import all GraphIso.Main.Reduce
import all GraphIso.Main.SharpWork
import all GraphIso.Main.SimsCounts
import all GraphIso.Main.SimsM4
import all GraphIso.Main.SimsM5
import all GraphIso.Main.SimsM5Ns
import all GraphIso.Main.SimsRD
import all GraphIso.Main.SimsSteps
import all GraphIso.Main.StepsBase
import all GraphIso.Main.StepsHint
import all GraphIso.Main.Transfer
import all GraphIso.Palomar.Bridge
import all GraphIso.Palomar.Statement
import all GraphIso.Programs.Checks
import all GraphIso.Programs.List
import all GraphIso.Programs.Perm
import all GraphIso.Programs.Validate
import all GraphIso.Programs.Window
import all GraphIso.Pyber.Bridge
import all GraphIso.Pyber.CompA
import all GraphIso.Pyber.Discharge
import all GraphIso.Pyber.Families
import all GraphIso.Pyber.Generators
import all GraphIso.Pyber.Imprimitive
import all GraphIso.Pyber.Lemma12
import all GraphIso.Pyber.MinNormal
import all GraphIso.Pyber.OddOrder
import all GraphIso.Pyber.Orbital
import all GraphIso.Pyber.Primes
import all GraphIso.Pyber.Residual
import all GraphIso.Pyber.Theorem7
import all GraphIso.Pyber.Wielandt
import all GraphIso.Recursion.Align
import all GraphIso.Recursion.Coarsen
import all GraphIso.Recursion.Hint
import all GraphIso.Recursion.PotOffset
import all GraphIso.Recursion.Potential
import all GraphIso.Recursion.Primitive
import all GraphIso.Recursion.Progress
import all GraphIso.Recursion.Pullback
import all GraphIso.Reductions.BlockAction
import all GraphIso.Reductions.BlockKernelProg
import all GraphIso.Reductions.Blocks
import all GraphIso.Reductions.BlocksProg
import all GraphIso.Reductions.Data
import all GraphIso.Reductions.Restriction
import all GraphIso.Reductions.RestrictionData
import all GraphIso.Reductions.RestrictionProg
import all GraphIso.Reductions.Sequential
import all GraphIso.Reductions.SequentialProg
import all GraphIso.Reductions.Subgroup
import all GraphIso.Reductions.SubgroupProg
import all GraphIso.Representation.Encoding
import all GraphIso.Representation.Group
import all GraphIso.Representation.Permutation
import all GraphIso.Semantics.Action
import all GraphIso.Semantics.Coset
import all GraphIso.Semantics.StringIso
import all GraphIso.Semantics.Window
import all GraphIso.Sims.Basic
import all GraphIso.Sims.Construct
import all GraphIso.Sims.ConstructProg
import all GraphIso.Sims.Cosets
import all GraphIso.Sims.CosetsProg
import all GraphIso.Sims.Ops
import all GraphIso.Sims.OpsProg
import all GraphIso.Sims.Oracle
import all GraphIso.Sims.Orbits
import all GraphIso.Sims.OrbitsProg
import all GraphIso.Sims.SiftProg
import all GraphIso.Sims.Table
import all GraphIso.Sims.Wf
import all GraphIso.SoJProg.BaseCase
import all GraphIso.SoJProg.BaseCaseData
import all GraphIso.SoJProg.Coherent
import all GraphIso.SoJProg.DLTest
import all GraphIso.SoJProg.Dary
import all GraphIso.SoJProg.Data
import all GraphIso.SoJProg.Johnson
import all GraphIso.SoJProg.JohnsonData
import all GraphIso.SoJProg.Twins
import all GraphIso.SoJProg.TwinsData
import all GraphIso.SoJProg.WLSets
import all GraphIso.SoJTree.Frame
import all GraphIso.SoJTree.LeafBound
import all GraphIso.SoJTree.LeafData
import all GraphIso.SoJTree.LeafProg
import all GraphIso.SoJTree.LeafStab
import all GraphIso.SoJTree.Measure
import all GraphIso.SoJTree.OrbitClosure
import all GraphIso.SoJTree.OrbitStab
import all GraphIso.SoJTree.StepProg
import all GraphIso.SoJTree.Trees
import all GraphIso.SoJTree.Worklist
import all GraphIso.Solver.Basic
import all GraphIso.Solver.Checked
import all GraphIso.Solver.Coherent
import all GraphIso.Solver.Compose
import all GraphIso.Solver.Correctness
import all GraphIso.Solver.Cost
import all GraphIso.Solver.Entry
import all GraphIso.Solver.Facts
import all GraphIso.Solver.Graph
import all GraphIso.Solver.GraphAll
import all GraphIso.Solver.Luks
import all GraphIso.Solver.LuksBounded
import all GraphIso.Solver.LuksSolvable
import all GraphIso.Solver.Main
import all GraphIso.Solver.Reference
import all GraphIso.Solver.ReferenceCompose
import all GraphIso.Solver.Sims
import all GraphIso.Solver.SimsCompose
import all GraphIso.Solver.Valence
import all GraphIso.Solver.ValenceAll
import all GraphIso.Solver.ValenceBounded
import all GraphIso.SplitJohnson.BipRelabelAux
import all GraphIso.SplitJohnson.Bipartite
import all GraphIso.SplitJohnson.BipartiteBasic
import all GraphIso.SplitJohnson.BipartiteCount
import all GraphIso.SplitJohnson.BipartiteDL
import all GraphIso.SplitJohnson.BipartiteDary
import all GraphIso.SplitJohnson.BipartiteDef
import all GraphIso.SplitJohnson.BipartiteRelabel
import all GraphIso.SplitJohnson.BipartiteValid
import all GraphIso.SplitJohnson.CTree
import all GraphIso.SplitJohnson.CoherentDef
import all GraphIso.SplitJohnson.CoherentSpec
import all GraphIso.SplitJohnson.DLAux
import all GraphIso.SplitJohnson.Main
import all GraphIso.SplitJohnson.MainDef
import all GraphIso.SplitJohnson.Output
import all GraphIso.SplitJohnson.Relabel
import all GraphIso.TM.Alloc
import all GraphIso.TM.Arith
import all GraphIso.TM.Bits
import all GraphIso.TM.Code
import all GraphIso.TM.Compile
import all GraphIso.TM.Env
import all GraphIso.TM.GI
import all GraphIso.TM.Heap
import all GraphIso.TM.Load
import all GraphIso.TM.Lookup
import all GraphIso.TM.Machine
import all GraphIso.TM.Main
import all GraphIso.TM.Num
import all GraphIso.TM.PrimLib
import all GraphIso.TM.Prims
import all GraphIso.TM.Rep
import all GraphIso.TM.Sat
import all GraphIso.TM.Ser
import all GraphIso.TM.SingleTape.Compile
import all GraphIso.TM.SingleTape.GI
import all GraphIso.TM.SingleTape.IO
import all GraphIso.TM.SingleTape.Model
import all GraphIso.TM.SingleTape.Programs
import all GraphIso.TM.SingleTape.Sim
import all GraphIso.TM.SingleTape.TM1Sim
import all GraphIso.TM.SingleTape.TM2Sim
import all GraphIso.TM.Vertices
import all GraphIso.TM.Write
import all GraphIso.Toolkit.Base
import all GraphIso.Toolkit.BaseBlocks
import all GraphIso.Toolkit.BlockStab
import all GraphIso.Toolkit.Extend
import all GraphIso.Toolkit.Labels
import all GraphIso.Toolkit.Orbital
import all GraphIso.Toolkit.Reduce
import all GraphIso.Toolkit.Transitivity
import all GraphIso.Valence.Algorithm
import all GraphIso.Valence.All
import all GraphIso.Valence.Bounded
import all GraphIso.Valence.CompProg
import all GraphIso.Valence.Domain
import all GraphIso.Valence.EdgeProg
import all GraphIso.Valence.Entry
import all GraphIso.Valence.Ind
import all GraphIso.Valence.LevelsProg
import all GraphIso.Valence.LiftProg
import all GraphIso.Valence.Solvable
import all GraphIso.Valence.Step
import all GraphIso.Valence.StepModel
import all GraphIso.Valence.StepProg
import all GraphIso.Valence.Subsets
import all GraphIso.Valence.Validate
import all GraphIso.Wielandt.Bound
import all GraphIso.Wielandt.Commutator
import all GraphIso.Wielandt.Final
import all GraphIso.Wielandt.Power
import all GraphIso.Wielandt.Support
import all GraphIsoChecks.Align
import all GraphIsoChecks.AltQuot
import all GraphIsoChecks.Case2b
import all GraphIsoChecks.Case3
import all GraphIsoChecks.CertProg
import all GraphIsoChecks.Certificates
import all GraphIsoChecks.Coherent
import all GraphIsoChecks.Conventions
import all GraphIsoChecks.Cost
import all GraphIsoChecks.Coverage
import all GraphIsoChecks.Exec
import all GraphIsoChecks.ExecSteps
import all GraphIsoChecks.Execution
import all GraphIsoChecks.Giant
import all GraphIsoChecks.Graph
import all GraphIsoChecks.GraphAll
import all GraphIsoChecks.GraphBrute
import all GraphIsoChecks.GraphQP
import all GraphIsoChecks.Luks
import all GraphIsoChecks.LuksBounded
import all GraphIsoChecks.LuksSolvable
import all GraphIsoChecks.MainFull
import all GraphIsoChecks.MainHints
import all GraphIsoChecks.MainM4
import all GraphIsoChecks.MainM5
import all GraphIsoChecks.MainM5CJ
import all GraphIsoChecks.MainM5CJRoute
import all GraphIsoChecks.MainM5b
import all GraphIsoChecks.MainMini
import all GraphIsoChecks.MainSimsSteps
import all GraphIsoChecks.MainSteps
import all GraphIsoChecks.MathlibAPI
import all GraphIsoChecks.NoStuck
import all GraphIsoChecks.Palomar
import all GraphIsoChecks.Pot
import all GraphIsoChecks.Pyber
import all GraphIsoChecks.PyberLemma12
import all GraphIsoChecks.PyberPerm
import all GraphIsoChecks.PyberThm7
import all GraphIsoChecks.QPBound
import all GraphIsoChecks.Recursion
import all GraphIsoChecks.Reductions
import all GraphIsoChecks.Reference
import all GraphIsoChecks.Restriction
import all GraphIsoChecks.Semantics
import all GraphIsoChecks.Sharp
import all GraphIsoChecks.Sims
import all GraphIsoChecks.SoJProg
import all GraphIsoChecks.SoJTree
import all GraphIsoChecks.SplitJohnson
import all GraphIsoChecks.Sweep
import all GraphIsoChecks.TM1Sim
import all GraphIsoChecks.TM2Sim
import all GraphIsoChecks.TMArith
import all GraphIsoChecks.TMCode
import all GraphIsoChecks.TMCompile
import all GraphIsoChecks.TMGI
import all GraphIsoChecks.TMGISingleTape
import all GraphIsoChecks.TMHeap
import all GraphIsoChecks.TMIO
import all GraphIsoChecks.TMMain
import all GraphIsoChecks.TMPrims
import all GraphIsoChecks.TMSim
import all GraphIsoChecks.TMSingleTape
import all GraphIsoChecks.TMSingleTapeModel
import all GraphIsoChecks.TMVertices
import all GraphIsoChecks.Toolkit
import all GraphIsoChecks.Valence
import all GraphIsoChecks.ValenceBounded
import all GraphIsoChecks.WellFormed
import all GraphIsoChecks.WielandtBound
import all GraphIsoChecks.WielandtFinal
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-!
# Logical audit

Checks every declaration defined in a `GraphIso` or `GraphIsoChecks` module: each may depend
only on `propext`, `Classical.choice` and `Quot.sound`. This rejects `sorry`, project axioms,
and `native_decide` (which introduces an auxiliary axiom). It also checks that every Lean
source file of the package (other than this file and the `GraphIsoChecks` root importing it)
is in this module's import closure, so nothing escapes the audit.

This file is a module (Lean's module system, `PLAN-19.md` §4). A module sees the private
declarations of another module only when it imports that module directly with `import all`, so
the header imports every module of the package that way; `scripts/gen-audit-imports.py`
generates it. The check below therefore requires every module to be loaded with all its data
(`importAll`), not merely to be in the import closure: a module reached only through other
imports would hide its private declarations from the enumeration.

The audit does not decide whether a definition or an unfolded theorem statement expresses the
intended claim; that requires review against `PLAN.md` and `docs/theorem-map.md`.

The axioms of the principal theorems are also listed by name in the build output.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let inProject (m : Name) : Bool :=
    (`GraphIso).isPrefixOf m || (`GraphIsoChecks).isPrefixOf m
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    if inProject mod then
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "{name} (in {mod}) depends on forbidden axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations found: the audit did not run."
  -- every source file under the two library roots must be imported here with `import all`
  let imported := (env.header.modules.filter fun m =>
    inProject m.module && m.importAll && m.hasData).map (·.module)
  let mut onDisk : Array Name := #[]
  for root in ["GraphIso", "GraphIsoChecks"] do
    onDisk := onDisk.push (Name.mkSimple root)
    for path in ← System.FilePath.walkDir root do
      if path.extension == some "lean" then
        let comps := (path.withExtension "").components
        onDisk := onDisk.push (comps.foldl (fun n s => Name.str n s) Name.anonymous)
  -- the audit itself, and the `GraphIsoChecks` root that imports it
  let exempt := #[`GraphIsoChecks.AxiomAudit, `GraphIsoChecks]
  for m in onDisk do
    unless exempt.contains m || imported.contains m do
      throwError "module {m} is not imported here with `import all` (run \
        scripts/gen-audit-imports.py)"
  logInfo m!"Axiom audit passed for {checked} project declarations in \
    {imported.size + 1} modules."

/-! ### The principal theorems -/

open Lean in
run_cmd do
  let principal := #[
    ``GraphIso.iso_eq_smul_aut,
    ``GraphIso.Solver.solve_correct, ``GraphIso.Solver.solve_none_iff,
    ``GraphIso.Solver.solve_some_group, ``GraphIso.Solver.solve_cost_le,
    ``GraphIso.Solver.solveEntry_spec, ``GraphIso.Solver.solve_backend_refinement,
    ``GraphIso.Solver.solveChecked_spec,
    ``GraphIso.Reference.refImpl_implements, ``GraphIso.Reference.solve_reference,
    ``GraphIso.Reference.solve_reference_checked,
    ``GraphIso.iso_eq_of_restrict, ``GraphIso.Programs.RunsWithin.restrictProg,
    ``GraphIso.Programs.RunsWithin.blockReduceProg,
    ``GraphIso.Solver.restrict_solve_spec, ``GraphIso.Solver.blockReduce_solve_spec,
    ``GraphIso.Reference.restrict_reference, ``GraphIso.Reference.blockReduce_reference,
    ``GraphIso.Sims.complete_of_closed, ``GraphIso.Sims.complete_build,
    ``GraphIso.Sims.RunsWithin.buildProg, ``GraphIso.Sims.orbitBFS_spec,
    ``GraphIso.Sims.orbitsModel_spec, ``GraphIso.Sims.cosetRepsModel_spec,
    ``GraphIso.Sims.liftModel_spec, ``GraphIso.Sims.ssOracle_meets,
    ``GraphIso.Sims.ssImpl_implements, ``GraphIso.Sims.ssImpl_wf, ``GraphIso.Sims.solve_sims,
    ``GraphIso.Sims.solve_sims_checked, ``GraphIso.Sims.restrict_sims,
    ``GraphIso.Sims.blockReduce_sims, ``GraphIso.Sims.simsQ_le, ``GraphIso.Sims.simsCost_le,
    ``GraphIso.Luks.closure_spec, ``GraphIso.Luks.maxLabels_spec,
    ``GraphIso.Luks.isPreprimitive_blocksOf, ``GraphIso.Luks.maxBlocks_spec,
    ``GraphIso.Luks.card_range_mul_card_blockKernel, ``GraphIso.Luks.RunsWithin.closureProg,
    ``GraphIso.Luks.RunsWithin.maxBlocksProg, ``GraphIso.Luks.luksBody_wf,
    ``GraphIso.Luks.luks_spec, ``GraphIso.Luks.luksEntry_spec,
    ``GraphIso.Luks.luks_backend_refinement, ``GraphIso.Luks.luksChecked_spec,
    ``GraphIso.Luks.card_eq_of_isPreprimitive_of_isNilpotent,
    ``GraphIso.Luks.primBounded_of_isNilpotent, ``GraphIso.Luks.primBounded_degree,
    ``GraphIso.Sims.luksSimsQ_le, ``GraphIso.Sims.luksSimsCost_le, ``GraphIso.Sims.solve_luks,
    ``GraphIso.Sims.solve_luks_checked, ``GraphIso.Sims.solve_luks_any,
    ``GraphIso.Sims.solve_luks_nilpotent, ``GraphIso.Sims.luksSimsCost_one_le,
    ``GraphIso.Graph.levels_spec, ``GraphIso.Graph.cnt_le_two, ``GraphIso.Graph.liftPerm_mem,
    ``GraphIso.Graph.autR_succ_eq, ``GraphIso.Graph.isPGroup_autR,
    ``GraphIso.Graph.closure_gens0, ``GraphIso.Graph.iso_iff_exists_gen,
    ``GraphIso.Graph.exists_iso_of_swap, ``GraphIso.Graph.xstr_iff,
    ``GraphIso.Graph.indHom_injective, ``GraphIso.Graph.denote_map_indData,
    ``GraphIso.Graph.readback, ``GraphIso.Graph.indDataB_eq, ``GraphIso.Graph.liftDataB_eq,
    ``GraphIso.Graph.nextGens_spec, ``GraphIso.Graph.RunsWithin.stepProg,
    ``GraphIso.Graph.RunsWithin.levelsProg, ``GraphIso.Graph.RunsWithin.edgeProg,
    ``GraphIso.Graph.reach_union, ``GraphIso.Graph.RunsWithin.mainProg,
    ``GraphIso.Graph.mem_HR_iff_extends, ``GraphIso.Graph.validGB_iff,
    ``GraphIso.Graph.RunsWithin.validGraphProg, ``GraphIso.Graph.conn_iff_connected,
    ``GraphIso.Graph.nonempty_iso_iff, ``GraphIso.Graph.gi3Checked_wf,
    ``GraphIso.Graph.RunsWithin.gi3Checked, ``GraphIso.Graph.checkedCost_le,
    ``GraphIso.Graph.gi3_checked, ``GraphIso.Graph.gi3_simpleGraph,
    ``GraphIso.Graph.toSimpleGraph_ofSimpleGraph, ``GraphIso.Graph.valid_ofSimpleGraph,
    ``GraphIso.Graph.gi3_simpleGraph',
    ``GraphIso.Graph.lev_lt_iff_reach, ``GraphIso.Graph.conn_subG, ``GraphIso.Graph.valid_subG,
    ``GraphIso.Graph.giso_imgComp, ``GraphIso.Graph.balanced_comps,
    ``GraphIso.Graph.Balanced.exists, ``GraphIso.Graph.Balanced.step,
    ``GraphIso.Graph.Balanced.eq_nil, ``GraphIso.Graph.glue_spec,
    ``GraphIso.Graph.RunsWithin.compsProg, ``GraphIso.Graph.RunsWithin.subGProg,
    ``GraphIso.Graph.RunsWithin.glueProg, ``GraphIso.Graph.RunsWithin.partnerStepProg,
    ``GraphIso.Graph.RunsWithin.matchStepProg, ``GraphIso.Graph.RunsWithin.allProg,
    ``GraphIso.Graph.wf_allProg, ``GraphIso.Graph.gi3AllChecked_wf,
    ``GraphIso.Graph.RunsWithin.gi3AllChecked, ``GraphIso.Graph.allCheckedCost_le,
    ``GraphIso.Graph.gi3_all_checked, ``GraphIso.Graph.gi3_all_simpleGraph,
    ``GraphIso.Graph.gi3_all_simpleGraph',
    ``GraphIso.Groups.card_le_two_pow_of_isPGroup_perm,
    ``GraphIso.Groups.centralizer_le_of_maximal, ``GraphIso.Groups.isReduced_adjoin_range,
    ``GraphIso.Groups.exists_idempotents, ``GraphIso.Groups.card_eq_prod_zeroSpace,
    ``GraphIso.Groups.card_le_of_isPGroup, ``GraphIso.Groups.card_le_of_isPGroup',
    ``GraphIso.Groups.card_le_of_coprime, ``GraphIso.Groups.exists_pcore,
    ``GraphIso.Groups.centralizer_le_of_pcore, ``GraphIso.Groups.card_le_of_isSolvable_linear,
    ``GraphIso.Groups.card_le_of_isQuasiPreprimitive_of_isSolvable,
    ``GraphIso.Groups.card_le_of_isPreprimitive_of_isSolvable,
    ``GraphIso.Luks.primBounded_of_isSolvable, ``GraphIso.Sims.luksSimsCost_le_pow,
    ``GraphIso.Sims.solve_luks_solvable,
    ``GraphIso.Graph.cnt_le, ``GraphIso.Graph.mem_closure_twinSwaps,
    ``GraphIso.Graph.Valence.mem_subsR, ``GraphIso.Graph.Valence.length_subsR_le,
    ``GraphIso.Graph.Valence.subAt_inj, ``GraphIso.Graph.Valence.subSet_subImg,
    ``GraphIso.Graph.Valence.xstr_iff, ``GraphIso.Graph.Valence.xSub_eq,
    ``GraphIso.Graph.Valence.indHom_injective, ``GraphIso.Graph.Valence.denote_map_indData,
    ``GraphIso.Graph.Valence.readback, ``GraphIso.Graph.Valence.isSolvable_pi,
    ``GraphIso.Graph.Valence.pow_twelve_eq_one, ``GraphIso.Graph.Valence.twinHom_injective,
    ``GraphIso.Graph.Valence.isSolvable_ker, ``GraphIso.Graph.Valence.ker_pow_twelve,
    ``GraphIso.Graph.Valence.isSolvable_autR, ``GraphIso.Graph.Valence.exists_pow_eq_one,
    ``GraphIso.Graph.Valence.card_primeFactors_autR_le,
    ``GraphIso.Graph.Valence.RunsWithin.levelsProg, ``GraphIso.Graph.Valence.indDataB_eq,
    ``GraphIso.Graph.Valence.RunsWithin.subsProg, ``GraphIso.Graph.Valence.RunsWithin.indProg,
    ``GraphIso.Graph.Valence.RunsWithin.xArrProg, ``GraphIso.Graph.Valence.RunsWithin.liftProg,
    ``GraphIso.Graph.Valence.RunsWithin.twinsProg,
    ``GraphIso.Graph.Valence.layerPrim_solvable, ``GraphIso.Graph.Valence.RunsWithin.stepProg,
    ``GraphIso.Graph.Valence.RunsWithin.edgeProg, ``GraphIso.Graph.Valence.RunsWithin.mainProg,
    ``GraphIso.Graph.Valence.wf_mainProg, ``GraphIso.Graph.Valence.validGB_iff,
    ``GraphIso.Graph.Valence.RunsWithin.validGraphProg, ``GraphIso.Graph.gi5Checked_wf,
    ``GraphIso.Graph.RunsWithin.gi5Checked, ``GraphIso.Graph.checkedCost5_le,
    ``GraphIso.Graph.gi5_checked, ``GraphIso.Graph.gi5_simpleGraph,
    ``GraphIso.Graph.gi5_simpleGraph', ``GraphIso.Graph.Valence.RunsWithin.allProg,
    ``GraphIso.Graph.Valence.wf_allProg, ``GraphIso.Graph.gi5AllChecked_wf,
    ``GraphIso.Graph.RunsWithin.gi5AllChecked, ``GraphIso.Graph.allCheckedCost5_le,
    ``GraphIso.Graph.gi5_all_checked, ``GraphIso.Graph.gi5_all_simpleGraph,
    ``GraphIso.Graph.gi5_all_simpleGraph',
    ``GraphIso.Groups.BoundedSections.of_ker, ``GraphIso.Groups.BoundedSections.pi,
    ``GraphIso.Groups.BoundedSections.card_primeFactors_le,
    ``GraphIso.Groups.exists_simple_factors, ``GraphIso.Groups.card_le_of_factors,
    ``GraphIso.Groups.two_pow_mul_card_sq_le, ``GraphIso.Groups.isSolvable_sup,
    ``GraphIso.Groups.exists_radical, ``GraphIso.Groups.eq_bot_of_abelian_normal_quotient,
    ``GraphIso.Groups.eq_bot_of_normal_isPGroup_of_normal,
    ``GraphIso.Groups.NoAbelianNormal.centralizer,
    ``GraphIso.Groups.exists_card_le_of_noAbelianNormal,
    ``GraphIso.Groups.card_le_of_boundedSections_linear,
    ``GraphIso.Groups.card_le_of_isQuasiPreprimitive_of_abelian,
    ``GraphIso.Groups.card_le_of_isQuasiPreprimitive_of_nonabelian,
    ``GraphIso.Groups.card_le_of_isQuasiPreprimitive_of_boundedSections,
    ``GraphIso.Groups.card_le_of_isPreprimitive_of_boundedSections,
    ``GraphIso.Luks.primBounded_of_boundedSections, ``GraphIso.Sims.solve_luks_bounded,
    ``GraphIso.Groups.BoundedSections.mono, ``GraphIso.Groups.boundedSections_of_isPGroup,
    ``GraphIso.Graph.Valence.card_tw_le_pred, ``GraphIso.Graph.Valence.boundedSections_ker,
    ``GraphIso.Graph.Valence.boundedSections_autR, ``GraphIso.Graph.Valence.layerPrim_bounded,
    ``GraphIso.Graph.giBoundedChecked_wf, ``GraphIso.Graph.RunsWithin.giBoundedChecked,
    ``GraphIso.Graph.giBoundedAllChecked_wf, ``GraphIso.Graph.RunsWithin.giBoundedAllChecked,
    ``GraphIso.Graph.layerCost_le_pow, ``GraphIso.Graph.mainCost_le_pow,
    ``GraphIso.Graph.checkedCostB_le_pow, ``GraphIso.Graph.allCheckedCostB_le_pow,
    ``GraphIso.Graph.gi_bounded_checked, ``GraphIso.Graph.gi_bounded_simpleGraph,
    ``GraphIso.Graph.gi_bounded_simpleGraph', ``GraphIso.Graph.gi_bounded_all_checked,
    ``GraphIso.Graph.gi_bounded_all_simpleGraph, ``GraphIso.Graph.gi_bounded_all_simpleGraph',
    ``GraphIso.Coherent.IsCoherent.card_filter_pred,
    ``GraphIso.Coherent.IsCoherent2.card_filter_pred,
    ``GraphIso.Coherent.fisher_inequality, ``GraphIso.Coherent.isTwin2_of_large_clique,
    ``GraphIso.Coherent.isCoherent2_skel2, ``GraphIso.Coherent.isCoherent2_restrict,
    ``GraphIso.Coherent.skel1_relabel, ``GraphIso.Coherent.skel2_relabel,
    ``GraphIso.Coherent.design_lemma_of_le_succ, ``GraphIso.Coherent.design_lemma,
    ``GraphIso.Coherent.wlStep_wlIter,
    ``GraphIso.Coherent.wl_isCoherent, ``GraphIso.Coherent.wl_decode,
    ``GraphIso.Coherent.wl_refines, ``GraphIso.Coherent.wl_relabel,
    ``GraphIso.Coherent.wl_iso_iff, ``GraphIso.Coherent.isTwin_wl_iff,
    ``GraphIso.Coherent.lexCmp_eq, ``GraphIso.Coherent.sortM_eq,
    ``GraphIso.Coherent.dedupSortM_eq, ``GraphIso.Coherent.idxM_eq,
    ``GraphIso.Coherent.tupList_eq, ``GraphIso.Coherent.infoAt_enc,
    ``GraphIso.Coherent.stepA_repSt, ``GraphIso.Coherent.initA_eq, ``GraphIso.Coherent.wlA_eq,
    ``GraphIso.Coherent.RunsWithin.wlProg, ``GraphIso.Coherent.wf_wlProg,
    ``GraphIso.Coherent.goodA_iff, ``GraphIso.Coherent.mem_cands,
    ``GraphIso.Coherent.searchA_eq_some, ``GraphIso.Coherent.searchA_eq_none,
    ``GraphIso.Coherent.RunsWithin.searchProg, ``GraphIso.Coherent.wf_searchProg,
    ``GraphIso.Coherent.wlChecked_wf, ``GraphIso.Coherent.descentChecked_wf,
    ``GraphIso.Coherent.RunsWithin.wlChecked, ``GraphIso.Coherent.RunsWithin.descentChecked,
    ``GraphIso.Coherent.wlCheckedCost_le, ``GraphIso.Coherent.descentCheckedCost_le,
    ``GraphIso.Coherent.wl_checked, ``GraphIso.Coherent.descent_checked,
    ``GraphIso.Coherent.isCoherent2_wl_skel2, ``GraphIso.Coherent.skel1_wl_relabel,
    ``GraphIso.Coherent.ray_chaudhuri_wilson, ``GraphIso.Coherent.wlOn_eq,
    ``GraphIso.Coherent.wlOn_isCoherent, ``GraphIso.Coherent.wlOn_refines,
    ``GraphIso.Coherent.isTwin_wlOn_iff, ``GraphIso.Coherent.wlOn_natural,
    ``GraphIso.Coherent.mem_comp, ``GraphIso.Coherent.IsCoh2On.subset,
    ``GraphIso.Coherent.IsCoh2On.symm_of_large,
    ``GraphIso.Coherent.IsCoh2On.not_isClique_of_large, ``GraphIso.Coherent.IsCoh2On.reach_iff,
    ``GraphIso.Coherent.IsCoh2On.walkCount_eq,
    ``GraphIso.Coherent.IsCoh2On.card_comp_eq, ``GraphIso.Coherent.IsCoh2On.two_le_card_comp,
    ``GraphIso.Coherent.IsCoh2On.two_mul_card_comp_le, ``GraphIso.Coherent.IsCoh2On.twin_iff,
    ``GraphIso.Coherent.IsCoh2On.twinAll_iff, ``GraphIso.Coherent.IsCoh2On.contract_deg_blocks,
    ``GraphIso.Coherent.IsCoh2On.contract_deg_points,
    ``GraphIso.Coherent.IsUniprimitive.exists_common,
    ``GraphIso.Coherent.two_mul_card_twinCls_le, ``GraphIso.Coherent.twin_split,
    ``GraphIso.SplitJohnson.CTree.reach_act, ``GraphIso.SplitJohnson.CTree.count_act,
    ``GraphIso.SplitJohnson.CTree.count_bind_le, ``GraphIso.SplitJohnson.CTree.act_bind,
    ``GraphIso.SplitJohnson.CTree.act_trans,
    ``GraphIso.SplitJohnson.coherent_split_or_johnson,
    ``GraphIso.SplitJohnson.coherent_split_or_johnson_relabel,
    ``GraphIso.SplitJohnson.johnson_valid, ``GraphIso.SplitJohnson.bigTwins_card_lt,
    ``GraphIso.SplitJohnson.exists_dlGood, ``GraphIso.SplitJohnson.dlCont_valid,
    ``GraphIso.SplitJohnson.bsoj_valid, ``GraphIso.SplitJohnson.bsoj_count_le,
    ``GraphIso.SplitJohnson.bipartite_split_or_johnson,
    ``GraphIso.SplitJohnson.bipartite_split_or_johnson_relabel,
    ``GraphIso.SplitJohnson.split_or_johnson, ``GraphIso.SplitJohnson.split_or_johnson_relabel,
    ``GraphIso.SplitJohnson.split_or_johnson_reach,
    ``GraphIso.AltQuot.altQuotientIso_succ, ``GraphIso.AltQuot.transitivityBound_id,
    ``GraphIso.AltQuot.alternatingGroup_commutator, ``GraphIso.AltQuot.card_le_index_of_ne_top,
    ``GraphIso.AltQuot.card_le_index_of_not_le, ``GraphIso.AltQuot.exists_le_ker_of_simple,
    ``GraphIso.AltQuot.stabilizer_map_ne_top, ``GraphIso.AltQuot.exists_affected,
    ``GraphIso.AltQuot.unaffected_stabilizer, ``GraphIso.AltQuot.card_orbit_ker_mul_index,
    ``GraphIso.AltQuot.affected_orbit, ``GraphIso.AltQuot.choose_mul_choose_le,
    ``GraphIso.AltQuot.card_sameCounts_le, ``GraphIso.AltQuot.choose_mul_pow_le,
    ``GraphIso.AltQuot.card_sameCounts_le_of_le,
    ``GraphIso.Certificates.beard_stable, ``GraphIso.Certificates.beardH_le_autW,
    ``GraphIso.Certificates.autW_univ_le_beard, ``GraphIso.Certificates.beardH_eq_autW,
    ``GraphIso.Certificates.aff_subset_beardW, ``GraphIso.Certificates.cert_full,
    ``GraphIso.Certificates.cert_not_full, ``GraphIso.Certificates.isFull_iff,
    ``GraphIso.Certificates.kernel_orbit, ``GraphIso.Certificates.beard_relabel,
    ``GraphIso.Certificates.isGiantOn_relabel, ``GraphIso.Certificates.isFull_relabel,
    ``GraphIso.Certificates.certK_relabel, ``GraphIso.Certificates.certM_relabel,
    ``GraphIso.Certificates.exists_degree, ``GraphIso.Certificates.exists_orbitPart,
    ``GraphIso.Certificates.orbitPart_valid, ``GraphIso.Certificates.large_orbit_unique,
    ``GraphIso.Certificates.fixing_transitive_not_two, ``GraphIso.Certificates.orbital_config,
    ``GraphIso.Certificates.fullGroup_le_autG, ``GraphIso.Certificates.fullGroup_relabel,
    ``GraphIso.Certificates.supp_conj, ``GraphIso.Certificates.no_large_twins,
    ``GraphIso.Recursion.card_fiber_smul, ``GraphIso.Recursion.card_fiber_le,
    ``GraphIso.Recursion.lab_smul_of_fix, ``GraphIso.Recursion.le_pot,
    ``GraphIso.Recursion.card_le_of_const,
    ``GraphIso.Recursion.IsHint.restrict, ``GraphIso.Recursion.hint_inter,
    ``GraphIso.Recursion.exists_nonConst_inter, ``GraphIso.Recursion.card_blockLabel_le,
    ``GraphIso.Recursion.card_blockSys_le, ``GraphIso.Recursion.hint_blockLabel,
    ``GraphIso.Recursion.hint_blockStab, ``GraphIso.Recursion.card_jUnion_le,
    ``GraphIso.Recursion.card_cells, ``GraphIso.Recursion.hint_jUnion,
    ``GraphIso.Recursion.fix_of_jUnion_const, ``GraphIso.Recursion.alt_le_iff,
    ``GraphIso.Recursion.exists_smul_eq_of_alt_le, ``GraphIso.Recursion.exists_blockStab_smul_eq,
    ``GraphIso.Recursion.orbital_uniprimitive, ``GraphIso.Recursion.colPart_orbit,
    ``GraphIso.Recursion.johnson_orbit, ``GraphIso.Recursion.iso_transporter,
    ``GraphIso.Recursion.iso_eq_align, ``GraphIso.Recursion.iso_reach,
    ``GraphIso.Recursion.index_stab_le_count, ``GraphIso.Recursion.cover_of_alt_le,
    ``GraphIso.Recursion.cover_of_alt_le_even, ``GraphIso.Recursion.iso_pullback,
    ``GraphIso.Recursion.aut_pullback, ``GraphIso.Recursion.two_mul_choose_le,
    ``GraphIso.Recursion.card_orbit_le_half, ``GraphIso.Recursion.kap_add_two_le,
    ``GraphIso.Recursion.pot_step, ``GraphIso.Recursion.pot_free, ``GraphIso.Recursion.pot0_le,
    ``GraphIso.Recursion.s_le_lam, ``GraphIso.Recursion.johnson_step_label,
    ``GraphIso.Recursion.orbit_child, ``GraphIso.Recursion.wlRel_natural,
    ``GraphIso.Recursion.wlRel_spec, ``GraphIso.Recursion.wlRel_uniprimitive,
    ``GraphIso.Recursion.wlRel_split_or_uniprimitive,
    ``GraphIso.Toolkit.baseHom_apply, ``GraphIso.Toolkit.HintValid.isHint,
    ``GraphIso.Toolkit.RunsWithin.rebaseProg, ``GraphIso.Toolkit.rebase_invariant,
    ``GraphIso.Toolkit.rebase_faithful, ``GraphIso.Toolkit.rebase_iso,
    ``GraphIso.Toolkit.RunsWithin.interLabProg, ``GraphIso.Toolkit.mem_subLab_iff_interLab,
    ``GraphIso.Toolkit.RunsWithin.blockLabProg, ``GraphIso.Toolkit.mem_blockLab_iff,
    ``GraphIso.Toolkit.RunsWithin.equidistProg, ``GraphIso.Toolkit.equidistB_iff,
    ``GraphIso.Toolkit.RunsWithin.jUnionProg, ``GraphIso.Toolkit.mem_jUnionData_iff,
    ``GraphIso.Toolkit.RunsWithin.complLabProg, ``GraphIso.Toolkit.mem_complLab_iff,
    ``GraphIso.Toolkit.RunsWithin.mapLabelsProg, ``GraphIso.Toolkit.getD_mapLabels,
    ``GraphIso.Toolkit.RunsWithin.degreeProg, ``GraphIso.Toolkit.degreeModel_spec,
    ``GraphIso.Toolkit.RunsWithin.giantProg, ``GraphIso.Toolkit.giantModel_iff,
    ``GraphIso.Toolkit.RunsWithin.baseBlocksProg, ``GraphIso.Toolkit.baseBlocks_spec,
    ``GraphIso.Toolkit.RunsWithin.orbitalProg, ``GraphIso.Toolkit.orbitalModel_spec,
    ``GraphIso.Toolkit.RunsWithin.relColProg, ``GraphIso.Toolkit.relColModel_spec,
    ``GraphIso.Toolkit.arrRel_orbital, ``GraphIso.Toolkit.RunsWithin.kerProg,
    ``GraphIso.Toolkit.RunsWithin.liftProg, ``GraphIso.Toolkit.RunsWithin.iterStabProg,
    ``GraphIso.Toolkit.RunsWithin.pointStabsProg, ``GraphIso.Toolkit.RunsWithin.giantSetStabProg,
    ``GraphIso.Toolkit.RunsWithin.blockStabProg,
    ``GraphIso.SoJProg.relOf_cell, ``GraphIso.SoJProg.card_setOf, ``GraphIso.SoJProg.card_famOf,
    ``GraphIso.SoJProg.deg_decode, ``GraphIso.SoJProg.twinCls_decode, ``GraphIso.SoJProg.tw_decode,
    ``GraphIso.SoJProg.tfDeg_decode, ``GraphIso.SoJProg.bigDegs_decode,
    ``GraphIso.SoJProg.optMin_bigDegs, ``GraphIso.SoJProg.twinPart_decode,
    ``GraphIso.SoJProg.RunsWithin.twinPartProg, ``GraphIso.SoJProg.RunsWithin.minBigDegProg,
    ``GraphIso.SoJProg.pascalRow_getD, ``GraphIso.SoJProg.nbr_decode, ``GraphIso.SoJProg.fOf_decode,
    ``GraphIso.SoJProg.johnson_decode, ``GraphIso.SoJProg.johnsonTest_decode,
    ``GraphIso.SoJProg.RunsWithin.chooseProg, ``GraphIso.SoJProg.RunsWithin.johnsonTestProg,
    ``GraphIso.SoJProg.RunsWithin.johnsonLeafProg, ``GraphIso.SoJProg.enums_decode,
    ``GraphIso.SoJProg.nbrCode_decode, ``GraphIso.SoJProg.colPart_decode,
    ``GraphIso.SoJProg.baseLeaf_decode, ``GraphIso.SoJProg.RunsWithin.enumsProg,
    ``GraphIso.SoJProg.RunsWithin.nbrCodeProg, ``GraphIso.SoJProg.RunsWithin.colBlkProg,
    ``GraphIso.SoJProg.RunsWithin.baseLeafProg, ``GraphIso.SoJProg.get_wlA_eq_wlOn,
    ``GraphIso.SoJProg.get_wlA_cells, ``GraphIso.SoJProg.cohOn_eq_wlA,
    ``GraphIso.SoJProg.cohOn_code_eq, ``GraphIso.SoJProg.RunsWithin.cohProg,
    ``GraphIso.SoJProg.clogD_eq, ``GraphIso.SoJProg.RunsWithin.clogProg,
    ``GraphIso.SoJProg.RunsWithin.arityProg, ``GraphIso.SoJProg.toFun_daryArr,
    ``GraphIso.SoJProg.wlOn_daryCol_eq, ``GraphIso.SoJProg.RunsWithin.daryArrProg,
    ``GraphIso.SoJProg.RunsWithin.daryWLProg, ``GraphIso.SoJProg.isTwin_cellSub_iff,
    ``GraphIso.SoJProg.bigTwins_decode, ``GraphIso.SoJProg.bigTwins_daryCol,
    ``GraphIso.SoJProg.RunsWithin.bigTwinsProg, ``GraphIso.SoJProg.pickSide_decode,
    ``GraphIso.SoJProg.RunsWithin.pickSideProg, ``GraphIso.SoJProg.goodA_iff_dlGood,
    ``GraphIso.SoJProg.dlGood_iff_goodA, ``GraphIso.SoJProg.goodList_decode,
    ``GraphIso.SoJProg.RunsWithin.goodListProg, ``GraphIso.SoJProg.allSmallL_iff,
    ``GraphIso.SoJProg.bigL_decode, ``GraphIso.SoJProg.constRectL_iff,
    ``GraphIso.SoJProg.selThirdL_decode, ``GraphIso.SoJProg.RunsWithin.selThirdProg,
    ``GraphIso.SoJProg.decode_cohSojD, ``GraphIso.SoJProg.decodeRes_cohSojD,
    ``GraphIso.SoJProg.RunsWithin.cohSojProg, ``GraphIso.SoJProg.cohSojCost_le,
    ``GraphIso.SoJProg.bipEdgeD_eq, ``GraphIso.SoJProg.relOf_bipRelD,
    ``GraphIso.SoJProg.RunsWithin.bipEdgeProg, ``GraphIso.SoJProg.RunsWithin.bipRelProg,
    -- milestone 14, stage 14d (PLAN-14.md §8): Split-or-Johnson trees and leaf stabilizers
    ``GraphIso.SplitJohnson.CTree.card_leafMs, ``GraphIso.SplitJohnson.CTree.mem_leafMs,
    ``GraphIso.SplitJohnson.CTree.leafMs_bind, ``GraphIso.SplitJohnson.CTree.leafMs_trans,
    ``GraphIso.SplitJohnson.CTree.size_le_of_live, ``GraphIso.SplitJohnson.height_bsoj_le,
    ``GraphIso.SplitJohnson.height_soj_le, ``GraphIso.SplitJohnson.card_orbit_le_count,
    ``GraphIso.SoJTree.decodeOut_addPieceD, ``GraphIso.SoJTree.decodeOut_extendD,
    ``GraphIso.SoJTree.outEqD_iff, ``GraphIso.SoJTree.decodeOut_actOutD,
    ``GraphIso.SoJTree.RunsWithin.outEqProg, ``GraphIso.SoJTree.RunsWithin.actOutProg,
    ``GraphIso.SoJTree.outSize_actOutD_le, ``GraphIso.SoJTree.outEqCost_le,
    ``GraphIso.SoJTree.actOutCost_le, ``GraphIso.SoJTree.RunsWithin.addPieceProg,
    ``GraphIso.SoJTree.RunsWithin.extendOutProg, ``GraphIso.SplitJohnson.leafMs_withPiece,
    ``GraphIso.SoJTree.FrameAux.bsoj_congr, ``GraphIso.SoJTree.FrameAux.cohSoj_agree,
    ``GraphIso.SoJTree.stepD_leafMs, ``GraphIso.SoJTree.stepD_children,
    ``GraphIso.SoJTree.stepD_size, ``GraphIso.SoJTree.sojAtD_leaf, ``GraphIso.SoJTree.sojAtD_frame,
    ``GraphIso.SoJTree.stepD_validP, ``GraphIso.SoJTree.RunsWithin.stepProg,
    ``GraphIso.SoJTree.worklistD_ms, ``GraphIso.SoJTree.enumMs_eq,
    ``GraphIso.SoJTree.RunsWithin.worklistProg,
    ``GraphIso.SoJTree.orbitD_spec, ``GraphIso.SoJTree.orbitD_length_eq,
    ``GraphIso.SoJTree.RunsWithin.orbitProg,
    ``GraphIso.SoJTree.exists_idxActHom, ``GraphIso.SoJTree.idxAct_fix_iff,
    ``GraphIso.SoJTree.RunsWithin.orbitStabProg,
    ``GraphIso.SoJTree.RunsWithin.leafStabProg, ``GraphIso.SoJTree.leafOrbit_length_eq,
    ``GraphIso.SoJTree.leafStab_index_le_count, ``GraphIso.SoJTree.leafStab_reps_le_count,
    ``GraphIso.SoJTree.bsojProg_leafMs, ``GraphIso.SoJTree.bsojProg_length,
    ``GraphIso.SoJTree.bsojProg_reach, ``GraphIso.SoJTree.RunsWithin.bsojProg,
    ``GraphIso.SoJTree.bsojProg_cost_le, ``GraphIso.SoJTree.sojProg_leafMs,
    ``GraphIso.SoJTree.sojProg_length, ``GraphIso.SoJTree.sojProg_reach,
    ``GraphIso.SoJTree.RunsWithin.sojProg, ``GraphIso.SoJTree.sojProg_cost_le,
    ``GraphIso.SoJTree.sojAtProg_leafMs, ``GraphIso.SoJTree.sojAtProg_length,
    ``GraphIso.SoJTree.sojAtProg_reach, ``GraphIso.SoJTree.RunsWithin.sojAtProg,
    ``GraphIso.SoJTree.stepD_outSize, ``GraphIso.SoJTree.bsojProg_outSize,
    ``GraphIso.SoJTree.sojAtProg_outSize, ``GraphIso.SoJTree.sojProg_outSize,
    ``GraphIso.SoJTree.leafStabCost_le_of_outSize,
    ``GraphIso.SoJTree.RunsWithin.leafStabProg_of_outSize,
    ``GraphIso.SoJTree.RunsWithin.leafStabProg_sojLeaf,
    -- milestone 14, stage 14e (PLAN-14.md §9): local certificates as programs
    ``GraphIso.Certificates.pairCoset_self, ``GraphIso.Certificates.pairCoset_eq_smul,
    ``GraphIso.Certificates.beardG_conj, ``GraphIso.Certificates.beardW_succ_conj,
    ``GraphIso.Certificates.pairCoset_succ, ``GraphIso.Certificates.certIso_iff,
    ``GraphIso.CertProg.exists_phi, ``GraphIso.CertProg.RunsWithin.stabSetProg,
    ``GraphIso.CertProg.toStab_stabSet, ``GraphIso.CertProg.moveD_spec,
    ``GraphIso.CertProg.RunsWithin.moveProg, ``GraphIso.CertProg.isGiantOn_toStab_iff,
    ``GraphIso.CertProg.RunsWithin.giantAProg, ``GraphIso.CertProg.giantAModel_iff,
    ``GraphIso.CertProg.RunsWithin.affProg, ``GraphIso.CertProg.pointStabs_reps_le_factorial,
    ``GraphIso.CertProg.RunsWithin.kerAProg, ``GraphIso.CertProg.kernel_orbit_of_giant,
    ``GraphIso.CertProg.kerOrbit_length_le, ``GraphIso.CertProg.denotes_iso_succ,
    ``GraphIso.CertProg.RunsWithin.beardStepProg, ``GraphIso.CertProg.pairCoset_stable,
    ``GraphIso.CertProg.RunsWithin.pairLoopProg, ``GraphIso.CertProg.atRound_none_iff,
    ``GraphIso.CertProg.RunsWithin.tupleTransProg, ``GraphIso.CertProg.RunsWithin.certProg,
    ``GraphIso.CertProg.giantGens_allValid, ``GraphIso.CertProg.stabSet_gens_le,
    ``GraphIso.CertProg.certIso_iff_transporter, ``GraphIso.CertProg.RunsWithin.certIsoProg,
    ``GraphIso.CertProg.cp_ps_run, ``GraphIso.CertProg.beardStepCost_eq,
    ``GraphIso.CertProg.beardStepCost_le, ``GraphIso.CertProg.pairLoopCost_le,
    ``GraphIso.CertProg.denotes_toStab, ``GraphIso.CertProg.certCost_le,
    ``GraphIso.CertProg.certIsoCost_le,
    -- milestone 14, stage 14f (PLAN-14.md §10): structures on the base and Align
    ``GraphIso.Align.trimJ_smul, ``GraphIso.Align.trimOut_smul, ``GraphIso.Align.isJohnson_trimJ,
    ``GraphIso.Align.validOut_trimOut, ``GraphIso.Align.bsoj_johnson_disjoint,
    ``GraphIso.Align.soj_johnson_disjoint, ``GraphIso.Align.trim_canonical,
    ``GraphIso.Align.setPart_valid, ``GraphIso.Align.setOps_spec,
    ``GraphIso.Align.RunsWithin.setGensProg, ``GraphIso.Align.RunsWithin.setIsoProg,
    ``GraphIso.Align.setGensCost_le, ``GraphIso.Align.setIsoCost_le,
    ``GraphIso.Align.partGens_closure, ``GraphIso.Align.partGens_valid,
    ``GraphIso.Align.partOps_spec, ``GraphIso.Align.RunsWithin.partGensProg,
    ``GraphIso.Align.RunsWithin.partIsoProg, ``GraphIso.Align.partGensCost_le,
    ``GraphIso.Align.partIsoCost_le, ``GraphIso.Align.johnGensD_closure,
    ``GraphIso.Align.johnIsoD_some, ``GraphIso.Align.johnIsoD_none, ``GraphIso.Align.johnOps_spec,
    ``GraphIso.Align.jvalid_of_isJohnson, ``GraphIso.Align.RunsWithin.johnGensProg,
    ``GraphIso.Align.RunsWithin.johnIsoProg, ``GraphIso.Align.closure_schreierSet,
    ``GraphIso.Align.closure_stabInPL, ``GraphIso.Align.isoInPL_spec,
    ``GraphIso.Align.closure_lifts_ker, ``GraphIso.Align.RunsWithin.stabInPProg,
    ``GraphIso.Align.RunsWithin.isoInPProg, ``GraphIso.Align.RunsWithin.pGroupProg,
    ``GraphIso.Align.RunsWithin.preProg, ``GraphIso.Align.iso_eq_isoTo,
    ``GraphIso.Align.iso_eq_iUnion_isoTo, ``GraphIso.Align.RunsWithin.alignCall,
    ``GraphIso.Align.RunsWithin.alignProg,
    -- milestone 14, stage 14g (PLAN-14.md §11): aggregation, Case 1, Case 2a
    ``GraphIso.Certificates.fullGroupK_le_autG, ``GraphIso.Certificates.fullGroupK_relabel,
    ``GraphIso.Certificates.fullGroupK_eq_fullGroup, ``GraphIso.Certificates.fullGroupK_eq_closure,
    ``GraphIso.Giant.ksubsD_finsetOf, ``GraphIso.Giant.length_ksubsD,
    ``GraphIso.Giant.agParts_length_le, ``GraphIso.Giant.RunsWithin.ksubsProg,
    ``GraphIso.Giant.agPart_ksubsD, ``GraphIso.Giant.RunsWithin.fullProg,
    ``GraphIso.Giant.caseD_spec, ``GraphIso.Giant.RunsWithin.caseProg,
    ``GraphIso.Giant.isOrbitPart_unique, ``GraphIso.Giant.isOrbitPart_smul,
    ``GraphIso.Giant.isColPart_of_isOrbitPart, ``GraphIso.Giant.orbitPartD_spec,
    ``GraphIso.Giant.orbitPart_canonical, ``GraphIso.Giant.RunsWithin.orbitPartProg,
    ``GraphIso.Giant.orbitPartCost_le, ``GraphIso.Giant.RunsWithin.case1Prog,
    ``GraphIso.Giant.case1Cost_le, ``GraphIso.Giant.c2_cover, ``GraphIso.Giant.RunsWithin.pbBranch,
    ``GraphIso.Giant.RunsWithin.pullbackProg, ``GraphIso.Giant.RunsWithin.case2aProg,
    ``GraphIso.Giant.c2_hhalf_of_labels, ``GraphIso.Giant.RunsWithin.pullbackProg_of_labels,
    ``GraphIso.Giant.RunsWithin.case2aProg_of_labels, ``GraphIso.Giant.c2_g1_spec,
    ``GraphIso.Giant.ag_certProg_gens, ``GraphIso.Giant.ag_ss_charges,
    ``GraphIso.Giant.largeOrbit_canonical, ``GraphIso.Giant.c2_orbit_stable,
    ``GraphIso.Giant.RunsWithin.case2aProg_canonical,
    -- milestone 14, stage 14h (PLAN-14.md §12): Case 2b
    ``GraphIso.Case2b.case2bTree_relabel, ``GraphIso.Case2b.case2bTree_relabel',
    ``GraphIso.Case2b.case2bTree_valid, ``GraphIso.Case2b.case2bTree_live,
    ``GraphIso.Case2b.case2bTree_count_le, ``GraphIso.Case2b.case2bHyp_of_degree,
    ``GraphIso.Case2b.case2b_reach, ``GraphIso.Case2b.leafTree_spec,
    ``GraphIso.Case2b.leafTree_relabel, ``GraphIso.Case2b.extPart_valid,
    ``GraphIso.Case2b.extJohn_valid, ``GraphIso.Case2b.outOps_spec,
    ``GraphIso.Case2b.length_outGensD_le, ``GraphIso.Case2b.RunsWithin.outGensProg,
    ``GraphIso.Case2b.RunsWithin.outIsoProg, ``GraphIso.Case2b.outGensCost_le,
    ``GraphIso.Case2b.outIsoCost_le, ``GraphIso.Case2b.colOf_wlColD,
    ``GraphIso.Case2b.decodeOut_compLeafD, ``GraphIso.Case2b.disconn_wlCol,
    ``GraphIso.Case2b.sojD_leafMs, ``GraphIso.Case2b.decodeOut_trimD,
    ``GraphIso.Case2b.decodeOut_extD, ``GraphIso.Case2b.mem_tuplesD, ``GraphIso.Case2b.mem_pairsD,
    ``GraphIso.Case2b.RunsWithin.leavesOfProg, ``GraphIso.Case2b.leavesOfD_decode_comp,
    ``GraphIso.Case2b.leavesOfD_decode_soj, ``GraphIso.Case2b.RunsWithin.resProg,
    ``GraphIso.Case2b.RunsWithin.colProg, ``GraphIso.Case2b.RunsWithin.choiceProg,
    ``GraphIso.Case2b.RunsWithin.allLeavesProg, ``GraphIso.Case2b.RunsWithin.firstLeafProg,
    ``GraphIso.Case2b.allLeavesD_leafMs, ``GraphIso.Case2b.firstLeafD_reach,
    ``GraphIso.Case2b.firstLeafD_ne_none, ``GraphIso.Case2b.allLeavesD_valid,
    ``GraphIso.Case2b.firstLeafD_valid, ``GraphIso.Case2b.sojSz_le,
    ``GraphIso.Case2b.RunsWithin.degProg, ``GraphIso.Case2b.degD_spec,
    ``GraphIso.Case2b.case2bHyp_degD, ``GraphIso.Case2b.RunsWithin.case2bProg,
    ``GraphIso.Case2b.RunsWithin.case2bProg_canonical,
    ``GraphIso.Case2b.RunsWithin.case2bProg_canonical', ``GraphIso.Case2b.c2b_ss_charges,
    -- milestone 14, stage 14i (PLAN-14.md §13): Case 3
    ``GraphIso.Case3.splitTree_relabel, ``GraphIso.Case3.splitTree_spec,
    ``GraphIso.Case3.domCls_eq, ``GraphIso.Case3.outTree_relabel, ``GraphIso.Case3.outTree_spec,
    ``GraphIso.Case3.case3Tree_relabel, ``GraphIso.Case3.case3_reach,
    ``GraphIso.Case3.case3_reach_eOf, ``GraphIso.Case3.case3Tree_spec,
    ``GraphIso.Case3.case3Tree_live, ``GraphIso.Case3.case3Tree_valid,
    ``GraphIso.Case3.case3Tree_count_le, ``GraphIso.Case3.no_twins_of_thresholds,
    ``GraphIso.Case3.certIso_refl, ``GraphIso.Case3.certIso_symm, ``GraphIso.Case3.certIso_trans,
    ``GraphIso.Case3.certIso_of_relabel, ``GraphIso.Case3.certIsoL_iff,
    ``GraphIso.Case3.tupleCol_iso, ``GraphIso.Case3.colX_eq_iff,
    ``GraphIso.Case3.RunsWithin.cmpProg, ``GraphIso.Case3.RunsWithin.tupleColProg,
    ``GraphIso.Case3.toFun_wlCD, ``GraphIso.Case3.mem_goodListsD,
    ``GraphIso.Case3.goodListsD_ne_nil, ``GraphIso.Case3.twinsD_spec, ``GraphIso.Case3.col1D_eq,
    ``GraphIso.Case3.outcomeD_small, ``GraphIso.Case3.outcomeD_dom,
    ``GraphIso.Case3.RunsWithin.wlCProg, ``GraphIso.Case3.RunsWithin.outcomeProg,
    ``GraphIso.Case3.RunsWithin.allStructsProg, ``GraphIso.Case3.RunsWithin.firstStructProg,
    ``GraphIso.Case3.RunsWithin.twinsFlagProg, ``GraphIso.Case3.allStructsD_leafMs,
    ``GraphIso.Case3.firstStructD_reach, ``GraphIso.Case3.firstStructD_ne_none,
    ``GraphIso.Case3.allStructsD_valid, ``GraphIso.Case3.firstStructD_valid,
    ``GraphIso.Case3.outSzD_le, ``GraphIso.Case3.twinsD_eq_false,
    ``GraphIso.Case3.htw_of_thresholds, ``GraphIso.Case3.outCostD_le,
    ``GraphIso.Case3.RunsWithin.case3Prog_ne, ``GraphIso.Case3.RunsWithin.case3Prog,
    ``GraphIso.Case3.case3_no_fallback, ``GraphIso.Case3.RunsWithin.case3Prog_canonical,
    ``GraphIso.Case3.c3_ss_charges]
  let mut lines : Array MessageData := #[]
  for name in principal do
    let axs ← collectAxioms name
    lines := lines.push m!"{name}: {axs.toList}"
  logInfo (MessageData.joinSep lines.toList "\n")

/-! The list continues in four more blocks of at most about 400 lines each. One array literal
of all the names exceeds the code generator's recursion depth, and, in this module, one of 1200
lines exceeds the default heartbeat budget of its elaboration. -/

open Lean in
run_cmd do
  let principal := #[
    -- milestone 14, stage 14j-1 (PLAN-14.md §14.1): hinted instances and derived hints
    ``GraphIso.Main.HInstValid.isHint, ``GraphIso.Main.HInstValid.transitive,
    ``GraphIso.Main.hmeasure_some, ``GraphIso.Main.hmeasure_none,
    ``GraphIso.Main.hintValid_of_forall, ``GraphIso.Main.RunsWithin.labM0Prog,
    ``GraphIso.Main.RunsWithin.m0Prog, ``GraphIso.Main.RunsWithin.interOProg,
    ``GraphIso.Main.RunsWithin.ncProg, ``GraphIso.Main.RunsWithin.pickProg,
    ``GraphIso.Main.RunsWithin.labM1Prog, ``GraphIso.Main.RunsWithin.singProg,
    ``GraphIso.Main.mf_exists_ncD, ``GraphIso.Main.mf_pickD_spec, ``GraphIso.Main.RunsWithin.m1Prog,
    ``GraphIso.Main.mf_blockLab_nonconst, ``GraphIso.Main.RunsWithin.m2aIdxProg,
    ``GraphIso.Main.RunsWithin.m2aProg, ``GraphIso.Main.wf_m0Prog, ``GraphIso.Main.wf_m1Prog,
    ``GraphIso.Main.wf_m2aProg, ``GraphIso.Main.RunsWithin.mr_pointStabsFact,
    ``GraphIso.Main.jfallback_half, ``GraphIso.Main.length_jUnionData_le,
    ``GraphIso.Main.jfallback_cells_le, ``GraphIso.Main.RunsWithin.jfallbackProg,
    ``GraphIso.Main.RunsWithin.m2bProg, ``GraphIso.Main.m2b_hintValid, ``GraphIso.Main.m2b_card,
    ``GraphIso.Main.wf_jfallbackProg, ``GraphIso.Main.wf_m2bProg, ``GraphIso.Main.inter_isHint,
    ``GraphIso.Main.blocks_label_isHint, ``GraphIso.Main.blocks_stab_isHint,
    ``GraphIso.Main.johnUnion_isHint, ``GraphIso.Main.johnFallback_fix,
    ``GraphIso.Main.johnFallback_half, ``GraphIso.Main.derived_colPart,
    ``GraphIso.Main.dm_cells_bound, ``GraphIso.Main.derived_johnson,
    ``GraphIso.Main.derived_cjohnson, ``GraphIso.Main.isColPart_ext_bound,
    ``GraphIso.Main.derived_extPart, ``GraphIso.Main.derived_set, ``GraphIso.Main.cj_smul_eq_iff,
    ``GraphIso.Main.cjohnGensD_closure, ``GraphIso.Main.length_cjohnGensD_le,
    ``GraphIso.Main.cjohnIsoD_some, ``GraphIso.Main.cjohnIsoD_none, ``GraphIso.Main.cjohnOps_spec,
    ``GraphIso.Main.RunsWithin.cjohnGensProg, ``GraphIso.Main.RunsWithin.cjohnIsoProg,
    ``GraphIso.Main.wf_cjohnGensProg, ``GraphIso.Main.wf_cjohnIsoProg,
    ``GraphIso.Main.DSetting.half, ``GraphIso.Main.DSetting.hintK,
    ``GraphIso.Main.RunsWithin.blocksProg, ``GraphIso.Main.RunsWithin.m1ContProg,
    ``GraphIso.Main.RunsWithin.deriveFreeProg, ``GraphIso.Main.dv_cells_child,
    ``GraphIso.Main.dv_jfallback, ``GraphIso.Main.RunsWithin.johnStepProg,
    ``GraphIso.Main.RunsWithin.deriveCJProg, ``GraphIso.Main.RunsWithin.deriveProg_free,
    ``GraphIso.Main.RunsWithin.deriveProg_cj, ``GraphIso.Main.dv_not_prim,
    ``GraphIso.Main.derivePart_ne_stuck, ``GraphIso.Main.dv_m1_colour,
    ``GraphIso.Main.deriveCJ_ne_stuck, ``GraphIso.Main.wf_deriveProg,
    -- milestone 14, stage 14j-2 (PLAN-14.md §14.2): the macro-step framework and M0–M3
    ``GraphIso.Main.hmeasure_eq, ``GraphIso.Main.StepChild.measLt, ``GraphIso.Main.FreeChild.measLt,
    ``GraphIso.Main.ChainChild.measLt, ``GraphIso.Main.ChildList.length_le,
    ``GraphIso.Main.ChildList.mono_factor, ``GraphIso.Main.SizeChild.closed,
    ``GraphIso.Main.SizeChild.mono, ``GraphIso.Main.HInstValid.win_pos,
    ``GraphIso.Main.le_foldr_max, ``GraphIso.Main.le_supTo,
    ``GraphIso.Main.tr_eq_of_agree, ``GraphIso.Main.tr_iso_eq,
    ``GraphIso.Main.tr_iso_eq_empty, ``GraphIso.Main.tr_lift_exists, ``GraphIso.Main.ChildOK.rel,
    ``GraphIso.Main.ChildOK.labels, ``GraphIso.Main.childHInst_valid,
    ``GraphIso.Main.noHintHInst_valid, ``GraphIso.Main.RunsWithin.childInstProg,
    ``GraphIso.Main.RunsWithin.transferProg, ``GraphIso.Main.RunsWithin.viaChildProg,
    ``GraphIso.Main.RunsWithin.sameDegProg, ``GraphIso.Main.wf_transferProg,
    ``GraphIso.Main.wf_viaChildProg, ``GraphIso.Main.wf_sameDegProg,
    ``GraphIso.Main.sb_hinstValid_plain, ``GraphIso.Main.sb_half_of_fix,
    ``GraphIso.Main.RunsWithin.plainSub, ``GraphIso.Main.sb_seqSub, ``GraphIso.Main.fixedTest_iff,
    ``GraphIso.Main.RunsWithin.fixedStepProg, ``GraphIso.Main.RunsWithin.chainProg,
    ``GraphIso.Main.RunsWithin.kerRedProg, ``GraphIso.Main.RunsWithin.m3Prog,
    ``GraphIso.Main.wf_fixedStepProg, ``GraphIso.Main.wf_chainProg, ``GraphIso.Main.wf_kerRedProg,
    ``GraphIso.Main.wf_m3Prog, ``GraphIso.Main.sh_childOf, ``GraphIso.Main.RunsWithin.m0StepProg,
    ``GraphIso.Main.RunsWithin.m1StepProg, ``GraphIso.Main.RunsWithin.m2aStepProg,
    ``GraphIso.Main.wf_m0StepProg, ``GraphIso.Main.wf_m1StepProg, ``GraphIso.Main.wf_m2aStepProg,
    ``GraphIso.Main.RunsWithin.dynSeqProg, ``GraphIso.Main.wf_dynSeqProg,
    ``GraphIso.Main.M2bChild.stepChild, ``GraphIso.Main.HSubSolves.mono, ``GraphIso.Main.ml_handle,
    ``GraphIso.Main.RunsWithin.m2bLoopProg, ``GraphIso.Main.RunsWithin.m2bStepProg,
    ``GraphIso.Main.wf_m2bLoopProg, ``GraphIso.Main.wf_m2bStepProg, ``GraphIso.Main.rd_cj_reps5,
    ``GraphIso.Main.rd_deg_free, ``GraphIso.Main.rd_deg_cj, ``GraphIso.Main.rd_sem0,
    ``GraphIso.Main.rd_sem124, ``GraphIso.Main.rd_sem3, ``GraphIso.Main.rd_sem5,
    ``GraphIso.Main.rd_sem6, ``GraphIso.Main.rd_base_inv_of_iso, ``GraphIso.Main.rd_handle,
    ``GraphIso.Main.rd_branch, ``GraphIso.Main.RunsWithin.rdProg,
    ``GraphIso.Main.RunsWithin.rdProg_general, ``GraphIso.Main.RunsWithin.rdProg_ns,
    ``GraphIso.Main.rd_ns_part, ``GraphIso.Main.rd_ns_cj, ``GraphIso.Main.rd_orbit_free,
    ``GraphIso.Main.rd_orbit_cj, ``GraphIso.Main.RunsWithin.rdProg_part_ns,
    ``GraphIso.Main.RunsWithin.rdProg_cj_ns, ``GraphIso.Main.rd_ss_bounds,
    ``GraphIso.Main.wf_rdProg,
    -- milestone 14, stage 14j-3 (PLAN-14.md §14.3): M4
    ``GraphIso.IsLeftCover.trans, ``GraphIso.Main.isLeftCover_prodRepsD,
    ``GraphIso.Main.length_prodRepsD, ``GraphIso.Main.RunsWithin.prodRepsLProg,
    ``GraphIso.Main.decodeOut_extD_shE, ``GraphIso.Main.baseHom_winE,
    ``GraphIso.Main.restrictHom_baseWin_val, ``GraphIso.Main.baseHom_extOut,
    ``GraphIso.Main.leafStab_baseHom_extOut, ``GraphIso.Main.leafStab_le,
    ``GraphIso.Main.cj_ext_stab, ``GraphIso.Main.cj_ext_hq, ``GraphIso.Main.pointwiseStab_range',
    ``GraphIso.Main.indiv_trans, ``GraphIso.Main.indiv_not_two, ``GraphIso.Main.one_le_degree,
    ``GraphIso.Main.indiv_of_degree, ``GraphIso.Main.msPsi_val, ``GraphIso.Main.ms_coherent2,
    ``GraphIso.Main.ms_uniprimitive, ``GraphIso.Main.ms_config, ``GraphIso.Main.ms_orbital,
    ``GraphIso.Main.ms_relab, ``GraphIso.Main.ms_comp_fixed, ``GraphIso.Main.ms_leaves,
    ``GraphIso.Main.RunsWithin.m4StructProg, ``GraphIso.Main.m4Struct_spec,
    ``GraphIso.Main.wf_m4StructProg, ``GraphIso.Main.indColsD_eq, ``GraphIso.Main.m4_run,
    ``GraphIso.Main.m4_ps_gens_le, ``GraphIso.Main.m4_core, ``GraphIso.Main.RunsWithin.m4StepProg,
    ``GraphIso.Main.m4_K_rel, ``GraphIso.Main.m4_part_facts, ``GraphIso.Main.m4_cj_facts,
    ``GraphIso.Main.RunsWithin.m4StepProg_ns, ``GraphIso.Main.m4_deg_le,
    ``GraphIso.Main.m4_deg_le_T, ``GraphIso.Main.m4_numeric, ``GraphIso.Main.m4Charges_exact,
    ``GraphIso.Main.wf_m4StepProg,
    -- milestone 14, stage 14j-4 (PLAN-14.md §14.4): M5
    ``GraphIso.Main.rb_iso_one_eq, ``GraphIso.Main.rb_iso_eq, ``GraphIso.Main.rb_iso_eq_empty,
    ``GraphIso.Main.rb_alt_two, ``GraphIso.Main.rb_proper_label, ``GraphIso.Main.rb_baseHom_eq_one,
    ``GraphIso.Main.rb_equivar, ``GraphIso.Main.rbHInst_valid, ``GraphIso.Main.AnsOK.rb_none,
    ``GraphIso.Main.AnsOK.rb_lift, ``GraphIso.Main.RunsWithin.rbLiftProg,
    ``GraphIso.Main.RunsWithin.restrictBaseProg, ``GraphIso.Main.rbHInst_measure,
    ``GraphIso.Main.wf_restrictBaseProg, ``GraphIso.Main.m5_hinstValid_step,
    ``GraphIso.Main.m5_stepSub, ``GraphIso.Main.m5Fmap_le, ``GraphIso.Main.m5Fmap_base,
    ``GraphIso.Main.m5Fmap_loc, ``GraphIso.Main.m5Fmap_relabel, ``GraphIso.Main.m5Fmap_matchesW,
    ``GraphIso.Main.RunsWithin.m5CertProg, ``GraphIso.Main.fullCost_le_count,
    ``GraphIso.Main.alt_le_of_tupTrans, ``GraphIso.Main.m5_hFalt, ``GraphIso.Main.m5_tupTrans_iff,
    ``GraphIso.Main.RunsWithin.m5CaseProg, ``GraphIso.Main.m5Case_spec,
    ``GraphIso.Main.wf_m5CertProg, ``GraphIso.Main.wf_m5CaseProg, ``GraphIso.Main.exists_allPermsD,
    ``GraphIso.Main.ar_branch_max, ``GraphIso.Main.ar_K_fix, ``GraphIso.Main.RunsWithin.alignRd,
    ``GraphIso.Main.RunsWithin.alignRd_general, ``GraphIso.Main.RunsWithin.alignRd_part_ns,
    ``GraphIso.Main.RunsWithin.alignRd_cj_ns, ``GraphIso.Main.wf_alignRdProg,
    ``GraphIso.Main.RunsWithin.m5Case1Prog, ``GraphIso.Main.RunsWithin.m5Case1Prog_ns,
    ``GraphIso.Main.m5_pbSub, ``GraphIso.Main.c2aCost_count, ``GraphIso.Main.m5_mem_listsOver,
    ``GraphIso.Main.m5_exists_genOut_le,
    ``GraphIso.Main.RunsWithin.m5Case2aProg, ``GraphIso.Main.RunsWithin.m5Case2bProg,
    ``GraphIso.Main.m5_leaf2b_valid, ``GraphIso.Main.RunsWithin.m5Case2bProg_part,
    ``GraphIso.Main.m5_c3First_unique, ``GraphIso.Main.RunsWithin.m5Case3Prog,
    ``GraphIso.Main.wf_m5Case1Prog, ``GraphIso.Main.wf_m5Case2aProg,
    ``GraphIso.Main.wf_m5Case2bProg, ``GraphIso.Main.wf_m5Case3Prog, ``GraphIso.Main.fixPtsD_spec,
    ``GraphIso.Main.m5_Fmap_iso, ``GraphIso.Main.m5_isA_iff, ``GraphIso.Main.m5_large_iso,
    ``GraphIso.Main.m5_tupTrans_iso, ``GraphIso.Main.RunsWithin.m5Dispatch,
    ``GraphIso.Main.RunsWithin.m5CoreProg, ``GraphIso.Main.wf_m5Dispatch,
    ``GraphIso.Main.wf_m5CoreProg, ``GraphIso.Main.m5s_giant, ``GraphIso.Main.RunsWithin.m5StepProg,
    ``GraphIso.Main.wf_m5StepProg,
    ``GraphIso.Main.m5_fix_iff_supp, ``GraphIso.Main.m5_no_twins,
    ``GraphIso.Main.RunsWithin.m5Case3Prog_part, ``GraphIso.Main.RunsWithin.m5Dispatch_ns,
    ``GraphIso.Main.RunsWithin.m5CoreProg_ns,
    -- milestone 14, stage 14j-4b (PLAN-14.md §14.5): coloured Johnson alignment in M5
    ``GraphIso.Main.outTree_jleaf, ``GraphIso.Main.leafTree_jleaf, ``GraphIso.Main.cj_hq_of_along,
    ``GraphIso.Main.splitTree_jleaf, ``GraphIso.Main.cj_ext_hq',
    ``GraphIsoChecks.MainM5CJ.j32_johnson, ``GraphIsoChecks.MainM5CJ.j32_valid,
    ``GraphIsoChecks.MainM5CJ.cj32_hq, ``GraphIsoChecks.MainM5CJ.al_j42,
    ``GraphIso.Main.choiceLeavesD_along, ``GraphIso.Main.outcomeD_along,
    ``GraphIso.Main.c3ClsD_facts, ``GraphIso.Main.get_q2bD, ``GraphIso.Main.get_q2bD_smul,
    ``GraphIso.Main.cj2b_reach, ``GraphIso.Main.cj2b_hq, ``GraphIso.Main.cj2b_valid,
    ``GraphIso.Main.get_q3D, ``GraphIso.Main.outTree_transport, ``GraphIso.Main.cj3_reach,
    ``GraphIso.Main.cj3_hq, ``GraphIso.Main.cj3_valid, ``GraphIso.Main.RunsWithin.q2bProg,
    ``GraphIso.Main.RunsWithin.q3Prog, ``GraphIso.Main.RunsWithin.cjOfProg,
    ``GraphIso.Main.RunsWithin.cjLeaves2bProg, ``GraphIso.Main.RunsWithin.c3ClsProg,
    ``GraphIso.Main.RunsWithin.cjOutcome3Prog, ``GraphIso.Main.RunsWithin.cjStructs3Prog,
    ``GraphIso.Main.c2bJD_true, ``GraphIso.Main.c2bJD_false,
    ``GraphIso.Main.RunsWithin.c2bJTestProg, ``GraphIso.Main.RunsWithin.c2bCJProg,
    ``GraphIso.Main.RunsWithin.m5Case2bCJProg, ``GraphIso.Main.RunsWithin.c3FirstClsProg,
    ``GraphIso.Main.RunsWithin.c3CJRouteProg, ``GraphIso.Main.RunsWithin.m5Case3CJProg,
    ``GraphIso.Main.RunsWithin.m5DispatchCJ, ``GraphIso.Main.RunsWithin.m5DispatchCJ_ns,
    ``GraphIso.Main.RunsWithin.m5CoreCJProg, ``GraphIso.Main.RunsWithin.m5CoreCJProg_ns,
    ``GraphIso.Main.RunsWithin.m5StepCJProg, ``GraphIso.Main.wf_m5Case2bCJProg,
    ``GraphIso.Main.wf_m5Case3CJProg, ``GraphIso.Main.wf_m5DispatchCJ,
    ``GraphIso.Main.wf_m5CoreCJProg, ``GraphIso.Main.wf_m5StepCJProg,
    ``GraphIsoChecks.MainM5CJRoute.memoL_spec, ``GraphIsoChecks.MainM5CJRoute.lookL_eq,
    ``GraphIsoChecks.MainM5CJRoute.ys2bM_eq,
    -- milestone 14, stage 14j-5b (PLAN-14.md §14.7): Schreier–Sims counts, the mini procedure
    ``GraphIso.Sims.ssBoundsS, ``GraphIso.Sims.ssOracle_meets_bnd, ``GraphIso.Sims.ssBoundsB,
    ``GraphIso.Main.rd_ss_boundsS, ``GraphIso.Main.dOutGens_of_dOutcome,
    ``GraphIso.Main.DSetting.ssBnd, ``GraphIso.Main.rd_ss_dOutGens_free,
    ``GraphIso.Main.rd_ss_dOutGens_cj, ``GraphIso.Main.rd_orbit_free_ss,
    ``GraphIso.Main.rd_orbit_cj_ss, ``GraphIso.Main.ss_generate_gens_le, ``GraphIso.Main.ss_hsR,
    ``GraphIso.Main.ss_hgR, ``GraphIso.Main.ss_kernel_gens_le, ``GraphIso.Main.ss_hsK,
    ``GraphIso.Main.ssBm, ``GraphIso.Main.ss_m2bRb_gens_le, ``GraphIso.Main.ss_m4K_gens_le,
    ``GraphIso.Main.wf_recurFun, ``GraphIso.Main.miniBody_wf, ``GraphIso.Main.miniEntry_wf,
    ``GraphIso.Main.HInstValid.base_pos, ``GraphIso.Main.HInstValid.winSize_le,
    ``GraphIso.Main.mini_m0_case, ``GraphIso.Main.ss_rebase_gens_le, ``GraphIso.Main.ss_m0_gens_le,
    ``GraphIso.Main.ss_ker_gens_le, ``GraphIso.Main.miniRk_lt, ``GraphIso.Main.le_miniC,
    ``GraphIso.Main.miniC_mono, ``GraphIso.Main.mini_sum_le, ``GraphIso.Main.StepChild.getD_le,
    ``GraphIso.Main.FreeChild.getD_le, ``GraphIso.Main.ChainChild.getD_le,
    ``GraphIso.Main.mini_rk_pos, ``GraphIso.Main.mini_child, ``GraphIso.Main.mini_repsCost_mono,
    ``GraphIso.Main.mini_hsub, ``GraphIso.Main.mini_chain, ``GraphIso.Main.mini_m0,
    ``GraphIso.Main.mini_m3, ``GraphIso.Main.IsOrbitPartition.length_le_win,
    ``GraphIso.Main.mini_cost_le, ``GraphIso.Main.mini_fixedTestCost_le, ``GraphIso.Main.mini_step,
    ``GraphIso.Main.mini_spec, ``GraphIso.Main.miniSolve_ss,
    -- milestone 14, stage 14j-5c (PLAN-14.md §14.8): the Schreier–Sims steps
    ``GraphIso.Main.baseWin_length, ``GraphIso.Main.rebaseGens_length,
    ``GraphIso.Main.ssB_generate, ``GraphIso.Main.ssB_orbits, ``GraphIso.Main.ssB_lift,
    ``GraphIso.Main.ssB_generate_le, ``GraphIso.Main.m1WorkSS, ``GraphIso.Main.m1WorkSS_mono,
    ``GraphIso.Main.RunsWithin.m1StepProg_ss, ``GraphIso.Main.m2aWorkSS,
    ``GraphIso.Main.m2aWorkSS_mono, ``GraphIso.Main.RunsWithin.m2aStepProg_ss,
    ``GraphIso.Main.extendGens_length, ``GraphIso.Main.ss_blockStab_sizes,
    ``GraphIso.Main.m2bWorkSS, ``GraphIso.Main.m2bStepCost_mono_k, ``GraphIso.Main.m2bWorkSS_mono,
    ``GraphIso.Main.RunsWithin.m2bStepProg_ss, ``GraphIso.Main.foldr_max_le,
    ``GraphIso.Main.supTo_le, ``GraphIso.Main.supTo_mono, ``GraphIso.Main.envSup,
    ``GraphIso.Main.envSup_mono_fun, ``GraphIso.Main.le_envSup, ``GraphIso.Main.envSup_mono,
    ``GraphIso.Main.forall₂_le_refl, ``GraphIso.Toolkit.HintValid.base_pos,
    ``GraphIso.Main.pickD_mem, ``GraphIso.Main.ss_m1O_facts, ``GraphIso.Main.ss_m1_child,
    ``GraphIso.Main.ss_mbD_facts, ``GraphIso.Main.ss_m1Charges, ``GraphIso.Main.ss_blkCharges_of,
    ``GraphIso.Main.ss_blkCharges, ``GraphIso.Main.ssBdF, ``GraphIso.Main.deriveFreeCost_mono_ps,
    ``GraphIso.Main.DSetting.orbit_length_le, ``GraphIso.Main.rd_orbit_free_ssU,
    ``GraphIso.Main.ss_cells_le, ``GraphIso.Main.ss_union_le, ``GraphIso.Main.ssBdJ,
    ``GraphIso.Main.deriveCJCost_mono, ``GraphIso.Main.rd_orbit_cj_ssU,
    ``GraphIso.Main.ss_leafStab_sizes, ``GraphIso.Main.os_extGens_length,
    ``GraphIso.Main.ss_m4Charges, ``GraphIso.Main.ss_m4_pre, ``GraphIso.Main.RDOrbit.mono,
    ``GraphIso.Main.m4WhSS, ``GraphIso.Main.m4W6SS, ``GraphIso.Main.m4CostSS,
    ``GraphIso.Main.m4WorkSS, ``GraphIso.Main.m4WorkNsSS, ``GraphIso.Main.m4WorkSS_mono,
    ``GraphIso.Main.m4WorkNsSS_mono, ``GraphIso.Main.ss_m4_hD,
    ``GraphIso.Main.RunsWithin.m4StepProg_ss, ``GraphIso.Main.RunsWithin.m4StepProg_ns_ss,
    ``GraphIso.Main.stabInPL_length_le, ``GraphIso.Main.flagsModel_length,
    ``GraphIso.Main.partGensD_length_le, ``GraphIso.Main.outGensD_length_le,
    ``GraphIso.Main.aligned_length_le, ``GraphIso.Main.degreeModel_le, ``GraphIso.Main.degD_le,
    ``GraphIso.Main.ss_baseOrbits, ``GraphIso.Main.ss_m5Cs_le, ``GraphIso.Main.ss_fixPts_le,
    ``GraphIso.Main.ss_kerReps_le, ``GraphIso.Main.ss_iterStab_le, ``GraphIso.Main.ss_giantGens_le,
    ``GraphIso.Main.c2bRU, ``GraphIso.Main.c2bR_le, ``GraphIso.Main.c3R_mono,
    ``GraphIso.Main.ssM5β, ``GraphIso.Main.ssBg1J, ``GraphIso.Main.ss_m5_rb,
    ``GraphIso.Main.pairsD_length_le, ``GraphIso.Main.cells_pairs_le, ``GraphIso.Main.cellSwaps_le,
    ``GraphIso.Main.jrest_length_le, ``GraphIso.Main.johnGensD_length_le_bound,
    ``GraphIso.Main.cjohnGensD_length_le_bound, ``GraphIso.Main.outGensD_length_le_bound,
    ``GraphIso.Main.m5DispNum, ``GraphIso.Main.m5WCJ_le, ``GraphIso.Main.cjB, ``GraphIso.Main.olB,
    ``GraphIso.Main.m5WorkRaw, ``GraphIso.Main.m5WorkSS, ``GraphIso.Main.m5WorkSS_mono,
    ``GraphIso.Main.le_m5WorkSS, ``GraphIso.Main.m5CoreWorkCJ_le, ``GraphIso.Main.M5Full.base_inv,
    ``GraphIso.Main.RunsWithin.m5StepCJProg_ss₀, ``GraphIso.Main.RunsWithin.m5StepCJProg_ss,
    ``GraphIso.Main.CJFacts, ``GraphIso.Main.RunsWithin.c2bCJProg_jp,
    ``GraphIso.Main.RunsWithin.m5Case2bCJProg_jp, ``GraphIso.Main.c2bJD_tag,
    ``GraphIso.Main.RunsWithin.c3CJRouteProg_jp, ``GraphIso.Main.RunsWithin.m5Case3CJProg_jp,
    ``GraphIso.Main.RunsWithin.m5CoreCJProg_jp, ``GraphIso.Main.RunsWithin.m5CoreCJProg_ns_jp,
    ``GraphIso.Main.RunsWithin.m5DispatchCJ_jp, ``GraphIso.Main.RunsWithin.m5DispatchCJ_ns_jp,
    ``GraphIso.Main.RunsWithin.m5StepCJProg_jp,
    -- round 2 of 14j-5c: the charges as lemmas, the parameter choices
    ``GraphIso.Main.ss_hint_hBo, ``GraphIso.Main.ss_hint_hB, ``GraphIso.Main.ss_hint_hBlift,
    ``GraphIso.Main.ss_hint_hBgen, ``GraphIso.Main.ss_m2b_sizes, ``GraphIso.Main.ss_m2bCharges,
    ``GraphIso.Main.ss_m2b_hBlift, ``GraphIso.Main.ss_m2b_hBgen, ``GraphIso.Main.ss_m2b_hBo,
    ``GraphIso.Main.ss_m2b_hBgen₂, ``GraphIso.Main.ssSIn, ``GraphIso.Main.ssSIn_spec,
    ``GraphIso.Main.m2b_params, ``GraphIso.Main.ssLgM4, ``GraphIso.Main.ssLgM4Ns,
    ``GraphIso.Main.m4_params, ``GraphIso.Main.m4ns_params, ``GraphIso.Main.ssLgM5,
    ``GraphIso.Main.m5_params, ``GraphIso.Main.m5_params_five, ``GraphIso.Main.ss_m5_hBgP,
    ``GraphIso.Main.ss_m5_hBmem, ``GraphIso.Main.ss_m5_hBlA, ``GraphIso.Main.ss_m5_hBg,
    ``GraphIso.Main.ss_m5_hBgk, ``GraphIso.Main.ss_m5_hBgs, ``GraphIso.Main.ss_m5_hBF,
    ``GraphIso.Main.ss_m5_hB3, ``GraphIso.Main.ss_m5_hBox, ``GraphIso.Main.ss_m5_hBoy,
    ``GraphIso.Main.ss_m5_hBg1₁, ``GraphIso.Main.ss_m5_hD₁, ``GraphIso.Main.ss_m5_hBg1₂ₐ,
    ``GraphIso.Main.ss_m5_hBgen₂ₐ, ``GraphIso.Main.ss_m5_hBpb, ``GraphIso.Main.ss_m5_hBgm,
    ``GraphIso.Main.ss_m5_hBlift, ``GraphIso.Main.ss_m5_hBker, ``GraphIso.Main.ss_m5_hBgn,
    ``GraphIso.Main.ss_m5_hBg1₂ᵦ, ``GraphIso.Main.ss_m5_hBgen₂ᵦ, ``GraphIso.Main.ss_m5_hD₂ᵦ,
    ``GraphIso.Main.ss_m5_hBg1₃, ``GraphIso.Main.ss_m5_hBgen₃, ``GraphIso.Main.ss_m5_hD₃,
    ``GraphIso.Main.ss_m5_hBg1J₂, ``GraphIso.Main.ss_m5_hLY₂, ``GraphIso.Main.ss_m5_hDJ₂,
    ``GraphIso.Main.ss_m5_hu₂, ``GraphIso.Main.ss_m5_hBg1J₃, ``GraphIso.Main.ss_m5_hLY₃,
    ``GraphIso.Main.ss_m5_hDJ₃, ``GraphIso.Main.ss_m5_hu₃, ``GraphIso.Main.ss_m5_hBgmR,
    ``GraphIso.Main.ss_m5_hBliftR, ``GraphIso.Main.ss_m5_hBkerR, ``GraphIso.Main.ss_m5_hsKR,
    ``GraphIso.Main.ss_m5_hBgnR,
    -- 14j-5d: the full procedure, the dispatcher and the recursion
    ``GraphIso.Main.thrConst_spec, ``GraphIso.Main.mainBody_wf, ``GraphIso.Main.wf_hintProg,
    ``GraphIso.Main.wf_bigProg, ``GraphIso.Main.wf_normLabProg, ``GraphIso.Main.wf_noStProg,
    ``GraphIso.Main.normLabD_getD, ``GraphIso.Main.m5OkD_iff, ``GraphIso.Main.m4OkD_iff,
    ``GraphIso.Main.noStD_fst, ``GraphIso.Main.RunsWithin.normLabProg,
    ``GraphIso.Main.RunsWithin.noStProg, ``GraphIso.Main.RunsWithin.m5OkProg,
    ``GraphIso.Main.RunsWithin.m4OkProg, ``GraphIso.Main.get_mem_of_invariant,
    ``GraphIso.Toolkit.HintValid.normLab, ``GraphIso.Main.HInstValid.normLab,
    ``GraphIso.Main.orbits_trans_iff, ``GraphIso.Main.base_trans_iff,
    ``GraphIso.Main.RunsWithin.hintProg_m1, ``GraphIso.Main.RunsWithin.hintProg_blocks,
    ``GraphIso.Main.RunsWithin.hintProg_m2a, ``GraphIso.Main.RunsWithin.hintProg_m2b,
    ``GraphIso.Main.RunsWithin.hintProg_big, ``GraphIso.Main.RunsWithin.bigProg_small,
    ``GraphIso.Main.RunsWithin.bigProg_deg, ``GraphIso.Main.RunsWithin.bigProg_m5,
    ``GraphIso.Main.RunsWithin.bigProg_m5_m3, ``GraphIso.Main.RunsWithin.bigProg_m4,
    ``GraphIso.Main.RunsWithin.bigProg_m4_m3, ``GraphIso.Main.rbCost_eq,
    ``GraphIso.Main.main_pred, ``GraphIso.Main.MainSub.step, ``GraphIso.Main.main_chain,
    ``GraphIso.Main.main_m0, ``GraphIso.Main.main_m1, ``GraphIso.Main.ss_mb_facts,
    ``GraphIso.Main.main_m2a, ``GraphIso.Main.main_m2b, ``GraphIso.Main.main_m3,
    ``GraphIso.Main.main_m4, ``GraphIso.Main.ss_m5CFCJ_le, ``GraphIso.Main.ss_m5CKCJ_le,
    ``GraphIso.Main.m5CH_le, ``GraphIso.Main.main_m5, ``GraphIso.Main.mainWork_eq,
    ``GraphIso.Main.main_top_hint, ``GraphIso.Main.main_step, ``GraphIso.Main.mainCase_m5,
    ``GraphIso.Main.mainCase_m4, ``GraphIso.Main.mainCase_none, ``GraphIso.Main.mainCase_some,
    ``GraphIso.Main.le_workEnv, ``GraphIso.Main.caseWork_le_env, ``GraphIso.Main.caseF_le_env,
    ``GraphIso.Main.caseA_le_env, ``GraphIso.Main.caseB_le_env, ``GraphIso.Main.mainCase_kj,
    ``GraphIso.Main.mainWork_le, ``GraphIso.Main.main_count_le, ``GraphIso.Main.miniRk_none_lt,
    ``GraphIso.Main.casePred_rk, ``GraphIso.Main.main_cost_le, ``GraphIso.Main.dom_base_le,
    ``GraphIso.Main.main_sub_of_ih, ``GraphIso.Main.main_ind_step, ``GraphIso.Main.main_spec,
    ``GraphIso.Main.mainSolve_ss, ``GraphIso.Main.mainSolve_ss_const,
    -- 14j-5d round 2: local thresholds and the parameters at the domain's bounds
    ``GraphIso.Cost.Prog.not_local_call, ``GraphIso.Cost.Prog.not_local_recur,
    ``GraphIso.Cost.foldRun_calls, ``GraphIso.Cost.Prog.Local.eval_calls,
    ``GraphIso.Cost.Prog.Local.runs_calls, ``GraphIso.Main.ThrSpec.calls,
    ``GraphIso.Main.m5FBu_self, ``GraphIso.Main.msCount_mono, ``GraphIso.Main.pow_le_dom,
    ``GraphIso.Main.m4R_le_dom, ``GraphIso.Main.c2bRU_mono, ``GraphIso.Main.c3R_le_dom,
    ``GraphIso.Main.m4_dom_params, ``GraphIso.Main.m5_dom_params,
    ``GraphIso.Main.ssLgM4_le_dom, ``GraphIso.Main.ssLgM5_le_dom,
    ``GraphIso.Main.ss_m5CFCJ_le_u, ``GraphIso.Main.main_m4_at, ``GraphIso.Main.main_m4_dom,
    ``GraphIso.Main.main_m5_at, ``GraphIso.Main.main_m5_dom, ``GraphIso.Main.caseWork_le_dom,
    ``GraphIso.Main.envSup_mono_box, ``GraphIso.Main.workEnv_mono_box,
    ``GraphIso.Main.mainW_le_dom, ``GraphIso.Main.miniC_mono_W, ``GraphIso.Main.main_spec_dom,
    ``GraphIso.Main.mainSolve_ss_dom,
    -- 14j-6a: the label invariant
    ``GraphIso.Toolkit.labLen, ``GraphIso.Toolkit.foldr_maxLen_le_iff,
    ``GraphIso.Toolkit.labLen_le_iff, ``GraphIso.Toolkit.length_le_labLen,
    ``GraphIso.Toolkit.length_getD_le_labLen, ``GraphIso.Toolkit.labLen_le_of_getD,
    ``GraphIso.Toolkit.labLen_mapLabels_le, ``GraphIso.Toolkit.labLen_mapLabels_short,
    ``GraphIso.Toolkit.length_interLab_le, ``GraphIso.Toolkit.length_filter_pos_blockCount_le,
    ``GraphIso.Toolkit.length_blockLab_le, ``GraphIso.Main.ell0, ``GraphIso.Main.LabInvAt,
    ``GraphIso.Main.LabInv, ``GraphIso.Main.LabInvAt.mono, ``GraphIso.Main.LabInvAt.of_le_one,
    ``GraphIso.Main.le_choose_two, ``GraphIso.Main.LabInvAt.johnson,
    ``GraphIso.Main.LabInv.of_none, ``GraphIso.Main.LabInv.entry,
    ``GraphIso.Main.LabInv.of_le,
    ``GraphIso.Main.SizeChild.lab_none, ``GraphIso.Main.SizeChild.lab_closed,
    ``GraphIso.Main.m1O_facts, ``GraphIso.Main.labLen_labM0D, ``GraphIso.Main.labLen_labM1D_le,
    ``GraphIso.Main.labLen_labM2aD_le, ``GraphIso.Main.labLen_m2bLabels_le,
    ``GraphIso.Main.labLen_labJUD_le, ``GraphIso.Main.labLen_labDiffD_le,
    ``GraphIso.Main.dv_johnson_choose_le, ``GraphIso.Main.dv_jdec_card,
    ``GraphIso.Main.dv_cj_choose_le, ``GraphIso.Main.childHInst_labInv,
    ``GraphIso.Main.MlChildL, ``GraphIso.Main.RunsWithin.m2bLoopProg_lab,
    ``GraphIso.Main.labLen_rbLabels_le, ``GraphIso.Main.LabInvIf, ``GraphIso.Main.MainSubB,
    ``GraphIso.Main.MainSubL, ``GraphIso.Main.MainSub.toB, ``GraphIso.Main.MainSubL.toB,
    ``GraphIso.Main.MainSubB.step, ``GraphIso.Main.main_predB,
    ``GraphIso.Main.labLen_normLabD_le, ``GraphIso.Main.LabInvIf.normLab,
    ``GraphIso.Main.main_step_gen, ``GraphIso.Main.main_step_lab,
    ``GraphIsoChecks.MainSteps.labInvAtB_iff, ``GraphIsoChecks.MainSteps.not_labInvAt,
    -- 14j-6b-1: the steps without stuck orbits
    ``GraphIso.Case2b.PartLe, ``GraphIso.Case2b.extPart_partLe, ``GraphIso.Case2b.leafTree_partLe,
    ``GraphIso.Case2b.cb_choice_facts, ``GraphIso.Case2b.cb_choice_partLe,
    ``GraphIso.Case2b.case2bTree_partLe, ``GraphIso.Case2b.firstLeafD_partLe,
    ``GraphIso.Case2b.degD_le_T, ``GraphIso.Case3.splitTree_uniprim,
    ``GraphIso.Case3.splitTree_partLe, ``GraphIso.Case3.outTree_dom,
    ``GraphIso.Case3.outTree_partLe, ``GraphIso.Case3.case3Tree_partLe,
    ``GraphIso.Case3.firstStructD_partLe, ``GraphIso.Main.ss_union_le_lab, ``GraphIso.Main.ssBdJU,
    ``GraphIso.Main.ssBdJ_eq, ``GraphIso.Main.rd_orbit_cj_ssUB, ``GraphIso.Main.rd_orbit_cj_ssL,
    ``GraphIso.Main.ss_m4_hDU, ``GraphIso.Main.m4WhUSS, ``GraphIso.Main.m4WhSS_eq,
    ``GraphIso.Main.m4WorkNsLSS, ``GraphIso.Main.m4WorkNsLSS_mono,
    ``GraphIso.Main.RunsWithin.m4StepProg_ns_ssU, ``GraphIso.Main.RunsWithin.m4StepProg_nsL_ss,
    ``GraphIso.Main.RunsWithin.m5DispatchCJ_ns_jpC, ``GraphIso.Main.RunsWithin.m5CoreCJProg_ns_jpC,
    ``GraphIso.Main.RunsWithin.m5StepCJProg_ns, ``GraphIso.Main.c2bRj,
    ``GraphIso.Main.c2bRU_eq_c2bRj, ``GraphIso.Main.c2bR_le_j, ``GraphIso.Main.c2bRj_mono,
    ``GraphIso.Main.ssM5βns, ``GraphIso.Main.m5Sel_four, ``GraphIso.Main.m5Sel_three,
    ``GraphIso.Main.ss_m5_degD_le_T, ``GraphIso.Main.ss_m5_depth_le,
    ``GraphIso.Main.ss_m5_hBgen₂ᵦ_ns, ``GraphIso.Main.ss_m5_hLY₂_ns, ``GraphIso.Main.ss_m5_hpart₂ᵦ,
    ``GraphIso.Main.ss_m5_hu₂_lab, ``GraphIso.Main.ss_m5_hu₃_lab, ``GraphIso.Main.ss_m5_c3_facts,
    ``GraphIso.Main.ss_m5_hnt₃, ``GraphIso.Main.ss_m5_hpart₃, ``GraphIso.Main.ss_m5_hDJ₂_lab,
    ``GraphIso.Main.ss_m5_hDJ₃_lab, ``GraphIso.Main.m5DispNumNs, ``GraphIso.Main.m5WnsCJ_le,
    ``GraphIso.Main.m5WorkRawNs, ``GraphIso.Main.m5WorkNsSS, ``GraphIso.Main.m5WorkNsSS_mono,
    ``GraphIso.Main.le_m5WorkNsSS, ``GraphIso.Main.m5CoreWorkNsCJ_le, ``GraphIso.Main.ssBdJU_mono_u,
    ``GraphIso.Main.RunsWithin.m5StepCJProg_ns_ss₀, ``GraphIso.Main.RunsWithin.m5StepCJProg_ns_ss,
    ``GraphIso.Main.m5FBns, ``GraphIso.Main.ss_m5CFnsCJ_le, ``GraphIso.Main.ssLgM5Ns,
    ``GraphIso.Main.m5ns_params, ``GraphIsoChecks.NoStuck.pfix, ``GraphIsoChecks.NoStuck.efix,
    ``GraphIsoChecks.NoStuck.pfix_valid,
    -- 14j-6b-2: the sharp dispatcher
    ``GraphIso.Main.TBelow, ``GraphIso.Main.SharpHyp, ``GraphIso.Certificates.Thresholds.of_le,
    ``GraphIso.Main.wielandtT, ``GraphIso.Main.supTo_wielandtT, ``GraphIso.Main.twelve_le_pow,
    ``GraphIso.Main.tBelow_wielandt, ``GraphIso.Main.not_tBelow_id,
    ``GraphIso.Main.ss_m4J_sharp, ``GraphIso.Main.bigCase_eq_m4,
    ``GraphIso.Main.bigCase_eq_m5, ``GraphIso.Main.mainCase_big, ``GraphIso.Main.mainCase_m3_le,
    ``GraphIso.Main.main_m4_sharp, ``GraphIso.Main.m5FBns_mono_u, ``GraphIso.Main.main_m5_sharp,
    ``GraphIso.Main.caseWorkS, ``GraphIso.Main.caseFS, ``GraphIso.Main.caseWorkS_of_ne,
    ``GraphIso.Main.caseFS_of_ne, ``GraphIso.Main.labT, ``GraphIso.Main.mainWorkS,
    ``GraphIso.Main.mainWorkS_eq, ``GraphIso.Main.mainWorkS_of_ne, ``GraphIso.Main.main_step_sharp,
    -- 14j-6b-2: corner bounds of the sharp work (`GraphIso.Main.SharpWork`) and its checks
    ``GraphIso.Main.psCostFrom_mono, ``GraphIso.Main.envSup_le,
    ``GraphIso.Main.pow_half_le_factorial, ``GraphIso.Main.CostMono.Align_isoInPCost,
    ``GraphIso.Main.CostMono.Toolkit_baseWinCost, ``GraphIso.Main.CostMono.Align_alignCallCost,
    ``GraphIso.Main.CostMono.Align_baseDCost, ``GraphIso.Main.CostMono.Align_preCost,
    ``GraphIso.Main.CostMono.Align_stabInPCost, ``GraphIso.Main.CostMono.Align_alignCost,
    ``GraphIso.Main.CostMono.Align_blkLCost, ``GraphIso.Main.CostMono.Align_preVCost,
    ``GraphIso.Main.CostMono.Align_jmapCost, ``GraphIso.Main.CostMono.Align_ordCost,
    ``GraphIso.Main.CostMono.Align_branchCost, ``GraphIso.Main.CostMono.Align_cellSwapCost,
    ``GraphIso.Main.CostMono.Align_exchDCost, ``GraphIso.Main.CostMono.Align_exchRowCost,
    ``GraphIso.Main.CostMono.Align_exchGensCost, ``GraphIso.Main.CostMono.Align_rowACost,
    ``GraphIso.Main.CostMono.Align_rowCCost, ``GraphIso.Main.CostMono.Align_johnGensCost,
    ``GraphIso.Main.CostMono.Align_sizesCost, ``GraphIso.Main.CostMono.Align_profCost,
    ``GraphIso.Main.CostMono.Align_johnIsoCost, ``GraphIso.Main.CostMono.Align_keyCost,
    ``GraphIso.Main.CostMono.Align_matchStepCost, ``GraphIso.Main.CostMono.Align_repsCost,
    ``GraphIso.Main.CostMono.Align_matchCost, ``GraphIso.Main.CostMono.Align_rowCost,
    ``GraphIso.Main.CostMono.Align_withinCost, ``GraphIso.Main.CostMono.Align_partGensCost,
    ``GraphIso.Main.CostMono.Align_permCost, ``GraphIso.Main.CostMono.Align_partIsoCost,
    ``GraphIso.Main.CostMono.Align_setPartCost, ``GraphIso.Main.CostMono.Align_setGensCost,
    ``GraphIso.Main.CostMono.Align_setIsoCost, ``GraphIso.Main.CostMono.Case2b_pairsCost,
    ``GraphIso.Main.CostMono.Case2b_tupleCost, ``GraphIso.Main.CostMono.Case2b_tupStepCost,
    ``GraphIso.Main.CostMono.Case2b_tuplesCost, ``GraphIso.Main.CostMono.Case2b_allCost,
    ``GraphIso.Main.CostMono.Case2b_c2bR, ``GraphIso.Main.CostMono.Coherent_infoAtCost,
    ``GraphIso.Main.CostMono.Coherent_pwTabCost, ``GraphIso.Main.CostMono.Coherent_extCost,
    ``GraphIso.Main.CostMono.Coherent_tupsCost, ``GraphIso.Main.CostMono.Coherent_infoCost,
    ``GraphIso.Main.CostMono.Coherent_ceSig0, ``GraphIso.Main.CostMono.Coherent_rankCost,
    ``GraphIso.Main.CostMono.Coherent_initCost, ``GraphIso.Main.CostMono.Coherent_ceSig,
    ``GraphIso.Main.CostMono.Coherent_sigCost, ``GraphIso.Main.CostMono.Coherent_roundCost,
    ``GraphIso.Main.CostMono.Coherent_wlRunCost, ``GraphIso.Main.CostMono.Coherent_wlCost,
    ``GraphIso.Main.CostMono.Toolkit_matrixCost, ``GraphIso.Main.CostMono.Toolkit_orbitalCost,
    ``GraphIso.Main.CostMono.Case2b_colCost, ``GraphIso.Main.CostMono.Case2b_extCost,
    ``GraphIso.Main.CostMono.Case2b_trimCost, ``GraphIso.Main.CostMono.SoJTree_outB,
    ``GraphIso.Main.CostMono.SoJTree_addPieceCost, ``GraphIso.Main.CostMono.SoJTree_exBlkCost,
    ``GraphIso.Main.CostMono.SoJTree_extendOutCost, ``GraphIso.Main.CostMono.SoJTree_opCost,
    ``GraphIso.Main.CostMono.SoJTree_stepK, ``GraphIso.Main.CostMono.Case2b_sojBranchCost,
    ``GraphIso.Main.CostMono.SoJProg_stepCost, ``GraphIso.Main.CostMono.SoJProg_compCost,
    ``GraphIso.Main.CostMono.SoJProg_compPartCost, ``GraphIso.Main.CostMono.SoJProg_offColsCost,
    ``GraphIso.Main.CostMono.SoJProg_disconnCost, ``GraphIso.Main.CostMono.Case2b_leavesOfCost,
    ``GraphIso.Main.CostMono.Case2b_resCost, ``GraphIso.Main.CostMono.Case2b_choiceCost,
    ``GraphIso.Main.CostMono.Case2b_chCost, ``GraphIso.Main.CostMono.Toolkit_degRound,
    ``GraphIso.Main.CostMono.Toolkit_degreeCost, ``GraphIso.Main.CostMono.Case2b_degCost,
    ``GraphIso.Main.CostMono.Case2b_leafB, ``GraphIso.Main.CostMono.Case2b_outGensCost,
    ``GraphIso.Main.CostMono.Case2b_outIsoCost, ``GraphIso.Main.CostMono.Case2b_c2bCost,
    ``GraphIso.Main.CostMono.Case2b_outGensB, ``GraphIso.Main.CostMono.Case2b_sojZ,
    ``GraphIso.Main.CostMono.Case3_c3R, ``GraphIso.Main.CostMono.Coherent_goodCost,
    ``GraphIso.Main.CostMono.Coherent_tupsBound, ``GraphIso.Main.CostMono.SoJProg_goodListCost,
    ``GraphIso.Main.CostMono.Case3_pipePrefixCost, ``GraphIso.Main.CostMono.Case3_structsCost,
    ``GraphIso.Main.CostMono.Case3_twinsFlagCost, ``GraphIso.Main.CostMono.Case3_c3Cost,
    ``GraphIso.Main.CostMono.Case3_skelCost, ``GraphIso.Main.CostMono.Case3_domCost,
    ``GraphIso.Main.CostMono.Case3_outPrefixCost, ``GraphIso.Main.CostMono.Case3_smallLeafCost,
    ``GraphIso.Main.CostMono.Case3_c3OutCost, ``GraphIso.Main.CostMono.Case3_cmpCost,
    ``GraphIso.Main.CostMono.Case3_firstIdxCost, ``GraphIso.Main.CostMono.Case3_nodupCost,
    ``GraphIso.Main.CostMono.Case3_entryXCost, ``GraphIso.Main.CostMono.Case3_entryYCost,
    ``GraphIso.Main.CostMono.Case3_tupleColCost, ``GraphIso.Main.CostMono.Case3_c3CostC,
    ``GraphIso.Main.CostMono.CertProg_giantACost, ``GraphIso.Main.CostMono.CertProg_affCost,
    ``GraphIso.Main.CostMono.CertProg_stepPoly₀, ``GraphIso.Main.CostMono.CertProg_stepPoly₁,
    ``GraphIso.Main.CostMono.CertProg_stepPoly, ``GraphIso.Main.CostMono.CertProg_unionCost,
    ``GraphIso.Main.CostMono.CertProg_loopPoly, ``GraphIso.Main.CostMono.CertProg_outsideCost,
    ``GraphIso.Main.CostMono.Toolkit_swapPairCost, ``GraphIso.Main.CostMono.CertProg_moveFixCost,
    ``GraphIso.Main.CostMono.CertProg_moveStepCost, ``GraphIso.Main.CostMono.CertProg_moveDataCost,
    ``GraphIso.Main.CostMono.CertProg_ttStepCost, ``GraphIso.Main.CostMono.CertProg_tupleTransCost,
    ``GraphIso.Main.CostMono.Toolkit_giantSetStabCost,
    ``GraphIso.Main.CostMono.CertProg_certIsoPoly, ``GraphIso.Main.CostMono.CertProg_certPoly,
    ``GraphIso.Main.CostMono.CertProg_kerACost, ``GraphIso.Main.CostMono.Giant_agExtCost,
    ``GraphIso.Main.CostMono.Giant_c1OrbitCost, ``GraphIso.Main.CostMono.Giant_c2aCost,
    ``GraphIso.Main.CostMono.Giant_orbitPartCost, ``GraphIso.Main.CostMono.Giant_case1Cost,
    ``GraphIso.Main.CostMono.Giant_caseCost, ``GraphIso.Main.CostMono.Giant_ksubsCost,
    ``GraphIso.Main.CostMono.Giant_pbBranchCost, ``GraphIso.Main.CostMono.Giant_pbCost,
    ``GraphIso.Main.CostMono.Luks_closureCost, ``GraphIso.Main.CostMono.Luks_mbCost,
    ``GraphIso.Main.CostMono.Luks_maxBlocksCost, ``GraphIso.Main.CostMono.Toolkit_blockLabCost,
    ``GraphIso.Main.CostMono.Toolkit_rebaseCost, ``GraphIso.Main.CostMono.Main_m2aCost,
    ``GraphIso.Main.CostMono.Toolkit_blockStabCost, ``GraphIso.Main.CostMono.Toolkit_interCost,
    ``GraphIso.Main.CostMono.Toolkit_markCost, ``GraphIso.Main.CostMono.Main_m2bCost,
    ``GraphIso.Main.CostMono.Toolkit_equidistCost, ``GraphIso.Main.CostMono.Main_neqCost,
    ``GraphIso.Main.CostMono.Toolkit_baseBlocksCost, ``GraphIso.Main.CostMono.Main_blocksCost,
    ``GraphIso.Main.CostMono.Programs_liftCost, ``GraphIso.Main.CostMono.Programs_restrictCost,
    ``GraphIso.Main.CostMono.Main_c2aWork, ``GraphIso.Main.CostMono.Main_cjPairCost,
    ``GraphIso.Main.CostMono.Main_q2bCost, ``GraphIso.Main.CostMono.Main_cjTupleCost,
    ``GraphIso.Main.CostMono.Main_cjAllCost, ``GraphIso.Main.CostMono.Main_cjohnGensCost,
    ``GraphIso.Main.CostMono.Main_ccolsCost, ``GraphIso.Main.CostMono.Main_crestCost,
    ``GraphIso.Main.CostMono.Main_cjohnIsoCost, ``GraphIso.Main.CostMono.Main_c2bCJCost,
    ``GraphIso.Main.CostMono.Main_c2bJTestCost, ``GraphIso.Main.CostMono.Main_c2bRU,
    ``GraphIso.Main.CostMono.Main_c2bRj, ``GraphIso.Main.CostMono.Main_c3ClsCost,
    ``GraphIso.Main.CostMono.Main_c3FirstClsCost, ``GraphIso.Main.CostMono.Main_q3Cost,
    ``GraphIso.Main.CostMono.Main_cjOut3Cost, ``GraphIso.Main.CostMono.Main_cjStructs3Cost,
    ``GraphIso.Main.CostMono.Main_c3CJCost, ``GraphIso.Main.CostMono.Main_c3ColWork,
    ``GraphIso.Main.CostMono.Main_c3PreWork, ``GraphIso.Main.CostMono.Main_c3Work,
    ``GraphIso.Main.CostMono.Main_certCount, ``GraphIso.Main.CostMono.Main_certWork,
    ``GraphIso.Main.CostMono.Main_cjB, ``GraphIso.Main.CostMono.Main_jfallbackCost,
    ``GraphIso.Main.CostMono.Main_interOCost, ``GraphIso.Main.CostMono.SoJTree_setEqCost,
    ``GraphIso.Main.CostMono.Main_ncPairCost, ``GraphIso.Main.CostMono.Main_ncCost,
    ``GraphIso.Main.CostMono.Main_ncBCost, ``GraphIso.Main.CostMono.Toolkit_jUnionCost,
    ``GraphIso.Main.CostMono.Main_johnStepCost, ``GraphIso.Main.CostMono.Main_labM1Cost,
    ``GraphIso.Main.CostMono.Main_pickCost, ``GraphIso.Main.CostMono.Main_m1Cost,
    ``GraphIso.Main.CostMono.Main_m1ContCost, ``GraphIso.Main.CostMono.Main_deriveCJCost,
    ``GraphIso.Main.CostMono.Main_deriveFreeCost, ``GraphIso.Main.CostMono.Main_dynStepCost,
    ``GraphIso.Main.CostMono.Main_dynSeqCost, ``GraphIso.Main.CostMono.Main_fixPtsCost,
    ``GraphIso.Main.CostMono.Main_mlHandleCost, ``GraphIso.Main.CostMono.Main_transferCost,
    ``GraphIso.Main.CostMono.Main_viaChildCost, ``GraphIso.Main.CostMono.Main_mlBranchCost,
    ``GraphIso.Main.CostMono.Main_m2bLoopCost, ``GraphIso.Main.CostMono.Main_msCount,
    ``GraphIso.Main.CostMono.Main_m4R, ``GraphIso.Main.CostMono.Main_m4StructCost,
    ``GraphIso.Main.CostMono.Main_prodRepsLCost, ``GraphIso.Main.CostMono.Main_rdCost,
    ``GraphIso.Main.CostMono.Toolkit_pointStabsCost, ``GraphIso.Main.CostMono.Main_m4StepCost,
    ``GraphIso.Main.CostMono.Sims_initCost, ``GraphIso.Main.CostMono.Sims_siftCost,
    ``GraphIso.Main.CostMono.Sims_itemCost, ``GraphIso.Main.CostMono.Sims_insCost,
    ``GraphIso.Main.CostMono.Sims_slotCost, ``GraphIso.Main.CostMono.Sims_buildCost,
    ``GraphIso.Main.CostMono.Sims_genCost, ``GraphIso.Main.CostMono.Sims_transCost,
    ``GraphIso.Main.CostMono.Sims_orbitsCost, ``GraphIso.Main.CostMono.Sims_stabCost,
    ``GraphIso.Main.CostMono.Main_m4CostSS, ``GraphIso.Main.CostMono.Main_rd5Cost,
    ``GraphIso.Main.CostMono.Main_rdOrbitWork, ``GraphIso.Main.CostMono.Main_ssBdF,
    ``GraphIso.Main.CostMono.Main_ssBdJU, ``GraphIso.Main.CostMono.Sims_liftCost,
    ``GraphIso.Main.CostMono.Main_m4WhUSS, ``GraphIso.Main.CostMono.Main_m5CaseCost,
    ``GraphIso.Main.CostMono.Main_m5Wb, ``GraphIso.Main.CostMono.Main_m5DispNumNs,
    ``GraphIso.Main.CostMono.Main_olB, ``GraphIso.Main.CostMono.Main_ssBg1J,
    ``GraphIso.Main.CostMono.Sims_kerCost, ``GraphIso.Main.CostMono.Sims_memCost,
    ``GraphIso.Main.CostMono.Sims_repsVisitCost, ``GraphIso.Main.CostMono.Sims_repsCost,
    ``GraphIso.Main.CostMono.Toolkit_psStepCost, ``GraphIso.Main.m4PtNsL,
    ``GraphIso.Main.m4PtNsL_mono, ``GraphIso.Main.m4WorkNsLSS_le, ``GraphIso.Main.m5CertPt,
    ``GraphIso.Main.m5CasePt, ``GraphIso.Main.m5DispPt, ``GraphIso.Main.m5WorkRawNs_eq,
    ``GraphIso.Main.m5WorkUB, ``GraphIso.Main.m5CertPt_mono, ``GraphIso.Main.m5CasePt_mono,
    ``GraphIso.Main.m5DispPt_mono, ``GraphIso.Main.m5WorkNsSS_le, ``GraphIso.Main.caseWorkS_m4_le,
    ``GraphIso.Main.caseWorkS_m5_le, ``GraphIsoChecks.Sharp.sharp_m4_work_lt,
    ``GraphIsoChecks.Sharp.sharp_m5_work_lt, ``GraphIsoChecks.Sharp.msCount_pow_le_caseWorkS_m4]
  let mut lines : Array MessageData := #[]
  for name in principal do
    let axs ← collectAxioms name
    lines := lines.push m!"{name}: {axs.toList}"
  logInfo (MessageData.joinSep lines.toList "\n")

/-! The list continues in the next block. -/

open Lean in
run_cmd do
  let principal := #[
    -- 14j-6c-1: the potential (`GraphIso.Recursion.PotOffset`, `GraphIso.Main.PotThr`,
    -- `PotWork`, `PotQ`, `FullPot`)
    ``GraphIso.Recursion.pow_le_pot, ``GraphIso.Recursion.pot_step_mul,
    ``GraphIso.Recursion.sum_map_add_const, ``GraphIso.Recursion.pot_step_off,
    ``GraphIso.Recursion.pot_free_child, ``GraphIso.Recursion.two_mul_le_pow,
    ``GraphIso.Recursion.pot_free_off, ``GraphIso.Recursion.pot_chain_off, ``GraphIso.Main.QPHyp,
    ``GraphIso.Main.qpL, ``GraphIso.Main.kQP, ``GraphIso.Main.ℓT, ``GraphIso.Main.ℓQP,
    ``GraphIso.Main.lam_add_one_le_qpL, ``GraphIso.Main.qpL_le, ``GraphIso.Main.kQP_eq,
    ``GraphIso.Main.five_le_kQP, ``GraphIso.Main.four_mul_kQP_le, ``GraphIso.Main.ℓT_le_ℓQP,
    ``GraphIso.Main.ell0_le_ℓQP, ``GraphIso.Main.two_pow_le_factorial,
    ``GraphIso.Main.thresholds_qp, ``GraphIso.Main.sq_succ_le_four_pow, ``GraphIso.Main.tBelow_qp,
    ``GraphIso.Main.TBelow.mono, ``GraphIso.Main.sharpHyp_qp, ``GraphIso.Main.cTQP,
    ``GraphIso.Main.thrQP, ``GraphIso.Main.thrQP_spec, ``GraphIso.Main.CostMono.Main_bigTestCost,
    ``GraphIso.Main.CostMono.Main_blkTestCost, ``GraphIso.Main.CostMono.Main_c3Count,
    ``GraphIso.Main.CostMono.Main_chainCost, ``GraphIso.Main.CostMono.Main_fixedStepCost,
    ``GraphIso.Main.CostMono.Main_fixedTestCost, ``GraphIso.Main.CostMono.Main_hintPreCost,
    ``GraphIso.Main.CostMono.Main_kerRedCost, ``GraphIso.Main.CostMono.Main_m0Cost,
    ``GraphIso.Main.CostMono.Main_m0StepCost, ``GraphIso.Main.CostMono.Main_m0WorkSS,
    ``GraphIso.Main.CostMono.Main_m1StepCost, ``GraphIso.Main.CostMono.Main_m1WorkSS,
    ``GraphIso.Main.CostMono.Main_m2aStepCost, ``GraphIso.Main.CostMono.Main_m2aWorkSS,
    ``GraphIso.Main.CostMono.Main_m2bStepCost, ``GraphIso.Main.CostMono.Main_m2bWorkSS,
    ``GraphIso.Main.CostMono.Main_m3WorkSS, ``GraphIso.Main.CostMono.Main_m5FBns,
    ``GraphIso.Main.CostMono.Main_neqTestCost, ``GraphIso.Main.CostMono.Main_mainTestCost,
    ``GraphIso.Main.CostMono.Main_rbCost, ``GraphIso.Main.CostMono.Main_rbOverSS,
    ``GraphIso.Main.CostMono.Main_ssLgM4Ns, ``GraphIso.Main.CostMono.Main_ssLgM5Ns,
    ``GraphIso.Main.m5WorkUB_mono, ``GraphIso.Main.sGQ, ``GraphIso.Main.uMaxQ,
    ``GraphIso.Main.jMaxQ, ``GraphIso.Main.mLQ, ``GraphIso.Main.qpTest, ``GraphIso.Main.qpM4,
    ``GraphIso.Main.qpM5, ``GraphIso.Main.qpCases, ``GraphIso.Main.qpWork, ``GraphIso.Main.qpFac,
    ``GraphIso.Main.QQP, ``GraphIso.Main.ss_m4J_le_T, ``GraphIso.Main.supTo_le_jMaxQ,
    ``GraphIso.Main.labLen_mul_lam_le, ``GraphIso.Main.caseWorkS_le_qpCases,
    ``GraphIso.Main.mainWorkS_le_QQP, ``GraphIso.Main.caseFAB_le_QQP,
    ``GraphIso.Main.winSize_add_two_le_QQP, ``GraphIso.Main.potO_none_mono,
    ``GraphIso.Main.sum_one_add, ``GraphIso.Main.sum_counted, ``GraphIso.Main.pot_free_case,
    ``GraphIso.Main.pot_step_case, ``GraphIso.Main.pot_chain_case,
    ``GraphIso.Main.ChildList.eq_nil_of_zero, ``GraphIso.Main.pot_case_le, ``GraphIso.Main.PotIH,
    ``GraphIso.Main.pot_sub_of_ih, ``GraphIso.Main.caseA_zero_win, ``GraphIso.Main.caseB_zero_win,
    ``GraphIso.Main.pot_ind_step, ``GraphIso.Main.main_pot, ``GraphIso.Main.mainSolve_qp,
    ``GraphIso.Main.mainSolve_qp_closed,
    -- 14j-6c-2: the closed bound (`GraphIso.Main.Growth`, `GrowthCosts` (generated),
    -- `QPBound`) and its checks (`GraphIsoChecks.QPBound`)
    ``GraphIso.Growth.PLB, ``GraphIso.Growth.QPB, ``GraphIso.Growth.one_le_X,
    ``GraphIso.Growth.self_le_two_pow, ``GraphIso.Growth.QPB.mono, ``GraphIso.Growth.QPB.const,
    ``GraphIso.Growth.QPB.lift, ``GraphIso.Growth.QPB.add, ``GraphIso.Growth.QPB.mul,
    ``GraphIso.Growth.QPB.max, ``GraphIso.Growth.QPB.min_left, ``GraphIso.Growth.QPB.sub,
    ``GraphIso.Growth.QPB.div, ``GraphIso.Growth.QPB.pow_const, ``GraphIso.Growth.QPB.clog,
    ``GraphIso.Growth.QPB.log, ``GraphIso.Growth.QPB.comp, ``GraphIso.Growth.PLB.mono,
    ``GraphIso.Growth.PLB.const, ``GraphIso.Growth.PLB.lift, ``GraphIso.Growth.PLB.add,
    ``GraphIso.Growth.PLB.mul, ``GraphIso.Growth.PLB.const_mul, ``GraphIso.Growth.PLB.mul_const,
    ``GraphIso.Growth.PLB.max, ``GraphIso.Growth.PLB.min_left, ``GraphIso.Growth.PLB.sub,
    ``GraphIso.Growth.PLB.div, ``GraphIso.Growth.PLB.pow_const, ``GraphIso.Growth.PLB.clog,
    ``GraphIso.Growth.PLB.log, ``GraphIso.Growth.PLB.comp, ``GraphIso.Growth.PLB.qpb,
    ``GraphIso.Growth.PLB.qpb', ``GraphIso.Growth.PLB.bvar_le, ``GraphIso.Growth.PLB.bvar_lt,
    ``GraphIso.Growth.QPB.pow, ``GraphIso.Growth.QPB.factorial, ``GraphIso.Growth.QPB.choose,
    ``GraphIso.Growth.QPB.two_pow, ``GraphIso.Growth.QPB.supTo, ``GraphIso.Growth.QPB.sum_range_le,
    ``GraphIso.Growth.QPB.sum_range, ``GraphIso.Growth.Main.fixedTestCost_qpb,
    ``GraphIso.Growth.Sims.transCost_qpb, ``GraphIso.Growth.Sims.orbitsCost_qpb,
    ``GraphIso.Growth.Toolkit.baseWinCost_qpb, ``GraphIso.Growth.Main.hintPreCost_qpb,
    ``GraphIso.Growth.Luks.closureCost_qpb, ``GraphIso.Growth.Luks.mbCost_qpb,
    ``GraphIso.Growth.Luks.maxBlocksCost_qpb, ``GraphIso.Growth.Toolkit.baseBlocksCost_qpb,
    ``GraphIso.Growth.Main.blkTestCost_qpb, ``GraphIso.Growth.Toolkit.equidistCost_qpb,
    ``GraphIso.Growth.Main.neqCost_qpb, ``GraphIso.Growth.Main.neqTestCost_qpb,
    ``GraphIso.Growth.Toolkit.degRound_qpb, ``GraphIso.Growth.Toolkit.degreeCost_qpb,
    ``GraphIso.Growth.Sims.initCost_qpb, ``GraphIso.Growth.Sims.siftCost_qpb,
    ``GraphIso.Growth.Sims.itemCost_qpb, ``GraphIso.Growth.Sims.insCost_qpb,
    ``GraphIso.Growth.Sims.slotCost_qpb, ``GraphIso.Growth.Sims.buildCost_qpb,
    ``GraphIso.Growth.Sims.stabCost_qpb, ``GraphIso.Growth.Main.bigTestCost_qpb,
    ``GraphIso.Growth.Main.mainTestCost_qpb, ``GraphIso.Growth.Main.fixedStepCost_qpb,
    ``GraphIso.Growth.Main.chainCost_qpb, ``GraphIso.Growth.Toolkit.rebaseCost_qpb,
    ``GraphIso.Growth.Main.m0Cost_qpb, ``GraphIso.Growth.Main.transferCost_qpb,
    ``GraphIso.Growth.Main.viaChildCost_qpb, ``GraphIso.Growth.Main.m0StepCost_qpb,
    ``GraphIso.Growth.Sims.genCost_qpb, ``GraphIso.Growth.Sims.liftCost_qpb,
    ``GraphIso.Growth.Main.m0WorkSS_qpb, ``GraphIso.Growth.Main.interOCost_qpb,
    ``GraphIso.Growth.SoJTree.setEqCost_qpb, ``GraphIso.Growth.Main.ncPairCost_qpb,
    ``GraphIso.Growth.Main.ncCost_qpb, ``GraphIso.Growth.Main.pickCost_qpb,
    ``GraphIso.Growth.Main.labM1Cost_qpb, ``GraphIso.Growth.Main.m1Cost_qpb,
    ``GraphIso.Growth.Main.m1StepCost_qpb, ``GraphIso.Growth.Main.m1WorkSS_qpb,
    ``GraphIso.Growth.Toolkit.blockLabCost_qpb, ``GraphIso.Growth.Main.m2aCost_qpb,
    ``GraphIso.Growth.Main.m2aStepCost_qpb, ``GraphIso.Growth.Main.m2aWorkSS_qpb,
    ``GraphIso.Growth.Toolkit.blockStabCost_qpb, ``GraphIso.Growth.Toolkit.markCost_qpb,
    ``GraphIso.Growth.Toolkit.interCost_qpb, ``GraphIso.Growth.Main.m2bCost_qpb,
    ``GraphIso.Growth.Main.ncBCost_qpb, ``GraphIso.Growth.Main.mlHandleCost_qpb,
    ``GraphIso.Growth.Main.dynStepCost_qpb, ``GraphIso.Growth.Main.dynSeqCost_qpb,
    ``GraphIso.Growth.Main.mlBranchCost_qpb, ``GraphIso.Growth.Main.m2bLoopCost_qpb,
    ``GraphIso.Growth.Main.m2bStepCost_qpb, ``GraphIso.Growth.Main.m2bWorkSS_qpb,
    ``GraphIso.Growth.Toolkit.psStepCost_qpb, ``GraphIso.Growth.Toolkit.psCostFrom_qpb,
    ``GraphIso.Growth.Toolkit.pointStabsCost_qpb, ``GraphIso.Growth.Toolkit.matrixCost_qpb,
    ``GraphIso.Growth.Toolkit.orbitalCost_qpb, ``GraphIso.Growth.SoJProg.offColsCost_qpb,
    ``GraphIso.Growth.SoJProg.stepCost_qpb, ``GraphIso.Growth.SoJProg.compCost_qpb,
    ``GraphIso.Growth.SoJProg.disconnCost_qpb, ``GraphIso.Growth.SoJTree.exBlkCost_qpb,
    ``GraphIso.Growth.SoJTree.extendOutCost_qpb, ``GraphIso.Growth.SoJTree.addPieceCost_qpb,
    ``GraphIso.Growth.SoJTree.opCost_qpb, ``GraphIso.Growth.SoJTree.stepK_qpb,
    ``GraphIso.Growth.Case2b.trimCost_qpb, ``GraphIso.Growth.SoJTree.outB_qpb,
    ``GraphIso.Growth.Case2b.sojBranchCost_qpb, ``GraphIso.Growth.SoJProg.compPartCost_qpb,
    ``GraphIso.Growth.Case2b.leavesOfCost_qpb, ``GraphIso.Growth.Case2b.sojZ_qpb,
    ``GraphIso.Growth.Main.msCount_qpb, ``GraphIso.Growth.Main.m4StructCost_qpb,
    ``GraphIso.Growth.Main.prodRepsLCost_qpb, ``GraphIso.Growth.Case2b.extCost_qpb,
    ``GraphIso.Growth.Main.rdCost_qpb, ``GraphIso.Growth.Main.m4R_qpb,
    ``GraphIso.Growth.Main.m4StepCost_qpb, ``GraphIso.Growth.Main.m4CostSS_qpb,
    ``GraphIso.Growth.Main.rd5Cost_qpb, ``GraphIso.Growth.Main.rdOrbitWork_qpb,
    ``GraphIso.Growth.Main.blocksCost_qpb, ``GraphIso.Growth.Main.m1ContCost_qpb,
    ``GraphIso.Growth.Main.deriveFreeCost_qpb, ``GraphIso.Growth.Main.ssBdF_qpb,
    ``GraphIso.Growth.Toolkit.jUnionCost_qpb, ``GraphIso.Growth.CertProg.kerACost_qpb,
    ``GraphIso.Growth.Main.jfallbackCost_qpb, ``GraphIso.Growth.Main.johnStepCost_qpb,
    ``GraphIso.Growth.Main.deriveCJCost_qpb, ``GraphIso.Growth.Main.ssBdJU_qpb,
    ``GraphIso.Growth.Main.m4WhUSS_qpb, ``GraphIso.Growth.Main.m4PtNsL_qpb,
    ``GraphIso.Growth.Main.ssLgM4Ns_qpb, ``GraphIso.Growth.Programs.liftCost_qpb,
    ``GraphIso.Growth.Main.rbCost_qpb, ``GraphIso.Growth.Sims.kerCost_qpb,
    ``GraphIso.Growth.Main.rbOverSS_qpb, ``GraphIso.Growth.Main.certCount_qpb,
    ``GraphIso.Growth.Giant.agExtCost_qpb, ``GraphIso.Growth.Giant.ksubsCost_qpb,
    ``GraphIso.Growth.CertProg.outsideCost_qpb, ``GraphIso.Growth.Toolkit.giantSetStabCost_qpb,
    ``GraphIso.Growth.CertProg.giantACost_qpb, ``GraphIso.Growth.CertProg.affCost_qpb,
    ``GraphIso.Growth.CertProg.stepPoly₀_qpb, ``GraphIso.Growth.CertProg.stepPoly₁_qpb,
    ``GraphIso.Growth.CertProg.stepPoly_qpb, ``GraphIso.Growth.CertProg.unionCost_qpb,
    ``GraphIso.Growth.CertProg.loopPoly_qpb, ``GraphIso.Growth.CertProg.certPoly_qpb,
    ``GraphIso.Growth.Main.certWork_qpb, ``GraphIso.Growth.Main.m5CertPt_qpb,
    ``GraphIso.Growth.Giant.caseCost_qpb, ``GraphIso.Growth.Main.m5CaseCost_qpb,
    ``GraphIso.Growth.Case2b.resCost_qpb, ``GraphIso.Growth.Case2b.degCost_qpb,
    ``GraphIso.Growth.Main.m5CasePt_qpb, ``GraphIso.Growth.Giant.c1OrbitCost_qpb,
    ``GraphIso.Growth.Giant.orbitPartCost_qpb, ``GraphIso.Growth.Align.baseDCost_qpb,
    ``GraphIso.Growth.Align.stabInPCost_qpb, ``GraphIso.Growth.Align.preCost_qpb,
    ``GraphIso.Growth.Align.isoInPCost_qpb, ``GraphIso.Growth.Align.alignCallCost_qpb,
    ``GraphIso.Growth.Align.alignCost_qpb, ``GraphIso.Growth.Align.blkLCost_qpb,
    ``GraphIso.Growth.Align.repsCost_qpb, ``GraphIso.Growth.Align.rowCost_qpb,
    ``GraphIso.Growth.Align.withinCost_qpb, ``GraphIso.Growth.Align.exchDCost_qpb,
    ``GraphIso.Growth.Align.exchRowCost_qpb, ``GraphIso.Growth.Align.exchGensCost_qpb,
    ``GraphIso.Growth.Align.partGensCost_qpb, ``GraphIso.Growth.Align.keyCost_qpb,
    ``GraphIso.Growth.Align.matchStepCost_qpb, ``GraphIso.Growth.Align.matchCost_qpb,
    ``GraphIso.Growth.Align.permCost_qpb, ``GraphIso.Growth.Align.partIsoCost_qpb,
    ``GraphIso.Growth.Giant.case1Cost_qpb, ``GraphIso.Growth.Main.m5Wb_qpb,
    ``GraphIso.Growth.Align.setPartCost_qpb, ``GraphIso.Growth.Align.setGensCost_qpb,
    ``GraphIso.Growth.Align.setIsoCost_qpb, ``GraphIso.Growth.Giant.c2aCost_qpb,
    ``GraphIso.Growth.Giant.pbBranchCost_qpb, ``GraphIso.Growth.Giant.pbCost_qpb,
    ``GraphIso.Growth.Programs.restrictCost_qpb, ``GraphIso.Growth.Main.c2aWork_qpb,
    ``GraphIso.Growth.Coherent.extCost_qpb, ``GraphIso.Growth.Coherent.tupsCost_qpb,
    ``GraphIso.Growth.Coherent.pwTabCost_qpb, ``GraphIso.Growth.Coherent.infoAtCost_qpb,
    ``GraphIso.Growth.Coherent.infoCost_qpb, ``GraphIso.Growth.Coherent.rankCost_qpb,
    ``GraphIso.Growth.Coherent.ceSig0_qpb, ``GraphIso.Growth.Coherent.initCost_qpb,
    ``GraphIso.Growth.Coherent.sigCost_qpb, ``GraphIso.Growth.Coherent.ceSig_qpb,
    ``GraphIso.Growth.Coherent.roundCost_qpb, ``GraphIso.Growth.Coherent.wlRunCost_qpb,
    ``GraphIso.Growth.Coherent.wlCost_qpb, ``GraphIso.Growth.Coherent.tupsBound_qpb,
    ``GraphIso.Growth.Coherent.goodCost_qpb, ``GraphIso.Growth.SoJProg.goodListCost_qpb,
    ``GraphIso.Growth.Case3.twinsFlagCost_qpb, ``GraphIso.Growth.Case3.pipePrefixCost_qpb,
    ``GraphIso.Growth.Case3.structsCost_qpb, ``GraphIso.Growth.Case3.c3R_qpb,
    ``GraphIso.Growth.Align.rowACost_qpb, ``GraphIso.Growth.Align.preVCost_qpb,
    ``GraphIso.Growth.Align.jmapCost_qpb, ``GraphIso.Growth.Align.cellSwapCost_qpb,
    ``GraphIso.Growth.Align.rowCCost_qpb, ``GraphIso.Growth.Align.johnGensCost_qpb,
    ``GraphIso.Growth.Case2b.outGensCost_qpb, ``GraphIso.Growth.Case2b.leafB_qpb,
    ``GraphIso.Growth.Align.sizesCost_qpb, ``GraphIso.Growth.Align.profCost_qpb,
    ``GraphIso.Growth.Align.ordCost_qpb, ``GraphIso.Growth.Align.branchCost_qpb,
    ``GraphIso.Growth.Align.johnIsoCost_qpb, ``GraphIso.Growth.Case2b.outIsoCost_qpb,
    ``GraphIso.Growth.Case3.c3Cost_qpb, ``GraphIso.Growth.Case2b.outGensB_qpb,
    ``GraphIso.Growth.Case3.nodupCost_qpb, ``GraphIso.Growth.Case3.firstIdxCost_qpb,
    ``GraphIso.Growth.Case3.entryXCost_qpb, ``GraphIso.Growth.Case3.cmpCost_qpb,
    ``GraphIso.Growth.Case3.entryYCost_qpb, ``GraphIso.Growth.Case3.tupleColCost_qpb,
    ``GraphIso.Growth.Case3.outPrefixCost_qpb, ``GraphIso.Growth.Case3.smallLeafCost_qpb,
    ``GraphIso.Growth.Case3.skelCost_qpb, ``GraphIso.Growth.Case3.domCost_qpb,
    ``GraphIso.Growth.Case3.c3OutCost_qpb, ``GraphIso.Growth.Case3.c3CostC_qpb,
    ``GraphIso.Growth.Toolkit.swapPairCost_qpb, ``GraphIso.Growth.CertProg.moveStepCost_qpb,
    ``GraphIso.Growth.CertProg.moveFixCost_qpb, ``GraphIso.Growth.CertProg.moveDataCost_qpb,
    ``GraphIso.Growth.CertProg.ttStepCost_qpb, ``GraphIso.Growth.CertProg.tupleTransCost_qpb,
    ``GraphIso.Growth.CertProg.certIsoPoly_qpb, ``GraphIso.Growth.Main.c3Work_qpb,
    ``GraphIso.Growth.Main.c3ColWork_qpb, ``GraphIso.Growth.Main.c3PreWork_qpb,
    ``GraphIso.Growth.Main.c3ClsCost_qpb, ``GraphIso.Growth.Main.c3FirstClsCost_qpb,
    ``GraphIso.Growth.Main.q3Cost_qpb, ``GraphIso.Growth.Main.cjOut3Cost_qpb,
    ``GraphIso.Growth.Main.cjStructs3Cost_qpb, ``GraphIso.Growth.Main.cjohnGensCost_qpb,
    ``GraphIso.Growth.Main.ccolsCost_qpb, ``GraphIso.Growth.Main.crestCost_qpb,
    ``GraphIso.Growth.Main.cjohnIsoCost_qpb, ``GraphIso.Growth.Main.c3CJCost_qpb,
    ``GraphIso.Growth.Main.fixPtsCost_qpb, ``GraphIso.Growth.Case2b.tupStepCost_qpb,
    ``GraphIso.Growth.Case2b.tuplesCost_qpb, ``GraphIso.Growth.Case2b.colCost_qpb,
    ``GraphIso.Growth.Case2b.choiceCost_qpb, ``GraphIso.Growth.Case2b.chCost_qpb,
    ``GraphIso.Growth.Main.c2bJTestCost_qpb, ``GraphIso.Growth.Main.q2bCost_qpb,
    ``GraphIso.Growth.Case2b.pairsCost_qpb, ``GraphIso.Growth.Main.cjPairCost_qpb,
    ``GraphIso.Growth.Main.cjTupleCost_qpb, ``GraphIso.Growth.Main.cjAllCost_qpb,
    ``GraphIso.Growth.Case2b.c2bR_qpb, ``GraphIso.Growth.Main.c2bCJCost_qpb,
    ``GraphIso.Growth.Case2b.tupleCost_qpb, ``GraphIso.Growth.Case2b.allCost_qpb,
    ``GraphIso.Growth.Case2b.c2bCost_qpb, ``GraphIso.Growth.Main.m5DispNumNs_qpb,
    ``GraphIso.Growth.Sims.memCost_qpb, ``GraphIso.Growth.Main.c2bRj_qpb,
    ``GraphIso.Growth.Sims.repsVisitCost_qpb, ``GraphIso.Growth.Sims.repsCost_qpb,
    ``GraphIso.Growth.Main.ssBg1J_qpb, ``GraphIso.Growth.Main.m5DispPt_qpb,
    ``GraphIso.Growth.Main.cjB_qpb, ``GraphIso.Growth.Main.olB_qpb,
    ``GraphIso.Growth.Main.m5WorkUB_qpb, ``GraphIso.Growth.Main.ssLgM5Ns_qpb,
    ``GraphIso.Growth.Main.m5FBns_qpb, ``GraphIso.Growth.Main.c3Count_qpb,
    ``GraphIso.Growth.Main.sGQ_qpb, ``GraphIso.Growth.Main.kerRedCost_qpb,
    ``GraphIso.Growth.Main.m3WorkSS_qpb, ``GraphIso.Growth.SoJProg.clogCost_qpb,
    ``GraphIso.Growth.Main.qpL_qpb, ``GraphIso.Growth.Main.cTQP_qpb, ``GraphIso.Growth.id_qpb,
    ``GraphIso.Growth.lt_two_pow_lam, ``GraphIso.Growth.qpL_le, ``GraphIso.Growth.kQP_le,
    ``GraphIso.Growth.ℓQP_le, ``GraphIso.Growth.jMaxQ_le, ``GraphIso.Growth.lam_plb,
    ``GraphIso.Growth.qpL_plb, ``GraphIso.Growth.kQP_plb, ``GraphIso.Growth.ℓQP_plb,
    ``GraphIso.Growth.mLQ_plb, ``GraphIso.Growth.uMaxQ_plb, ``GraphIso.Growth.jMaxQ_plb,
    ``GraphIso.Growth.m3_sub_plb, ``GraphIso.Growth.Main.qpTest_qpb,
    ``GraphIso.Growth.Main.qpM4_qpb, ``GraphIso.Growth.Main.qpM5_qpb,
    ``GraphIso.Growth.Main.qpCases_qpb, ``GraphIso.Growth.Main.qpWork_qpb,
    ``GraphIso.Growth.Main.qpFac_qpb, ``GraphIso.Growth.Main.QQP_qpb, ``GraphIso.Main.QQP_le_exp,
    ``GraphIso.Main.qp_exponent_le, ``GraphIso.Main.qp_closed_le, ``GraphIso.Main.mainSolve_qp_exp,
    ``GraphIsoChecks.QPBound.sq_le_two_pow, ``GraphIsoChecks.QPBound.not_qpb_two_pow,
    ``GraphIsoChecks.QPBound.not_qpb_pow_self, ``GraphIsoChecks.QPBound.not_qpb_self_pow,
    -- 14j-6c-3: the graph-isomorphism entry (`GraphIso.Main.GraphEntry`, `GraphEntryProg`,
    -- `GraphQP`) and its checks (`GraphIsoChecks.GraphQP`)
    ``GraphIso.Main.gN, ``GraphIso.Main.ptEquiv, ``GraphIso.Main.ptEquiv_inl,
    ``GraphIso.Main.ptEquiv_inr, ``GraphIso.Main.liftPerm, ``GraphIso.Main.liftPerm_apply,
    ``GraphIso.Main.liftPerm_inl, ``GraphIso.Main.liftPerm_inr, ``GraphIso.Main.liftPerm_injective,
    ``GraphIso.Main.liftFun, ``GraphIso.Main.div_mod_pair, ``GraphIso.Main.pt_cases,
    ``GraphIso.Main.liftFun_pair, ``GraphIso.Main.val_liftPerm, ``GraphIso.Main.mem_foldl_prepend,
    ``GraphIso.Main.offArr, ``GraphIso.Main.get_offArr, ``GraphIso.Main.size_replicate_writes,
    ``GraphIso.Main.liftRow, ``GraphIso.Main.liftWrites, ``GraphIso.Main.liftArr,
    ``GraphIso.Main.size_liftArr, ``GraphIso.Main.liftData, ``GraphIso.Main.get_liftArr,
    ``GraphIso.Main.liftData_eq, ``GraphIso.Main.valid_liftData, ``GraphIso.Main.denote_liftData,
    ``GraphIso.Main.strWrites, ``GraphIso.Main.gStr, ``GraphIso.Main.mem_strWrites,
    ``GraphIso.Main.get_gStr, ``GraphIso.Main.gStr_inl, ``GraphIso.Main.gStr_inr,
    ``GraphIso.Main.rotF, ``GraphIso.Main.rotI, ``GraphIso.Main.swF, ``GraphIso.Main.size_rotF,
    ``GraphIso.Main.size_rotI, ``GraphIso.Main.size_swF, ``GraphIso.Main.get_range_toArray,
    ``GraphIso.Main.get_write_one, ``GraphIso.Main.get_rotF, ``GraphIso.Main.get_rotI,
    ``GraphIso.Main.get_swF, ``GraphIso.Main.rot_eq, ``GraphIso.Main.sw_eq,
    ``GraphIso.Main.gensData, ``GraphIso.Main.gensData_valid, ``GraphIso.Main.gensData_denote,
    ``GraphIso.Main.iso_graph, ``GraphIso.Main.restrictArr, ``GraphIso.Main.restrictData,
    ``GraphIso.Main.get_restrictArr, ``GraphIso.Main.restrict_lift, ``GraphIso.Main.decodeAns,
    ``GraphIso.Main.GICosetOK, ``GraphIso.Main.coset_pullback, ``GraphIso.Main.decode_ok,
    ``GraphIso.Main.offElemProg, ``GraphIso.Main.offProg, ``GraphIso.Main.liftElemProg,
    ``GraphIso.Main.liftStepProg, ``GraphIso.Main.liftArrProg, ``GraphIso.Main.liftDataProg,
    ``GraphIso.Main.strElemProg, ``GraphIso.Main.strStepProg, ``GraphIso.Main.strProg,
    ``GraphIso.Main.succProg, ``GraphIso.Main.predProg, ``GraphIso.Main.rotFProg,
    ``GraphIso.Main.rotIProg, ``GraphIso.Main.swFProg, ``GraphIso.Main.gensProg,
    ``GraphIso.Main.restrictArrProg, ``GraphIso.Main.restrictProg, ``GraphIso.Main.Ty.giCoset,
    ``GraphIso.Main.decodeProg, ``GraphIso.Main.giEntry, ``GraphIso.Main.giEntry_wf,
    ``GraphIso.Main.offCost, ``GraphIso.Main.RunsWithin.offElemProg,
    ``GraphIso.Main.RunsWithin.offProg, ``GraphIso.Main.length_foldl_prepend,
    ``GraphIso.Main.liftArrCost, ``GraphIso.Main.RunsWithin.liftElemProg,
    ``GraphIso.Main.RunsWithin.liftStepProg, ``GraphIso.Main.RunsWithin.liftArrProg,
    ``GraphIso.Main.liftDataCost, ``GraphIso.Main.RunsWithin.liftDataProg, ``GraphIso.Main.strCost,
    ``GraphIso.Main.RunsWithin.strElemProg, ``GraphIso.Main.RunsWithin.strStepProg,
    ``GraphIso.Main.RunsWithin.strProg, ``GraphIso.Main.RunsWithin.succProg,
    ``GraphIso.Main.RunsWithin.predProg, ``GraphIso.Main.vtxCost,
    ``GraphIso.Main.RunsWithin.rotFProg, ``GraphIso.Main.RunsWithin.rotIProg,
    ``GraphIso.Main.RunsWithin.swFProg, ``GraphIso.Main.gensCost,
    ``GraphIso.Main.RunsWithin.gensProg, ``GraphIso.Main.RunsWithin.restrictArrProg,
    ``GraphIso.Main.RunsWithin.restrictProg, ``GraphIso.Main.decCost,
    ``GraphIso.Main.RunsWithin.decodeProg, ``GraphIso.Main.giInst, ``GraphIso.Main.encCost,
    ``GraphIso.Main.giEntry_runs, ``GraphIso.Main.entryI, ``GraphIso.Main.entry_hinst,
    ``GraphIso.Main.entry_ok, ``GraphIso.Main.mainEntry_of_body, ``GraphIso.Main.mainSolve_ss_gens,
    ``GraphIso.Main.mainSolve_qp_gens, ``GraphIso.Main.mainSolve_qp_exp_gens,
    ``GraphIso.Main.mainSolver, ``GraphIso.Main.qpSolver, ``GraphIso.Main.giCostSS,
    ``GraphIso.Main.giInst_valid, ``GraphIso.Main.gi_close, ``GraphIso.Main.giSolve_ss,
    ``GraphIso.Main.lam_gN_le, ``GraphIso.Main.gi_poly_le, ``GraphIso.Main.gi_cost_le,
    ``GraphIso.Main.giSolve_qp_exp, ``GraphIso.Main.isIso_ofSimpleGraph_iff,
    ``GraphIso.Main.gi_qp_simpleGraph, ``GraphIsoChecks.GraphQP.p3c1, ``GraphIsoChecks.GraphQP.p3c0,
    ``GraphIsoChecks.GraphQP.p3c2, ``GraphIsoChecks.GraphQP.k3, ``GraphIsoChecks.GraphQP.k2,
    ``GraphIsoChecks.GraphQP.e2, ``GraphIsoChecks.GraphQP.mulL, ``GraphIsoChecks.GraphQP.closeStep,
    ``GraphIsoChecks.GraphQP.closureL, ``GraphIsoChecks.GraphQP.insAll,
    ``GraphIsoChecks.GraphQP.perms, ``GraphIsoChecks.GraphQP.isosB,
    ``GraphIsoChecks.GraphQP.cosetOK, ``GraphIsoChecks.GraphQP.gBody, ``GraphIsoChecks.GraphQP.noF,
    ``GraphIsoChecks.GraphQP.cfgG, ``GraphIsoChecks.GraphQP.giP, ``GraphIsoChecks.GraphQP.gi_k2k2,
    ``GraphIsoChecks.GraphQP.gi_k2e2, ``GraphIsoChecks.GraphQP.gi_e2e2,
    ``GraphIsoChecks.GraphQP.gi_p3p3, ``GraphIsoChecks.GraphQP.gi_p3k3,
    ``GraphIsoChecks.GraphQP.gi_k3k3, ``GraphIsoChecks.GraphQP.swapInst,
    ``GraphIsoChecks.GraphQP.swapP, ``GraphIsoChecks.GraphQP.gi_swap,
    -- 15a: abelian composition factors (`GraphIso.Pyber.CompA`, `Families`, `Residual`,
    -- `Generators`) and their checks (`GraphIsoChecks.Pyber`)
    ``GraphIso.Pyber.compA, ``GraphIso.Pyber.card_primeFactors_le_log,
    ``GraphIso.Pyber.compA_subset_primeFactors, ``GraphIso.Pyber.compA_finite,
    ``GraphIso.Pyber.ncard_compA_le_card_primeFactors, ``GraphIso.Pyber.ncard_compA_le,
    ``GraphIso.Pyber.compA_eq_empty_of_subsingleton, ``GraphIso.Pyber.normal_comap_pair,
    ``GraphIso.Pyber.normal_map_pair, ``GraphIso.Pyber.compA_subset_of_surjective,
    ``GraphIso.Pyber.compA_eq_of_mulEquiv, ``GraphIso.Pyber.isSubnormal_map_of_range,
    ``GraphIso.Pyber.compA_subset_of_injective, ``GraphIso.Pyber.compA_subset_of_isSubnormal,
    ``GraphIso.Pyber.compA_range_subset, ``GraphIso.Pyber.mem_compA_of_index,
    ``GraphIso.Pyber.mem_compA_of_comm, ``GraphIso.Pyber.compA_eq_empty_of_isSimpleGroup,
    ``GraphIso.Pyber.relIndex_ne_zero_of_finite, ``GraphIso.Pyber.relIndex_eq_mul_relIndex,
    ``GraphIso.Pyber.relIndex_subgroupOf_eq, ``GraphIso.Pyber.compA_subset_union,
    ``GraphIso.Pyber.compA_subset_union_of_hom, ``GraphIso.Pyber.compA_quot_subset_of_hom,
    ``GraphIso.Pyber.relIndex_dvd_index_of_normal_right,
    ``GraphIso.Pyber.relIndex_dvd_index_of_isSubnormal, ``GraphIso.Pyber.compA_sdiff_subset,
    ``GraphIso.Pyber.compA_eq_empty_of_top_eq_bot, ``GraphIso.Pyber.compA_subset_biUnion_of_ker,
    ``GraphIso.Pyber.compA_subset_iUnion_of_iInf, ``GraphIso.Pyber.compA_sup_subset,
    ``GraphIso.Pyber.compA_biSup_subset, ``GraphIso.Pyber.compA_subset_iUnion_of_iSup,
    ``GraphIso.Pyber.isSolvable_of_mulEquiv, ``GraphIso.Pyber.isSolvable_sup,
    ``GraphIso.Pyber.isSolvable_biSup, ``GraphIso.Pyber.CharSimple, ``GraphIso.Pyber.IsMinNormal,
    ``GraphIso.Pyber.exists_isMinNormal, ``GraphIso.Pyber.IsMinNormal.charSimple,
    ``GraphIso.Pyber.comm_of_mem, ``GraphIso.Pyber.finite_mulAut,
    ``GraphIso.Pyber.iSup_map_mulAut_eq_top, ``GraphIso.Pyber.comm_of_commutator_eq_bot,
    ``GraphIso.Pyber.compA_eq_empty_of_charSimple_aux,
    ``GraphIso.Pyber.compA_eq_empty_of_charSimple, ``GraphIso.Pyber.SChain,
    ``GraphIso.Pyber.SChain.le, ``GraphIso.Pyber.SChain.trans, ``GraphIso.Pyber.SChain.isSubnormal,
    ``GraphIso.Pyber.normal_inf_pair, ``GraphIso.Pyber.compA_inf_section_subset,
    ``GraphIso.Pyber.SChain.inf_left, ``GraphIso.Pyber.SChain.inf, ``GraphIso.Pyber.resid,
    ``GraphIso.Pyber.resid_le_of_schain, ``GraphIso.Pyber.schain_resid, ``GraphIso.Pyber.SChain.map,
    ``GraphIso.Pyber.resid_map, ``GraphIso.Pyber.mem_normalizer_resid,
    ``GraphIso.Pyber.resid_eq_of_step, ``GraphIso.Pyber.compA_subset_of_schain,
    ``GraphIso.Pyber.compA_subset_of_resid_eq_bot, ``GraphIso.Pyber.exists_list_closure_sup_eq_top,
    ``GraphIso.Pyber.exists_list_closure_eq_top, ``GraphIsoChecks.Pyber.card_perm3,
    ``GraphIsoChecks.Pyber.card_alt3, ``GraphIsoChecks.Pyber.card_alt5,
    ``GraphIsoChecks.Pyber.mem_compA_of_card, ``GraphIsoChecks.Pyber.two_mem_compA_perm3,
    ``GraphIsoChecks.Pyber.three_mem_compA_alt3, ``GraphIsoChecks.Pyber.three_mem_compA_perm3,
    ``GraphIsoChecks.Pyber.compA_perm3, ``GraphIsoChecks.Pyber.alt5_noncomm,
    ``GraphIsoChecks.Pyber.compA_alt5, ``GraphIsoChecks.Pyber.compA_section_perm3,
    -- 15b: permutation groups and the odd-order bound (`GraphIso.Pyber.Bridge`, `Orbital`,
    -- `OddOrder`) and their checks (`GraphIsoChecks.PyberPerm`)
    ``GraphIso.Pyber.mem_normalCore_iff, ``GraphIso.Pyber.Faithful,
    ``GraphIso.Pyber.normalCore_stabilizer_eq_bot, ``GraphIso.Pyber.faithful_perm,
    ``GraphIso.Pyber.isPretransitive_range, ``GraphIso.Pyber.faithful_quotient,
    ``GraphIso.Pyber.nontrivial_quotient, ``GraphIso.Pyber.isPreprimitive_quotient,
    ``GraphIso.Pyber.normalCore_map_mk, ``GraphIso.Pyber.index_map_mk,
    ``GraphIso.Pyber.primeFactors_card_subset, ``GraphIso.Pyber.compA_subset_compA_quot,
    ``GraphIso.Pyber.sup_eq_of_covBy, ``GraphIso.Pyber.relIndex_eq_of_sup_eq,
    ``GraphIso.Pyber.exists_covBy_ne_top, ``GraphIso.Pyber.smul_mem_orbit_pair,
    ``GraphIso.Pyber.mem_orbit_stabilizer_iff, ``GraphIso.Pyber.diag_notMem_orbit,
    ``GraphIso.Pyber.ncard_orbit_stabilizer, ``GraphIso.Pyber.relIndex_comm_of_index_eq,
    ``GraphIso.Pyber.ncard_paired_eq, ``GraphIso.Pyber.swap_notMem_orbit,
    ``GraphIso.Pyber.two_mul_ncard_suborbit_add_one_le, ``GraphIso.Pyber.swap_mem_orbit_of_mul_self,
    ``GraphIso.Pyber.eq_univ_of_closed, ``GraphIso.Pyber.prime_dvd_card_range,
    ``GraphIso.Pyber.two_mul_tri, ``GraphIso.Pyber.tri_add_le, ``GraphIso.Pyber.tri_mono,
    ``GraphIso.Pyber.add_tri_le, ``GraphIso.Pyber.log_add_log_le, ``GraphIso.Pyber.log_add_one_le,
    ``GraphIso.Pyber.card_primeFactors_mul_le, ``GraphIso.Pyber.card_primeFactors_le_of_odd_aux,
    ``GraphIso.Pyber.card_primeFactors_le_of_odd,
    ``GraphIso.Pyber.card_primeFactors_le_of_odd_action, ``GraphIsoChecks.PyberPerm.faithful_perm3,
    ``GraphIsoChecks.PyberPerm.selfPaired_perm3, ``GraphIsoChecks.PyberPerm.suborbit_perm3,
    ``GraphIsoChecks.PyberPerm.ncard_suborbit_perm3,
    ``GraphIsoChecks.PyberPerm.card_stabilizer_perm3,
    ``GraphIsoChecks.PyberPerm.isPretransitive_alt3, ``GraphIsoChecks.PyberPerm.odd_alt3,
    ``GraphIsoChecks.PyberPerm.rot_add_two, ``GraphIsoChecks.PyberPerm.isPretransitive_rot4,
    -- 15c: Theorem 7 (`GraphIso.Pyber.Wielandt`, `MinNormal`, `Imprimitive`, `Theorem7`) and its
    -- checks (`GraphIsoChecks.PyberThm7`)
    ``GraphIso.Pyber.suborbitKer, ``GraphIso.Pyber.mem_suborbitKer, ``GraphIso.Pyber.suborbitKer_le,
    ``GraphIso.Pyber.suborbitKer_normal, ``GraphIso.Pyber.suborbitKer_normal_self,
    ``GraphIso.Pyber.suborbitKer_smul, ``GraphIso.Pyber.stabilizer_inf_smul,
    ``GraphIso.Pyber.resid_eq_of_schain, ``GraphIso.Pyber.compA_suborbitKer_subset,
    ``GraphIso.Pyber.ker_toPermHom_suborbit, ``GraphIso.Pyber.compA_stabilizer_subset,
    ``GraphIso.Pyber.isPretransitive_of_normal, ``GraphIso.Pyber.stabilizer_eq_bot_of_comm,
    ``GraphIso.Pyber.card_eq_of_comm, ``GraphIso.Pyber.conj_injective,
    ``GraphIso.Pyber.card_le_of_comm, ``GraphIso.Pyber.compA_subset_of_noncomm,
    ``GraphIso.Pyber.card_le_or_compA_subset, ``GraphIso.Pyber.compA_subset_union_core,
    ``GraphIso.Pyber.compA_subgroupOf_comm, ``GraphIso.Pyber.exists_ncard_compA_le,
    ``GraphIso.Pyber.tri_le_F, ``GraphIso.Pyber.F_mono, ``GraphIso.Pyber.F_add_le,
    ``GraphIso.Pyber.F_add_add_le, ``GraphIso.Pyber.log_pow_lt, ``GraphIso.Pyber.log_pow_le_F,
    ``GraphIso.Pyber.ncard_suborbit_lt, ``GraphIso.Pyber.ncard_compA_le_of_coreFree_aux,
    ``GraphIso.Pyber.ncard_compA_le_of_coreFree, ``GraphIso.Pyber.ncard_compA_stabilizer_le,
    ``GraphIso.Pyber.ncard_compA_le_of_transitive, ``GraphIsoChecks.PyberThm7.faithful_perm4,
    ``GraphIsoChecks.PyberThm7.isPreprimitive_alt3, ``GraphIsoChecks.PyberThm7.nontrivial_alt3,
    -- 15d: Lemma 12 and the discharge (`GraphIso.Pyber.Primes`, `Lemma12`, `Discharge`) and its
    -- checks (`GraphIsoChecks.PyberLemma12`)
    ``GraphIso.Pyber.lcmUpto_le_pow, ``GraphIso.Pyber.two_pow_le_mul_pow_card,
    ``GraphIso.Pyber.card_primesLE_ge, ``GraphIso.Pyber.exists_odd_primes,
    ``GraphIso.Pyber.exists_mem_alternatingGroup, ``GraphIso.Pyber.Kpy, ``GraphIso.Pyber.Kpy_mono,
    ``GraphIso.Pyber.lemma12_arith, ``GraphIso.Pyber.injective_of_surjective_alt,
    ``GraphIso.Pyber.altQuotientIso_pyber, ``GraphIso.Pyber.Kpy_le_lam,
    ``GraphIso.Pyber.qpHyp_pyber, ``GraphIso.Pyber.mainSolve_qp_exp_pyber,
    ``GraphIso.Pyber.giSolve_qp_exp_pyber, ``GraphIso.Pyber.gi_qp_simpleGraph_pyber,
    ``GraphIsoChecks.PyberLemma12.card_primesLE_64, ``GraphIsoChecks.PyberLemma12.subsingleton_alt2,
    -- kernel-checked executions, proved in pieces (`GraphIsoChecks.Exec`)
    ``GraphIsoChecks.Exec.runsS_of_check, ``GraphIsoChecks.ExecSteps.flatMap_recF,
    ``GraphIsoChecks.MainM4.m4_step_agl_tr, ``GraphIsoChecks.MainM4.m4_step_c5_tr,
    ``GraphIsoChecks.MainM5.disp_case1, ``GraphIsoChecks.MainM5.disp_differ,
    ``GraphIsoChecks.MainM5.disp_case2a, ``GraphIsoChecks.MainM5.cert_xA,
    ``GraphIsoChecks.MainM5.cert_yA, ``GraphIsoChecks.MainM5.cert_xB,
    ``GraphIsoChecks.MainM5.cert_yB, ``GraphIsoChecks.MainM5.step_iso,
    ``GraphIsoChecks.MainM5.step_noniso, ``GraphIsoChecks.MainM5b.c3_iso,
    ``GraphIsoChecks.MainM5b.c3_noniso, ``GraphIsoChecks.MainM5b.c3_fallback,
    ``GraphIsoChecks.MainM5b.c2b_klein, ``GraphIsoChecks.MainM5b.cert_x5,
    ``GraphIsoChecks.MainM5b.cert_y5, ``GraphIsoChecks.MainM5b.step5]
  let mut lines : Array MessageData := #[]
  for name in principal do
    let axs ← collectAxioms name
    lines := lines.push m!"{name}: {axs.toList}"
  logInfo (MessageData.joinSep lines.toList "\n")

/-! The list continues in the next block. -/

open Lean in
run_cmd do
  let principal := #[
    -- 16a: the transitivity bound (`GraphIso.Wielandt.Commutator`, `Support`, `Power`, `Bound`)
    -- and its checks (`GraphIsoChecks.WielandtBound`)
    ``GraphIso.Wielandt.support_commutatorElement_subset,
    ``GraphIso.Wielandt.card_support_commutatorElement_le,
    ``GraphIso.Wielandt.sign_commutatorElement, ``GraphIso.Wielandt.isThreeCycle_commutatorElement,
    ``GraphIso.Wielandt.ite_eq_of_pos, ``GraphIso.Wielandt.ite_eq_of_neg, ``GraphIso.Wielandt.emb3,
    ``GraphIso.Wielandt.exists_mem_map3, ``GraphIso.Wielandt.card_inter_map_eq,
    ``GraphIso.Wielandt.exists_mem_card_inter_le, ``GraphIso.Wielandt.three_mul_lt,
    ``GraphIso.Wielandt.exists_isThreeCycle_mem,
    ``GraphIso.Wielandt.alternatingGroup_le_of_support_le,
    ``GraphIso.Wielandt.prod_dvd_of_pairwise_coprime,
    ``GraphIso.Wielandt.ordProj_dvd_of_not_dvd_div, ``GraphIso.Wielandt.exists_pow_support_lt,
    ``GraphIso.Wielandt.lcmCycles, ``GraphIso.Wielandt.card_primesLE_le,
    ``GraphIso.Wielandt.sum_lcmCycles_le, ``GraphIso.Wielandt.two_le_of_mem_lcmCycles,
    ``GraphIso.Wielandt.exists_perm_lcmUpto_dvd, ``GraphIso.Wielandt.exists_mem_orderOf_dvd,
    ``GraphIso.Wielandt.seven_mul_add_le, ``GraphIso.Wielandt.Tq,
    ``GraphIso.Wielandt.transitivityBound_quad, ``GraphIsoChecks.WielandtBound.inter_card_cycles,
    ``GraphIsoChecks.WielandtBound.commutator_cycles_ne_one, ``GraphIsoChecks.WielandtBound.σ10,
    ``GraphIsoChecks.WielandtBound.orderOf_σ10,
    ``GraphIsoChecks.WielandtBound.not_alternatingGroup_le_rot4,
    ``GraphIsoChecks.WielandtBound.not_transitivityBound_zero,
    -- 16b: the unconditional theorems (`GraphIso.Main.QPJ`, `GraphIso.Wielandt.Final`) and their
    -- checks (`GraphIsoChecks.WielandtFinal`)
    ``GraphIso.Main.QPHypJ, ``GraphIso.Main.QPHyp.toJ, ``GraphIso.Main.thresholds_qpJ,
    ``GraphIso.Main.sharpHyp_qpJ, ``GraphIso.Main.qpM4J, ``GraphIso.Main.qpM5J,
    ``GraphIso.Main.qpCasesJ, ``GraphIso.Main.qpWorkJ, ``GraphIso.Main.qpFacJ, ``GraphIso.Main.QQPJ,
    ``GraphIso.Main.QQP_eq_QQPJ, ``GraphIso.Main.caseWorkS_le_qpCasesJ,
    ``GraphIso.Main.mainWorkS_le_QQPJ, ``GraphIso.Main.caseFAB_le_QQPJ,
    ``GraphIso.Main.winSize_add_two_le_QQPJ, ``GraphIso.Main.pot_ind_stepJ,
    ``GraphIso.Main.main_potJ, ``GraphIso.Main.mainSolve_qpJ, ``GraphIso.Main.mainSolve_qp_closedJ,
    ``GraphIso.Growth.Main.qpM4J_qpb, ``GraphIso.Growth.Main.qpM5J_qpb,
    ``GraphIso.Growth.Main.qpCasesJ_qpb, ``GraphIso.Growth.Main.qpWorkJ_qpb,
    ``GraphIso.Growth.Main.qpFacJ_qpb, ``GraphIso.Growth.Main.QQPJ_qpb, ``GraphIso.Main.QQPJ_le_exp,
    ``GraphIso.Main.mainSolve_qp_expJ, ``GraphIso.Main.mainSolve_qp_gensJ,
    ``GraphIso.Main.mainSolve_qp_exp_gensJ, ``GraphIso.Main.giSolve_qp_expJ,
    ``GraphIso.Main.gi_qp_simpleGraphJ, ``GraphIso.Wielandt.Tq_mono,
    ``GraphIso.Wielandt.supTo_Tq_le, ``GraphIso.Wielandt.sq_le_two_pow,
    ``GraphIso.Wielandt.tBelow_Tq, ``GraphIso.Wielandt.jq, ``GraphIso.Wielandt.jq_plb,
    ``GraphIso.Wielandt.qpHypJ_final, ``GraphIso.Wielandt.mainSolve_final,
    ``GraphIso.Wielandt.giSolve_final, ``GraphIso.Wielandt.gi_simpleGraph_final,
    ``GraphIsoChecks.WielandtFinal.not_tle_Tq, ``GraphIsoChecks.WielandtFinal.not_qpHyp_Tq,
    -- 17a: stack programs and Turing machines (`GraphIso.TM.Code`, `Machine`) and their checks
    -- (`GraphIsoChecks.TMCode`)
    ``GraphIso.TM.Regs, ``GraphIso.TM.Regs.empty, ``GraphIso.TM.Act, ``GraphIso.TM.Cond,
    ``GraphIso.TM.Code, ``GraphIso.TM.Cfg, ``GraphIso.TM.Program, ``GraphIso.TM.Act.run,
    ``GraphIso.TM.Cond.eval, ``GraphIso.TM.Exec, ``GraphIso.TM.run, ``GraphIso.TM.Exec.one_le,
    ``GraphIso.TM.run_of_exec, ``GraphIso.TM.Exec.det, ``GraphIso.TM.exec_of_run, ``GraphIso.TM.Lab,
    ``GraphIso.TM.reach, ``GraphIso.TM.mem_reach_self, ``GraphIso.TM.Succ, ``GraphIso.TM.reach_succ,
    ``GraphIso.TM.reach_tail, ``GraphIso.TM.labs, ``GraphIso.TM.nil_mem_labs,
    ``GraphIso.TM.body_mem_labs, ``GraphIso.TM.labs_succ, ``GraphIso.TM.labs_tail,
    ``GraphIso.TM.Label, ``GraphIso.TM.MΓ, ``GraphIso.TM.mainLab, ``GraphIso.TM.MState,
    ``GraphIso.TM.MStmt,
    ``GraphIso.TM.actStmt, ``GraphIso.TM.stmt, ``GraphIso.TM.mach, ``GraphIso.TM.embedStk,
    ``GraphIso.TM.mcfg, ``GraphIso.TM.toFinTM2, ``GraphIso.TM.embedStk_update_some,
    ``GraphIso.TM.embedStk_update_none, ``GraphIso.TM.stepAux_actStmt, ``GraphIso.TM.iter_succ,
    ``GraphIso.TM.iter_add, ``GraphIso.TM.sim, ``GraphIso.TM.halts, ``GraphIso.TM.inStk,
    ``GraphIso.TM.inCfg, ``GraphIso.TM.initList_eq, ``GraphIso.TM.haltList_eq,
    ``GraphIso.TM.outputsInTime, ``GraphIso.TM.stepsOf, ``GraphIso.TM.stepsOf_eq,
    ``GraphIso.TM.computableInTime, ``GraphIsoChecks.TMCode.st, ``GraphIsoChecks.TMCode.negElse,
    ``GraphIsoChecks.TMCode.negBody, ``GraphIsoChecks.TMCode.negProg, ``GraphIsoChecks.TMCode.upd0,
    ``GraphIsoChecks.TMCode.upd1, ``GraphIsoChecks.TMCode.upd2, ``GraphIsoChecks.TMCode.updR,
    ``GraphIsoChecks.TMCode.negBody_exec, ``GraphIsoChecks.TMCode.inStk_zero,
    ``GraphIsoChecks.TMCode.inStk_two, ``GraphIsoChecks.TMCode.main_exec,
    ``GraphIsoChecks.TMCode.negTM, ``GraphIsoChecks.TMCode.negM, ``GraphIsoChecks.TMCode.stkOf,
    ``GraphIsoChecks.TMCode.regOf, ``GraphIsoChecks.TMCode.after,
    ``GraphIsoChecks.TMCode.running_lt_33, ``GraphIsoChecks.TMCode.not_outputs_32,
    ``GraphIsoChecks.TMCode.st0, ``GraphIsoChecks.TMCode.st1, ``GraphIsoChecks.TMCode.st2,
    -- 17b: numbers and arithmetic on stacks (`GraphIso.TM.Sat`, `Bits`, `Num`, `Arith`) and their
    -- checks (`GraphIsoChecks.TMArith`)
    ``GraphIso.TM.Sat, ``GraphIso.TM.Sat.exec, ``GraphIso.TM.Sat.mono, ``GraphIso.TM.Sat.act,
    ``GraphIso.TM.Sat.skip, ``GraphIso.TM.Sat.seq, ``GraphIso.TM.Sat.seq_le,
    ``GraphIso.TM.Sat.act_le, ``GraphIso.TM.Sat.act_seq, ``GraphIso.TM.Sat.ite_true,
    ``GraphIso.TM.Sat.ite_false, ``GraphIso.TM.Sat.ite, ``GraphIso.TM.Sat.ite_true_le,
    ``GraphIso.TM.Sat.ite_false_le, ``GraphIso.TM.Sat.call, ``GraphIso.TM.Sat.loop,
    ``GraphIso.TM.Tag, ``GraphIso.TM.Sym, ``GraphIso.TM.ofBits, ``GraphIso.TM.ofBits_nil,
    ``GraphIso.TM.ofBits_cons, ``GraphIso.TM.ofBits_append, ``GraphIso.TM.ofBits_lt,
    ``GraphIso.TM.hd, ``GraphIso.TM.tl, ``GraphIso.TM.hd_nil, ``GraphIso.TM.hd_cons,
    ``GraphIso.TM.ofBits_hd_tl, ``GraphIso.TM.zipL, ``GraphIso.TM.zipL_nil, ``GraphIso.TM.zipL_step,
    ``GraphIso.TM.length_zipL, ``GraphIso.TM.fullAdd, ``GraphIso.TM.fullSub, ``GraphIso.TM.diffBit,
    ``GraphIso.TM.zipL_add, ``GraphIso.TM.zipL_sub, ``GraphIso.TM.zipL_sub_borrow,
    ``GraphIso.TM.zipL_sub_val, ``GraphIso.TM.zipL_add_val, ``GraphIso.TM.zipL_diff,
    ``GraphIso.TM.addBits, ``GraphIso.TM.ofBits_addBits, ``GraphIso.TM.length_addBits,
    ``GraphIso.TM.subBits, ``GraphIso.TM.ofBits_subBits, ``GraphIso.TM.length_subBits_le,
    ``GraphIso.TM.zipL_sub_lt, ``GraphIso.TM.zipL_diff_false, ``GraphIso.TM.Rg, ``GraphIso.TM.bits,
    ``GraphIso.TM.bits_nil, ``GraphIso.TM.bits_cons, ``GraphIso.TM.bits_append,
    ``GraphIso.TM.length_bits, ``GraphIso.TM.rv, ``GraphIso.TM.rv_zero, ``GraphIso.TM.rv_one,
    ``GraphIso.TM.rv_two, ``GraphIso.TM.rv_three, ``GraphIso.TM.update_rv_zero,
    ``GraphIso.TM.update_rv_one, ``GraphIso.TM.update_rv_two, ``GraphIso.TM.update_rv_three,
    ``GraphIso.TM.empty_eq_rv, ``GraphIso.TM.Cond.or, ``GraphIso.TM.Cond.or_eval,
    ``GraphIso.TM.isBit, ``GraphIso.TM.isBit_eval_bit, ``GraphIso.TM.isBit_eval_nd,
    ``GraphIso.TM.moveBits, ``GraphIso.TM.moveBits_sat, ``GraphIso.TM.moveBits2,
    ``GraphIso.TM.moveBits2_sat, ``GraphIso.TM.copyNum, ``GraphIso.TM.copyNum_sat,
    ``GraphIso.TM.dropNum, ``GraphIso.TM.exists_cons_bits, ``GraphIso.TM.dropNum_sat,
    ``GraphIso.TM.pushNum, ``GraphIso.TM.pushNum_sat, ``GraphIso.TM.moveSeg,
    ``GraphIso.TM.eq_last_iff, ``GraphIso.TM.moveSeg_sat, ``GraphIso.TM.dropSeg,
    ``GraphIso.TM.dropSeg_sat, ``GraphIso.TM.erase, ``GraphIso.TM.erase_sat, ``GraphIso.TM.readBit,
    ``GraphIso.TM.readBit_sat, ``GraphIso.TM.bitCase, ``GraphIso.TM.bitCase_sat,
    ``GraphIso.TM.zipTable, ``GraphIso.TM.zipTable_sat, ``GraphIso.TM.zipBody, ``GraphIso.TM.zipNum,
    ``GraphIso.TM.isBit_eval_head, ``GraphIso.TM.zipNum_sat, ``GraphIso.TM.addNum,
    ``GraphIso.TM.addNum_sat, ``GraphIso.TM.subNum, ``GraphIso.TM.subNum_sat, ``GraphIso.TM.ltNum,
    ``GraphIso.TM.ltNum_sat, ``GraphIso.TM.eqNum, ``GraphIso.TM.eqNum_sat, ``GraphIso.TM.incNum,
    ``GraphIso.TM.incNum_sat, ``GraphIso.TM.decNum, ``GraphIso.TM.decNum_sat,
    ``GraphIsoChecks.TMArith.prog1, ``GraphIsoChecks.TMArith.cfg, ``GraphIsoChecks.TMArith.num,
    ``GraphIsoChecks.TMArith.go, ``GraphIsoChecks.TMArith.none4, ``GraphIsoChecks.TMArith.cAdd,
    ``GraphIsoChecks.TMArith.add_spec, ``GraphIsoChecks.TMArith.eq_spec,
    ``GraphIsoChecks.TMArith.add_not_128,
    -- 17c: the heap (`GraphIso.TM.Heap`, `Lookup`, `Alloc`, `Rep`) and its checks
    -- (`GraphIsoChecks.TMHeap`)
    ``GraphIso.TM.Stk, ``GraphIso.TM.moveSeg2, ``GraphIso.TM.moveSeg2_sat, ``GraphIso.TM.Cell,
    ``GraphIso.TM.encFields, ``GraphIso.TM.cellBody, ``GraphIso.TM.encCell, ``GraphIso.TM.encHeap,
    ``GraphIso.TM.encScan, ``GraphIso.TM.HeapWF, ``GraphIso.TM.mk_not_mem_bits,
    ``GraphIso.TM.mk_not_mem_encFields, ``GraphIso.TM.mk0_not_mem_cellBody,
    ``GraphIso.TM.encCell_reverse, ``GraphIso.TM.mk1_not_mem_reverse, ``GraphIso.TM.encHeap_append,
    ``GraphIso.TM.encHeap_cons, ``GraphIso.TM.encHeap_take_succ, ``GraphIso.TM.encScan_drop,
    ``GraphIso.TM.length_encHeap, ``GraphIso.TM.one_le_length_encCell,
    ``GraphIso.TM.le_sum_of_mem_nat, ``GraphIso.TM.length_encCell_le,
    ``GraphIso.TM.length_le_encHeap, ``GraphIso.TM.length_addr_lt, ``GraphIso.TM.length_cellBody,
    ``GraphIso.TM.addrTest, ``GraphIso.TM.addrTest_sat, ``GraphIso.TM.lookup,
    ``GraphIso.TM.lookupBound, ``GraphIso.TM.lookupBound_le, ``GraphIso.TM.lookup_sat,
    ``GraphIso.TM.encFields_nil, ``GraphIso.TM.encFields_cons, ``GraphIso.TM.encFields_append,
    ``GraphIso.TM.length_encFields_cons, ``GraphIso.TM.length_le_encFields,
    ``GraphIso.TM.encFields_reverse_map, ``GraphIso.TM.moveNums, ``GraphIso.TM.moveNums_sat,
    ``GraphIso.TM.length_encFields_reverse_map, ``GraphIso.TM.HeapAt, ``GraphIso.TM.alloc,
    ``GraphIso.TM.allocBound, ``GraphIso.TM.alloc_sat, ``GraphIso.TM.CellAt, ``GraphIso.TM.Rep,
    ``GraphIso.TM.CellAt.mono, ``GraphIso.TM.Rep.mono, ``GraphIso.TM.Rep.nat_inv,
    ``GraphIso.TM.Rep.lt, ``GraphIsoChecks.TMHeap.prog1, ``GraphIsoChecks.TMHeap.h₃,
    ``GraphIsoChecks.TMHeap.h₃_wf, ``GraphIsoChecks.TMHeap.cfgH, ``GraphIsoChecks.TMHeap.go,
    ``GraphIsoChecks.TMHeap.none4, ``GraphIsoChecks.TMHeap.cnt3,
    ``GraphIsoChecks.TMHeap.lookup_spec, ``GraphIsoChecks.TMHeap.alloc_spec,
    ``GraphIsoChecks.TMHeap.rep_pair, ``GraphIsoChecks.TMHeap.h₄,
    ``GraphIsoChecks.TMHeap.rep_pair_mono, ``GraphIsoChecks.TMHeap.rep_some,
    ``GraphIsoChecks.TMHeap.not_rep_pair, ``GraphIsoChecks.TMHeap.not_rep_bool,
    ``GraphIsoChecks.TMHeap.not_wf,
    -- 17d: input and output (`GraphIso.TM.Ser`, `Load`, `Write`, `Sat.loop_list`) and its checks
    -- (`GraphIsoChecks.TMIO`)
    ``GraphIso.TM.toBits, ``GraphIso.TM.ofBits_toBits, ``GraphIso.TM.length_toBits_le,
    ``GraphIso.TM.ser, ``GraphIso.TM.wt, ``GraphIso.TM.one_le_wt, ``GraphIso.TM.serElems,
    ``GraphIso.TM.serElems_cons, ``GraphIso.TM.length_serElems, ``GraphIso.TM.ser_list,
    ``GraphIso.TM.ser_array, ``GraphIso.TM.RepList, ``GraphIso.TM.RepList.mono,
    ``GraphIso.TM.readElems, ``GraphIso.TM.buildList, ``GraphIso.TM.alloc0, ``GraphIso.TM.load,
    ``GraphIso.TM.cellsB, ``GraphIso.TM.ldB, ``GraphIso.TM.HeapAt.frame, ``GraphIso.TM.LoadSpec,
    ``GraphIso.TM.readElems_sat, ``GraphIso.TM.allocBound_mono, ``GraphIso.TM.cellAt_new,
    ``GraphIso.TM.alloc0_sat, ``GraphIso.TM.load_unit, ``GraphIso.TM.load_bool,
    ``GraphIso.TM.load_nat, ``GraphIso.TM.load_prod, ``GraphIso.TM.load_option,
    ``GraphIso.TM.sum_map_const, ``GraphIso.TM.blB, ``GraphIso.TM.buildList_sat,
    ``GraphIso.TM.length_encFields_le, ``GraphIso.TM.load_list, ``GraphIso.TM.load_array,
    ``GraphIso.TM.load_sat, ``GraphIso.TM.sum_le_wt, ``GraphIso.TM.cellsB_le, ``GraphIso.TM.PL,
    ``GraphIso.TM.PL_ge, ``GraphIso.TM.length_le_sum_succ, ``GraphIso.TM.le_wtP,
    ``GraphIso.TM.le_mul_of_parts, ``GraphIso.TM.wtP_add, ``GraphIso.TM.wtP_add1,
    ``GraphIso.TM.sum_wtP, ``GraphIso.TM.ldB_le, ``GraphIso.TM.strip, ``GraphIso.TM.moveNum2,
    ``GraphIso.TM.xferNums, ``GraphIso.TM.moveNum2_sat, ``GraphIso.TM.xferNums_sat,
    ``GraphIso.TM.openCell, ``GraphIso.TM.fetchCell, ``GraphIso.TM.closeCell,
    ``GraphIso.TM.writeElems, ``GraphIso.TM.write, ``GraphIso.TM.toBits_eq_nil,
    ``GraphIso.TM.toBits_bit, ``GraphIso.TM.strip_cons_of_ne, ``GraphIso.TM.strip_cons_of_eq,
    ``GraphIso.TM.strip_eq_toBits, ``GraphIso.TM.length_strip_le, ``GraphIso.TM.openCell_sat,
    ``GraphIso.TM.closeCell_sat, ``GraphIso.TM.lookupBound_mono, ``GraphIso.TM.fcB,
    ``GraphIso.TM.fetchCell_sat, ``GraphIso.TM.Rep.unit_inv, ``GraphIso.TM.Rep.bool_inv,
    ``GraphIso.TM.Rep.pair_inv, ``GraphIso.TM.Rep.none_inv, ``GraphIso.TM.Rep.some_inv,
    ``GraphIso.TM.Rep.nil_inv, ``GraphIso.TM.Rep.cons_inv, ``GraphIso.TM.Rep.arr_inv,
    ``GraphIso.TM.length_field_le, ``GraphIso.TM.visB, ``GraphIso.TM.fcB_visB, ``GraphIso.TM.wrB,
    ``GraphIso.TM.WriteSpec, ``GraphIso.TM.sum_map_fst_zip, ``GraphIso.TM.writeElems_sat,
    ``GraphIso.TM.write_unit, ``GraphIso.TM.write_bool, ``GraphIso.TM.head_dropWhile_false,
    ``GraphIso.TM.write_nat, ``GraphIso.TM.write_prod, ``GraphIso.TM.write_option,
    ``GraphIso.TM.listTag, ``GraphIso.TM.ListCell, ``GraphIso.TM.Rep.list_inv,
    ``GraphIso.TM.write_list, ``GraphIso.TM.write_array, ``GraphIso.TM.write_sat,
    ``GraphIso.TM.visB_ge, ``GraphIso.TM.wrB_le, ``GraphIso.TM.Sat.loop_list,
    ``GraphIsoChecks.TMIO.prog1, ``GraphIsoChecks.TMIO.cfgIn, ``GraphIsoChecks.TMIO.cfgOut,
    ``GraphIsoChecks.TMIO.go, ``GraphIsoChecks.TMIO.none4, ``GraphIsoChecks.TMIO.T₁,
    ``GraphIsoChecks.TMIO.v₁, ``GraphIsoChecks.TMIO.ser_v₁, ``GraphIsoChecks.TMIO.ser_arr,
    ``GraphIsoChecks.TMIO.ad, ``GraphIsoChecks.TMIO.h₁, ``GraphIsoChecks.TMIO.h₁_wf,
    ``GraphIsoChecks.TMIO.rep_v₁, ``GraphIsoChecks.TMIO.not_rep_some_false,
    ``GraphIsoChecks.TMIO.load_spec, ``GraphIsoChecks.TMIO.write_spec,
    ``GraphIsoChecks.TMIO.load_not_4659, ``GraphIsoChecks.TMIO.write_not_other,
    ``GraphIsoChecks.TMIO.roundTrip,
    -- 17e: the compiler (`GraphIso.TM.Env`, `Compile`) and its checks (`GraphIsoChecks.TMCompile`)
    ``GraphIso.TM.encNums, ``GraphIso.TM.encNums_nil, ``GraphIso.TM.encNums_cons,
    ``GraphIso.TM.encNums_append, ``GraphIso.TM.envEnc, ``GraphIso.TM.envEnc_nil,
    ``GraphIso.TM.envEnc_concat, ``GraphIso.TM.moveN, ``GraphIso.TM.moveN_sat,
    ``GraphIso.TM.sum_map_le_mul, ``GraphIso.TM.fetchTo, ``GraphIso.TM.fetchB,
    ``GraphIso.TM.fetchTo_sat, ``GraphIso.TM.fetchLv, ``GraphIso.TM.fetchLv_sat, ``GraphIso.TM.Lv,
    ``GraphIso.TM.PrimCode, ``GraphIso.TM.tySize, ``GraphIso.TM.pw, ``GraphIso.TM.goMark,
    ``GraphIso.TM.pushEnv, ``GraphIso.TM.popEnv, ``GraphIso.TM.fetchArgs, ``GraphIso.TM.iteCode,
    ``GraphIso.TM.optCode, ``GraphIso.TM.listCode, ``GraphIso.TM.foldStep, ``GraphIso.TM.foldCode,
    ``GraphIso.TM.loopStep, ``GraphIso.TM.loopCode, ``GraphIso.TM.comp, ``GraphIso.TM.psize,
    ``GraphIso.TM.HeapBnd, ``GraphIso.TM.EnvAt, ``GraphIso.TM.ArgsRep, ``GraphIso.TM.fcE,
    ``GraphIso.TM.ctrlB, ``GraphIso.TM.PrimSpec, ``GraphIso.TM.Pushes,
    ``GraphIso.TM.length_encHeap_append, ``GraphIso.TM.length_encHeap_mono,
    ``GraphIso.TM.length_encFields, ``GraphIso.TM.HeapBnd.field_lt, ``GraphIso.TM.HeapBnd.of_length,
    ``GraphIso.TM.length_encHeap_le_bnd, ``GraphIso.TM.EnvAt.mono, ``GraphIso.TM.EnvAt.push,
    ``GraphIso.TM.EnvAt.sub, ``GraphIso.TM.EnvAt.var, ``GraphIso.TM.fetchB_mono,
    ``GraphIso.TM.fetchCellE_sat, ``GraphIso.TM.fetchVar_sat, ``GraphIso.TM.fetchArgs_sat,
    ``GraphIso.TM.length_args_le, ``GraphIso.TM.two_le_pw, ``GraphIso.TM.fetchB_le_ctrlB,
    ``GraphIso.TM.lin_le_ctrlB, ``GraphIso.TM.fcE_le_ctrlB, ``GraphIso.TM.fcE_mono,
    ``GraphIso.TM.length_le_encHeap_append, ``GraphIso.TM.ctrl_le, ``GraphIso.TM.bnd_one,
    ``GraphIso.TM.bnd_bind, ``GraphIso.TM.bnd_mono, ``GraphIso.TM.fetchVarCell,
    ``GraphIso.TM.exec_ite_cond, ``GraphIso.TM.bnd_branch, ``GraphIso.TM.bnd_recur,
    ``GraphIso.TM.foldHead, ``GraphIso.TM.bnd_iter, ``GraphIso.TM.Sim, ``GraphIso.TM.sim_ret,
    ``GraphIso.TM.sim_bind, ``GraphIso.TM.sim_prim, ``GraphIso.TM.sim_ite, ``GraphIso.TM.sim_opt,
    ``GraphIso.TM.sim_list, ``GraphIso.TM.sim_recur, ``GraphIso.TM.foldLoop_sat,
    ``GraphIso.TM.sim_fold, ``GraphIso.TM.loopLoop_sat, ``GraphIso.TM.sim_loop,
    ``GraphIso.TM.sim_all, ``GraphIso.TM.comp_sat, ``GraphIsoChecks.TMCompile.alloc1,
    ``GraphIsoChecks.TMCompile.alloc2, ``GraphIsoChecks.TMCompile.proj,
    ``GraphIsoChecks.TMCompile.pcDemo, ``GraphIsoChecks.TMCompile.revFold,
    ``GraphIsoChecks.TMCompile.copyRec, ``GraphIsoChecks.TMCompile.revLoop,
    ``GraphIsoChecks.TMCompile.optBr, ``GraphIsoChecks.TMCompile.testProg,
    ``GraphIsoChecks.TMCompile.cfgIn, ``GraphIsoChecks.TMCompile.go,
    ``GraphIsoChecks.TMCompile.idle, ``GraphIsoChecks.TMCompile.empty11,
    ``GraphIsoChecks.TMCompile.revFold_not_47015, ``GraphIsoChecks.TMCompile.copyRec_not_rev,
    ``GraphIsoChecks.TMCompile.idleOpt, ``GraphIsoChecks.TMCompile.optBr_not_two,
    ``GraphIsoChecks.TMCompile.comp_revFold, ``GraphIsoChecks.TMCompile.frame3,
    ``GraphIsoChecks.TMCompile.h₀, ``GraphIsoChecks.TMCompile.h₀_bnd,
    ``GraphIsoChecks.TMCompile.h₀_not_bnd, ``GraphIsoChecks.TMCompile.O₀,
    ``GraphIsoChecks.TMCompile.copyRec_wf,
    -- 17f: the primitives (`GraphIso.TM.PrimLib`, `Prims`) and their checks
    -- (`GraphIsoChecks.TMPrims`)
    ``GraphIso.TM.Fr, ``GraphIso.TM.Fr.refl, ``GraphIso.TM.Fr.trans, ``GraphIso.TM.Fr.mono,
    ``GraphIso.TM.Fr.restore, ``GraphIso.TM.fr1, ``GraphIso.TM.fr2, ``GraphIso.TM.fr3,
    ``GraphIso.TM.fr_push, ``GraphIso.TM.fr_pop, ``GraphIso.TM.fr_set, ``GraphIso.TM.fr_peek,
    ``GraphIso.TM.HeapAt.fr, ``GraphIso.TM.HeapBnd.snoc, ``GraphIso.TM.allocB_sat,
    ``GraphIso.TM.encFields_eq_encNums, ``GraphIso.TM.allocArgs, ``GraphIso.TM.sum_move_le,
    ``GraphIso.TM.allocArgs_sat, ``GraphIso.TM.openTop, ``GraphIso.TM.openTop_sat,
    ``GraphIso.TM.natTo, ``GraphIso.TM.natTo_sat, ``GraphIso.TM.cntBits,
    ``GraphIso.TM.ofBits_cntBits, ``GraphIso.TM.length_cntBits_le, ``GraphIso.TM.head_bits_ne_mk,
    ``GraphIso.TM.moveAll, ``GraphIso.TM.moveAll_sat, ``GraphIso.TM.countAll,
    ``GraphIso.TM.countAll_sat, ``GraphIso.TM.walkList, ``GraphIso.TM.walkList_sat,
    ``GraphIso.TM.buildListB, ``GraphIso.TM.buildListB_sat, ``GraphIso.TM.primB,
    ``GraphIso.TM.PrimOut, ``GraphIso.TM.PrimOut.of_sat, ``GraphIso.TM.sizes_le,
    ``GraphIso.TM.primB_ge, ``GraphIso.TM.primB_ge', ``GraphIso.TM.le_mul_primB,
    ``GraphIso.TM.out_allocArgs, ``GraphIso.TM.natLitCode, ``GraphIso.TM.out_natLit,
    ``GraphIso.TM.fstCode, ``GraphIso.TM.sndCode, ``GraphIso.TM.out_old, ``GraphIso.TM.out_fst,
    ``GraphIso.TM.out_snd, ``GraphIso.TM.notCode, ``GraphIso.TM.out_not, ``GraphIso.TM.dropSnd,
    ``GraphIso.TM.dropSnd_sat, ``GraphIso.TM.boolSel, ``GraphIso.TM.andCode, ``GraphIso.TM.orCode,
    ``GraphIso.TM.boolSel_sat, ``GraphIso.TM.out_old', ``GraphIso.TM.out_and, ``GraphIso.TM.out_or,
    ``GraphIso.TM.natTo2_sat, ``GraphIso.TM.arithCode, ``GraphIso.TM.out_arith,
    ``GraphIso.TM.out_add, ``GraphIso.TM.out_sub, ``GraphIso.TM.finish0, ``GraphIso.TM.cmpCode,
    ``GraphIso.TM.out_cmp, ``GraphIso.TM.out_natEq, ``GraphIso.TM.out_natLt,
    ``GraphIso.TM.le_succ_mul, ``GraphIso.TM.lengthCode, ``GraphIso.TM.out_length,
    ``GraphIso.TM.le_succ_mul2, ``GraphIso.TM.reverseCode, ``GraphIso.TM.out_reverse,
    ``GraphIso.TM.appendCode, ``GraphIso.TM.out_append, ``GraphIso.TM.arrayOfListCode,
    ``GraphIso.TM.RepList.rep_arr, ``GraphIso.TM.out_arrayOfList, ``GraphIso.TM.Rep.arr_list,
    ``GraphIso.TM.arrayToListCode, ``GraphIso.TM.out_arrayToList, ``GraphIso.TM.arraySizeCode,
    ``GraphIso.TM.out_arraySize, ``GraphIso.TM.le_succ_mul0, ``GraphIso.TM.mkTest,
    ``GraphIso.TM.mkTest_sat, ``GraphIso.TM.arrayMkCode, ``GraphIso.TM.out_arrayMk,
    ``GraphIso.TM.le_succ_mul1, ``GraphIso.TM.rangeTest, ``GraphIso.TM.rangeTest_sat,
    ``GraphIso.TM.range_rev_succ, ``GraphIso.TM.RangeInv, ``GraphIso.TM.rangeBody,
    ``GraphIso.TM.rangeCode, ``GraphIso.TM.range_step, ``GraphIso.TM.out_range,
    ``GraphIso.TM.PrimOut.seq, ``GraphIso.TM.allocDefault, ``GraphIso.TM.one_le_tySize,
    ``GraphIso.TM.allocDefault_sat, ``GraphIso.TM.getTest, ``GraphIso.TM.getTest_sat,
    ``GraphIso.TM.getBody, ``GraphIso.TM.getScan, ``GraphIso.TM.getFinish,
    ``GraphIso.TM.arrayGetCode, ``GraphIso.TM.GetInv, ``GraphIso.TM.get_step, ``GraphIso.TM.fcE_ge,
    ``GraphIso.TM.allocBound_ge, ``GraphIso.TM.out_arrayGet, ``GraphIso.TM.updTest,
    ``GraphIso.TM.updTest_sat, ``GraphIso.TM.updBody, ``GraphIso.TM.UpdInv, ``GraphIso.TM.upd_step,
    ``GraphIso.TM.setTail, ``GraphIso.TM.setTail_sat, ``GraphIso.TM.setAt, ``GraphIso.TM.setAt_sat,
    ``GraphIso.TM.RepList.set, ``GraphIso.TM.applyW, ``GraphIso.TM.applyW_sat, ``GraphIso.TM.reMark,
    ``GraphIso.TM.reMark_sat, ``GraphIso.TM.writesLoop, ``GraphIso.TM.applyWrites_snoc,
    ``GraphIso.TM.writesLoop_sat, ``GraphIso.TM.le_comb, ``GraphIso.TM.upd_bound,
    ``GraphIso.TM.arrayUpdateCode, ``GraphIso.TM.out_arrayUpdate, ``GraphIso.TM.primCode,
    ``GraphIso.TM.PrimOut.spec, ``GraphIso.TM.Args.eq_nil, ``GraphIso.TM.Args.eq_one,
    ``GraphIso.TM.Args.eq_two, ``GraphIso.TM.ArgsRep.nil_inv, ``GraphIso.TM.ArgsRep.one_inv,
    ``GraphIso.TM.ArgsRep.two_inv, ``GraphIso.TM.primCode_spec, ``GraphIso.TM.primB_mono,
    ``GraphIso.TM.ctrlB_mono, ``GraphIsoChecks.TMPrims.primProg, ``GraphIsoChecks.TMPrims.same,
    ``GraphIsoChecks.TMPrims.natOps, ``GraphIsoChecks.TMPrims.boolOps,
    ``GraphIsoChecks.TMPrims.listOps, ``GraphIsoChecks.TMPrims.listOps',
    ``GraphIsoChecks.TMPrims.arrOps, ``GraphIsoChecks.TMPrims.updOps,
    ``GraphIsoChecks.TMPrims.pairDefault, ``GraphIsoChecks.TMPrims.optOps,
    ``GraphIsoChecks.TMPrims.natOps_not_44991, ``GraphIsoChecks.TMPrims.arrOps_default,
    ``GraphIsoChecks.TMPrims.updOps_oob, ``GraphIsoChecks.TMPrims.copy_spec,
    ``GraphIsoChecks.TMPrims.hNil, ``GraphIsoChecks.TMPrims.cNil, ``GraphIsoChecks.TMPrims.copy_nil,
    -- 17g: the simulation on Turing machines (`GraphIso.TM.Main`) and its checks
    -- (`GraphIsoChecks.TMMain`)
    ``GraphIso.TM.Exec.length_le, ``GraphIso.TM.canonPtr, ``GraphIso.TM.canonPtr_sat,
    ``GraphIso.TM.mainBody, ``GraphIso.TM.mainProg, ``GraphIso.TM.uB, ``GraphIso.TM.heapB,
    ``GraphIso.TM.fB, ``GraphIso.TM.bB, ``GraphIso.TM.nCells, ``GraphIso.TM.nSym, ``GraphIso.TM.qB,
    ``GraphIso.TM.mainT, ``GraphIso.TM.Sat.of_exec, ``GraphIso.TM.visB_mono,
    ``GraphIso.TM.heapLen_mono, ``GraphIso.TM.kP, ``GraphIso.TM.dP, ``GraphIso.TM.main_sat,
    ``GraphIso.TM.pow_step, ``GraphIso.TM.pow_mono_le, ``GraphIso.TM.one_le_pow',
    ``GraphIso.TM.le_pow_mul, ``GraphIso.TM.le_pow_one, ``GraphIso.TM.kappa, ``GraphIso.TM.PL_le,
    ``GraphIso.TM.lookupBound_le_pow, ``GraphIso.TM.fcE_le_pow, ``GraphIso.TM.allocBound_le_pow,
    ``GraphIso.TM.mainT_le, ``GraphIso.TM.mainPoly, ``GraphIso.TM.main_exec, ``GraphIso.TM.main_tm,
    ``GraphIsoChecks.TMMain.goMain, ``GraphIsoChecks.TMMain.empty13,
    ``GraphIsoChecks.TMMain.same_wf, ``GraphIsoChecks.TMMain.share,
    ``GraphIsoChecks.TMMain.copyMain, ``GraphIsoChecks.TMMain.natMain,
    ``GraphIsoChecks.TMMain.listMain, ``GraphIsoChecks.TMMain.shareMain,
    ``GraphIsoChecks.TMMain.copyMain_not_42339, ``GraphIsoChecks.TMMain.copyMain_not_rev,
    ``GraphIsoChecks.TMMain.trCopy, ``GraphIsoChecks.TMMain.copy_runs,
    ``GraphIsoChecks.TMMain.copy_entry_wf, ``GraphIsoChecks.TMMain.copy_bound,
    ``GraphIsoChecks.TMMain.copy_exec, ``GraphIsoChecks.TMMain.copyTM,
    ``GraphIsoChecks.TMMain.square,
    -- 17h: graph isomorphism on Turing machines (`GraphIso.TM.GI`) and its checks
    -- (`GraphIsoChecks.TMGI`)
    ``GraphIso.TM.GraphPair, ``GraphIso.TM.GraphPair.data, ``GraphIso.TM.GraphPair.enc,
    ``GraphIso.TM.isoDecide, ``GraphIso.TM.isoDecide_iff, ``GraphIso.TM.length_le_serElems,
    ``GraphIso.TM.size_le_ser_array, ``GraphIso.TM.GraphPair.n_le_enc,
    ``GraphIso.TM.length_ser_nat_le, ``GraphIso.TM.length_ser_arrNat_le,
    ``GraphIso.TM.permValid_mem_lt, ``GraphIso.TM.length_ser_perm_le,
    ``GraphIso.TM.length_ser_coset_le, ``GraphIso.TM.giCosetEntry, ``GraphIso.TM.giDecEntry,
    ``GraphIso.TM.giCosetEntry_wf, ``GraphIso.TM.giDecEntry_wf, ``GraphIso.TM.giDecProg,
    ``GraphIso.TM.giCosetProg, ``GraphIso.TM.runs_giDec, ``GraphIso.TM.gi_runs,
    ``GraphIso.TM.exp_arith, ``GraphIso.TM.poly_le_exp, ``GraphIso.TM.gi_bound,
    ``GraphIso.TM.gi_dec_exec, ``GraphIso.TM.exp_succ_le, ``GraphIso.TM.gi_tm,
    ``GraphIso.TM.gi_coset_tm, ``GraphIsoChecks.TMGI.ofAdj, ``GraphIsoChecks.TMGI.path₁,
    ``GraphIsoChecks.TMGI.path₂, ``GraphIsoChecks.TMGI.tri, ``GraphIsoChecks.TMGI.pp,
    ``GraphIsoChecks.TMGI.pt, ``GraphIsoChecks.TMGI.pp_iso, ``GraphIsoChecks.TMGI.pt_not_iso,
    ``GraphIsoChecks.TMGI.cosetData, ``GraphIsoChecks.TMGI.pe,
    ``GraphIsoChecks.TMGI.costF, ``GraphIsoChecks.TMGI.localCost_eq_costF,
    ``GraphIsoChecks.TMGI.sum_append_eq, ``GraphIsoChecks.TMGI.pe_runs,
    -- 18a: graph isomorphism on Turing machines in the number of vertices
    -- (`GraphIso.TM.Vertices`) and its checks (`GraphIsoChecks.TMVertices`)
    ``GraphIso.TM.length_ser_natList_le, ``GraphIso.TM.length_ser_graph_le,
    ``GraphIso.TM.GraphPair.enc_length_le, ``GraphIso.TM.GraphPair.lam_enc_le,
    ``GraphIso.TM.exp_enc_le_vertices, ``GraphIso.TM.outputsInTime_mono,
    ``GraphIso.TM.gi_tm_vertices, ``GraphIso.TM.gi_coset_tm_vertices,
    ``GraphIsoChecks.TMVertices.emptyPair,
    -- 18b: finite single-tape machines, timed outputs and framed tapes
    -- (`GraphIso.TM.SingleTape.Model`) and their checks (`GraphIsoChecks.TMSingleTapeModel`)
    ``GraphIso.TM.SingleTape.StepsIn, ``GraphIso.TM.SingleTape.stepsIn_succ,
    ``GraphIso.TM.SingleTape.StepsIn.trans, ``GraphIso.TM.SingleTape.StepsIn.halt_unique,
    ``GraphIso.TM.SingleTape.StepsIn.reaches, ``GraphIso.TM.SingleTape.StepsIn.evalsToInTime,
    ``GraphIso.TM.SingleTape.EvalsToInTime.stepsIn, ``GraphIso.TM.SingleTape.SimIn,
    ``GraphIso.TM.SingleTape.SimIn.run, ``GraphIso.TM.SingleTape.FinTM0,
    ``GraphIso.TM.SingleTape.FinTM0.step, ``GraphIso.TM.SingleTape.TM0OutputsInTime,
    ``GraphIso.TM.SingleTape.TM0OutputsInTime.mono,
    ``GraphIso.TM.SingleTape.TM0OutputsInTime.mem_eval,
    ``GraphIso.TM.SingleTape.TM0OutputsInTime.unique,
    ``GraphIso.TM.SingleTape.TM0OutputsInTime.steps_le, ``GraphIso.TM.SingleTape.mk_append_inj,
    ``GraphIso.TM.SingleTape.Sym, ``GraphIso.TM.SingleTape.encodeIn,
    ``GraphIso.TM.SingleTape.encodeOut, ``GraphIso.TM.SingleTape.length_encodeIn,
    ``GraphIso.TM.SingleTape.length_encodeOut, ``GraphIso.TM.SingleTape.encodeIn_injective,
    ``GraphIso.TM.SingleTape.encodeOut_injective, ``GraphIso.TM.SingleTape.mk_encodeIn_inj,
    ``GraphIso.TM.SingleTape.mk_encodeOut_inj, ``GraphIsoChecks.TMSingleTapeModel.copyM,
    ``GraphIsoChecks.TMSingleTapeModel.copy_run, ``GraphIsoChecks.TMSingleTapeModel.copy_out,
    -- 18c: the simulation of stack machines on one tape, counted
    -- (`GraphIso.TM.SingleTape.TM2Sim`) and its checks (`GraphIsoChecks.TM2Sim`)
    ``GraphIso.TM.SingleTape.acts, ``GraphIso.TM.SingleTape.stepAux_length_le,
    ``GraphIso.TM.SingleTape.step_length_le, ``GraphIso.TM.SingleTape.go_steps,
    ``GraphIso.TM.SingleTape.ret_steps, ``GraphIso.TM.SingleTape.trNormal_steps,
    ``GraphIso.TM.SingleTape.tr2_step, ``GraphIso.TM.SingleTape.run_length_le,
    ``GraphIso.TM.SingleTape.tr2_run, ``GraphIso.TM.SingleTape.tmActs,
    ``GraphIso.TM.SingleTape.tmActs_le, ``GraphIso.TM.SingleTape.initList_length_le,
    ``GraphIso.TM.SingleTape.run_bound_le, ``GraphIso.TM.SingleTape.tr2_outputs,
    ``GraphIso.TM.SingleTape.length_out_le, ``GraphIsoChecks.TM2Sim.revTM,
    ``GraphIsoChecks.TM2Sim.rev_outputs, ``GraphIsoChecks.TM2Sim.sim_running_lt_21,
    ``GraphIsoChecks.TM2Sim.mixM,
    -- 18d: machines with local state on one tape, counted, with finite control
    -- (`GraphIso.TM.SingleTape.TM1Sim`) and its checks (`GraphIsoChecks.TM1Sim`)
    ``GraphIso.TM.SingleTape.stmtSize, ``GraphIso.TM.SingleTape.stepAux_steps,
    ``GraphIso.TM.SingleTape.tr1_simIn, ``GraphIso.TM.SingleTape.tr1_run,
    ``GraphIso.TM.SingleTape.tr1_halt, ``GraphIso.TM.SingleTape.Reachable,
    ``GraphIso.TM.SingleTape.Reachable.mem, ``GraphIso.TM.SingleTape.finite_reachable,
    ``GraphIso.TM.SingleTape.restrict, ``GraphIso.TM.SingleTape.restrict_eq_some,
    ``GraphIso.TM.SingleTape.restrict_steps, ``GraphIso.TM.SingleTape.restrict_halt,
    ``GraphIso.TM.SingleTape.FinTM0.ofTM1, ``GraphIso.TM.SingleTape.ofTM1_outputs,
    ``GraphIsoChecks.TM1Sim.walkM, ``GraphIsoChecks.TM1Sim.walk_tr_run,
    ``GraphIsoChecks.TM1Sim.walk_outputs,
    -- 18d: the composed simulation and its finite control (`GraphIso.TM.SingleTape.Sim`), the
    -- compiled stack programs (`GraphIso.TM.SingleTape.Programs`), checks (`GraphIsoChecks.TMSim`)
    ``GraphIso.TM.SingleTape.stmtSize_trNormal, ``GraphIso.TM.SingleTape.supportsStmt_univ,
    ``GraphIso.TM.SingleTape.stmtSize_tr, ``GraphIso.TM.SingleTape.sim_run,
    ``GraphIso.TM.SingleTape.mainInhabited, ``GraphIso.TM.SingleTape.initList_eq_init,
    ``GraphIso.TM.SingleTape.sim_outputs, ``GraphIso.TM.SingleTape.tr_supports_univ,
    ``GraphIso.TM.SingleTape.finite_Γ', ``GraphIso.TM.SingleTape.simTM0,
    ``GraphIso.TM.SingleTape.simTM0_outputs, ``GraphIso.TM.finite_toFinTM2,
    ``GraphIso.TM.exec_simTM0, ``GraphIsoChecks.TMSim.revS, ``GraphIsoChecks.TMSim.negS,
    ``GraphIsoChecks.TMSim.tmActs_negM,
    -- 18e: the compiler from stack machines to single-tape machines
    -- (`GraphIso.TM.SingleTape.IO`, `Compile`) and its checks (`GraphIsoChecks.TMSingleTape`)
    ``GraphIso.TM.SingleTape.tapeMirror, ``GraphIso.TM.SingleTape.tapeMirror_move,
    ``GraphIso.TM.SingleTape.workTape, ``GraphIso.TM.SingleTape.workTape_move,
    ``GraphIso.TM.SingleTape.workTape_write, ``GraphIso.TM.SingleTape.simStmt,
    ``GraphIso.TM.SingleTape.simCfg, ``GraphIso.TM.SingleTape.stepAux_simStmt,
    ``GraphIso.TM.SingleTape.steps_sim, ``GraphIso.TM.SingleTape.supportsStmt_simStmt,
    ``GraphIso.TM.SingleTape.scan_steps, ``GraphIso.TM.SingleTape.stmtSize_simStmt,
    ``GraphIso.TM.SingleTape.Lab, ``GraphIso.TM.SingleTape.compM,
    ``GraphIso.TM.SingleTape.inMark_tape, ``GraphIso.TM.SingleTape.input_steps,
    ``GraphIso.TM.SingleTape.halt_tape, ``GraphIso.TM.SingleTape.output_steps,
    ``GraphIso.TM.SingleTape.compM_run, ``GraphIso.TM.SingleTape.compM_size,
    ``GraphIso.TM.SingleTape.compM_supports, ``GraphIso.TM.SingleTape.finite_cSym,
    ``GraphIso.TM.SingleTape.compile, ``GraphIso.TM.SingleTape.compileConst,
    ``GraphIso.TM.SingleTape.compile_outputs,
    ``GraphIsoChecks.TMSingleTape.revTM0, ``GraphIsoChecks.TMSingleTape.rev_view,
    ``GraphIsoChecks.TMSingleTape.rev_exact, ``GraphIsoChecks.TMSingleTape.negTM0,
    ``GraphIsoChecks.TMSingleTape.neg_outputs,
    -- 18f: graph isomorphism on a single tape (`GraphIso.TM.SingleTape.GI`) and its checks
    -- (`GraphIsoChecks.TMGISingleTape`)
    ``GraphIso.TM.giDecTM0, ``GraphIso.TM.giCosetTM0, ``GraphIso.TM.compile_growth,
    ``GraphIso.TM.GraphPair.lam_tape_le, ``GraphIso.TM.exp_tape_le_vertices,
    ``GraphIso.TM.length_giDec_tape, ``GraphIso.TM.length_giCoset_tape, ``GraphIso.TM.gi_tm0,
    ``GraphIso.TM.gi_coset_tm0, ``GraphIso.TM.gi_tm0_vertices, ``GraphIso.TM.gi_coset_tm0_vertices,
    ``GraphIsoChecks.TMGISingleTape.tape_pp, ``GraphIsoChecks.TMGISingleTape.tape_pt,
    ``GraphIsoChecks.TMGISingleTape.tape_coset]
  let mut lines : Array MessageData := #[]
  for name in principal do
    let axs ← collectAxioms name
    lines := lines.push m!"{name}: {axs.toList}"
  logInfo (MessageData.joinSep lines.toList "\n")

/-! The list continues in a last block. -/

open Lean in
run_cmd do
  let principal := #[
    -- 19c: the Palomar statement (`GraphIso.Palomar.Statement`, `Bridge`) and its checks
    -- (`GraphIsoChecks.Palomar`)
    ``GraphIsoPalomar.Sym, ``GraphIsoPalomar.natWord, ``GraphIsoPalomar.listWord,
    ``GraphIsoPalomar.nbrs, ``GraphIsoPalomar.graphWord, ``GraphIsoPalomar.input,
    ``GraphIsoPalomar.output, ``GraphIsoPalomar.tapeAlphabet_eq, ``GraphIsoPalomar.symbolMap,
    ``GraphIsoPalomar.symbolMap_injective, ``GraphIsoPalomar.symbolEmbedding,
    ``GraphIsoPalomar.symbolEmbedding_ne_default, ``GraphIsoPalomar.bits_eq_toBits,
    ``GraphIsoPalomar.natWord_map, ``GraphIsoPalomar.listWord_map,
    ``GraphIsoPalomar.numberList_map, ``GraphIsoPalomar.graphWord_map,
    ``GraphIsoPalomar.input_map, ``GraphIsoPalomar.output_map,
    ``GraphIsoPalomar.gi_singleTape_proof,
    ``GraphIsoChecks.Palomar.eq_of_symEq, ``GraphIsoChecks.Palomar.eq_of_wordEq,
    -- 19d: the Palomar coset statement (`GraphIso.Palomar.Statement`, `Bridge`) and its checks
    -- (`GraphIsoChecks.Palomar`)
    ``GraphIsoPalomar.permWord, ``GraphIsoPalomar.cosetWord, ``GraphIsoPalomar.Writes,
    ``GraphIsoPalomar.Writes.natWord_map, ``GraphIsoPalomar.Writes.listWord_map,
    ``GraphIsoPalomar.Writes.numberList_map, ``GraphIsoPalomar.Writes.graphWord_map,
    ``GraphIsoPalomar.Writes.input_map, ``GraphIsoPalomar.Writes.permWord_map,
    ``GraphIsoPalomar.Writes.gensWord_map, ``GraphIsoPalomar.writes_symbolEmbedding,
    ``GraphIsoPalomar.CosetAlphabet, ``GraphIsoPalomar.cosetAlphabet_eq,
    ``GraphIsoPalomar.cosetInMap, ``GraphIsoPalomar.cosetOutMap,
    ``GraphIsoPalomar.cosetInMap_injective, ``GraphIsoPalomar.cosetOutMap_injective,
    ``GraphIsoPalomar.cosetIn, ``GraphIsoPalomar.cosetOut, ``GraphIsoPalomar.cosetIn_ne_default,
    ``GraphIsoPalomar.cosetOut_ne_default, ``GraphIsoPalomar.writes_cosetIn,
    ``GraphIsoPalomar.writes_cosetOut, ``GraphIsoPalomar.cosetIn_input_map,
    ``GraphIsoPalomar.cosetData, ``GraphIsoPalomar.cosetWord_map, ``GraphIsoPalomar.PrefixCode,
    ``GraphIsoPalomar.eq_of_append_cons, ``GraphIsoPalomar.natWord_prefixCode,
    ``GraphIsoPalomar.listWord_cons, ``GraphIsoPalomar.PrefixCode.list,
    ``GraphIsoPalomar.permWord_prefixCode, ``GraphIsoPalomar.cosetWord_injective_proof,
    ``GraphIsoPalomar.gi_coset_singleTape_proof,
    ``GraphIsoChecks.Palomar.c3d, ``GraphIsoChecks.Palomar.swd]
  let mut lines : Array MessageData := #[]
  for name in principal do
    let axs ← collectAxioms name
    lines := lines.push m!"{name}: {axs.toList}"
  logInfo (MessageData.joinSep lines.toList "\n")
