(*
 * Optimization Levels and Pipeline
 *
 * Port of vyper/venom/optimization_levels/*.py and vyper/venom/__init__.py.
 *)

Theory optimizationLevels
Ancestors
  list alist pred_set
  orderedSet
  venomInst
  addrSpace
  cfgAnalysis
  memoryAllocator
  optimizationFlags
  fcgAnalysis
  functionInliner
  floatAllocas
  cfgNormalization
  phiTransform
  algebraicOpt
  sccp
  assignElim
  mem2Var
  loadElim
  rtaPassDefs
  memMerging
  lowerDload
  removeUnusedVars
  deadStoreElim
  concretizeMemLoc
  branchOpt
  commonSubexpressionElim
  singleUseExpansion
  dft
  literalsCodesize

Datatype:
  pass_kind =
    | PassFixMemLocations
    | PassFloatAllocas
    | PassSimplifyCFG
    | PassMakeSSA
    | PassPhiElimination
    | PassAlgebraicOptimization
    | PassSCCP
    | PassAssignElimination
    | PassMem2Var
    | PassLoadElimination
    | PassRevertToAssert
    | PassMemMerge
    | PassLowerDload
    | PassRemoveUnusedVariables
    | PassDeadStore addr_space
    | PassConcretizeMemLoc
    | PassBranchOptimization
    | PassCSE
    | PassSingleUseExpansion
    | PassDFT
    | PassCFGNormalization
    | PassReduceLiteralsCodesize
End

Definition passes_O2_def:
  passes_O2 =
    [PassFixMemLocations;
     PassFloatAllocas;
     PassSimplifyCFG;
     PassMakeSSA;
     PassPhiElimination;
     PassAlgebraicOptimization;
     PassSCCP;
     PassSimplifyCFG;
     PassAssignElimination;
     PassMem2Var;
     PassMakeSSA;
     PassPhiElimination;
     PassSCCP;
     PassSimplifyCFG;
     PassAssignElimination;
     PassAlgebraicOptimization;
     PassLoadElimination;
     PassPhiElimination;
     PassAssignElimination;
     PassSCCP;
     PassAssignElimination;
     PassRevertToAssert;
     PassSimplifyCFG;
     PassMemMerge;
     PassLowerDload;
     PassRemoveUnusedVariables;
     PassDeadStore MEMORY;
     PassDeadStore STORAGE;
     PassDeadStore TRANSIENT;
     PassAssignElimination;
     PassRemoveUnusedVariables;
     PassConcretizeMemLoc;
     PassSCCP;
     PassSimplifyCFG;
     PassMemMerge;
     PassRemoveUnusedVariables;
     PassBranchOptimization;
     PassAlgebraicOptimization;
     PassRemoveUnusedVariables;
     PassPhiElimination;
     PassAssignElimination;
     PassCSE;
     PassAssignElimination;
     PassRemoveUnusedVariables;
     PassSingleUseExpansion;
     PassDFT;
     PassCFGNormalization]
End

Definition passes_O3_def:
  passes_O3 = passes_O2
End

Definition passes_Os_def:
  passes_Os =
    [PassFixMemLocations;
     PassFloatAllocas;
     PassSimplifyCFG;
     PassMakeSSA;
     PassPhiElimination;
     PassAlgebraicOptimization;
     PassSCCP;
     PassSimplifyCFG;
     PassAssignElimination;
     PassMem2Var;
     PassMakeSSA;
     PassPhiElimination;
     PassSCCP;
     PassSimplifyCFG;
     PassAssignElimination;
     PassAlgebraicOptimization;
     PassLoadElimination;
     PassPhiElimination;
     PassAssignElimination;
     PassSCCP;
     PassAssignElimination;
     PassRevertToAssert;
     PassSimplifyCFG;
     PassMemMerge;
     PassLowerDload;
     PassRemoveUnusedVariables;
     PassDeadStore MEMORY;
     PassDeadStore STORAGE;
     PassDeadStore TRANSIENT;
     PassAssignElimination;
     PassRemoveUnusedVariables;
     PassConcretizeMemLoc;
     PassSCCP;
     PassSimplifyCFG;
     PassMemMerge;
     PassRemoveUnusedVariables;
     PassBranchOptimization;
     PassAlgebraicOptimization;
     PassRemoveUnusedVariables;
     PassPhiElimination;
     PassAssignElimination;
     PassCSE;
     PassAssignElimination;
     PassRemoveUnusedVariables;
     PassSingleUseExpansion;
     PassReduceLiteralsCodesize;
     PassDFT;
     PassCFGNormalization]
End

Definition passes_for_level_def:
  passes_for_level OPT_O2 = passes_O2 /\
  passes_for_level OPT_O3 = passes_O3 /\
  passes_for_level OPT_Os = passes_Os /\
  passes_for_level OPT_CODESIZE = passes_Os /\
  passes_for_level OPT_NONE = passes_O2 /\
  passes_for_level OPT_GAS = passes_O2
End

Definition pass_disabled_def:
  pass_disabled flags PassAlgebraicOptimization = flags.vof_disable_algebraic_optimization /\
  pass_disabled flags PassSCCP = flags.vof_disable_sccp /\
  pass_disabled flags PassMem2Var = flags.vof_disable_mem2var /\
  pass_disabled flags PassLoadElimination = flags.vof_disable_load_elimination /\
  pass_disabled flags PassRemoveUnusedVariables = flags.vof_disable_remove_unused_variables /\
  pass_disabled flags (PassDeadStore _) = flags.vof_disable_dead_store_elimination /\
  pass_disabled flags PassBranchOptimization = flags.vof_disable_branch_optimization /\
  pass_disabled flags PassCSE = flags.vof_disable_cse /\
  pass_disabled flags PassSimplifyCFG = flags.vof_disable_simplify_cfg /\
  pass_disabled flags _ = F
End

Datatype:
  pipeline_state = <|
    ps_ctx : ir_context;
    ps_allocator : mem_allocator
  |>
End

Datatype:
  pipeline_result =
    | PipelineOK pipeline_state
    | PipelineFail string
End

Definition pipeline_state_init_def:
  pipeline_state_init ctx allocator =
    <| ps_ctx := ctx; ps_allocator := allocator |>
End

Definition remove_unreachable_functions_def:
  remove_unreachable_functions ctx =
    case ctx.ctx_entry of
      NONE => ctx
    | SOME _ =>
        let fcg = fcg_analyze ctx in
        ctx with ctx_functions :=
          FILTER (λfn. MEM fn.fn_name fcg.reachable) ctx.ctx_functions
End

Definition run_global_passes_def:
  run_global_passes flags st =
    let ctx1 = st.ps_ctx in
    let ctx2 = ctx1 in
    let ctx3 = function_inliner_context flags ctx2 in
    st with ps_ctx := ctx3
End

Definition phi_elim_function_def:
  phi_elim_function fn = phiTransform$transform_function fn
End

Definition rta_function_def:
  rta_function fn = rtaPassDefs$transform_function fn
End

Definition apply_pass_on_name_def:
  apply_pass_on_name mcopy_available flags pass st fn_name =
    if pass_disabled flags pass then PipelineOK st
    else
      case lookup_function fn_name st.ps_ctx.ctx_functions of
        NONE => PipelineOK st
      | SOME fn =>
          let ctx = st.ps_ctx in
          let alloc = st.ps_allocator in
          case pass of
            PassFixMemLocations => PipelineOK st
          | PassFloatAllocas =>
              let fn' = float_allocas_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassSimplifyCFG => PipelineOK st
          | PassMakeSSA => PipelineOK st
          | PassPhiElimination =>
              let fn' = phi_elim_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassAlgebraicOptimization =>
              let fn' = algebraic_opt_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassSCCP =>
              (case sccp_run fn of
                 SCCP_FAIL msg => PipelineFail msg
               | SCCP_OK fn' =>
                   PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn'))
          | PassAssignElimination =>
              let fn' = assign_elim_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassMem2Var =>
              let fn' = mem2var_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassLoadElimination =>
              let fn' = load_elim_function ctx fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassRevertToAssert =>
              let fn' = rta_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassMemMerge =>
              let fn' = memmerge_function mcopy_available fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassLowerDload =>
              let fn' = lower_dload_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassRemoveUnusedVariables =>
              let cfg = cfg_analyze fn in
              let fn' = remove_unused_function fn cfg in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassDeadStore space =>
              let fn' = dead_store_elim_function ctx space fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassConcretizeMemLoc =>
              let (fn', alloc') = concretize_mem_loc_function alloc ctx fn in
              PipelineOK (st with <| ps_ctx := ctx_replace_function ctx fn.fn_name fn';
                                     ps_allocator := alloc' |>)
          | PassBranchOptimization =>
              let fn' = branch_optimize_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassCSE =>
              let fn' = cse_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassSingleUseExpansion =>
              let fn' = single_use_expand_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassDFT =>
              let fn' = dft_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassCFGNormalization =>
              let fn' = cfg_normalize_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
          | PassReduceLiteralsCodesize =>
              let fn' = reduce_literals_codesize_function fn in
              PipelineOK (st with ps_ctx := ctx_replace_function ctx fn.fn_name fn')
End

Definition run_passes_for_function_def:
  run_passes_for_function mcopy_available flags passes fn_name st =
    FOLDL
      (λacc pass.
         case acc of
           PipelineFail msg => PipelineFail msg
         | PipelineOK st' => apply_pass_on_name mcopy_available flags pass st' fn_name)
      (PipelineOK st) passes
End

Definition run_passes_on_walk_def:
  run_passes_on_walk mcopy_available flags passes walk st =
    FOLDL
      (λacc fn_name.
         case acc of
           PipelineFail msg => PipelineFail msg
         | PipelineOK st' => run_passes_for_function mcopy_available flags passes fn_name st')
      (PipelineOK st) walk
End

Definition run_passes_on_def:
  run_passes_on flags mcopy_available ctx =
    let st0 = pipeline_state_init ctx mem_allocator_init in
    let st1 = run_global_passes flags st0 in
    let ctx1 = remove_unreachable_functions st1.ps_ctx in
    let st2 = st1 with ps_ctx := ctx1 in
    let fcg = fcg_analyze ctx1 in
    let passes = passes_for_level flags.vof_level in
    let walk = build_call_walk fcg ctx1 in
    run_passes_on_walk mcopy_available flags passes walk st2
End

val _ = export_theory();
