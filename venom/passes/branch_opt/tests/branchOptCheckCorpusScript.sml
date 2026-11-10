(* The branch_opt checker on compiled code: each parity fixture program is
   lowered to its runtime unit and run through the O1 pipeline, and on every
   function of the result branch_opt runs (both variants, with Python's
   liveness heuristic) and the checker judges the output. HOL has no O2
   pipeline, so the pass sees post-O1 functions. branchOptCorpusLib evaluates
   it with EVAL; branchOptCheckCorpusA..J split the fixtures between them. *)
Theory branchOptCheckCorpus
Ancestors
  compileVyper evalCompiler evalCompilerSubsetAbiBuiltins
  evalCompilerSubsetAbiEvents evalCompilerSubsetAbiExternalCalls
  evalCompilerSubsetAbiExternal evalCompilerSubsetAbiInternalCalls
  evalCompilerSubsetBuiltins evalCompilerSubsetControlDeploy
  evalCompilerSubsetScalars evalCompilerSubsetState codegenReadyCompute
  branchOptDefs branchOptCheck livenessDefs irSupply alist integer_word
(* The runtime unit after the O1 pipeline, as compile_vyper builds it. *)
Definition bo_corpus_unit_def:
  bo_corpus_unit tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            case run_venom_pipeline (K T) (K T) (K T) rpolicy
                   o1_pipeline_spec unit of
              NONE => NONE
            | SOME out => SOME out.po_unit
End

(* Per function: did each variant rewrite it, and does the check accept the
   result. live_at is the size of the live set at a block's entry, as in
   Python's heuristic. *)
Definition bo_corpus_fn_def:
  bo_corpus_fn s0 fn =
    let lv = liveness_analyze fn in
    let live = (\l. LENGTH (live_vars_at lv l 0)) in
    let fn1 = branch_opt_function live fn in
    let fn2 = FST (branch_opt_function_supply live s0 fn) in
      (fn1.fn_blocks <> fn.fn_blocks, check_branch_opt_fn fn fn1,
       fn2.fn_blocks <> fn.fn_blocks, check_branch_opt_fn fn fn2)
End

Definition bo_corpus_def:
  bo_corpus tops =
    case bo_corpus_unit tops of
      NONE => NONE
    | SOME unit =>
        SOME (MAP (bo_corpus_fn (init_ir_supply unit))
                  unit.cu_context.ctx_functions)
End
