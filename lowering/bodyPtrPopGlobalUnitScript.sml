Theory bodyPtrPopGlobalUnit
Ancestors
  bodyPtrPopGlobalStatements bodyPtrPopGlobalDispatch
  bodyPtrPopGlobalLoweringBoundary bodyPtrPopGlobalInternal
  moduleLowering compileEnv vyperCompiler compileVyper
Libs monadsyntax

Theorem pop_global_runtime_computed:
  compile_generate_runtime [] [] pop_global_packages NONE Linear 0 0
    ([] : dense_bucket list) (K ("",0,F)) (initial_compile_state "__entry") =
  ((),pop_global_returned_state)
Proof
  rewrite_tac[pop_global_runtime_suffix, pop_global_packages_def,
              compile_internal_fn_bodies_def] >>
  mp_tac pop_global_internal_computed >>
  simp[comp_ignore_bind_def, comp_bind_def, pop_global_prologue_steps] >>
  Cases_on `compile_internal_function pop_global_package_env [] F F 0 F F F 0
    pop_global_body (SOME (BaseT (UintT 256))) pop_global_block_state` >>
  simp[comp_return_def]
QED

(* Closed output abbreviations share the already computed block stream. *)
Definition pop_global_entry_blocks_def:
  pop_global_entry_blocks = REVERSE pop_global_dispatch_state.cs_blocks ++
    [<| bb_label := "@fallback_0";
        bb_instructions := pop_global_dispatch_state.cs_current_insts |>]
End
Definition pop_global_internal_blocks_def:
  pop_global_internal_blocks =
    REVERSE (TAKE 6 pop_global_returned_state.cs_blocks) ++
    [<| bb_label := "@wcopy_exit_7";
        bb_instructions := pop_global_returned_state.cs_current_insts |>]
End
Definition pop_global_runtime_context_def:
  pop_global_runtime_context = mk_venom_context
    [mk_raw_function "__entry" pop_global_entry_blocks;
     mk_internal_function "internal 0 replace()_runtime"
       pop_global_internal_blocks F 1] (SOME "__entry")
End

Theorem pop_global_descriptors:
  internal_fn_descriptors pop_global_packages =
    [("internal 0 replace()_runtime",F,1)]
Proof
  simp[pop_global_packages_def, internal_fn_descriptors_def, pop_global_return_count]
QED

Theorem pop_global_blocks_packaged:
  package_internal_blocks [("internal 0 replace()_runtime",F,1)]
    (REVERSE pop_global_returned_state.cs_blocks ++
      [<| bb_label := pop_global_returned_state.cs_current_bb;
          bb_instructions := pop_global_returned_state.cs_current_insts |>]) =
    SOME (pop_global_entry_blocks,
      [mk_internal_function "internal 0 replace()_runtime" pop_global_internal_blocks F 1])
Proof
  EVAL_TAC
QED

Theorem pop_global_data_empty:
  REVERSE pop_global_returned_state.cs_data_sections = []
Proof
  EVAL_TAC
QED

Theorem pop_global_context_extracted:
  extract_context_with_internals "__entry" pop_global_packages pop_global_returned_state =
    SOME (pop_global_runtime_context,[])
Proof
  simp[extract_context_with_internals_def, pop_global_descriptors,
       pop_global_blocks_packaged, pop_global_runtime_context_def,
       pop_global_data_empty]
QED

Theorem pop_global_context_valid:
  lowering_context_ok pop_global_runtime_context
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem pop_global_unit_lowered:
  lower_vyper_runtime_unit pop_global_tops pop_global_policy =
    SOME <| cu_context := pop_global_runtime_context; cu_data_segment := [] |>
Proof
  simp[pop_global_lowering_boundary, pop_global_runtime_computed,
       pop_global_context_extracted, pop_global_context_valid]
QED
