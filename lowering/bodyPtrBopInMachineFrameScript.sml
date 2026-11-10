Theory bodyPtrBopInMachineFrame
Ancestors
  bodyPtrBopInMachineMemory bodyPtrBopInJointSource bodyPtrBopInActualSuffix
  bodyPtrDefs compileEnv loweringStateRelDefs compileVyper venomState ptrDiscipline finite_map
  bodyPtrBopInSourceFrame bodyPtrBopInLiveSourceFrame vyperState vyperContext

(* The machine witness starts at the contained interior suffix, not at entry.
   Empty allocation bookkeeping models borrowed, disjoint local buffers. *)
Definition joint_machine_def:
  joint_machine = (init_venom_state "fn_probe") with
    <| vs_memory := joint_memory;
       vs_vars := FEMPTY |+ ("%10",64w) |+ ("%13",128w);
       vs_alloca_next := 192;
       vs_inst_idx := LENGTH (actual_suffix_start equality_selector).cs_current_insts;
       vs_block_ctx := empty_block_context with bc_number := 1w |>
End

Definition joint_provenance_def:
  joint_provenance = FEMPTY |+ ("%10",(64,64)) |+ ("%13",(128,64))
End

Theorem joint_machine_coverage:
  ptr_covers joint_provenance entry_taint "%10" joint_machine 64 /\
  ptr_covers joint_provenance entry_taint "%13" joint_machine 64
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem joint_machine_ghost:
  ghost_inv NONE joint_cenv joint_cx joint_es joint_provenance entry_taint
    joint_machine
Proof
  simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
       entry_taint_def, joint_cenv_def, joint_es_def, probe_es_def,
       build_compile_env_def, lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `name = "y"` >> gvs[] >>
  Cases_on `name = "x"` >> gvs[] >>
  simp[ptr_covers_def, joint_provenance_def, op_taint_def,
       entry_taint_def, joint_machine_def, lookup_var_def, FLOOKUP_UPDATE,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  rpt strip_tac >>
  gvs[joint_machine_def, lookup_var_def, FLOOKUP_UPDATE,
      wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  drule joint_memory_robust_strings >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem joint_machine_local_ptrs:
  local_ptrs_rel (equality_runtime_function equality_selector)
    joint_cenv joint_es.scopes joint_machine
Proof
  simp[local_ptrs_rel_def, local_region_def, joint_cenv_def, joint_es_def,
       probe_es_def, build_compile_env_def, lookup_scopes_def,
       FLOOKUP_UPDATE, joint_machine_def, lookup_var_def,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  conj_tac
  >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `name = "y"` >> gvs[] >>
      Cases_on `name = "x"` >> gvs[] >>
      simp[local_backed_def, init_venom_state_def, joint_memory_strings,
           wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `n1 = "y"` >> gvs[] >>
  Cases_on `n1 = "x"` >> gvs[] >>
  Cases_on `n2 = "y"` >> gvs[] >>
  Cases_on `n2 = "x"` >> gvs[] >>
  simp[regions_disjoint_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256]
QED

Theorem joint_machine_state_rel:
  state_rel (equality_runtime_function equality_selector)
    joint_cenv joint_cx joint_es joint_machine
Proof
  simp[state_rel_def, joint_machine_local_ptrs] >>
  simp[storage_rel_def, storage_vars_rel_def, transient_rel_def,
       transient_vars_rel_def, accounts_rel_def, immutables_rel_def,
       logs_rel_def, call_ctx_rel_def, joint_cenv_def, joint_cx_def,
       joint_es_def, joint_machine_def, probe_es_def, probe_live_cx_def,
       probe_cx_def, empty_evaluation_context_def, build_compile_env_def] >>
  EVAL_TAC >> simp[]
QED

Theorem joint_machine_no_direct_calls:
  !sel a b. ~fn_directly_calls (equality_runtime_context sel) a b
Proof
  EVAL_TAC >>
  simp[venomInstTheory.fn_insts_blocks_def] >> rpt strip_tac >> gvs[]
QED

Theorem joint_machine_no_calls:
  !a b. ~TC (fn_directly_calls (equality_runtime_context equality_selector)) a b
Proof
  once_rewrite_tac[relationTheory.TC_CASES1] >>
  simp[joint_machine_no_direct_calls]
QED

Theorem joint_machine_alloca_room:
  alloca_room (equality_runtime_context equality_selector)
    (equality_runtime_function equality_selector) joint_machine
Proof
  simp[exprLoweringPropsTheory.alloca_room_def, joint_machine_no_calls,
       bodyPtrBopInUnitTheory.equality_function_member,
       bodyPtrBopInUnitTheory.equality_function_lookup,
       exprLoweringPropsTheory.pending_alloca_size_def, joint_machine_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem joint_machine_stmt_state_rel:
  stmt_state_rel (equality_runtime_context equality_selector)
    (equality_runtime_function equality_selector)
    joint_cenv joint_cx joint_es joint_machine
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, joint_machine_state_rel,
       joint_machine_alloca_room, exprLoweringPropsTheory.fmp_room_def,
       joint_machine_no_calls, exprLoweringPropsTheory.immutable_alloca_sep_def,
       immutable_base_zero_def,
       joint_cenv_def, build_compile_env_def, joint_machine_def,
       init_venom_state_def, venomMemDefsTheory.alloca_inv_def] >>
  EVAL_TAC >> simp[]
QED

