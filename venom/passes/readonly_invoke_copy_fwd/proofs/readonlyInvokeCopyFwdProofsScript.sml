(*
 * Readonly Invoke Arg Copy Forwarding — Proofs
 *
 * Proves the fold form of the block pass, function-name preservation, and
 * a concrete non-vacuity witness (ricf_witness_ctx) for ricf_pass_correct
 * (readonlyInvokeCopyFwdSim): every premise holds, readonly_mem_analyze
 * infers a readonly parameter, and ricf forwards a pre-invoke staging
 * MCOPY.
 *)

Theory readonlyInvokeCopyFwdProofs
Ancestors
  readonlyInvokeCopyFwdHistoryCopyAbort readonlyInvokeCopyFwdHistoryInheritedAccess
  readonlyInvokeCopyFwdHistorySuspension readonlyInvokeCopyFwdOpaqueStep
  readonlyInvokeCopyFwdOperationalEntry readonlyInvokeCopyFwdOrdinaryPremises
  readonlyInvokeCopyFwdSteps readonlyInvokeCopyFwdStepsDelegate
  readonlyInvokeCopyFwdStepsErrors readonlyInvokeCopyFwdStepsHash
  readonlyInvokeCopyFwdStepsMemoryAll readonlyInvokeCopyFwdStepsSelfdestruct
  readonlyInvokeCopyFwdStepsValues
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdSim readonlyInvokeCopyFwdDefs internalReturnCopyFwdDefs invokeCopyFwdCommonDefs
  readonlyMemoryArgsProps readonlyMemoryArgsDefs callLayoutDefs dfgDefs
  memLocDefs o1PassContract ptrDiscipline unitTransformDefs copyFwdEquiv
  passSharedDefs venomWf venomInst venomInstProps venomExecSemantics
  venomState stateEquiv While list rich_list finite_map pred_set arithmetic
  pair option words ptrSafeRun ptrOkCheck memSafeRun unitMemInv
  taintAgree contextCodegenRel contextCodegenRelProps calleeTransport
  pointerConfinedDefs

(* Structural transformation facts are exported by readonlyInvokeCopyFwdPlan. *)
(* ==========================================================================
   3. Concrete Non-Vacuity Witness (ricf_witness_ctx)
   ========================================================================== *)

Definition ricf_witness_callee_def:
  ricf_witness_callee : ir_function =
    mk_raw_function "callee" [
      <| bb_label := "callee";
         bb_instructions := [
           mk_inst 10 PARAM [Lit 0w] ["%arg"];
           mk_inst 11 RETPC_PARAM [Lit 1w] ["%retpc"];
           mk_inst 12 MLOAD [Var "%arg"] ["%val"];
           mk_inst 13 RET [Var "%val"; Var "%retpc"] []
         ] |>
    ]
End

Definition ricf_witness_main_def:
  ricf_witness_main : ir_function =
    mk_raw_function "main" [
      <| bb_label := "main";
         bb_instructions := [
           mk_inst 1 ALLOCA [Lit 32w] ["%src"];
           mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
           mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
           mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
           mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
           mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
           mk_inst 7 STOP [] []
         ] |>
    ]
End

Definition ricf_witness_ctx_def:
  ricf_witness_ctx : venom_context =
    <| ctx_functions := [ricf_witness_callee; ricf_witness_main];
       ctx_entry := SOME "main";
       ctx_global_reserved := [] |>
End

Theorem ricf_witness_main_blocks[simp]:
  ricf_witness_main.fn_blocks = [
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
  ]
Proof
  simp[ricf_witness_main_def, mk_raw_function_def]
QED

Theorem ricf_witness_main_aliases[simp]:
  icf_assign_root (dfg_build_function ricf_witness_main) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ricf_witness_main) {} "%src" = "%src" /\
  dfg_get_def (dfg_build_function ricf_witness_main) "%dst" =
    SOME (mk_inst 2 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ricf_witness_main) "%src" =
    SOME (mk_inst 1 ALLOCA [Lit 32w] ["%src"]) /\
  icf_collect_aliases (dfg_build_function ricf_witness_main) "%dst" = {"%dst"} /\
  icf_collect_aliases (dfg_build_function ricf_witness_main) "%src" = {"%src"} /\
  icf_use_positions (dfg_build_function ricf_witness_main) "%src" =
    [(mk_inst 3 MSTORE [Var "%src"; Lit 99w] [], 0);
     (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 1)] /\
  icf_use_positions (dfg_build_function ricf_witness_main) "%dst" =
    [(mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 0);
     (mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"], 1)] /\
  icf_is_readonly_op (FEMPTY |+ ("callee", [T]) |+ ("main", []))
    (mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"]) 1 = T
Proof
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (irule icf_collect_aliases_no_assign >> EVAL_TAC)
  >- (irule icf_collect_aliases_no_assign >> EVAL_TAC)
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
QED

Theorem ricf_witness_rma:
  readonly_mem_analyze ricf_witness_ctx =
    FEMPTY |+ ("callee", [T]) |+ ("main", [])
Proof
  simp[readonly_mem_analyze_def, rma_analyze_def, icf_fn_meta_of_def,
       icf_fn_meta_of_fn_def, callLayoutDefsTheory.fn_user_param_insts_def,
       callLayoutDefsTheory.fn_entry_insts_def,
       default_internal_call_abi_def, ricf_witness_ctx_def,
       ricf_witness_callee_def, ricf_witness_main_def, mk_raw_function_def,
       mk_inst_def, entry_block_def, entry_param_outputs_def,
       collect_param_info_def, has_ret_instruction_def, build_param_index_def,
       rma_init_state_def, FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[rma_fixpoint_step_def, FLOOKUP_UPDATE, rma_analyze_fn_def,
       mem_write_ops_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[]
QED

Definition ricf_witness_bb1_def:
  ricf_witness_bb1 : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_nop_inst (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
         mk_inst 5 INVOKE [Label "callee"; Var "%src"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
End

Theorem ricf_witness_try_forward_3[simp]:
  ricf_try_forward
    (icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
       ricf_witness_ctx.ctx_functions
       (FEMPTY |+ ("callee", [T]) |+ ("main", []))
       ricf_witness_main)
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
    3 =
  SOME (SOME "%src",
        [(mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"], 1)])
Proof
  simp[ricf_try_forward_def, icf_build_ctx_def,
       icf_is_assign_output_use_def, findi_def, INDEX_FIND_def,
       icf_assign_root_op_def, ricf_has_mutable_sibling_def] >>
  EVAL_TAC
QED

Theorem ricf_witness_wf:
  o1_ctx_shape ricf_witness_ctx /\
  EVERY wf_ssa ricf_witness_ctx.ctx_functions /\
  EVERY ricf_full_alloca_copies ricf_witness_ctx.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling ricf_witness_ctx.ctx_functions
Proof
  rpt conj_tac
  >- (simp[o1_ctx_shape_def] >> rpt conj_tac
      >- EVAL_TAC
      >- EVAL_TAC
      >- (simp[ricf_witness_ctx_def] >> conj_tac
          >- (irule single_block_o1_fn_shape >>
              simp[ricf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
          >- (irule single_block_o1_fn_shape >>
              simp[ricf_witness_main_def, mk_raw_function_def] >> EVAL_TAC)))
  >- (simp[ricf_witness_ctx_def] >> conj_tac
      >- (irule single_block_wf_ssa >>
          simp[ricf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
      >- (irule single_block_wf_ssa >>
          simp[ricf_witness_main_def, mk_raw_function_def] >> EVAL_TAC))
  >- (simp[ricf_witness_ctx_def, ricf_full_alloca_copies_def] >>
      conj_tac
      >- (rw[ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[])
      >- (rw[mk_inst_def] >>
          gvs[icf_assign_root_op_def, icf_matches_alloca_size_def, mk_inst_def]))
  >- (simp[ricf_witness_ctx_def, ricf_no_derived_mutable_sibling_def] >>
      conj_tac
      >- (rw[ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[])
      >- (rw[mk_inst_def] >> gvs[]))
QED

Theorem ricf_block_step_non_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode <> MCOPY ==>
  ricf_block_step ctx (changed, cur_bb) i = (changed, cur_bb)
Proof
  rw[ricf_block_step_def]
QED

Theorem ricf_block_step_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode = MCOPY ==>
  ricf_block_step ctx (changed, cur_bb) i =
    case ricf_try_forward ctx cur_bb i of
      NONE => (changed, cur_bb)
    | SOME (src_var_opt, rewrite_sites) =>
        let src_op =
          case src_var_opt of
            SOME sv => Var sv
          | NONE =>
              EL 1 (EL i cur_bb.bb_instructions).inst_operands in
        let new_insts = ricf_apply_forward
          cur_bb.bb_instructions i src_op rewrite_sites in
        (T, cur_bb with bb_instructions := new_insts)
Proof
  rw[ricf_block_step_def]
QED

Theorem ricf_witness_step_1[simp]:
  ricf_function_step
    (icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
       ricf_witness_ctx.ctx_functions
       (FEMPTY |+ ("callee", [T]) |+ ("main", []))
       ricf_witness_main)
    ricf_witness_main =
  (T, ricf_witness_main with fn_blocks := [ricf_witness_bb1])
Proof
  `COUNT_LIST 7 = [0; 1; 2; 3; 4; 5; 6]` by EVAL_TAC >>
  simp[ricf_function_step_def] >>
  simp[ricf_pass_block_eq_foldl, ricf_apply_forward_def, mk_nop_inst_def,
       ricf_witness_bb1_def]
QED

Theorem ricf_witness_step_2[simp]:
  ricf_function_step
    ctx
    (ricf_witness_main with fn_blocks := [ricf_witness_bb1]) =
  (F, ricf_witness_main with fn_blocks := [ricf_witness_bb1])
Proof
  `COUNT_LIST 7 = [0; 1; 2; 3; 4; 5; 6]` by EVAL_TAC >>
  simp[ricf_function_step_def, ricf_witness_bb1_def] >>
  simp[ricf_pass_block_eq_foldl, mk_nop_inst_def]
QED

Theorem ricf_witness_forwards:
  FLOOKUP (readonly_mem_analyze ricf_witness_ctx) "callee" = SOME [T] /\
  ricf_transform_function
    (icf_fn_meta_of ricf_witness_ctx)
    ricf_witness_ctx.ctx_functions
    (readonly_mem_analyze ricf_witness_ctx)
    ricf_witness_main <> ricf_witness_main /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions)
    (ricf_transform_function
      (icf_fn_meta_of ricf_witness_ctx)
      ricf_witness_ctx.ctx_functions
      (readonly_mem_analyze ricf_witness_ctx)
      ricf_witness_main).fn_blocks
Proof
  simp[ricf_witness_rma, FLOOKUP_UPDATE] >>
  simp[ricf_transform_function_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[ricf_witness_bb1_def, clear_nops_function_def, clear_nops_block_def,
       mk_nop_inst_def] >>
  simp[ricf_witness_main_def, mk_raw_function_def, mk_inst_def]
QED

Theorem ricf_witness_no_dalloca[local]:
  ~ctx_has_dalloca ricf_witness_ctx
Proof
  EVAL_TAC
QED

Theorem ricf_witness_source_checks[local]:
  EVERY ricf_src_alloca ricf_witness_ctx.ctx_functions /\
  EVERY ricf_param_order_ok ricf_witness_ctx.ctx_functions
Proof
  conj_tac
  >- (simp[ricf_witness_ctx_def, ricf_src_alloca_def] >> conj_tac
      >- (rw[ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[] >>
          `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
      rw[mk_inst_def] >> gvs[] >>
      `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`
        by decide_tac >> gvs[] >>
      simp[icf_is_alloca_def, mk_inst_def] >> conj_tac
      >- (rw[ricf_witness_main_def, mk_raw_function_def, fn_insts_def,
              fn_insts_blocks_def, mk_inst_def, is_pointer_preserving_op_def] >>
          gvs[is_pointer_preserving_op_def]) >>
      rpt strip_tac >>
      `j = 3 \/ j = 4 \/ j = 5 \/ j = 6` by decide_tac >>
      gvs[mem_write_ops_def, mk_inst_def]) >>
  EVAL_TAC >> simp[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem ricf_witness_ptr_static[local]:
  EVERY (fn_ptr_ok (\nm. if nm = "callee" then {0} else {}))
    ricf_witness_ctx.ctx_functions /\
  EVERY (\f. fn_ptr_ok (\nm. if nm = "callee" then {0} else {})
    (reachable_fn f)) ricf_witness_ctx.ctx_functions /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) ricf_witness_ctx.ctx_functions
Proof
  `reachable_fn ricf_witness_callee = fn_reachable_blocks ricf_witness_callee` by
    (sym_tac >> irule fn_reachable_blocks_reachable_fn >> EVAL_TAC) >>
  `reachable_fn ricf_witness_main = fn_reachable_blocks ricf_witness_main` by
    (sym_tac >> irule fn_reachable_blocks_reachable_fn >> EVAL_TAC) >>
  ` (\nm:string. if nm = "callee" then {0:num} else {}) =
    (\nm. set (if nm = "callee" then [0] else []))` by
    (simp[FUN_EQ_THM] >> gen_tac >> IF_CASES_TAC >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[ricf_witness_ctx_def] >> rpt conj_tac
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- EVAL_TAC
  >- EVAL_TAC
QED

Theorem ricf_witness_callee_mem_safe[local]:
  !fuel s.
    s.vs_current_bb = "callee" /\ s.vs_params = [32w] /\
    64 <= s.vs_alloca_next ==>
    mem_safe_blocks (SUC fuel) ricf_witness_ctx ricf_witness_callee s
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once mem_safe_blocks_def, ricf_witness_callee_def,
    mk_raw_function_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once mem_safe_block_def, Once run_block_non_phis_def,
    get_instruction_def, mem_safe_step_def, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, update_var_def,
    is_terminator_def] >>
  simp[Once mem_safe_block_def, Once run_block_non_phis_def,
    get_instruction_def, mem_safe_step_def, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, update_var_def,
    is_terminator_def] >>
  simp[Once mem_safe_block_def, Once run_block_non_phis_def,
    get_instruction_def, mem_safe_step_def, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    update_var_def, is_terminator_def] >>
  simp[Once mem_safe_block_def, Once run_block_non_phis_def,
    get_instruction_def, mem_safe_step_def, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, is_terminator_def]
QED

Theorem ricf_witness_main_block_halts[local]:
  ?u. exec_block 2 ricf_witness_ctx (EL 0 ricf_witness_main.fn_blocks)
    (init_venom_state "main") = Halt u
Proof
  simp[ricf_witness_main_def, mk_raw_function_def,
    mk_inst_def, init_venom_state_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_alloca_def, eval_operand_def,
    update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_alloca_def, eval_operand_def,
    update_var_def, is_terminator_def, FLOOKUP_UPDATE] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    decode_invoke_def, lookup_function_def, ricf_witness_ctx_def,
    ricf_witness_callee_def, mk_raw_function_def, FIND_thm,
    eval_operands_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    setup_callee_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  qpat_abbrev_tac `value = mload _ _` >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def,
    update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def,
    eval_operands_def, lookup_var_def, FLOOKUP_UPDATE,
    empty_call_context_def, sstore_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, halt_state_def, is_terminator_def]
QED

Theorem ricf_witness_run_no_error[local]:
  !e. run_blocks 3 ricf_witness_ctx ricf_witness_main
    (init_venom_state "main") <> Error e
Proof
  qx_choose_then `u` strip_assume_tac ricf_witness_main_block_halts >>
  fs[Once run_blocks_def, ricf_witness_main_def, mk_raw_function_def,
    lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
    mk_inst_def, init_venom_state_def] >>
  qpat_x_assum `Halt u = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem ricf_witness_mem_safe_three[local]:
  mem_safe_blocks 3 ricf_witness_ctx ricf_witness_main
    (init_venom_state "main")
Proof
  qx_choose_then `u` strip_assume_tac ricf_witness_main_block_halts >>
  fs[ricf_witness_main_def, mk_raw_function_def, mk_inst_def,
    init_venom_state_def] >>
  simp[Once mem_safe_blocks_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  qpat_x_assum `Halt u = _` (SUBST1_TAC o SYM) >> simp[] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def,
    eval_operand_def, update_var_def, is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def,
    eval_operand_def, update_var_def, is_terminator_def, FLOOKUP_UPDATE] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    step_inst_def, step_inst_base_opcode_eqs, exec_write2_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.sized_source_write_range_def,
    step_inst_def, step_inst_base_opcode_eqs, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[Once mem_safe_block_def, mem_safe_step_def,
    get_instruction_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, decode_invoke_def,
    lookup_function_def, ricf_witness_ctx_def, ricf_witness_callee_def,
    mk_raw_function_def, FIND_thm, eval_operands_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, setup_callee_def] >>
  conj_tac
  >- (disj2_tac >> irule (SRULE [ricf_witness_ctx_def, ricf_witness_callee_def,
        mk_raw_function_def] (Q.SPEC `1` ricf_witness_callee_mem_safe)) >> simp[]) >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  qpat_abbrev_tac `value = mload _ _` >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def,
    update_var_def, is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, exec_write2_def,
    eval_operands_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    empty_call_context_def, sstore_def, is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, mem_safe_step_def,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    step_inst_def, step_inst_base_opcode_eqs, halt_state_def]
QED

val ricf_witness_ptr_clean =
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    ctx_has_dalloca_def, fn_insts_def, fn_insts_blocks_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    codegenRelTheory.sized_source_write_range_def,
    mem_read_ops_def, mem_write_ops_def, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE, op_prov_def, op_taint_def,
    RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM];

Theorem ricf_witness_ptr_safe_three[local]:
  ptr_safe_blocks
    (<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K UNIV |>)
    0 3 ricf_witness_ctx ricf_witness_main [] FEMPTY entry_taint
    (init_venom_state "main")
Proof
  simp[Once ptr_safe_blocks_def, ricf_witness_main_def, mk_raw_function_def,
    lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
    mk_inst_def, init_venom_state_def] >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``run_blocks``, ``ghost_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  conj_tac
  >- (simp[Once ptr_safe_blocks_def, lookup_block_def, FIND_thm,
        eval_phis_def, phi_prefix_length_def] >>
      simp[Once ptr_safe_block_def, get_instruction_def] >>
      computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
        ``mload``, ``word_to_bytes``, ``read_memory``] >>
      ricf_witness_ptr_clean >>
      simp[Once ptr_safe_block_def, get_instruction_def] >>
      computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
        ``mload``, ``word_to_bytes``, ``read_memory``] >>
      ricf_witness_ptr_clean >>
      simp[Once ptr_safe_block_def, get_instruction_def] >>
      computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
        ``mload``, ``word_to_bytes``, ``read_memory``] >>
      ricf_witness_ptr_clean >>
      simp[Once ptr_safe_block_def, get_instruction_def] >>
      computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
        ``mload``, ``word_to_bytes``, ``read_memory``] >>
      ricf_witness_ptr_clean >> simp[EXTENSION] >>
      qx_gen_tac `j` >> Cases_on `j < 32` >> simp[] >>
      `j + 32 < 64` by decide_tac >> simp[]) >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, update_var_def, is_terminator_def] >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, update_var_def, is_terminator_def] >>
  qpat_abbrev_tac `value = mload _ _` >>
  simp[Once run_block_non_phis_def, get_instruction_def, step_inst_def,
    step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, is_terminator_def] >>
  simp[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def,
    update_var_def, is_terminator_def] >>
  simp[Once ghost_blocks_def, lookup_block_def, FIND_thm,
    eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once ghost_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ghost_block``, ``ptr_inst_ok``,
    ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  simp[Once ghost_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ghost_block``, ``ptr_inst_ok``,
    ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  simp[Once ghost_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ghost_block``, ``ptr_inst_ok``,
    ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  simp[Once ghost_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >>
  simp[Once ptr_safe_block_def, get_instruction_def] >>
  computeLib.RESTR_EVAL_TAC [``ptr_inst_ok``, ``ptr_safe_block``, ``ptr_safe_blocks``,
    ``mload``, ``word_to_bytes``, ``read_memory``] >>
  ricf_witness_ptr_clean >> simp[EXTENSION] >> decide_tac
QED

Theorem ricf_witness_frontier_package[local]:
  ?J.
    reachability_closed J ricf_witness_ctx /\
    fn_entry_inv J ricf_witness_ctx ricf_witness_main
      (init_venom_state "main") /\
    (!f inst s. J ricf_witness_ctx f inst s ==>
       s.vs_alloca_next < dimword (:256))
Proof
  `!ir st. (adopt_return_fmp ir st).vs_alloca_next = st.vs_alloca_next` by
    (rpt gen_tac >> irule adopt_return_fmp_projection >> simp[]) >>
  qexists_tac `\c f i s.
    (f = ricf_witness_main /\
     s.vs_alloca_next <= 32 * MIN 2 s.vs_inst_idx) \/
    (f = ricf_witness_callee /\ s.vs_alloca_next <= 64)` >>
  simp[reachability_closed_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[active_inst_def, ricf_witness_main_def, ricf_witness_callee_def,
          mk_raw_function_def, MEM, mk_inst_def] >>
      `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/
       s.vs_inst_idx = 2 \/ s.vs_inst_idx = 3 \/
       s.vs_inst_idx = 4 \/ s.vs_inst_idx = 5 \/ s.vs_inst_idx = 6`
        by decide_tac >>
      gvs[EL, MIN_DEF, is_terminator_def] >>
      gvs[step_inst_def, step_inst_base_opcode_eqs] >>
      gvs[exec_alloca_def, exec_read1_def, exec_write2_def,
          eval_operands_def, eval_operand_def] >>
      gvs[lookup_var_def, update_var_def, mstore_def, mcopy_def,
          write_memory_with_expansion_def, sstore_def, decode_invoke_def] >>
      gvs[AllCaseEqs()] >>
      drule bind_outputs_shared_fields >> strip_tac >>
      gvs[])
  >- (rpt gen_tac >> strip_tac >>
      gvs[active_inst_def, ricf_witness_main_def, ricf_witness_callee_def,
          mk_raw_function_def, MEM, mk_inst_def] >>
      `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/
       s.vs_inst_idx = 2 \/ s.vs_inst_idx = 3 \/
       s.vs_inst_idx = 4 \/ s.vs_inst_idx = 5 \/ s.vs_inst_idx = 6`
        by decide_tac >>
      gvs[EL, is_terminator_def, step_inst_def,
          step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
          lookup_var_def, halt_state_def, AllCaseEqs()])
  >- (rpt gen_tac >> strip_tac >>
      gvs[active_inst_def, ricf_witness_main_def, ricf_witness_callee_def,
          mk_raw_function_def, MEM, mk_inst_def] >>
      `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/
       s.vs_inst_idx = 2 \/ s.vs_inst_idx = 3 \/
       s.vs_inst_idx = 4 \/ s.vs_inst_idx = 5 \/ s.vs_inst_idx = 6`
        by decide_tac >>
      gvs[EL, decode_invoke_def, lookup_function_def, FIND_thm,
          ricf_witness_ctx_def, ricf_witness_callee_def,
          ricf_witness_main_def, mk_raw_function_def,
          mk_inst_def, setup_callee_def] >>
      simp[fn_entry_inv_def, enters_block_def, lookup_block_def,
          FIND_thm, eval_phis_def, phi_prefix_length_def, mk_inst_def])
  >- (simp[fn_entry_inv_def, enters_block_def, lookup_block_def,
           ricf_witness_main_def, mk_raw_function_def, FIND_thm,
           eval_phis_def, phi_prefix_length_def, mk_inst_def,
           init_venom_state_def] >> rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `32 * MIN 2 s.vs_inst_idx <= 64` by
        (simp[MIN_DEF] >> rw[] >> decide_tac) >>
      `64 < dimword (:256)` by simp[dimword_def] >> decide_tac)
QED

(* Every premise of ricf_pass_correct holds on ricf_witness_ctx, and the pass
   changes it.  D treats every storage, transient, immutable and return-data
   byte as dead, as o1_pipeline_correct instantiates it. *)
Theorem ricf_pass_correct_nonvacuity:
  ?D lo vs.
    o1_ctx_shape ricf_witness_ctx /\
    EVERY wf_ssa ricf_witness_ctx.ctx_functions /\
    EVERY ricf_full_alloca_copies ricf_witness_ctx.ctx_functions /\
    EVERY ricf_no_derived_mutable_sibling ricf_witness_ctx.ctx_functions /\
    EVERY ricf_src_alloca ricf_witness_ctx.ctx_functions /\
    EVERY ricf_param_order_ok ricf_witness_ctx.ctx_functions /\
    ptr_discipline lo ricf_witness_ctx vs /\ mem_inv raw_mem_ok ricf_witness_ctx vs /\
    vs.vs_allocas = FEMPTY /\
    ~vs.vs_halted /\ ~ctx_has_dalloca ricf_witness_ctx /\
    taint_within D ricf_witness_ctx vs /\ dead_wf D /\
    ricf_transform_ctx (icf_fn_meta_of ricf_witness_ctx)
      (readonly_mem_analyze ricf_witness_ctx) ricf_witness_ctx <>
    ricf_witness_ctx
Proof
  `(init_venom_state "main" with
      <| vs_prev_bb := NONE; vs_current_bb := "main";
         vs_inst_idx := 0 |>) = init_venom_state "main" /\
   (init_venom_state "main").vs_alloca_next = 0 /\
   (init_venom_state "main").vs_allocas = FEMPTY /\
   ~(init_venom_state "main").vs_halted` by
    simp[init_venom_state_def] >>
  `!fuel. ptr_safe_blocks
     (<| d_stor := K (K UNIV); d_trans := K (K UNIV);
         d_imm := K UNIV; d_ret := K UNIV |>)
     0 fuel ricf_witness_ctx ricf_witness_main [] FEMPTY entry_taint
     (init_venom_state "main")` by
    (irule ptr_safe_blocks_all_fuel >> qexists_tac `3` >>
     simp[ricf_witness_ptr_safe_three, ricf_witness_run_no_error]) >>
  `!fuel. mem_safe_blocks fuel ricf_witness_ctx ricf_witness_main
     (init_venom_state "main")` by
    (irule mem_safe_blocks_all_fuel >> qexists_tac `3` >>
     simp[ricf_witness_mem_safe_three, ricf_witness_run_no_error]) >>
  `ricf_witness_ctx.ctx_entry = SOME "main" /\
   lookup_function "main" ricf_witness_ctx.ctx_functions =
     SOME ricf_witness_main /\
   fn_entry_label ricf_witness_main = SOME "main"` by EVAL_TAC >>
  `ptr_discipline 0 ricf_witness_ctx (init_venom_state "main") /\
   taint_within
     (<| d_stor := K (K UNIV); d_trans := K (K UNIV);
         d_imm := K UNIV; d_ret := K UNIV |>)
     ricf_witness_ctx (init_venom_state "main")` by
    (match_mp_tac (Q.SPECL
       [`<| d_stor := K (K UNIV); d_trans := K (K UNIV);
            d_imm := K UNIV; d_ret := K UNIV |>`, `0`,
        `\nm. if nm = "callee" then {0} else {}`,
        `ricf_witness_ctx`, `init_venom_state "main"`,
        `"main"`, `ricf_witness_main`, `"main"`]
       ptr_safe_ptr_discipline) >>
     simp[ricf_witness_ptr_static]) >>
  `mem_inv raw_mem_ok ricf_witness_ctx (init_venom_state "main")` by
    (rewrite_tac[GSYM raw_unit_memory_ok_mem_inv] >>
     qx_choose_then `J` strip_assume_tac ricf_witness_frontier_package >>
     match_mp_tac (Q.SPECL
       [`ricf_witness_ctx`, `init_venom_state "main"`, `"main"`,
        `ricf_witness_main`, `"main"`, `J`]
       mem_safe_raw_unit_memory_ok) >>
     simp[ricf_witness_ptr_static] >>
     qpat_x_assum `!f inst s. J _ _ _ _ ==> _` ACCEPT_TAC) >>
  qexistsl_tac
    [`<| d_stor := K (K UNIV); d_trans := K (K UNIV);
         d_imm := K UNIV; d_ret := K UNIV |>`, `0`,
     `init_venom_state "main"`] >>
  simp[ricf_witness_wf, ricf_witness_source_checks,
       ricf_witness_no_dalloca, dead_wf_def] >>
  strip_tac >>
  qpat_x_assum `ricf_transform_ctx _ _ _ = _`
    (mp_tac o Q.AP_TERM `\ctx. EL 1 ctx.ctx_functions`) >>
  simp[ricf_transform_ctx_def, ricf_witness_ctx_def] >>
  mp_tac ricf_witness_forwards >> simp[ricf_witness_ctx_def]
QED
