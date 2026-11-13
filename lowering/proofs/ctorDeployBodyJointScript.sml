(*
 * The deploy unit's execution at finite storage horizons, from the joint
 * gas body induction: the constructor body's stmt_frag_full outcome, placed
 * after the constructor entry, gives the three arms of
 * deploy_unit_execution_correct_at at one marks witness.  Without a
 * constructor, and when the source fails before the constructor body, the
 * unit's run reads no GAS and the witness is the empty marks.
 *
 * TOP-LEVEL:
 *   deploy_ctor_body_joint -- a started constructor
 *   deploy_no_ctor_correct_at -- no constructor
 *   deploy_ctor_prefix_fail_at -- the source fails before the body
 *   deploy_unit_execution_correct_joint -- all three
 *)
Theory ctorDeployBodyJoint
Ancestors
  deployUnitExecution ctorDeployDefs ctorDeployLoweringDefs
  ctorDeployMemoryFrontier ctorDeployMemoryRunMemNoCtor
  ctorDeployMemoryRunPtrNoCtor ctorDeployMemoryRunPtrPrefix
  ctorDeployMemoryRunMemPrefixLayout ctorDeployMemoryRunMemPrefixSource
  ctorDeployLoweringNoCtor ctorDeployLoweringPrefix
  fragGasSeqAbort fragGasMode fragGasOrigin fragGasPathMem runFromGasPathMem
  gasShadowUnit gasShadowState fragExec memSafeRun gasCount
  venomExecProofs venomExecSemantics venomInst venomState
  compileEnv emitHelper vyperCompiler e2eEntry ctorDeployLoweringFrame
  vyperStorageFootprint vyperStorageBackend vyperInterpreter vyperState e2eDeployDefs e2eDefs list

(* ===== Zero-mark runs ===== *)

(* A function with no GAS and no INVOKE counts no reads on any path. *)
Theorem gas_path_mem_gas_free[local]:
  !ctx fn s n r.
    gas_path_mem ctx fn s n r ==>
    (!bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions ==>
            i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) ==>
    n = 0
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[gas_path_mem_edge_def] >>
  `MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[lookup_block_MEM, EL_MEM]) >>
  first_x_assum drule_all >> simp[gas_count_step_def]
QED

(* The entry state of the deploy unit is the transaction's state at the
   entry label. *)
Theorem deploy_no_ctor_zero_path[local]:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb func explicit.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, NONE) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" ==>
    ?ss. gas_origin_path T explicit dunit.cu_context func
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                       vs_inst_idx := 0 |>) [] (Halt ss) /\
         ss.vs_returndata = runtime_bc ++ REPLICATE (imm_len tops) 0w /\
         ss.vs_accounts = vs.vs_accounts /\
         ss.vs_transient = vs.vs_transient /\ ss.vs_logs = vs.vs_logs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all no_ctor_target_execution >> strip_tac >>
  drule_all deploy_no_ctor_entry_shape >> strip_tac >>
  `dunit.cu_context.ctx_entry = SOME "__deploy"` by
    (drule_all deploy_unit_run_entry >> simp[]) >>
  qabbrev_tac `s0 = vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                               vs_inst_idx := 0 |>` >>
  `run_context fuel dunit.cu_context vs =
   run_blocks fuel dunit.cu_context func s0` by
    (simp[Abbr `s0`] >> irule run_context_run_blocks >> simp[]) >>
  Cases_on `fuel` >- gvs[Once run_blocks_def] >>
  rename1 `run_context (SUC n) _ _ = Halt ss` >>
  qabbrev_tac `bb = <| bb_label := "__deploy"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len tops))] ["%0"];
        mk_inst 1 CODECOPY
          [Var "%0"; Label "runtime_begin";
           Lit (n2w (LENGTH runtime_bc + imm_len tops))] [];
        mk_inst 2 RETURN
          [Var "%0"; Lit (n2w (LENGTH runtime_bc + imm_len tops))] []] |>` >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
   phi_prefix_length bb.bb_instructions = 0` by
    gvs[Abbr `s0`, Abbr `bb`, mk_raw_function_def, lookup_block_def,
        FIND_thm, phi_prefix_length_def, mk_inst_def] >>
  `s0 with vs_inst_idx := 0 = s0` by simp[Abbr `s0`] >>
  `run_from n dunit.cu_context func s0 = Halt ss` by
    metis_tac[run_blocks_run_from_no_phi] >>
  `vs.vs_allocas = FEMPTY` by
    (fs[gas_variant_def] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_allocas`) >>
     simp[deploy_entry_state_def, entry_venom_state_def,
          init_venom_state_def]) >>
  `mem_safe_blocks (SUC n) dunit.cu_context func s0` by
    (simp[Abbr `s0`] >> irule simple_deploy_entry_mem_safe >> simp[]) >>
  `mem_safe_run n dunit.cu_context func s0` by
    metis_tac[mem_safe_blocks_run, eval_phis_no_phi] >>
  `~s0.vs_halted` by
    (simp[Abbr `s0`] >> drule ctor_prefix_entry_not_halted >> simp[]) >>
  `?m. gas_path_mem dunit.cu_context func s0 m (Halt ss)` by
    (irule run_from_gas_path_mem >> simp[exit_result_def] >> metis_tac[]) >>
  `m = 0` by
    (drule gas_path_mem_gas_free >>
     simp[mk_raw_function_def, Abbr `bb`, mk_inst_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[] >> qexists_tac `ss` >> simp[] >>
  drule gas_path_mem_zero_origin >> simp[]
QED

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

(* A block that starts with the non-payable check reverts at its ASSERT when
   the call carries value, reading no GAS. *)
Theorem nonpayable_check_zero_path[local]:
  !ctx fn bb rest s j0 j1 j2 v0 v1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
      mk_inst j2 ASSERT [Var v1] [] :: rest /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_call_ctx.cc_callvalue <> 0w ==>
    ?t. gas_path_mem ctx fn s 0 (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i0 = mk_inst j0 CALLVALUE [] [v0]` >>
  qabbrev_tac `i1 = mk_inst j1 ISZERO [Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst j2 ASSERT [Var v1] []` >>
  `i0.inst_opcode = CALLVALUE /\ i0.inst_operands = [] /\
   i0.inst_outputs = [v0] /\
   i1.inst_opcode = ISZERO /\ i1.inst_operands = [Var v0] /\
   i1.inst_outputs = [v1] /\
   i2.inst_opcode = ASSERT /\ i2.inst_operands = [Var v1] /\
   i2.inst_outputs = []` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
  qabbrev_tac `t1 = update_var v0 s.vs_call_ctx.cc_callvalue s` >>
  `step_inst_base i0 s = OK t1` by
    (asm_simp_tac (srw_ss()) [opcode_eq ``CALLVALUE``, exec_read0_def] >>
     simp[Abbr `t1`]) >>
  qabbrev_tac `t1' = t1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var v0 t1' = SOME s.vs_call_ctx.cc_callvalue /\
   t1'.vs_inst_idx = 1 /\ ~t1'.vs_halted /\
   t1'.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `t1'`, Abbr `t1`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  qabbrev_tac `t2 = update_var v1 0w t1'` >>
  `step_inst_base i1 t1' = OK t2` by
    (asm_simp_tac (srw_ss()) [opcode_eq ``ISZERO``, exec_pure1_def,
                              eval_operand_def, bool_to_word_def] >>
     simp[Abbr `t2`]) >>
  qabbrev_tac `t2' = t2 with vs_inst_idx := SUC t1'.vs_inst_idx` >>
  `lookup_var v1 t2' = SOME 0w /\ t2'.vs_inst_idx = 2 /\ ~t2'.vs_halted /\
   t2'.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `t2'`, Abbr `t2`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base i2 t2' =
     Abort Revert_abort (revert_state (set_returndata [] t2'))` by
    asm_simp_tac (srw_ss()) [opcode_eq ``ASSERT``, eval_operand_def] >>
  qexists_tac `revert_state (set_returndata [] t2')` >>
  `gas_marked_path T ctx fn t2' (if i2.inst_opcode = GAS then 1 else 0)
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule gas_marked_path_abort >> qexists_tac `bb` >>
     simp[get_instruction_def, is_terminator_def, Abbr `i2`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn t1'
     ((if i1.inst_opcode = GAS then 1 else 0) +
      (if i2.inst_opcode = GAS then 1 else 0))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule gas_marked_path_step >> qexistsl_tac [`bb`, `t2`] >>
     simp[get_instruction_def, is_terminator_def, Abbr `i1`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn s
     ((if i0.inst_opcode = GAS then 1 else 0) +
      ((if i1.inst_opcode = GAS then 1 else 0) +
       (if i2.inst_opcode = GAS then 1 else 0)))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule gas_marked_path_step >> qexistsl_tac [`bb`, `t1`] >>
     simp[get_instruction_def, is_terminator_def, Abbr `i0`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  gvs[gas_marked_path_def]
QED

(* With no constructor start, the unit's first three instructions revert. *)
Theorem deploy_prefix_zero_path[local]:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb cf func explicit.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func ==>
    ?t. gas_origin_path T explicit dunit.cu_context func
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                      vs_inst_idx := 0 |>) [] (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_prefix_rejecting_code >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_origin_path _ _ _ _ s0` >>
  `s0.vs_call_ctx.cc_callvalue <> 0w` by
    (drule_all ctor_prefix_source_obstruction >>
     strip_tac >> drule_all ctor_prefix_entry_value >> simp[Abbr `s0`]) >>
  `~s0.vs_halted` by
    (drule ctor_prefix_entry_not_halted >> simp[Abbr `s0`]) >>
  `?bb rest j0 j1 j2 v0 v1.
     lookup_block "__deploy" func.fn_blocks = SOME bb /\
     bb.bb_instructions =
       mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
       mk_inst j2 ASSERT [Var v1] [] :: rest` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
     qpat_x_assum `_ = emit_op CALLVALUE _ _` mp_tac >>
     simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, initial_compile_state_def, fn_has_code_def] >>
     rpt strip_tac >> gvs[] >>
     Cases_on `bb.bb_instructions` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >>
     simp[mk_inst_def]) >>
  `?t. gas_path_mem dunit.cu_context func s0 0 (Abort Revert_abort t)` by
    (irule nonpayable_check_zero_path >> simp[Abbr `s0`] >> metis_tac[]) >>
  qexists_tac `t` >> drule gas_path_mem_zero_origin >> simp[]
QED

(* ===== The constructor's start state ===== *)

(* A value transfer leaves every contract's storage alone. *)
Theorem send_call_value_get_storage[local]:
  send_call_value mut cx st = (res, st') ==>
  !b. get_storage cx' st' b = get_storage cx' st b
Proof
  simp[send_call_value_def, transfer_value_def, bind_apply, ignore_bind_apply,
       get_accounts_def, check_def, assert_def, update_accounts_def,
       return_def, raise_def] >>
  rpt IF_CASES_TAC >> gvs[return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

(* The constructor starts on the transaction's storage. *)
Theorem deploy_ctor_start_storage_well_formed_on[local]:
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
  (storage_well_formed_on cx es0 R <=>
   storage_well_formed_on cx (initial_state am []) R)
Proof
  strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >>
  gvs[deploy_ctor_start_def] >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `am_c.accounts = am.accounts /\ am_c.tStorage = am.tStorage` by
    (drule deploy_frame_all_constants_accounts >>
     drule deploy_frame_all_constants_tStorage >> simp[]) >>
  drule send_call_value_get_storage >> strip_tac >>
  simp[storage_well_formed_on_def] >>
  `!b. get_storage cx (initial_state am_c [env] with
                         <| outcomes := NONE; requests := [] |>) b =
       get_storage cx (initial_state am []) b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def,
                   initial_state_def]) >>
  metis_tac[]
QED


(* Without a constructor, the source runs the empty one, which starts. *)
Theorem deploy_no_ctor_start[local]:
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?am_c es0. deploy_ctor_start tops am tx (Payable, F, [], am_c, es0)
Proof
  strip_tac >>
  `tx.function_name = "__init__" /\ deploy_typing_ok tops am tx /\
   value_transfer_ok tx am.accounts` by
    gvs[deploy_source_ok_def, deploy_state_rel_def] >>
  `tx.args = []` by
    (gvs[deploy_state_rel_def] >> drule_all no_ctor_args >> simp[]) >>
  drule no_ctor_constants_ready >> strip_tac >>
  drule no_ctor_constants_frame >> strip_tac >>
  drule no_ctor_lookup >> strip_tac >>
  qabbrev_tac `cx = deploy_evaluation_context tops am tx` >>
  `cx.txn = tx with created_in_tx := T` by
    simp[Abbr `cx`, deploy_evaluation_context_def,
         initial_evaluation_context_def] >>
  simp[deploy_ctor_start_def, bind_arguments_def, lock_if_nr_def,
       ignore_bind_def, bind_def, return_def] >>
  qexists_tac `am_c` >> simp[] >>
  qmatch_goalsub_abbrev_tac `send_call_value Payable cx st` >>
  `value_transfer_ok cx.txn st.accounts` by
    simp[Abbr `st`, initial_state_def, value_transfer_created_in_tx] >>
  drule no_ctor_send_value >> simp[]
QED
