(*
 * The deploy unit's execution at finite storage horizons, from the joint
 * gas body induction: the constructor body's stmt_frag_full outcome, placed
 * after the constructor entry, gives the three arms of
 * deploy_unit_execution_correct_at at one marks witness.  Without a
 * constructor, and when the source fails before the constructor body, the
 * unit's run reads no GAS and the witness is the empty marks.
 *
 * The constructor arm starts at the selected raw FMP.
 *)
Theory ctorDeployBodyJoint
Ancestors
  fnPlanPlaceRevertPostamble asmOptimizer deployUnitProducers ptrDiscipline
  bodyFullShadowBodyInv
  deployUnitExecution ctorDeployDefs ctorDeployLoweringDefs
  ctorDeployMemoryFrontier ctorDeployMemoryRunMemNoCtor
  ctorDeployMemoryRunPtrNoCtor ctorDeployMemoryRunPtrPrefix
  ctorDeployMemoryRunMemPrefixLayout ctorDeployMemoryRunMemPrefixSource
  ctorDeployLoweringNoCtor ctorDeployLoweringPrefix simpleDeployRaw
  fragGasSeqAbort fragGasMode fragGasOrigin fragGasPathMem runFromGasPathMem
  gasShadowUnit gasShadowState fragExec memSafeRun gasCount
  venomExecProofs venomExecProps venomExecSemantics venomInst venomState
  compileEnv emitHelper vyperCompiler e2eEntry ctorDeployLoweringFrame
  vyperStorageFootprint vyperStorageBackend vyperInterpreter vyperState e2eDeployDefs e2eDefs list
  ctorDeployBodyFallthrough ctorDeployMemoryRunPtrFrameRet
  ctorReturnFrame bodyFullShared fragGasEmitCtrl bodyPtrDefs
  ctorDeployLoweringArms gasShadowUnitGuards gasShadowState
  ctorDeployBodySimulation ctorDeployBodyShadow ctorDeployLoweringEntry
  deployBodyReachability allocaBudgetProps unitTransformDefs contextRawReachable
  ctorDeployLoweringEntryTransport
  ctorDeployLoweringReturn ctorDeployLoweringHaltCode ctorDeployDead
  gasShadowStmtEnv gasOutcomeFull gasOutcomeFullCompose gasStorage gasExemptCert
  fragGasOriginPtr fragGasOriginPtrExec fragExecPtr loweringShapeDefs
  bodySimFull bodySim loweringPosts stmtSimDefs stmtSimProps exprLowering
  ctorDeployLoweringCode ctorDeployLoweringEntryPrefix
  ctorDeployLoweringSource ctorDeployLoweringSourceOk
  ctorDeployMemoryRunPtrPrefixInit gasContext
  ctorDeployLoweringFrameRet loweringStateRelDefs
  entryStateRel exprSimDefs loweringHalt vyperTypeDeploymentMachine evalNoHalt
  codegenRel contextCodegenRel o1PassContract

val _ = Parse.hide "body";

(* ===== Zero-mark runs ===== *)

(* The entry state of the deploy unit is the transaction's state at the
   entry label. *)
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
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `t2'`, `bb`, `i2`,
       `Revert_abort`, `revert_state (set_returndata [] t2')`]
       gas_marked_path_abort) >>
     simp[get_instruction_def, is_terminator_def, Abbr `i2`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn t1'
     ((if i1.inst_opcode = GAS then 1 else 0) +
      (if i2.inst_opcode = GAS then 1 else 0))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `t1'`, `bb`, `i1`, `t2`,
       `if i2.inst_opcode = GAS then 1 else 0`,
       `Abort Revert_abort (revert_state (set_returndata [] t2'))`]
       gas_marked_path_step) >>
     gvs[get_instruction_def, is_terminator_def, Abbr `i1`, Abbr `t2'`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `gas_marked_path T ctx fn s
     ((if i0.inst_opcode = GAS then 1 else 0) +
      ((if i1.inst_opcode = GAS then 1 else 0) +
       (if i2.inst_opcode = GAS then 1 else 0)))
     (Abort Revert_abort (revert_state (set_returndata [] t2')))` by
    (irule (Q.SPECL [`T`, `ctx`, `fn`, `s`, `bb`, `i0`, `t1`,
       `(if i1.inst_opcode = GAS then 1 else 0) +
        (if i2.inst_opcode = GAS then 1 else 0)`,
       `Abort Revert_abort (revert_state (set_returndata [] t2'))`]
       gas_marked_path_step) >>
     gvs[get_instruction_def, is_terminator_def, Abbr `i0`, Abbr `t1'`, mk_inst_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  gvs[gas_marked_path_def]
QED

(* A contract without a constructor returns its runtime code and zeroed immutables. *)
Theorem deploy_no_ctor_zero_path[local]:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   off exts ints fb func explicit.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
    off < dimword(:256) /\ DROP off (assemble prog') = runtime_bc /\
    classify_functions tops = (exts, ints, fb, NONE) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" ==>
    ?ss. gas_origin_path T explicit dunit.cu_context func
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                       vs_inst_idx := 0 |>) [] (Halt ss) /\
         ss.vs_returndata = runtime_bc ++ REPLICATE (imm_len tops) 0w /\
         ss.vs_accounts = vs.vs_accounts /\
         ss.vs_transient = vs.vs_transient /\ ss.vs_logs = vs.vs_logs /\
         ss.vs_pending_deletions = vs.vs_pending_deletions /\
         ss.vs_requests = vs.vs_requests
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
    (qspecl_then [`fuel`, `dunit.cu_context`, `vs`, `"__deploy"`,
       `func`, `"__deploy"`] mp_tac run_context_run_blocks >> simp[Abbr `s0`]) >>
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
     qpat_x_assum `(opt_deploy_entry_state_own _ _ _ _ _ with vs_outcomes := _) = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_allocas`) >>
     simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def,
          init_venom_state_def]) >>
  `mem_safe_blocks (SUC n) dunit.cu_context func s0` by
    (simp[Abbr `s0`, Abbr `bb`] >> irule simple_deploy_entry_mem_safe >> simp[]) >>
  `mem_safe_run n dunit.cu_context func s0` by
    metis_tac[mem_safe_blocks_run, eval_phis_no_phi] >>
  `~s0.vs_halted` by
    (simp[Abbr `s0`] >> drule ctor_prefix_entry_not_halted >> simp[]) >>
  `?m. gas_path_mem dunit.cu_context func s0 m (Halt ss)` by
    (irule run_from_gas_path_mem >> simp[exit_result_def] >> metis_tac[]) >>
  `!bb i. MEM bb func.fn_blocks /\ MEM i bb.bb_instructions ==>
      i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (simp[mk_raw_function_def, Abbr `bb`, mk_inst_def] >>
     rpt strip_tac >> gvs[]) >>
  `m = 0` by metis_tac[gas_path_mem_gas_free] >>
  gvs[] >> qexists_tac `ss` >> simp[] >>
  drule gas_path_mem_zero_origin >> simp[]
QED

(* With no constructor start, the unit's first three instructions revert. *)
Theorem deploy_prefix_zero_path[local]:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   exts ints fb cf func explicit.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs.vs_call_ctx.cc_callvalue <> 0w /\ ~vs.vs_halted /\
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
  `?bb rest j0 j1 j2 v0 v1.
     lookup_block "__deploy" func.fn_blocks = SOME bb /\
     bb.bb_instructions =
       mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
       mk_inst j2 ASSERT [Var v1] [] :: rest` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
     qpat_x_assum `emit_op CALLVALUE _ _ = _` mp_tac >>
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
  `!b. get_storage cx es0 b =
       get_storage cx (initial_state am_c [env] with
                         <| outcomes := NONE; requests := [] |>) b` by
    (drule send_call_value_accounts >> strip_tac >> Cases >>
     rw[vyperStorageBackendTheory.get_storage_def,
        accounts_after_transfer_def, LET_THM,
        vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
        combinTheory.APPLY_UPDATE_THM] >> rpt IF_CASES_TAC >> gvs[]) >>
  simp[storage_well_formed_on_def] >>
  `!b. get_storage cx (initial_state am_c [env] with
                         <| outcomes := NONE; requests := [] |>) b =
       get_storage cx (initial_state am []) b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def,
                   initial_state_def]) >>
  metis_tac[]
QED

Theorem deploy_ctor_start_storage_well_formed_outcomes[local]:
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
  (storage_well_formed_on cx (es0 with outcomes := oc) R <=>
   storage_well_formed_on cx (initial_state am []) R)
Proof
  strip_tac >> drule_all deploy_ctor_start_storage_well_formed_on >>
  `storage_well_formed_on cx (es0 with outcomes := oc) R <=>
   storage_well_formed_on cx es0 R` by
    (irule storage_well_formed_on_backends >> simp[]) >> simp[]
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
  drule no_ctor_send_value >> gvs[Abbr `cx`, Abbr `st`]
QED

(* The empty constructor fixes the source result without consulting either
   the gas stream or the outcome oracle. *)
Theorem deploy_joint_terminal_with[local]:
  dunit.cu_context.ctx_entry = SOME "__deploy" /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  gas_shadow_context dunit.cu_context shadow_ctx /\
  gas_shadow_function func shadow_func /\
  MEM func dunit.cu_context.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  (!tail. load_contract_trace (SOME vs.vs_outcomes)
     (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
     [(NONE, tops)] [] = (src, obs)) /\
  exit_result r /\
  storage_trace_domain (deploy_evaluation_context tops am tx)
    (initial_state am []) obs /\
  (!H. valid_horizon (deploy_evaluation_context tops am tx)
         (initial_state am []) H obs ==>
    gas_origin_ptr_path
      (deploy_dead H tops runtime_bc am tx, imm_len tops,
       gas_explicit_sites dunit.cu_context shadow_ctx,
       dunit.cu_context, func, [])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0|>, FEMPTY, entry_taint)
      [] (OK s0, G0, tn0) /\
    ((!fuel. ptr_safe_run (deploy_dead H tops runtime_bc am tx)
         (imm_len tops) fuel dunit.cu_context func [] G0 tn0 s0) ==>
      !fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
        (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                   vs_inst_idx := 0|>)) /\
    gas_origin_ptr_path
      (deploy_dead H tops runtime_bc am tx, imm_len tops,
       gas_explicit_sites dunit.cu_context shadow_ctx,
       dunit.cu_context, func, [])
      (s0, G0, tn0) marks (r, G1, tn1) /\
    deploy_venom_result_rel H tops runtime_bc tx src r) ==>
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx dunit vs
Proof
  strip_tac >>
  `valid_horizon (deploy_evaluation_context tops am tx)
     (initial_state am []) (storage_trace_horizon obs) obs` by
    fs[storage_trace_domain_def] >>
  `gas_origin_path T (gas_explicit_sites dunit.cu_context shadow_ctx)
     dunit.cu_context func
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                vs_inst_idx := 0|>) marks r` by
    (first_x_assum drule >> strip_tac >>
     qpat_x_assum `gas_origin_ptr_path _ _ [] (OK s0, G0, tn0)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >> simp[] >>
     disch_then drule_all >>
     metis_tac[gas_origin_ptr_path_projections]) >>
  rewrite_tac[deploy_unit_execution_correct_with_def] >>
  qexistsl_tac [`func`, `shadow_func`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac [`src`, `obs`] >> (conj_tac >- simp[]) >>
  disj2_tac >> qexists_tac `r` >> simp[] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  `!fuel. ptr_safe_run (deploy_dead H tops runtime_bc am tx)
     (imm_len tops) fuel dunit.cu_context func [] G0 tn0 s0` by
    (qpat_x_assum `gas_origin_ptr_path _ (s0, G0, tn0) _ _`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_exec) >>
     fs[exit_result_def] >>
     metis_tac[ptr_safe_run_all_fuel, exit_result_not_error]) >>
  metis_tac[]
QED

Theorem deploy_no_ctor_trace[local]:
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?src. !orc gs.
    load_contract_trace orc gs am tx [(NONE, tops)] [] = (src, [])
Proof
  strip_tac >> drule_all deploy_no_ctor_start >> strip_tac >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `es0.storage_trace = []` by metis_tac[deploy_ctor_start_storage_trace] >>
  qspecl_then [`tops`, `am`, `tx`, `Payable`, `[]`, `am_c`, `es0`]
    mp_tac deploy_ctor_source_trace >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `deploy_ctor_finish tops tx
    (deploy_evaluation_context tops am tx) F Payable am_c (INL ()) es0` >>
  rpt gen_tac >>
  qpat_x_assum `!orc gobs res st. _`
    (qspecl_then [`orc`, `gs`, `INL ()`,
      `es0 with <| gas_obs := gs; outcomes := orc |>`] mp_tac) >>
  simp[Once evaluate_def, return_def, deploy_ctor_finish_def,
       unlock_if_nr_def, abstract_machine_from_state_def]
QED

Theorem deploy_no_ctor_correct_with:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   off exts ints fb.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
    off < dimword(:256) /\ DROP off (assemble prog') = runtime_bc /\
    classify_functions tops = (exts, ints, fb, NONE) ==>
    deploy_unit_execution_correct_with dunit.cu_context [] tops runtime_bc am tx dunit vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_no_ctor_entry_shape >> strip_tac >>
  qpat_x_assum `fn = mk_raw_function _ _` kall_tac >>
  qpat_x_assum `DROP off (assemble prog') = runtime_bc`
    (fn th => gvs[] >> assume_tac th) >>
  drule_all deploy_no_ctor_trace >> strip_tac >>
  `!gs. load_contract NONE gs am tx [(NONE, tops)] [] = src` by
    simp[load_contract_def] >>
  `MEM fn dunit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `gas_shadow_context dunit.cu_context dunit.cu_context /\
   gas_shadow_function fn fn` by
    simp[gas_shadow_context_def, gas_shadow_function_def, LIST_REL_refl,
         gas_shadow_block_def, gas_shadow_inst_def] >>
  drule_all deploy_no_ctor_zero_path >>
  disch_then (qspec_then
    `gas_explicit_sites dunit.cu_context dunit.cu_context` strip_assume_tac) >>
  rewrite_tac[deploy_unit_execution_correct_with_def] >>
  qexistsl_tac [`fn`, `fn`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac [`src`, `[]`] >> (conj_tac >- simp[]) >>
  disj2_tac >> qexists_tac `Halt ss` >>
  simp[exit_result_def] >> (conj_tac >- (EVAL_TAC >> simp[])) >>
  gen_tac >> strip_tac >> conj_tac
  >- (drule_all (INST_TYPE [``:'a`` |-> ``:256``] no_ctor_source_halt) >>
      simp[] >> metis_tac[]) >>
  irule deploy_no_ctor_run_ptr_safe >> simp[] >> metis_tac[]
QED

Theorem deploy_prefix_trace[local]:
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  (!mut nr body am_c es0.
     ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
  !orc gs. load_contract_trace orc gs am tx [(NONE, tops)] [] =
    (INR (Error (RuntimeError "not Payable")), [])
Proof
  strip_tac >> drule_all deploy_prefix_no_start_nonpayable >> strip_tac >>
  `deploy_typing_ok tops am tx /\ tx.function_name = "__init__"` by
    fs[deploy_source_ok_def, deploy_state_rel_def] >>
  drule deploy_prefix_constants_ready >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by
    (drule_all deploy_prefix_constructor_binding >> strip_tac >> gvs[]) >>
  `evaluate_module_constants_trace (deploy_evaluation_context tops am tx)
     (am with <| immutables updated_by CONS (tx.target, imms);
                 exports updated_by CONS (tx.target, []) |>)
     tx.target (constants_order [(NONE, tops)]) = (SOME am_c, [])` by
    (drule_all deploy_constants_trace_nil >>
     qpat_x_assum `evaluate_all_constants _ _ _ _ = _` mp_tac >>
     simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
     Cases_on `evaluate_module_constants_trace
       (deploy_evaluation_context tops am tx)
       (am with <| immutables updated_by CONS (tx.target, imms);
                   exports updated_by CONS (tx.target, []) |>)
       tx.target (constants_order [(NONE, tops)])` >> gvs[]) >>
  `deploy_evaluation_context tops
     (am with <| exports updated_by CONS (tx.target, []);
                 immutables updated_by CONS (tx.target, imms) |>) tx =
   deploy_evaluation_context tops am tx` by simp[deploy_evaluation_context_def] >>
  rpt gen_tac >>
  simp[load_contract_trace_def, GSYM deploy_evaluation_context_def] >>
  simp[call_external_function_trace_def] >>
  simp[send_call_value_def, deploy_evaluation_context_def,
       initial_evaluation_context_def, ignore_bind_def, bind_def,
       check_def, assert_def, raise_def, initial_state_def] >>
  gvs[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_ctor_prefix_fail_with_fields:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs
   exts ints fb cf shadow_ctx fn shadow_func.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs.vs_call_ctx.cc_callvalue <> 0w /\ ~vs.vs_halted /\
    vs.vs_allocas = FEMPTY /\ allocas_below_fmp vs /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__deploy" /\
    gas_shadow_context dunit.cu_context shadow_ctx /\
    gas_shadow_function fn shadow_func /\
    MEM shadow_func shadow_ctx.ctx_functions ==>
    deploy_unit_execution_correct_with shadow_ctx [] tops runtime_bc am tx dunit vs
Proof
  rpt gen_tac >> strip_tac >>
  `dunit.cu_context.ctx_entry = SOME "__deploy"` by
    metis_tac[deploy_phases_def, deployUnitProducersTheory.lower_vyper_deploy_unit_entry] >>
  drule_all ctor_prefix_task_entry_label >> strip_tac >> gvs[] >>
  drule_all deploy_prefix_trace >> strip_tac >>
  `!marks. ~deploy_source_exempt tops
      (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
        [(NONE, tops)] [])` by
    simp[load_contract_def, deploy_source_exempt_def,
         unspecified_behaviour_exempt_def] >>
  `MEM fn dunit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all deploy_prefix_zero_path >>
  disch_then (qspec_then
    `gas_explicit_sites dunit.cu_context shadow_ctx` strip_assume_tac) >>
  rewrite_tac[deploy_unit_execution_correct_with_def] >>
  qexistsl_tac [`fn`, `shadow_func`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "not Payable"))`, `[]`] >>
  (conj_tac >- simp[]) >> disj2_tac >> qexists_tac `Abort Revert_abort t` >>
  simp[exit_result_def, deploy_venom_result_rel_def] >>
  (conj_tac >- (EVAL_TAC >> simp[])) >> gen_tac >> strip_tac >>
  irule deploy_ctor_prefix_fail_run_ptr_safe_fields >> simp[] >> metis_tac[]
QED

Theorem deploy_ctor_body_halt_pending:
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,F,raw_body,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) raw_body
    (es0 with <|outcomes := SOME os; gas_obs := gs|>) = (INR HaltException,ee) ==>
  MEM tx.target ee.pending_deletions
Proof
  strip_tac >>
  drule eval_stmts_halt_pending_deletions >>
  simp[deploy_evaluation_context_def, vyperInterpreterTheory.initial_evaluation_context_def]
QED

(* Entry, body and suffix share the body's marks, including its focused arms. *)
Theorem deploy_ctor_halt_result[local]:
  deploy_ctor_start tops am tx (mut,nr,raw_body,am_c,es0) /\
  deploy_state_rel tops bc am tx es /\
  halt_rel H (deploy_evaluation_context tops am tx) ee ss /\
  ss.vs_returndata = [] /\
  MEM tx.target ee.pending_deletions ==>
  deploy_venom_result_rel H tops runtime_bc tx
    (INL (finalize_pending_deletions
      (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts ee),
      ee.requests)) (Halt ss)
Proof
  strip_tac >>
  `am_c.sources = am.sources` by
    (qpat_x_assum `deploy_ctor_start _ _ _ _` mp_tac >>
     simp[deploy_ctor_start_def] >> rpt strip_tac >>
     drule evaluate_all_constants_preserves_machine_static_components >>
     simp[]) >>
  `ALOOKUP am_c.sources tx.target = NONE` by fs[deploy_state_rel_def] >>
  qspecl_then [`H`, `deploy_evaluation_context tops am tx`, `ee`, `ss`,
    `tops`, `tx`, `(deploy_evaluation_context tops am tx).sources`,
    `am_c.exports`, `(deploy_evaluation_context tops am tx).layouts`] mp_tac
    external_halt_rel_success >>
  impl_tac >- simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
  fs[deploy_venom_result_rel_def, halt_rel_def,
     abstract_machine_from_state_def, finalize_pending_deletions_def,
     initial_evaluation_context_def] >> gvs[]
QED

Theorem deploy_ctor_body_joint_raw_with:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan off am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut nr' body' am_c es0 shadow_ctx shadow_func shadow_sa shadow_sb.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
    off < dimword(:256) /\ off <= LENGTH (assemble prog') /\
    DROP off (assemble prog') = runtime_bc /\
    raw_variant vs.vs_initial_fmp vs
      (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    (ctx_has_dalloca dunit.cu_context ==>
      imm_len tops + unit_alloca_budget dunit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    (ctx_has_dalloca dunit.cu_context ==> !fn inst s.
      raw_reachable vs dunit.cu_context fn inst s ==> dalloca_fmp_headroom inst s) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) /\
    shadow_body_inv tops dunit.cu_context shadow_ctx /\
    gas_shadow_context dunit.cu_context shadow_ctx /\
    gas_shadow_function func shadow_func /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    compile_stmts (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body) shadow_sa =
      ((), shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code shadow_sa shadow_sb shadow_func ==>
    ?marks.
      deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx dunit vs
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (FLOOKUP (lo_reloc prog prog') "runtime_begin")` by simp[] >>
  drule_all deploy_ctor_entry_joint_raw >> strip_tac >>
  qpat_x_assum `nr' = nr` SUBST_ALL_TAC >>
  `nr = F` by metis_tac[deploy_ctor_not_nonreentrant] >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_ctor_code_def] >>
  `!os gx. eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <|outcomes := os; gas_obs := gx|>) =
    eval_stmts (deploy_evaluation_context tops am tx) body'
      (es0 with <|outcomes := os; gas_obs := gx|>)` by
    (gvs[] >> drule_all deploy_ctor_body_substitution >> simp[]) >>
  qpat_x_assum `body = subst_consts_stmts _ body'` kall_tac >>
  drule deploy_ctor_return_metadata >> strip_tac >>
  drule_all deploy_ctor_immutable_size >> strip_tac >>
  qspecl_then [`tops`, `am`, `tx`, `mut`, `nr`, `body`, `body'`, `am_c`, `es0`,
    `rpolicy`, `runtime_bc`, `dunit`, `cenv`, `nkey`, `ut`, `imm`,
    `exit_lbl`, `sa`, `sb`, `sj`, `st_exit`, `st_epilogue`, `st_final`,
    `func`, `assemble prog'`, `es`] mp_tac deploy_ctor_immutable_epilogue >>
  impl_tac >- simp[] >> disch_tac >>
  `supported_program tops /\ supported_program_deploy tops /\
   tx.function_name = "__init__"` by fs[deploy_source_ok_def, deploy_state_rel_def] >>
  `cx_tops (deploy_evaluation_context tops am tx) = tops` by
    simp[cx_tops_def, deploy_evaluation_context_def,
         initial_evaluation_context_def, vyperContextTheory.get_module_code_def] >>
  drule_all deploy_ctor_original_entry_shape >> strip_tac >>
  `!bb label. lookup_block label func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all deploy_ctor_raw_blocks_no_phi >> simp[]) >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `enters_block func entry entry` by
    simp[enters_block_def, Abbr `entry`, eval_phis_no_phi, venom_state_fupdfupds] >>
  `!i. active_inst func i entry ==> raw_reachable vs dunit.cu_context func i entry` by
    (rpt strip_tac >> irule raw_reachable_entry >> fs[Abbr `entry`]) >>
  `!i. active_inst func i s0 ==> raw_reachable vs dunit.cu_context func i s0` by
    (rpt strip_tac >>
     qpat_assum `gas_path _ _ entry 0 (OK s0)` (fn path =>
       irule raw_reachable_gas_path >> irule_at Any path >> simp[] >>
       first_assum ACCEPT_TAC)) >>
  `es0.storage_trace = []` by
    (irule deploy_ctor_start_storage_trace >> gvs[] >> metis_tac[]) >>
  `MEM func dunit.cu_context.ctx_functions /\ fn_inst_ids_distinct func /\
   compile_stmts cenv NoLoop NoneT body sa = ((), sb) /\
   fn_has_code sa sb func /\ fn_has_code sb sj func /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   st_epilogue = st_exit /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
     st_exit = ((), st_final) /\ fn_has_code st_exit st_final func /\
   (~block_is_terminated sb ==>
      emit_inst JMP [Label exit_lbl] [] sb = ((), sj))` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, comp_return_def, new_block_def] >>
     rpt strip_tac >> FIRST [gvs[]]) >>
  `SND (stmts_env cenv NoLoop NoneT body sa) = sb /\
   SND (stmts_env (gas_shadow_env T cenv) NoLoop NoneT
          (MAP gas_shadow_stmt body) shadow_sa) =
     shadow_sb` by fs[compile_stmts_env] >>
  qabbrev_tac `cenv' = FST (stmts_env cenv NoLoop NoneT body sa)` >>
  `stmts_env cenv NoLoop NoneT body sa = (cenv', sb)` by
    (Cases_on `stmts_env cenv NoLoop NoneT body sa` >> fs[Abbr `cenv'`]) >>
  `stmts_env (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body)
     shadow_sa = (gas_shadow_env T cenv', shadow_sb)` by
    (mp_tac (Q.SPECL [`body`, `cenv`, `NoLoop`, `NoneT`]
       (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env)) >>
     rewrite_tac[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `stmts_env (gas_shadow_env T cenv) NoLoop NoneT
       (MAP gas_shadow_stmt body) shadow_sa` >>
     fs[]) >>
  `gas_admissible (eval_stmts (deploy_evaluation_context tops am tx) body)
     (stmt_res_ok NoLoop) (es0 with outcomes := SOME vs.vs_outcomes)` by
    (simp[gas_admissible_def, vyperStateTheory.evaluation_state_fupdcanon] >>
     rpt strip_tac >>
     irule deploy_ctor_body_source_ok >>
     fs[vyperStateTheory.evaluation_state_fupdcanon] >> metis_tac[]) >>
  `!H. valid_horizon (deploy_evaluation_context tops am tx)
      (initial_state am []) H (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
    gas_origin_ptr_path
      (deploy_dead H tops runtime_bc am tx, imm_len tops,
       gas_explicit_sites dunit.cu_context shadow_ctx,
       dunit.cu_context, func, [])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0|>, FEMPTY, entry_taint)
      [] (OK s0, G0, tn0)` by
    (simp[] >> rpt strip_tac >>
     qpat_x_assum `!st0 H. valid_horizon _ st0 H _ ==> _`
       (qspecl_then [`initial_state am []`, `H`] mp_tac) >> simp[]) >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`,
        `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`,
        `opt_deploy_entry_state_own prog prog' cplan tops es with
           vs_outcomes := vs.vs_outcomes`, `body`, `cenv`, `F`,
        `nkey`, `ut`, `imm`, `exit_lbl`, `sa`, `sb`, `sj`, `st_exit`,
        `st_exit`, `st_final`, `func`, `mut`, `body'`, `am_c`, `es0`,
        `shadow_ctx`, `shadow_func`] mp_tac deploy_ctor_body_frag_full >>
  impl_tac >- gvs[gas_variant_def, venom_state_fupdfupds] >>
  simp[] >>
  rewrite_tac[stmt_frag_full_def] >>
  disch_then (qspecl_then [`initial_state am []`, `sa`, `sb`, `shadow_sa`,
    `shadow_sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[ret_pc_ok_def, return_buf_frame_def, return_buf_sep_def] >> rpt conj_tac
      >- metis_tac[deploy_dead_lo_ok]
      >- fs[return_buf_frame_def]
      >- (rpt strip_tac >> Cases_on `ctx_has_dalloca dunit.cu_context`
          >- (drule_all raw_reachable_through_fragment >> metis_tac[]) >>
          drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
          fs[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM,
             unitTransformDefsTheory.dalloca_fmp_headroom_def] >> metis_tac[])
      >> gen_tac >> disch_tac >>
      qpat_x_assum `!st0 H. valid_horizon _ st0 H _ ==> _`
        (qspecl_then [`initial_state am []`, `H`] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      drule_all (INST_TYPE [alpha |-> ``:256``]
        deploy_ctor_start_storage_well_formed_outcomes) >>
      strip_tac >> fs[valid_horizon_def]) >>
  simp[gas_outcome_full_def, vyperStateTheory.evaluation_state_fupdcanon] >>
  strip_tac
  (* bad storage and exempt source errors use the same entry prefix *)
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (`storage_trace_domain (deploy_evaluation_context tops am tx)
          (initial_state am [])
          (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
       valid_horizon (deploy_evaluation_context tops am tx)
          (initial_state am []) H
          (es0 with outcomes := SOME vs.vs_outcomes).storage_trace` by fs[] >>
      `gas_bad_storage_at (deploy_evaluation_context tops am tx) (initial_state am [])
        (eval_stmts (deploy_evaluation_context tops am tx) body')
        (es0 with outcomes := SOME vs.vs_outcomes) s0 marks` by
        (qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _` mp_tac >>
         simp[gas_bad_storage_at_def, vyperStateTheory.evaluation_state_fupdcanon]) >>
      drule_all deploy_ctor_bad_storage_arm >> strip_tac >>
      qexists_tac `marks` >> rewrite_tac[deploy_unit_execution_correct_with_def] >>
      qexistsl_tac [`func`, `shadow_func`] >> simp[] >>
      disj1_tac >> simp[] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (`storage_trace_domain (deploy_evaluation_context tops am tx)
          (initial_state am [])
          (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
       valid_horizon (deploy_evaluation_context tops am tx)
          (initial_state am []) H
          (es0 with outcomes := SOME vs.vs_outcomes).storage_trace` by fs[] >>
      drule gas_exempt_cert_execution >> strip_tac >>
      `!tail. eval_stmts (deploy_evaluation_context tops am tx) body'
         (es0 with <|gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail;
                     outcomes := SOME vs.vs_outcomes|>) =
         (INR (Error err), ee with gas_obs := tail)` by
        (gen_tac >>
         qpat_x_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `tail` mp_tac) >>
         simp[ignore_bind_def, bind_def, return_def,
              vyperStateTheory.evaluation_state_fupdcanon] >>
         Cases_on `eval_stmts (deploy_evaluation_context tops am tx) body'
           (es0 with <|outcomes := SOME vs.vs_outcomes;
                       gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail|>)` >>
         Cases_on `q` >> simp[vyperStateTheory.evaluation_state_fupdcanon]) >>
      drule_all deploy_ctor_exempt_arm >> strip_tac >>
      qexists_tac `marks` >> rewrite_tac[deploy_unit_execution_correct_with_def] >>
      qexistsl_tac [`func`, `shadow_func`] >> simp[] >>
      disj2_tac >> metis_tac[]) >>
  (* One endpoint and one source trace precede the horizon choice. *)
  `valid_horizon (deploy_evaluation_context tops am tx) (initial_state am [])
     (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon (deploy_evaluation_context tops am tx)
      (initial_state am []) H ee.storage_trace ==>
    valid_horizon (deploy_evaluation_context tops am tx)
      (initial_state am []) H es0.storage_trace` by
    simp[valid_horizon_def, storage_observations_ok_def,
         storage_trace_regions_def, storage_trace_locks_def,
         storage_roots_fit_def, storage_trace_backends_well_formed_def] >>
  `eval_stmts (deploy_evaluation_context tops am tx) body'
     (es0 with <|gas_obs := gas_explicit marks vs.vs_gas_readings;
                 outcomes := SOME vs.vs_outcomes|>) =
       (res, ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_fupdcanon]) >>
  qabbrev_tac `src_result =
    if res = INR HaltException then
      INL (finalize_pending_deletions
        (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts ee),
        ee.requests)
    else deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
      F mut am_c res ee` >>
  `!tail. load_contract_trace (SOME vs.vs_outcomes)
     (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE,tops)] [] =
       (src_result, ee.storage_trace)` by
    (gen_tac >>
     qspecl_then [`tops`, `am`, `tx`, `mut`, `body'`, `am_c`, `es0`]
       mp_tac deploy_ctor_source_trace >>
     impl_tac >- gvs[] >>
     disch_then (qspecl_then [`SOME vs.vs_outcomes`,
       `gas_explicit marks vs.vs_gas_readings ++ tail`, `res`,
       `ee with gas_obs := tail`] mp_tac) >>
     fs[Abbr `src_result`, deploy_ctor_finish_gas_obs,
        abstract_machine_from_state_def,
        vyperStateTheory.evaluation_state_fupdcanon]) >>
  `?r1 G1 tn1. exit_result r1 /\
    !H. valid_horizon (deploy_evaluation_context tops am tx)
        (initial_state am []) H ee.storage_trace ==>
      gas_origin_ptr_path
        (deploy_dead H tops runtime_bc am tx, imm_len tops,
         gas_explicit_sites dunit.cu_context shadow_ctx,
         dunit.cu_context, func, [])
        (s0, G0, tn0) marks (r1, G1, tn1) /\
      deploy_venom_result_rel H tops runtime_bc tx src_result r1` by
    (qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
        gas_origin_ptr_path _ _ _ _ /\ _`
       (fn th => assume_tac th >>
         qspec_then `storage_trace_horizon ee.storage_trace` mp_tac th) >>
     impl_tac >- simp[] >> strip_tac
     (* body fallthrough: append the common zero-mark suffix *)
     >- (fs[stmt_lands_def] >>
         `same_frame cenv cenv'` by metis_tac[cenv_top_ext_same_frame] >>
         `!H. valid_horizon (deploy_evaluation_context tops am tx)
             (initial_state am []) H ee.storage_trace ==>
           stmt_state_rel H dunit.cu_context func cenv'
             (deploy_evaluation_context tops am tx) (ee with gas_obs := []) t /\
           ghost_inv_at (deploy_dead H tops runtime_bc am tx) (imm_len tops)
             NONE cenv' (deploy_evaluation_context tops am tx)
             (ee with gas_obs := []) G' tn' t` by
           (rpt strip_tac >>
            qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
              gas_origin_ptr_path _ _ _ _ /\ _`
              (qspec_then `H` mp_tac) >> simp[exit_result_def]) >>
         qspecl_then
           [`\H. valid_horizon (deploy_evaluation_context tops am tx)
                    (initial_state am []) H ee.storage_trace`,
            `storage_trace_horizon ee.storage_trace`, `tops`, `runtime_bc`,
            `am`, `tx`, `imm`, `cenv`, `cenv'`,
            `deploy_evaluation_context tops am tx`, `ee with gas_obs := []`,
            `dunit.cu_context`, `func`, `sb`, `sj`, `st_exit`, `st_final`,
            `exit_lbl`, `nkey`, `ut`, `t`, `G'`, `tn'`,
            `gas_explicit_sites dunit.cu_context shadow_ctx`]
           mp_tac deploy_ctor_fallthrough_joint >>
         impl_tac >- fs[] >>
         disch_then (qx_choose_then `final`
           (qx_choose_then `fall_G`
             (qx_choose_then `fall_tn` strip_assume_tac))) >>
         qexistsl_tac [`Halt final`, `fall_G`, `fall_tn`] >>
         simp[exit_result_def] >> gen_tac >> strip_tac >>
         `gas_origin_ptr_path
            (deploy_dead H tops runtime_bc am tx, imm_len tops,
             gas_explicit_sites dunit.cu_context shadow_ctx,
             dunit.cu_context, func, [])
            (s0, G0, tn0) marks (Halt final, fall_G, fall_tn)` by
           (qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
                gas_origin_ptr_path _ _ _ _ /\ _`
              (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum `!H. _ ==>
                gas_origin_ptr_path (deploy_dead H tops runtime_bc am tx, _, _, _, _, _)
                  (t, G', tn') [] _`
              (qspec_then `H` mp_tac) >> simp[] >> disch_tac >>
            qpat_x_assum `gas_origin_ptr_path _ (s0, G0, tn0) marks (OK t, G', tn')`
              (mp_tac o MATCH_MP gas_origin_ptr_path_append) >> simp[] >>
            disch_then (qspecl_then [`[]`, `Halt final`, `fall_G`, `fall_tn`] mp_tac) >>
            simp[]) >>
         simp[] >>
         `final.vs_code = vs.vs_code /\ final.vs_labels = vs.vs_labels` by
           (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >>
            strip_tac >> drule run_from_halt_code >> simp[]) >>
         qpat_x_assum `!H. _ ==> constructor_return_q H _ _ _ _ _ _ _ _ _ _`
           (qspec_then `H` mp_tac) >> simp[] >> disch_tac >>
         qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`,
           `dunit`, `dout`, `prog`, `prog'`, `cplan`, `off`, `am`, `tx`, `es`, `vs`,
           `body`, `cenv`, `F`, `nkey`, `ut`, `imm`, `exit_lbl`, `sa`, `sb`,
           `sj`, `st_exit`, `st_epilogue`, `st_final`, `func`, `mut`, `body'`, `am_c`,
           `es0`, `gas_explicit marks vs.vs_gas_readings`, `INL ()`,
           `ee with gas_obs := []`, `final`, `H`] mp_tac deploy_ctor_return >>
         impl_tac >- gvs[vyperStateTheory.evaluation_state_fupdcanon] >>
         simp[Abbr `src_result`, deploy_ctor_finish_gas_obs]) >>
     (* body exit: its H-indexed return predicate already covers the suffix *)
     qexistsl_tac [`r`, `G'`, `tn'`] >> simp[] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
       gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[] >> strip_tac >> fs[exit_result_def] >>
     Cases_on `res = INR HaltException`
     >- (fs[halt_exit_def] >>
         qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
           (qspec_then `[]` mp_tac) >>
         simp[stmt_exit_ptr_def, expr_exit_def, Abbr `src_result`] >>
         strip_tac >>
         `MEM tx.target ee.pending_deletions` by
           (mp_tac (Q.INST
              [`tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`,
               `mut` |-> `mut`, `raw_body` |-> `body'`,
               `am_c` |-> `am_c`, `es0` |-> `es0`,
               `os` |-> `vs.vs_outcomes`,
               `gs` |-> `gas_explicit marks vs.vs_gas_readings`,
               `ee` |-> `ee with gas_obs := []`]
              deploy_ctor_body_halt_pending) >> simp[]) >>
         mp_tac (Q.INST
           [`tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`,
            `mut` |-> `mut`, `nr` |-> `F`, `raw_body` |-> `body'`,
            `am_c` |-> `am_c`, `es0` |-> `es0`,
            `bc` |-> `assemble prog'`, `es` |-> `es`,
            `H` |-> `H`, `ee` |-> `ee`, `ss` |-> `s'`,
            `runtime_bc` |-> `runtime_bc`]
           (INST_TYPE [alpha |-> ``:256``] deploy_ctor_halt_result)) >>
         simp[] >> disch_then MATCH_MP_TAC >>
         fs[halt_rel_def, accounts_rel_def]) >>
     fs[Abbr `src_result`] >>
     qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
       (qspec_then `[]` mp_tac) >>
     simp[stmt_exit_ptr_def] >> strip_tac
     >- (Cases_on `res` >> fs[expr_exit_def] >>
         rename1 `expr_exit (INR e) _` >>
         `e <> ReturnException NoneV` by
           (strip_tac >> Cases_on `r` >> gvs[expr_exit_def]) >>
         qpat_x_assum `expr_exit (INR e) r` mp_tac >>
         qpat_x_assum `e <> HaltException` mp_tac >>
         qpat_x_assum `e <> ReturnException NoneV` mp_tac >>
         rpt (pop_assum kall_tac) >>
         Cases_on `r` >> Cases_on `e` >>
         simp[expr_exit_def, deploy_ctor_finish_def, deploy_venom_result_rel_def] >>
         rename1 `abort = Revert_abort` >> Cases_on `abort` >> simp[] >>
         rename1 `expr_exit (INR (Error err)) _` >>
         Cases_on `err` >> simp[expr_exit_def]) >>
     `v = NoneV /\ ?final. r = Halt final` by fs[constructor_return_q_def] >>
     qpat_x_assum `DROP off (assemble prog') = runtime_bc`
       (fn th => gvs[] >> assume_tac th) >>
     `final.vs_code = vs.vs_code /\ final.vs_labels = vs.vs_labels` by
       (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >>
        strip_tac >> drule run_from_halt_code >> simp[]) >>
     `constructor_return_q H func cenv (deploy_evaluation_context tops am tx)
        (LENGTH runtime_bc) (imm_len tops) F nkey NoneV
        ((ee with gas_obs := []) with scopes := []) (Halt final)` by
       metis_tac[constructor_return_q_gas_obs] >>
     once_rewrite_tac[GSYM (Q.INST [`g` |-> `[]`] deploy_ctor_finish_gas_obs)] >>
     irule deploy_ctor_return >>
     qpat_assum `deploy_phases _ _ _ _` (irule_at Any) >>
     qpat_assum `deploy_ctor_code _ _ _ _ _` (irule_at Any) >>
     qpat_assum `deploy_ctor_start _ _ _ _` (irule_at Any) >>
     qpat_assum `deploy_state_rel _ (assemble prog') _ _ es` (irule_at Any) >>
     qpat_assum `FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off`
       (irule_at Any) >>
     qexistsl_tac [`vs`, `gas_explicit marks vs.vs_gas_readings`] >>
     simp[vyperStateTheory.evaluation_state_fupdcanon]) >>
  qexists_tac `marks` >>
  mp_tac (Q.INST
    [`tops` |-> `tops`, `runtime_bc` |-> `runtime_bc`,
     `am` |-> `am`, `tx` |-> `tx`, `dunit` |-> `dunit`, `vs` |-> `vs`,
     `shadow_ctx` |-> `shadow_ctx`, `marks` |-> `marks`,
     `src` |-> `src_result`, `obs` |-> `ee.storage_trace`,
     `r` |-> `r1`, `s0` |-> `s0`, `G0` |-> `G0`, `tn0` |-> `tn0`,
     `G1` |-> `G1`, `tn1` |-> `tn1`, `func` |-> `func`,
     `shadow_func` |-> `shadow_func`]
    (INST_TYPE [alpha |-> ``:256``] deploy_joint_terminal_with)) >>
  impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
       gas_origin_ptr_path _ (s0,G0,tn0) marks _ /\ _`
       (qspec_then `H` strip_assume_tac) >>
     gvs[] >>
     qpat_assum `!st0 H. valid_horizon _ st0 H _ ==> _`
       (qspecl_then [`initial_state am []`,`H`] mp_tac) >>
     impl_tac >- (simp[] >> first_assum irule >> first_assum ACCEPT_TAC) >>
     strip_tac >> fs[]) >>
  simp[]
QED
