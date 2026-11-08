(*
 * S3 piece: once the external entry accepts the call value, the lowered
 * unit's run is memory-safe.  The memory twin of loweringRuntimeCorrect's
 * lower_vyper_runtime_unit_body: the entry reaches the body
 * (external_entry_reaches_body_mem), the body runs (bodyMemory's
 * body_stmts_sim_mem) and returns (external_frame_ret_ok_mem) or falls off
 * its end (compile_guarded_body_end_mem_safe).  bodyMemory joins the
 * ancestors with the composition's proof, once bodyMemory's own cone
 * builds after the GAS join; its body_stmts_sim_mem's abi_decode target
 * premise holds for the called body by bodyAbiDecodeTarget's
 * lookup_function_abi_decode_target_occurs.
 *)
Theory loweringMemBodyRun
Ancestors
  stmtSimDefs
  loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem fragGasMode fragGasPathMem bodyMemoryDefs
  entryHaltMem loweringPtrCorrect bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs
  bodyAbiDecodeTarget loweringMemEntryReach loweringMemFrameRet gasSummary
  bodyMemory loweringMemBodySourceGas
  gasOutcome gasExemptCert gasContext vyperTypeSelectedEntrySoundness externalBodyFrame

val _ = Parse.hide "body";

(* ===== The end of the body ===== *)

(* Falling off the end of the guarded body (no lock): a STOP, or INVALID
   for a function with a return type; neither touches memory. *)
Theorem compile_guarded_body_end_mem_safe:
  !ctx cenv nkey ut iv stmts rt st x st' sb fn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `rt` >>
  gvs[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, comp_get_def, emitHelperTheory.emit_inst_def,
      fresh_id_def, emit_def] >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts ++ [inst]` >>
  drule fn_has_code_same_block >> simp[] >>
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[] >>
  gen_tac >>
  `mem_safe_step fuel ctx inst s` by
    simp[Abbr `inst`, mem_safe_step_non_invoke,
         inst_mem_below_frontier_def, source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  `?r. step_inst fuel ctx inst s = r /\
       (!s'. r <> OK s') /\ (!e. r <> Error e)` by
    simp[Abbr `inst`, step_inst_non_invoke, step_inst_base_opcode_eqs,
         mk_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all run_from_step_exit >> simp[]
QED

(* The source exemption rules out the body judgment's exceptional error. *)
Theorem external_body_not_empty_bytes_error:
  !tops am tx ret mut args fbody env orc es0 res es'.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es0 = (res, es') /\
    ~source_exempt tops (call_external orc [] am tx) ==>
    res <> INR (Error (RuntimeError "convert empty bytes to signed"))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule_all call_external_selected_body >> strip_tac >>
  `es0.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `es0 with scopes := [env] = es0` by
    (qpat_assum `es0.scopes = [env]` (SUBST1_TAC o SYM) >> simp[]) >>
  gvs[vyperTypeSelectedEntrySoundnessTheory.call_external_body_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.set_scopes_def, source_exempt_def,
      unspecified_behaviour_exempt_def]
QED

(* ===== The counted body judgment, completed ===== *)

(* A counted memory summary makes the run memory-safe at every fuel, once
   every normal landing it can reach continues memory-safely: the marked
   path is a gas_path_mem, which carries the check of each step. *)
Theorem gas_summary_at_mem_safe_run:
  !ctx func marks source es s0 Q R.
    gas_summary_at T (ctx, func) marks source (es, s0) Q R /\
    (!res ee t. Q res ee t ==>
       ?fuel. mem_safe_run fuel ctx func t /\
              (!e. run_from fuel ctx func t <> Error e)) ==>
    !fuel. mem_safe_run fuel ctx func s0
Proof
  rpt gen_tac >> strip_tac >>
  fs[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  drule gas_path_mem_exec >> strip_tac >> gvs[]
  >- (first_x_assum drule >> strip_tac >>
      rename1 `mem_safe_run f0 ctx func t` >>
      qpat_x_assum `!fuel. (!e. run_from _ _ _ _ <> _) ==> _`
        (qspec_then `f0` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      metis_tac[mem_safe_run_all_fuel])
  >> TRY (gvs[exit_result_def] >> NO_TAC)
  >> metis_tac[exit_result_not_error, mem_safe_run_all_fuel]
QED

(* The counted stmt_frag_mem, completed: from a memory-safe continuation
   at each normal landing, the run from the fragment's start is
   memory-safe at every fuel.  The exempt branch of gas_outcome only
   knows a target prefix, so the caller rules it out. *)
Theorem stmt_frag_mem_complete:
  !d ctx func cx lctx RetQ cenv m source es sa sb s0 cenv'.
    stmt_frag_mem d ctx func cx lctx RetQ cenv m source es /\
    m sa = (cenv', sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\
    ~block_is_terminated sa /\
    gas_admissible source (stmt_res_ok lctx) es /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!marks err ee leaf finish.
       ~gas_exempt_cert T (cx_tops cx) (ctx, func)
          (ignore_bind source (return ())) (es, s0) marks (err, ee)
          (leaf, finish)) /\
    (!res s. stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb) ==>
         ?fuel. mem_safe_run fuel ctx func s /\
                (!e. run_from fuel ctx func s <> Error e)) ==>
    !fuel. mem_safe_run fuel ctx func s0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [stmt_frag_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  simp[gas_outcome_def] >> strip_tac
  >- (drule_then irule gas_summary_at_mem_safe_run >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* ===== The selected call at any gas observations ===== *)

(* Moving the call value reads and writes only the accounts. *)
Theorem send_call_value_scopes_gas[local]:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.scopes = s.scopes /\
    !sc g. send_call_value mut cx (s with <| scopes := sc; gas_obs := g |>) =
           (r, s' with <| scopes := sc; gas_obs := g |>)
Proof
  rpt gen_tac >>
  Cases_on `cx.txn.value = 0` >-
   (simp[vyperInterpreterTheory.send_call_value_def, LET_THM,
         vyperStateTheory.return_def] >>
    strip_tac >> gvs[]) >>
  Cases_on `mut = Payable` >-
   (Cases_on `cx.txn.sender = cx.txn.target` >-
     (simp[vyperInterpreterTheory.send_call_value_def,
          vyperInterpreterTheory.transfer_value_def, LET_THM,
          vyperStateTheory.return_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
          vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
          vyperStateTheory.update_accounts_def] >>
      strip_tac >> gvs[]) >>
    simp[vyperInterpreterTheory.send_call_value_def,
          vyperInterpreterTheory.transfer_value_def, LET_THM,
          vyperStateTheory.return_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
          vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
          vyperStateTheory.update_accounts_def] >>
    Cases_on `cx.txn.value <= (lookup_account cx.txn.sender s.accounts).balance` >>
    Cases_on `(lookup_account cx.txn.target s.accounts).balance + cx.txn.value <
              2 ** 256` >>
    simp[] >> strip_tac >> gvs[]) >>
  simp[vyperInterpreterTheory.send_call_value_def, LET_THM,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def] >>
  strip_tac >> gvs[]
QED

(* call_external_body sets the scopes before it reads them. *)
Theorem call_external_body_scopes_gas[local]:
  !am cx mut tenv s sc env body ret.
    call_external_body am cx F mut tenv (s with scopes := sc) env body ret =
    call_external_body am cx F mut tenv s env body ret
Proof
  simp[vyperTypeSelectedEntrySoundnessTheory.call_external_body_def,
       bind_def, ignore_bind_def, set_scopes_def, return_def]
QED

(* loweringRuntimeCorrect's call_external_selected_body at any gas
   observations: the selected call runs the body from es0 with them. *)
Theorem call_external_selected_body_gas:
  !tops am tx ret mut args fbody env orc es0 gobs.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc gobs am tx =
      case vyperTypeSelectedEntrySoundness$call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             F mut (type_env tops) (es0 with gas_obs := gobs) env fbody ret
      of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rpt strip_tac >>
  drule send_call_value_scopes_gas >> strip_tac >>
  first_x_assum (qspecl_then [`[FEMPTY]`, `gobs`] mp_tac) >>
  `initial_state am [env] with
     <| outcomes := orc; requests := []; scopes := [FEMPTY];
        gas_obs := gobs |> =
   initial_state am [FEMPTY] with
     <| outcomes := orc; requests := []; gas_obs := gobs |>` by
    simp[initial_state_def] >>
  simp[] >> strip_tac >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  `call_external_body am
     (initial_evaluation_context am.sources am.layouts tx NONE)
     F mut (type_env tops) (es0 with gas_obs := gobs) env fbody ret =
   call_external_body am
     (initial_evaluation_context am.sources am.layouts tx NONE)
     F mut (type_env tops) (es0 with <| scopes := [FEMPTY]; gas_obs := gobs |>)
     env fbody ret` by
    (once_rewrite_tac[GSYM call_external_body_scopes_gas] >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
  fs[source_deployment_rel_def] >>
  simp[call_external_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function orc gobs am cx` >>
  `call_external_function orc gobs am cx F mut tops [(NONE, tops)] args []
     tx.args fbody ret =
   call_external_body am cx F mut (type_env tops)
     (es0 with <| scopes := [FEMPTY]; gas_obs := gobs |>) env fbody ret` by
    (qpat_assum `_ = type_env tops` (SUBST1_TAC o SYM) >>
     irule call_external_function_body >>
     simp[Abbr `cx`, eval_external_defaults_def, finally_def, bind_def,
          get_scopes_def, set_scopes_def, ignore_bind_def, return_def,
          evaluate_def] >>
     qpat_x_assum
       `send_call_value _ _ _ = (_, es0 with <| scopes := _; gas_obs := _ |>)`
       mp_tac >>
     qpat_x_assum
       `initial_state _ [env] with
          <| scopes := _; outcomes := _; requests := _; gas_obs := _ |> = _`
       SUBST1_TAC >>
     simp[initial_evaluation_context_def]) >>
  simp[]
QED

(* ===== The body run ===== *)

(* No exempt certificate for the called body: its exempt error, at the
   gas observations the certificate selects from the target's readings,
   would be the selected call's, which the premise excludes. *)
Theorem external_body_no_exempt_cert:
  !tops am tx vs mut args ret fbody env es0 ctx func s0.
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    s0.vs_gas_readings = vs.vs_gas_readings ==>
    !marks err ee leaf finish.
      ~gas_exempt_cert T
         (cx_tops (initial_evaluation_context am.sources am.layouts tx NONE))
         (ctx, func)
         (ignore_bind
            (eval_stmts
               (initial_evaluation_context am.sources am.layouts tx NONE)
               fbody) (return ()))
         (es0, s0) marks (err, ee) (leaf, finish)
Proof
  rpt strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) =
   tops` by metis_tac[cx_tops_module, source_deployment_context] >>
  pop_assum SUBST_ALL_TAC >>
  simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  `es0.scopes = [env]` by
    (drule send_call_value_scopes_gas >> simp[initial_state_def]) >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `gas_explicit marks vs.vs_gas_readings`
                assume_tac) >>
  `!g. es0 with <| gas_obs := g; scopes := [env] |> = es0 with gas_obs := g /\
       es0 with <| scopes := [env]; gas_obs := g |> = es0 with gas_obs := g`
    by simp[evaluation_state_component_equality] >>
  first_x_assum (qspec_then `marks` mp_tac) >>
  asm_simp_tac (srw_ss())
    [source_exempt_def,
     vyperTypeSelectedEntrySoundnessTheory.call_external_body_def,
     vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
     vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
     LET_THM]
QED

(* Once the external entry accepts the call value, the lowered run is
   memory-safe: the entry reaches the body, and the body's counted memory
   judgment runs it to a return (external_frame_ret_ok_mem) or to its end
   (compile_guarded_body_end_mem_safe). *)
Theorem lower_vyper_runtime_unit_body_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. mem_safe_blocks fuel unit.cu_context efn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    metis_tac[gas_explicit_nil] >>
  drule_all external_entry_reaches_body_mem >> strip_tac >>
  drule_all external_body_frame >> strip_tac >>
  drule_all external_frame_ret_ok_mem >>
  disch_then (qspec_then `func` assume_tac) >>
  `rt = if ret = NoneT then NONE else SOME ret` by
    gvs[package_external_fn_def, set_external_package_target_def] >>
  drule guarded_body_code >> strip_tac >>
  drule_all guarded_body_stmts_env >> strip_tac >>
  `!target. supported_stmts_expr_exists
              (expr_abi_decode_target_root target) fbody ==>
            occurs_abi_decode_target target tops` by
    metis_tac[lookup_function_abi_decode_target_occurs] >>
  drule_all body_stmts_sim_mem >>
  disch_then (qspec_then `NoLoop` assume_tac) >>
  `fn_has_code sa sb func /\ fn_has_code sb st' func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `(!fuel. mem_safe_run _ _ _ _) ==> _` irule >>
  drule stmt_frag_mem_complete >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[ret_pc_ok_def, return_buf_frame_def] >> rpt conj_tac
      >~ [`gas_admissible _ _ _`]
      >- (irule external_body_source_ok_gas_mem >> metis_tac[])
      >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
      >- (irule external_body_no_exempt_cert >> metis_tac[]) >>
      rpt strip_tac >> gvs[stmt_lands_def] >>
      drule compile_guarded_body_end_mem_safe >>
      disch_then (qspecl_then [`unit.cu_context`, `sb`, `func`, `s`]
        mp_tac) >>
      simp[] >> disch_then (qspec_then `0` mp_tac) >> metis_tac[]) >>
  simp[]
QED
