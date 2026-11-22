(* Selected cuts at an internal-call frame boundary. *)
Theory entryCreateInvokeCut
Ancestors
  entryCreateBodyCut dftGasFromListTraceDefs bodyIntCallSeams fragGasFocus
  contextCodegenRel bodyFullIntCallEntryShadow gasShadow gasShadowCompileHelpers
  gasShadowCompileCallSupport gasShadowCompile externalCallSelected
  vyperFiniteStoragePreservation vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState gasOutcomeFull fragGasMode gasSummary list
  venomExecSemantics venomRunBounded

(* Resolve the selected call by its saved caller state, not just its label.
   The setup state is before PHIs, whereas the child judgment starts after them. *)
Theorem create_cut_invoke_entry:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?name ops args setup.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME setup /\
    enters_block callee setup entered /\
    trace_step p d fuel ctx caller inst s =
      trace_blocks ((d,inst.inst_id)::p) d fuel ctx callee setup
Proof
  simp[gas_invoke_entry_def, enters_block_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[trace_step_invoke]
QED

(* Split at the chosen position, not at another visit with the same PC.
   The right arm can only occur after the actual IntRet and frame restore. *)
Theorem create_cut_invoke_trace_split:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  trace_block p d fuel ctx caller bb s = before ++ hit::after ==>
  let call = ((p,d,inst.inst_id),caller,inst,s) in
  let child = trace_step p d fuel ctx caller inst s in
    (before = [] /\ hit = call) \/
    (?inside suffix. before = call::inside /\ child = inside ++ hit::suffix) \/
    (?right ret finish out. before = call::(child ++ right) /\
       step_inst fuel ctx inst s = OK out /\
       (?name ops args setup.
          decode_invoke inst = SOME (name,ops) /\
          lookup_function name ctx.ctx_functions = SOME callee /\
          eval_operands ops s = SOME args /\ setup_callee callee args s = SOME setup /\
          enters_block callee setup entered /\
          run_blocks fuel ctx callee setup = IntRet ret finish) /\
       bind_outputs inst.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state s finish)) = SOME out /\
       trace_block p d fuel ctx caller bb
         (out with vs_inst_idx := SUC s.vs_inst_idx) = right ++ hit::after)
Proof
  strip_tac >> drule_all create_cut_invoke_entry >>
  disch_then (qspecl_then [`p`,`fuel`,`d`] strip_assume_tac) >>
  qpat_x_assum `trace_block p d fuel ctx caller bb s = _` mp_tac >>
  simp[Once trace_defs] >>
  qmatch_goalsub_abbrev_tac `child ++ rest` >>
  Cases_on `before` >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `trace_step _ _ _ _ _ _ _ ++ rest = _`
    (strip_assume_tac o REWRITE_RULE[APPEND_EQ_APPEND_MID] o SYM)
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> Cases_on `step_inst fuel ctx inst s` >>
  gvs[Abbr `rest`, venomInstTheory.is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  once_rewrite_tac[step_inst_def] >> simp[] >>
  Cases_on `run_blocks fuel ctx callee setup` >> simp[AllCaseEqs()] >>
  metis_tac[]
QED

(* Neither seeding a callee's compile environment nor compiling omitted
   defaults requires excluding source msg.gas. *)
Theorem create_cut_internal_omitted_defaults_shadow:
  !ce name n flags tys. gas_shadow_compiles
    (compile_stage_intcall_args compile_expr (cenv_without_defaults ce name)
      (omitted_defaults ce name n) flags tys)
    (compile_stage_intcall_args compile_expr
      (cenv_without_defaults (gas_shadow_env T ce) name)
      (omitted_defaults (gas_shadow_env T ce) name n) flags tys)
Proof
  simp[gas_shadow_env_without_defaults, gas_shadow_env_omitted_defaults] >>
  match_mp_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`sd` |-> `T`, `sh` |-> `T`] gas_shadow_compiles_stage_intcall_args_env)) >>
  simp[gas_shadow_compile_expr_env]
QED

Theorem create_cut_internal_entry_shadow:
  gas_shadow_state entry entryS /\
  compile_internal_function_entry ce params has_rb ctor ilen rt entry =
    ((ce0,rpc,imm),prologue) ==>
  ?prologueS.
    compile_internal_function_entry (gas_shadow_env T ce) params has_rb
      ctor ilen rt entryS = ((gas_shadow_env T ce0,rpc,imm),prologueS) /\
    gas_shadow_state prologue prologueS
Proof
  metis_tac[intcall_shadow_entry_cut]
QED

Theorem create_cut_unlock_total[local]:
  ?out. unlock_if_nr cx nr view st = (INL (),out)
Proof
  Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, return_def, nonreentrantEquivTheory.release_nonreentrant_lock_execution] >>
  IF_CASES_TAC >> simp[return_def, nonreentrantEquivTheory.release_nonreentrant_lock_execution]
QED

(* Runtime errors are not source function returns. Scope pop and unlock
   preserve the error and only extend the body's storage trace. *)
Theorem create_cut_intcall_body_post[local]:
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
  eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
    (locked with gas_obs := obs) = (body_res,body_end) /\
  intcall_rest cx name mut nr ss prev rtv (es with gas_obs := obs) = (res,out) ==>
  (?extra. out.storage_trace = body_end.storage_trace ++ extra) /\
  (!err. body_res = INR (Error err) ==> res = INR (Error err))
Proof
  strip_tac >> drule_then (qspec_then `obs` assume_tac) lock_if_nr_with_gas_obs >>
  `?unlocked. unlock_if_nr cx nr (is_view_mut mut) (body_end with scopes := prev) =
                 (INL (),unlocked)` by simp[create_cut_unlock_total] >>
  pop_assum strip_assume_tac >>
  `storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
    simp[storage_trace_frame_optional_locks] >>
  `?extra. unlocked.storage_trace = body_end.storage_trace ++ extra` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  qpat_x_assum `intcall_rest _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `body_res`
  >- (Cases_on `safe_cast rtv NoneV` >>
      asm_simp_tac bool_ss [intcall_rest_def, finally_def, finally_unless_halt_def,
        try_def, pop_function_def, set_scopes_def, handle_function_def,
        ignore_bind_def, bind_def, return_def, raise_def, lift_option_type_def,
        pairTheory.pair_case_thm, sumTheory.sum_case_def, optionTheory.option_case_def] >>
      simp[] >> metis_tac[]) >>
  rename1 `eval_stmts _ _ _ = (INR ex,_)` >> Cases_on `ex` >>
  asm_simp_tac bool_ss [intcall_rest_def, finally_def, finally_unless_halt_def,
    try_def, pop_function_def, set_scopes_def, handle_function_def,
    ignore_bind_def, bind_def, return_def, raise_def, lift_option_type_def,
    pairTheory.pair_case_thm, sumTheory.sum_case_def, exception_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `safe_cast rtv v` >> gvs[return_def, raise_def]
QED

Theorem create_cut_horizon_stk[local]:
  valid_horizon (cx with stk updated_by f) st0 H trace <=>
  valid_horizon cx st0 H trace
Proof
  simp[valid_horizon_def, storage_well_formed_on_stk, storage_observations_ok_stk]
QED

Theorem create_cut_intcall_body[local]:
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
  create_body_cut explicit tops (cx with stk updated_by CONS (NONE,name)) st0
    (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
    (locked,start) (inside,hit) /\
  create_cut_marks explicit prologue = [] /\
  start.vs_gas_readings = s.vs_gas_readings ==>
  create_body_cut explicit tops cx st0 (intcall_rest cx name mut nr ss prev rtv)
    (es,s) (prologue ++ inside,hit)
Proof
  rewrite_tac[create_body_cut_def] >>
  strip_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `intcall_rest _ _ _ _ _ _ _ (es with gas_obs := obs)` >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
              (locked with gas_obs := obs)` >>
  rename1 `eval_stmts _ _ _ = (body_res,body_end)` >>
  drule_all create_cut_intcall_body_post >> strip_tac >>
  `valid_horizon (cx with stk updated_by CONS (NONE,name)) st0 H
                 body_end.storage_trace` by
    (simp[create_cut_horizon_stk] >> metis_tac[valid_horizon_append]) >>
  `create_cut_failure tops body_res` by
    (qpat_x_assum `_ ==> !H tail res ee. _` mp_tac >> simp[] >>
     disch_then (qspecl_then [`H`,`tail`,`body_res`,`body_end`] mp_tac) >>
     qpat_x_assum `eval_stmts _ _ _ = (body_res,body_end)` mp_tac >>
     qpat_x_assum `Abbrev (obs = _)`
       (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     rewrite_tac[create_cut_marks_append] >> asm_rewrite_tac[APPEND] >>
     strip_tac >> simp[]) >>
  fs[create_cut_failure_def] >> metis_tac[]
QED

Theorem create_body_cut_invoke_cons[local]:
  inst.inst_opcode = INVOKE ==>
  (create_body_cut explicit tops cx st0 source (es,s) ((key,fnc,inst,t)::before,hit) <=>
   create_body_cut explicit tops cx st0 source (es,s) (before,hit))
Proof
  strip_tac >> simp[create_body_cut_def, create_cut_marks_invoke]
QED

(* This rule starts at the fetched call, after evaluation of the explicit
   arguments and omitted defaults. A pending call needs only the child cut,
   not an IntRet. On return the marked source/target replay must end at
   the restored caller state and must include every child reading. *)
Theorem create_cut_internal_activation:
  let call = ((p,d,inst.inst_id),caller,inst,s) in
  let child = trace_step p d fuel ctx caller inst s in
  let source = intcall_rest cx name mut nr ss prev rtv in
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  trace_block p d fuel ctx caller bb s = before ++ hit::after /\
  (!inside suffix. child = inside ++ hit::suffix /\ before = call::inside ==>
    ?locked start prologue body_pre.
      inside = prologue ++ body_pre /\
      create_cut_marks explicit prologue = [] /\
      gas_marked_path F ctx callee entered 0 (OK start) /\
      lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
      create_body_cut explicit tops (cx with stk updated_by CONS (NONE,name)) st0
        (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
        (locked,start) (body_pre,hit)) /\
  (!right out. before = call::(child ++ right) /\
       step_inst fuel ctx inst s = OK out /\
       trace_block p d fuel ctx caller bb
         (out with vs_inst_idx := SUC s.vs_inst_idx) = right ++ hit::after ==>
    ?r mid.
      gas_marked_exec F (ctx,caller) source (es,s)
        (create_cut_marks explicit child) r mid
        (OK (out with vs_inst_idx := SUC s.vs_inst_idx)) /\
      (create_cut_failure tops r \/
       ?v G tn. r = INL v /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==>
              Q H v mid G tn (out with vs_inst_idx := SUC s.vs_inst_idx)) /\
         (!H. valid_horizon cx st0 H mid.storage_trace /\
              Q H v mid G tn (out with vs_inst_idx := SUC s.vs_inst_idx) ==>
            create_body_cut explicit tops cx st0 (next v)
              (mid,out with vs_inst_idx := SUC s.vs_inst_idx) (right,hit)))) /\
  (!v. storage_trace_frame (next v)) ==>
  create_body_cut explicit tops cx st0 (bind source next) (es,s) (before,hit)
Proof
  simp_tac std_ss [LET_THM] >> strip_tac >>
  `inst.inst_opcode = INVOKE` by fs[gas_invoke_entry_def] >>
  drule_all create_cut_invoke_trace_split >>
  simp_tac std_ss [LET_THM] >> disch_then strip_assume_tac
  >- simp[create_body_cut_def, inst_create_size_ok_def]
  >- (qpat_x_assum `!inside suffix. _` drule_all >> strip_tac >>
      `start.vs_gas_readings = s.vs_gas_readings` by
        metis_tac[gas_marked_path_ok_suffix, gas_invoke_entry_readings, DROP_0] >>
      drule_all create_cut_intcall_body >>
      disch_then (qspecl_then [`rtv`,`prev`] assume_tac) >>
      irule create_cut_bind_left >> simp[] >>
      qpat_x_assum `before = _` SUBST_ALL_TAC >>
      qpat_x_assum `inside = _` SUBST_ALL_TAC >>
      simp[create_body_cut_invoke_cons]) >>
  qpat_x_assum `!right out. _` drule_all >> strip_tac >>
  qabbrev_tac `left =
    ((p,d,inst.inst_id),caller,inst,s)::trace_step p d fuel ctx caller inst s` >>
  `create_cut_bind_split explicit tops cx st0 (ctx,caller)
    (intcall_rest cx name mut nr ss prev rtv) next (es,s) Q (left,right,hit)` by
    (simp[Abbr `left`, create_cut_bind_split_def, create_cut_marks_invoke] >>
     qexistsl_tac [`out with vs_inst_idx := SUC s.vs_inst_idx`,`r`,`mid`] >>
     simp[] >> metis_tac[]) >>
  `before = left ++ right` by simp[Abbr `left`] >>
  drule_at Any create_cut_bind_right >> simp[]
QED

(* The split before INVOKE includes both explicit arguments and defaults;
   its all-tails equation is the one used to feed the activation above. *)
Theorem create_cut_internal_completed_arguments:
  (!args. storage_trace_frame (rest args)) /\
  gas_marked_exec F (ctx,caller) args_and_defaults (es,s)
    (create_cut_marks explicit args_prefix) r mid (OK invoke_state) /\
  (create_cut_failure tops r \/
   ?args G tn. r = INL args /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q H args mid G tn invoke_state) /\
     (!H. valid_horizon cx st0 H mid.storage_trace /\ Q H args mid G tn invoke_state ==>
       create_body_cut explicit tops cx st0 (rest args) (mid,invoke_state) (remaining,hit))) ==>
  create_body_cut explicit tops cx st0 (bind args_and_defaults rest)
    (es,s) (args_prefix ++ remaining,hit)
Proof
  strip_tac >>
  `create_cut_bind_split explicit tops cx st0 (ctx,caller)
     args_and_defaults rest (es,s) Q (args_prefix,remaining,hit)` by
    (simp[create_cut_bind_split_def] >>
     qexistsl_tac [`invoke_state`,`r`,`mid`] >> simp[] >> metis_tac[]) >>
  drule_at Any create_cut_bind_right >> simp[]
QED

(* A concrete shadow-compile check at an omitted msg.gas default. The
   activation interface allows this input without any gas-freeness premise. *)
Theorem create_cut_omitted_msg_gas_check[local]:
  omitted_defaults ce name n = [Builtin ty (Env MsgGas) []] /\
  gas_shadow_state entry entryS /\
  compile_internal_function_entry callee_ce params has_rb ctor ilen rt entry =
    ((ce0,rpc,imm),prologue) ==>
  ?prologueS.
    compile_internal_function_entry (gas_shadow_env T callee_ce) params has_rb
      ctor ilen rt entryS = ((gas_shadow_env T ce0,rpc,imm),prologueS) /\
    gas_shadow_state prologue prologueS /\
    gas_shadow_compiles
      (compile_stage_intcall_args compile_expr (cenv_without_defaults ce name)
        [Builtin ty (Env MsgGas) []] flags tys)
      (compile_stage_intcall_args compile_expr
        (cenv_without_defaults (gas_shadow_env T ce) name)
        [Builtin ty (Env GasPrice) []] flags tys)
Proof
  strip_tac >> drule_all create_cut_internal_entry_shadow >> strip_tac >>
  qexists_tac `prologueS` >> simp[] >>
  qspecl_then [`ce`,`name`,`n`,`flags`,`tys`] mp_tac
    create_cut_internal_omitted_defaults_shadow >>
  simp[gas_shadow_env_omitted_defaults, gas_shadow_expr_def, gas_shadow_builtin_def]
QED
