(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a local of a word type (S1's
   body_assign_local_word).  The lowering evaluates e and stores its word
   with one MSTORE at the local's pointer, whose region (at least 32
   bytes, as the local's type lays out in a word) is below the frontier. *)
Theory bodyMemAssignLocalWord
Ancestors
  bodySim vyperTypeCallGraph
  bodyMemoryPreds bodyMemoryDefs bodyDeclMemoryCounted bodyDeclMemoryCore
  allocaFootprint exprSimMemDefs exprSimSource bodyExprPreFacts
  stmtSimAssign stmtSimAssignSource stmtSimAssignStore stmtSimDeclStore
  stmtSimDeclCompose stmtSimProps stmtSimDefs exprSimDefs loweringPosts gasOracleReplay
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  gasContext
  exprSimHypsDefs exprLoweringProps emitHelperProps emitHelper exprLowering
  compileEnv fragExecMem supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem vyperLookup vyperInterpreter vyperState
  venomInst venomState list rich_list finite_map
Libs
  monadsyntax

(* The MSTORE of the typed word of v at a live local's pointer, run on a
   memory-safe path: the local's region holds a word (store_lays_out) and
   lies below the frontier (local_ptrs_rel). *)
Theorem assign_local_word_store_path_mem:
  !ctx func cenv cx es s id p sz pre env entry rest v etv op st st'.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME (typed_val_to_w256 etv v) /\
    stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    store_lays_out etv entry.type v ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        alloca_history func t /\
        gas_marked_path T ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w /\ w2n w + sz <= s.vs_alloca_next /\
       type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 etv v) s` >>
  `run_inst_seq (emitted_insts st st') s = OK u` by
    (`step_inst_base (mk_inst st.cs_next_id MSTORE [Var p; op] []) s = OK u` by
       (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (qspecl_then [`Var p`, `op`, `st`, `st'`, `s`, `w`] mp_tac
       emit_mstore_mem_ok >> simp[eval_operand_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `st` >> simp[is_terminator_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `st`] >> simp[is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

(* x = e for a local x of a word type and e of a word type, for every
   outcome, on a memory-safe path: e's errors exit, and on a value it is
   stored at x's pointer. *)
Theorem assign_local_word_frag_mem[local]:
  !d ctx func cx lctx RetQ cenv ty id e es p sz vtyp etv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sb'.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >> decide_tac) >>
  `!m res ee r.
     gas_marked_exec T (ctx,func)
       (bind (bind (eval_expr cx e) (read_result cx))
          (write_place cx (MemoryPlace id []))) (es,s0) m res ee r ==>
     gas_marked_exec T (ctx,func)
       (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
       m res ee r` by
    (drule assign_local_admissible_run >> rpt strip_tac >>
     fs[gas_marked_exec_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb'`, `op`, `s0`] mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[] >>
  metis_tac[gas_exempt_cert_unforce_result]
QED

Resume assign_local_word_frag_mem[exception]:
  markerLib.RESUME_TAC >> (
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (first_x_assum irule >> irule gas_marked_exec_bind_exception >>
      simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type])
QED

Resume assign_local_word_frag_mem[normal]:
  markerLib.RESUME_TAC >> (
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v, es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id es_end.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by
    (qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl [`es_end with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings`] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es_end`, `t`, `id`, `p`, `sz`,
    `pre`, `env`, `entry`, `rest`, `v`, `etv`, `op`, `sb'`, `sb`] mp_tac
    assign_local_word_store_path_mem >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  qexistsl_tac [`INL ()`,
    `es_end with scopes :=
       pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`,
    `OK u`] >>
  conj_tac
  >- (qpat_x_assum `!m res ee r. gas_marked_exec _ _ _ _ _ _ _ _ ==> _`
        irule >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
        |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
      conj_tac
      >- (irule gas_marked_exec_end_gas_obs >> simp[]) >>
      simp[gas_marked_exec_def, gas_explicit_def, gas_prefix_def]) >>
  disj1_tac >> simp[] >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> metis_tac[])
QED

Finalise assign_local_word_frag_mem

Theorem body_assign_local_word_mem:
  !cx id e ty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME ty` by metis_tac[expr_sim_inv_def] >>
  `expr_sim_mem ctx func cenv cx ty e es` by
    metis_tac[body_expr_mem_ok_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?etv. evaluate_type (get_tenv cx) ty = SOME etv` by
    (gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     `IS_SOME (lookup_scopes id es.scopes)` by metis_tac[] >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  irule assign_local_word_frag_mem >> simp[] >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME entry.type` by
    (qpat_x_assum `expr_sim_inv _ _ _ es1`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def,
          env_consistent_def, env_scopes_consistent_def]) >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes _ es1.scopes = _ ==> _`
       irule >>
     qexists_tac `id` >> simp[]) >>
  gvs[] >> metis_tac[store_lays_out_typed]
QED
