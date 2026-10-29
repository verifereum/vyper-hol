(*
 * Internal calls: the return step (#638)
 *
 * The callee's body ends in an IntRet that result_rel accepts (intret_q:
 * a stack return, or a memory return through the caller's buffer,
 * intret_mem_q).  The caller's INVOKE then gives merge_callee_state with
 * the outputs bound, and the caller's statement relation holds again at
 * the source state eval_expr's IntCall case returns: the callee's final
 * state with the caller's scopes back.
 *
 * TOP-LEVEL:
 *   eval_expr_intcall_return — the source side: a body that returns a
 *                              well-typed value makes the call return it,
 *                              with the caller's scopes back
 *   invoke_intret_state_rel  — the Venom side: the INVOKE returns, the
 *                              caller's stmt_state_rel holds at that
 *                              source state, and the outputs hold the
 *                              returned words
 *
 * The caller's live locals surviving the callee's memory writes comes from
 * intCallFrame: invoke_intret_state_rel takes its callee_writes_above
 * premise, with the exempt regions missing the caller's live regions.
 *
 * Helpers: run_blocks_intret_data_section
 *)

Theory intCallReturn
Ancestors
  list rich_list finite_map
  intCallStep intCallFrame stmtSimReturn exprLoweringProps localPtrsProps compileEnv
  vyperCall vyperTyping vyperInterpreter vyperState
  venomExecSemantics venomExecProofs venomInstProofs opcodeClass venomInst
  venomState
Libs
  monadsyntax

(* ===== The source side ===== *)

(* eval_expr's IntCall case when the callee's body returns v, of the
   return type: the call's value is v, in the callee's final state with
   the caller's scopes back (pop_function), as handle_function and
   safe_cast leave a well-typed v alone. *)
Theorem eval_expr_intcall_return:
  !cx ty src fn es_args drv st ts mut ps dflts ret body vs es env tv v es2.
    ~MEM (src,fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut, F, ps, dflts, ret, body) /\
    LENGTH es_args = LENGTH ps /\
    (do rs <- eval_expr_results cx es_args; read_results cx rs od) st =
      (INL vs, es) /\
    bind_arguments (get_tenv cx) ps vs = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME tv /\
    eval_stmts (cx with stk updated_by CONS (src,fn)) body
      (es with scopes := [env]) = (INR (ReturnException v), es2) /\
    value_has_type tv v ==>
    eval_expr cx (Call ty (IntCall (src,fn)) es_args drv) st =
      (INL (Value v), es2 with scopes := es.scopes)
Proof
  rpt strip_tac >>
  qpat_x_assum `(do rs <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `eval_expr_results cx es_args st` >>
  rename1 `_ = (raw, st1)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_results_state >> gvs[] >>
  drule_all eval_expr_intcall_unfold >>
  disch_then (fn th => simp[th]) >>
  drule safe_cast_well_typed >>
  simp[handle_function_def, lift_option_type_def, bind_def, return_def]
QED

(* ===== The Venom side ===== *)

Theorem pack_dret_dynamic_data_section[local]:
  !cursor pairs s ptrs fc s'.
    pack_dret_dynamic cursor pairs s = (ptrs, fc, s') ==>
    s'.vs_data_section = s.vs_data_section
Proof
  Induct_on `pairs` >> simp[] >>
  Cases >> rw[pack_dret_dynamic_def] >>
  pairarg_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

(* A terminator that continues the function (a jump) or returns from it
   (RET, RETFMP, DRET) leaves the data section alone. *)
Theorem step_inst_base_term_data_section[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    (step_inst_base inst s = OK s' \/ ?r. step_inst_base inst s = IntRet r s') ==>
    s'.vs_data_section = s.vs_data_section
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_assum `inst.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC
      [tryfind (fn th => MATCH_MP th eq)
         (CONJUNCTS step_inst_base_opcode_eqs)]) >>
  simp[AllCaseEqs(), jump_to_def] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac pack_dret_dynamic_data_section >> gvs[]
QED

Theorem eval_phis_data_section[local]:
  !insts s s'. eval_phis s insts = OK s' ==>
               s'.vs_data_section = s.vs_data_section
Proof
  Induct >> rw[eval_phis_def] >> gvs[AllCaseEqs(), update_var_def] >>
  res_tac
QED

(* An instruction that continues the block or returns from the function
   leaves the data section alone; an INVOKE keeps the caller's. *)
Theorem step_inst_data_section[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' \/
    (?r. step_inst fuel ctx inst s = IntRet r s') ==>
    s'.vs_data_section = s.vs_data_section
Proof
  rpt gen_tac >> strip_tac
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
          irule step_inst_base_term_data_section >>
          gvs[Once step_inst_def] >> metis_tac[]) >>
      drule_all step_preserves_data_section >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >> IF_CASES_TAC
  >- (simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  strip_tac >>
  `is_terminator inst.inst_opcode` by
    (drule step_inst_base_intret_opcodes >> strip_tac >>
     gvs[is_terminator_def]) >>
  irule step_inst_base_term_data_section >> metis_tac[]
QED

Theorem exec_block_data_section[local]:
  !n fuel ctx bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx ==>
    (!s'. exec_block fuel ctx bb s = OK s' ==>
          s'.vs_data_section = s.vs_data_section) /\
    (!r s'. exec_block fuel ctx bb s = IntRet r s' ==>
            s'.vs_data_section = s.vs_data_section)
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  simp[Once exec_block_def, AllCaseEqs()] >> strip_tac >>
  gvs[get_instruction_def] >>
  imp_res_tac step_inst_data_section >> gvs[] >>
  rename1 `exec_block fuel ctx bb (s1 with vs_inst_idx := _)` >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
    `s1 with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem run_block_data_section[local]:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' \/ (?r. run_block fuel ctx bb s = IntRet r s') ==>
    s'.vs_data_section = s.vs_data_section
Proof
  rpt gen_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  simp[run_block_def] >>
  rename1 `eval_phis s _ = OK s0` >>
  drule eval_phis_data_section >> rpt strip_tac >>
  qspecl_then [`LENGTH bb.bb_instructions -
                  phi_prefix_length bb.bb_instructions`, `fuel`, `ctx`, `bb`,
               `s0 with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
    mp_tac exec_block_data_section >>
  simp[] >> metis_tac[]
QED

(* A callee's run leaves the data section alone. *)
Theorem run_blocks_intret_data_section:
  !fuel ctx fn s ret s'.
    run_blocks fuel ctx fn s = IntRet ret s' ==>
    s'.vs_data_section = s.vs_data_section
Proof
  Induct_on `fuel` >- simp[Once run_blocks_def] >>
  rpt gen_tac >> simp[run_blocks_unfold, AllCaseEqs()] >> strip_tac >>
  imp_res_tac run_block_data_section >> res_tac >> gvs[]
QED

(* The caller's INVOKE of a callee whose run ends in an IntRet that
   intret_q accepts, at the source state es2 the callee's body ends in.
   s and es are the caller's states at the INVOKE (after the arguments,
   the return buffer and the staged arguments).  The INVOKE returns s',
   in which:
   - the caller's stmt_state_rel holds at es2 with the caller's scopes,
     the state eval_expr's IntCall case returns
     (eval_expr_intcall_return);
   - the outputs hold the returned words, which intret_vals_match relates
     to v (store_multi_results_frag's input for a stack return), and
     memory is the callee's, so a memory return's value is in the buffer
     (intret_mem_q, buffer_vv_holds);
   - other variables, the allocations and the control fields are the
     caller's.
   Hypotheses beyond the call itself:
   - the outputs are distinct and none is a live local's pointer (the
     fresh outputs of compile_call's emit_multi_op);
   - the callee's relation is at the caller's transaction (cx' may be cx
     with the callee pushed on stk) and its compile env places immutables
     as the caller's does;
   - FRAME: the callee changed no byte below the caller's frontier
     outside the exempt regions excl, which miss the caller's live
     regions (step_inst_invoke_live_regions's premises). *)
Theorem immutables_rel_env_transport[local]:
  immutables_rel cenv' addr src ctor es ss /\
  (!n off. FLOOKUP cenv.ce_vars (module_var_key (src,n)) =
             SOME (ImmutableLoc off) ==>
           FLOOKUP cenv'.ce_vars (module_var_key (src,n)) =
             SOME (ImmutableLoc off)) ==>
  immutables_rel cenv addr src ctor es ss
Proof
  simp_tac bool_ss [immutables_rel_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  first_x_assum irule >> qexists_tac `name` >> simp[]
QED

Theorem invoke_intret_state_rel:
  !fuel ctx inst s name arg_ops callee args cs ret cs'
   func cenv cenv' cx cx' es es2 tv v excl.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name, arg_ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops s = SOME args /\
    setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    LENGTH inst.inst_outputs = LENGTH ret.iret_values /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (not_local_ptr cenv es.scopes) inst.inst_outputs /\
    stmt_state_rel func cenv cx es s /\
    immutable_alloca_sep func cenv cx (es2 with scopes := es.scopes) s /\
    intret_q callee cenv' cx' tv v (es2 with scopes := []) (IntRet ret cs') /\
    cx'.txn = cx.txn /\
    cenv'.ce_module = cenv.ce_module /\ cenv'.ce_is_ctor = cenv.ce_is_ctor /\
    (!n off. FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module, n)) =
               SOME (ImmutableLoc off) ==>
             FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module, n)) =
               SOME (ImmutableLoc off)) /\
    callee_writes_above s.vs_alloca_next excl s.vs_memory cs'.vs_memory /\
    (!n lo sz. local_region cenv es.scopes s n lo sz ==>
       EVERY (\(eb,esz). regions_disjoint lo sz eb esz) excl) ==>
    ?s'. step_inst fuel ctx inst s = OK s' /\
         stmt_state_rel func cenv cx (es2 with scopes := es.scopes) s' /\
         intret_vals_match tv v ret.iret_values /\
         (!i. i < LENGTH inst.inst_outputs ==>
              lookup_var (EL i inst.inst_outputs) s' =
                SOME (EL i ret.iret_values)) /\
         (!x. ~MEM x inst.inst_outputs ==> lookup_var x s' = lookup_var x s) /\
         s'.vs_memory = cs'.vs_memory /\
         s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
         s'.vs_current_bb = s.vs_current_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
         s'.vs_halted = s.vs_halted
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all step_inst_invoke_live_regions >> strip_tac >>
  qexists_tac `s'` >> simp[] >>
  `bind_outputs inst.inst_outputs ret.iret_values
     (adopt_return_fmp ret (merge_callee_state s cs')) = SOME s'` by
    (drule_all step_inst_invoke_intret >> strip_tac >> gvs[]) >>
  drule_all bind_outputs_lookup >> strip_tac >>
  gvs[intret_q_def, result_rel_def, adopt_return_fmp_def] >>
  `cs.vs_data_section = s.vs_data_section` by gvs[setup_callee_def] >>
  drule run_blocks_intret_data_section >> strip_tac >>
  `immutables_rel cenv' cx.txn.target cenv.ce_module cenv.ce_is_ctor es2 cs'` by
    (fs[state_rel_def] >>
     qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
     simp[immutables_rel_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es2 cs'` by
    (irule immutables_rel_env_transport >> qexists_tac `cenv'` >> simp[]) >>
  gvs[merge_callee_state_def, lookup_var_def] >>
  irule stmt_state_rel_allocas_frame >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`, `es2 with scopes := es.scopes`] >> simp[] >>
      rpt strip_tac >> qexists_tac `id` >>
      gvs[local_region_def] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` >>
      `~MEM p inst.inst_outputs` by
        (gvs[EVERY_MEM, not_local_ptr_def] >> metis_tac[]) >>
      qpat_x_assum `!x. ~MEM x inst.inst_outputs ==> _` drule >>
      gvs[lookup_var_def]) >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
  qpat_x_assum `state_rel _ _ _ _ cs'` mp_tac >>
  simp[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, log_entry_equiv_def] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `immutables_rel cenv _ _ _ es2 cs'` mp_tac >>
      simp[immutables_rel_def]) >>
  irule LIST_REL_mono >>
  qexists_tac `log_entry_equiv cenv' cx.txn.target` >>
  simp[log_entry_equiv_def]
QED
