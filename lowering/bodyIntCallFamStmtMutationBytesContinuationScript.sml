(* Counted bytes initialization and source-local activation.  The physical
   source capacity is independent of both semantic and destination capacity. *)
Theory bodyIntCallFamStmtMutationBytesContinuation
Ancestors
  bodyIntCallFamStmtMutationBytesAssign bodyIntCallFamStmtMutationSourceActivation
  bodyIntCallFamStmtMutationActivate bodyIntCallFamStmtReturnEndpointTypes
  gasSummary stmtSimDefs loweringPosts venomInst venomState
  vyperState vyperInterpreter valueEncoding valueEncodingTyping exprLoweringProps
  bodyDeclCopyMemory bodyIntCallJointContract exprSimHypsDefs
  localPtrsProps freshWrites bodySim compileEnv exprSimHyps
  allocLimits emitHelperProps venomMemDefs exprReasonOperand

Theorem intcall_annassign_bytes_continuation:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa0 s0 /\
  supported_stmt fp.jc_tops bindings (AnnAssign id ty e) /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AnnAssign id ty e)) /\
  stmt_env ce lctx ret (AnnAssign id ty e) sa0 = (c,sf) /\
  declare_local ce id ty sa0 = (c,st) /\ ce.ce_alloca_locals /\
  gas_admissible (eval_stmt fp.jc_cx (AnnAssign id ty e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  is_bytestring_type ty /\ is_bytestring_type (post_value_type c e) /\
  is_bytestring_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type c e) = SOME av /\
  evaluate_type (get_tenv fp.jc_cx) (lowered_value_type ce e) = SOME pv /\
  value_has_type av v /\ value_has_type dtv v /\ value_has_type pv v /\
  type_memory_bytes c (post_value_type c e) = type_memory_size av /\
  type_memory_bytes c (lowered_value_type ce e) = type_memory_size pv /\
  type_memory_size av + 64 < dimword (:256) /\
  type_memory_size pv + 64 < dimword (:256) /\
  expr_body_pre c fp.jc_cx env e es /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
  compile_assign_value c (Var p) LocMemory op F loc ty
    (lowered_value_type ce e) info bytes sB = ((),sf) /\
  fn_has_code sB sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sf /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
  intcall_expr_res fp c env es sA salloc /\ lookup_var p salloc = SOME w /\
  FLOOKUP salloc.vs_allocas st.cs_next_id =
    SOME (w2n w,w2n (n2w (type_memory_bytes ce ty) : bytes32)) /\
  fp.jc_lo <= w2n w /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
    (fn_insts fp.jc_func) /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    (es,salloc) marks (INL v) ee (OK t) /\
  expr_val_rel fp.jc_cx (post_value_type c e) v op t /\
  (!x. op = Var x ==> not_fresh_at sB x) /\
  intcall_expr_cont fp c env es sA salloc (ee with gas_obs := []) sB t ==>
  ?ff u. gas_marked_exec F (fp.jc_ctx,fp.jc_func) (new_variable id dtv v)
    (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
    stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
    cenv_top_ext ce c ff.scopes /\
    intcall_joint_res fp c env' (ff with gas_obs := []) sf u /\
    (!x wd. not_fresh_at sA x /\ lookup_var x salloc = SOME wd ==>
            lookup_var x u = SOME wd) /\
    (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    salloc.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  drule_all intcall_annassign_source_activation >> strip_tac >>
  `!ty. type_memory_bytes c ty = type_memory_bytes ce ty` by
    metis_tac[declare_local_memory_types_mem] >>
  `type_memory_bytes ce ty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size,expr_body_pre_def] >>
  `type_memory_size dtv < 2 ** 64` by
    fs[stmt_exprs_ok_def,alloc_limits_stmt_def] >>
  `w2n (n2w (type_memory_size dtv) : bytes32) = type_memory_size dtv` by
    (simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >> gvs[]) >>
  `local_ptrs_reserved c sA` by fs[intcall_expr_res_def] >>
  `not_fresh_at sA p` by metis_tac[local_ptrs_reserved_def] >>
  `sA.cs_next_var <= sB.cs_next_var` by metis_tac[compile_expr_grows] >>
  `not_fresh_at sB p` by fs[not_fresh_at_def] >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_size dtv)` by
    (fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `not_local_ptr c ee.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  suspend "run"
QED

Resume intcall_annassign_bytes_continuation[run]:
  `!lbl. op <> Label lbl` by
    (drule lower_compile_expr_not_label >>
     disch_then (qspec_then `env` mp_tac) >>
     simp[expr_body_pre_def,expr_sim_inv_def] >>
     fs[expr_body_pre_def,expr_sim_inv_def]) >>
  `?sw. eval_operand op t = SOME sw /\
    val_in_memory av v (w2n sw) t.vs_memory` by
    (fs[expr_val_rel_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  `intcall_expr_res fp c env (ee with gas_obs := []) sB t /\
   ~t.vs_halted /\ t.vs_current_bb = sB.cs_current_bb /\
   t.vs_inst_idx = LENGTH sB.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `!name a n. local_region c ee.scopes t name a n ==>
    regions_disjoint (w2n w) (type_memory_size dtv) a n` by
    (rpt strip_tac >>
     `(mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes ce ty))] [p]).inst_outputs = [p]` by
       simp[mk_inst_def] >>
     `FLOOKUP t.vs_allocas (mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes ce ty))] [p]).inst_id =
        SOME (w2n w,type_memory_size dtv)` by simp[mk_inst_def] >>
     `alloca_inv t /\ local_ptrs_rel fp.jc_func c ee.scopes t` by
       fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
  `?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    val_in_memory dtv v (w2n w) u.vs_memory /\
    intcall_expr_res fp c env (ee with gas_obs := []) sf u /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!x wd. not_fresh_at sB x /\ lookup_var x t = SOME wd ==>
       lookup_var x u = SOME wd) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    t.vs_alloca_next <= u.vs_alloca_next` by
    (irule intcall_bytes_initializer_run >> simp[] >>
     conj_tac >-
       (qexistsl [`w2n w`,`mk_inst st.cs_next_id ALLOCA
          [Lit (n2w (type_memory_bytes ce ty))] [p]`,`type_memory_size dtv`] >>
        simp[mk_inst_def] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[eval_operand_def] >>
     metis_tac[]) >>
  suspend "activation"
QED

Resume intcall_annassign_bytes_continuation[activation]:
  `val_wf dtv v` by metis_tac[value_has_type_val_wf] >>
  `lookup_var p u = SOME w /\
   FLOOKUP u.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_size dtv)` by
    metis_tac[] >>
  `intcall_joint_res fp c env' (ff with gas_obs := []) sf u` by
    (qpat_assum `ff = _` SUBST1_TAC >> simp[] >>
     irule (intcall_declared_local_activate_resources |> SIMP_RULE bool_ss [LET_THM]) >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (qpat_assum `expr_sim_inv c _ env' _` mp_tac >>
        qpat_assum `ff = _` SUBST1_TAC >>
        `!ei ss gs. ei with <|scopes := ss; gas_obs := gs|> =
          (ei with scopes := ss) with gas_obs := gs` by
          simp[evaluation_state_component_equality] >>
        pop_assum (fn th => pure_once_rewrite_tac[th]) >>
        simp[expr_sim_inv_gas_obs]) >>
     conj_tac >-
       (qexists `mk_inst st.cs_next_id ALLOCA
          [Lit (n2w (type_memory_bytes ce ty))] [p]` >>
        simp[mk_inst_def] >> metis_tac[]) >>
     metis_tac[]) >>
  qexistsl [`ff`,`u`] >>
  conj_tac >-
    (simp[gas_marked_exec_def,gas_explicit_def] >> metis_tac[]) >>
  simp[stmt_lands_def] >>
  fs[intcall_expr_cont_def] >>
  rpt strip_tac >>
  `not_fresh_at sB x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Finalise intcall_annassign_bytes_continuation
