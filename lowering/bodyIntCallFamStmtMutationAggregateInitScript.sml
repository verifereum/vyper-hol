(* Counted aggregate initialization followed by source-local activation. *)
Theory bodyIntCallFamStmtMutationAggregateInit
Ancestors
  bodyIntCallFamStmtMutationForcedInit bodyIntCallFamStmtMutationSourceActivation
  bodyIntCallFamStmtMutationActivate bodyIntCallFamStmtReturnEndpointTypes
  gasSummary stmtSimDefs loweringPosts venomInst venomState
  vyperState vyperInterpreter valueEncoding exprLoweringProps
  bodyDeclCopyMemory bodyIntCallJointContract exprSimHypsDefs
  localPtrsProps freshWrites bodySim compileEnv exprSimHyps

Theorem intcall_annassign_aggregate_continuation:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx /\
  intcall_joint_res fp ce env es sa0 s0 /\
  supported_stmt fp.jc_tops bindings (AnnAssign id ty e) /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AnnAssign id ty e)) /\
  stmt_env ce lctx ret (AnnAssign id ty e) sa0 = (c,sf) /\
  declare_local ce id ty sa0 = (c,st) /\ ce.ce_alloca_locals /\
  gas_admissible (eval_stmt fp.jc_cx (AnnAssign id ty e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
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
  expr_val_at c fp.jc_cx (post_value_type c e) sA sB
    (ee with gas_obs := []) v op t /\
  (!x. op = Var x ==> not_fresh_at sB x) /\
  (post_value_type c e <> NoneT /\ ~is_word_type (post_value_type c e) /\
   ~is_bytestring_type (post_value_type c e) ==>
    !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type c e) = SOME tv ==>
      ?sw a k. eval_operand op t = SOME sw /\ a <= w2n sw /\
        w2n sw + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
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
  drule_all intcall_annassign_forced_initializer_run >> strip_tac >>
  suspend "activation"
QED

Resume intcall_annassign_aggregate_continuation[activation]:
  drule_all intcall_annassign_compound_post_type >> strip_tac >>
  drule_all marked_forced_destination_typed >> strip_tac >>
  `val_wf dtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!ty. type_memory_bytes c ty = type_memory_bytes ce ty` by
    metis_tac[declare_local_memory_types_mem] >>
  `type_memory_bytes ce ty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size,expr_body_pre_def] >>
  `local_ptrs_reserved c sA` by fs[intcall_expr_res_def] >>
  `not_fresh_at sA p` by metis_tac[local_ptrs_reserved_def] >>
  `sA.cs_next_var <= sB.cs_next_var` by metis_tac[compile_expr_grows] >>
  `not_fresh_at sB p` by fs[not_fresh_at_def] >>
  `lookup_var p t = SOME w` by metis_tac[intcall_expr_cont_def] >>
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
  suspend "framing"
QED

Resume intcall_annassign_aggregate_continuation[framing]:
  qexistsl [`ff`,`u`] >>
  conj_tac >-
    (simp[gas_marked_exec_def,gas_explicit_def] >> metis_tac[]) >>
  simp[stmt_lands_def] >>
  fs[intcall_expr_cont_def] >>
  rpt strip_tac >>
  `not_fresh_at sB x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Finalise intcall_annassign_aggregate_continuation
