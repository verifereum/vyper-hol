(* Declaration entry: the pending compile binding uses expression resources. *)
Theory bodyIntCallFamStmtMutationEntry
Ancestors
  bodyIntCallFamStmtMutationDeclAlloc bodyIntCallFamStmtMutationDeclEntry
  bodyIntCallJointContract bodySimDeclCases bodyExprPreFacts bodySim
  vyperTypeSystem vyperTypeInvariants exprSimHypsDefs supportedStmtTraverse
  vyperTypeCallGraph vyperTypeCallStackSoundness gasContext finite_map
  bodyDeclMemoryCore stmtSimProps exprLoweringProps fragExec

Theorem intcall_pending_declaration_pre:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa s /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  supported_expr fp.jc_tops e /\ stmt_exprs_ok ce (AnnAssign id ty e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id ty e) ==> occurs_abi_decode_target target fp.jc_tops) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  declare_local ce id ty sa = (c,st) ==>
  lookup_scopes id es.scopes = NONE /\ FLOOKUP ce.ce_vars id = NONE /\
  same_frame ce c /\ body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx /\
  intcall_expr_res fp c env es st s /\ expr_body_pre c fp.jc_cx env e es
Proof
  strip_tac >>
  `well_typed_expr env e /\ id NOTIN FDOM env.var_types` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `FLOOKUP ce.ce_vars id = NONE` by
    (irule declared_name_unbound >> fs[intcall_joint_res_def] >> metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
        finite_mapTheory.FLOOKUP_DEF] >>
     Cases_on `lookup_scopes id es.scopes` >> gvs[] >> metis_tac[]) >>
  `same_frame ce c` by (drule declare_local_same_frame >> simp[]) >>
  `body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx` by
    metis_tac[body_inv_same_frame] >>
  `intcall_expr_res fp c env es st s` by
    (irule intcall_expr_res_declare_local_pending >>
     qexistsl_tac [`ce`, `id`, `sa`, `ty`] >> fs[intcall_joint_res_def]) >>
  simp[] >>
  drule supported_expr_body_calls >> strip_tac >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre)) >>
  simp[] >>
  `stmt_exprs_ok c (AnnAssign id ty e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  fs[intcall_expr_res_def, stmt_exprs_ok_def,
     supported_stmt_expr_exists_def, intcall_frame_ok_def,
     body_inv_def, gasContextTheory.cx_tops_def,
     call_evaluation_safe_def] >>
  metis_tac[]
QED

(* The compiler's declaration/ALLOCA prefix, with exclusions derived rather
   than required from its caller.  The inactive slot is safe to initialize. *)
Theorem intcall_declaration_alloca_prefix:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  ce.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  declare_local ce id ty sa = (c,st) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  fn_has_code sa sA fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_res fp c env es sA t /\
    ~t.vs_halted /\ t.vs_current_bb = sA.cs_current_bb /\
    t.vs_inst_idx = LENGTH sA.cs_current_insts /\
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (w2n w,w2n (n2w (type_memory_bytes ce ty) : bytes32)) /\
    fp.jc_lo <= w2n w /\ t.vs_memory = s.vs_memory /\
    (!op. op <> Var p ==> eval_operand op t = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sa s /\ local_ptrs_reserved ce sa` by
    metis_tac[intcall_joint_res_def, intcall_expr_res_def] >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by simp[] >>
  drule_all annassign_setup_shape >> strip_tac >>
  `intcall_expr_res fp c env es st s` by
    (irule intcall_expr_res_declare_local_pending >>
     qexistsl_tac [`ce`, `id`, `sa`, `ty`] >> simp[]) >>
  drule_all intcall_declare_local_pointer_exclusions >> strip_tac >>
  `fn_has_code st sA fp.jc_func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all intcall_declared_alloca_entry >> metis_tac[]
QED
