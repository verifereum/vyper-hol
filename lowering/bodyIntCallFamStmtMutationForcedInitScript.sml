(* Normalize a forced aggregate initializer without changing its provenance. *)
Theory bodyIntCallFamStmtMutationForcedInit
Ancestors
  bodyIntCallFamStmtMutationAssignRun bodyIntCallFamStmtReturnTypes
  bodyIntCallFamStmtReturnEndpointTypes bodyDeclCopyMemory
  bodyIntCallJointStmtBoundary exprSimHyps exprSimHypsDefs exprSimSource
  bodySim vyperTypeSystem vyperTypeInvariants typedMemoryCopy
  compileEnv loweringPosts vyperTypeArgFits bodyIntCallJointContract
  allocLimits exprLoweringProps emitHelperProps localPtrsProps venomState
  venomInst venomMemDefs fragExec gasSummary vyperInterpreter vyperState
  exprReasonOperand freshWrites

Theorem intcall_annassign_compound_post_type:
  expr_body_pre c cx env e es /\
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  lowered_value_type ce e = post_value_type c e /\
  type_widens_to (get_tenv cx) (post_value_type c e) ty /\
  ~is_word_type (post_value_type c e) /\
  ~is_bytestring_type (post_value_type c e)
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    fs[type_stmt_def,AllCaseEqs()] >>
  `expr_sim_inv c cx env es` by fs[expr_body_pre_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_from_word,type_widens_from_bytestring] >>
  drule expr_body_pre_var_types_well_formed >> disch_then assume_tac >>
  `sfields_tenv_consistent c.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  drule_all compound_lowered_post_type >> strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all return_post_type_widens >> strip_tac >>
  metis_tac[type_widens_from_word,type_widens_from_bytestring]
QED

Theorem intcall_annassign_forced_initializer_run:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx /\
  expr_body_pre c fp.jc_cx env e es /\
  declare_local ce id ty sa0 = (c,st) /\ ce.ce_alloca_locals /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty e) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
  compile_assign_value c (Var p) LocMemory op F loc ty
    (lowered_value_type ce e) info bytes sB = ((),sf) /\
  fn_has_code sB sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
  intcall_expr_res fp c env es sA salloc /\
  lookup_var p salloc = SOME w /\
  FLOOKUP salloc.vs_allocas st.cs_next_id =
    SOME (w2n w,w2n (n2w (type_memory_bytes ce ty) : bytes32)) /\
  fp.jc_lo <= w2n w /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
    (fn_insts fp.jc_func) /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    (es,salloc) marks (INL v) ee (OK t) /\
  lookup_scopes id ee.scopes = NONE /\
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
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    val_in_memory dtv v (w2n w) u.vs_memory /\
    intcall_expr_res fp c env (ee with gas_obs := []) sf u /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!x wd. not_fresh_at sB x /\ lookup_var x t = SOME wd ==>
       lookup_var x u = SOME wd) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
    not_local_ptr c ee.scopes p
Proof
  strip_tac >> drule_all intcall_annassign_compound_post_type >> strip_tac >>
  drule_all marked_forced_post_typed >> strip_tac >>
  drule_all marked_forced_destination_typed >> strip_tac >>
  `expr_sim_inv c fp.jc_cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes c ty = type_memory_size dtv /\
   type_memory_bytes c (post_value_type c e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  `type_memory_size dtv < 2 ** 64` by
    fs[stmt_exprs_ok_def,alloc_limits_stmt_def] >>
  `type_memory_size dtv + 64 < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> gvs[]) >>
  `post_value_type c e <> NoneT` by
    (strip_tac >> fs[type_stmt_def,AllCaseEqs(),assignable_type_def]) >>
  suspend "resource_premises"
QED

Resume intcall_annassign_forced_initializer_run[resource_premises]:
  `?sw a k. eval_operand op t = SOME sw /\ a <= w2n sw /\
    w2n sw + type_memory_size tv <= a+k /\ a+k < dimword (:256)` by
    metis_tac[] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `local_ptrs_reserved c sA` by fs[intcall_expr_res_def] >>
  `not_fresh_at sA p` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_size dtv)` by
    (fs[intcall_expr_cont_def] >>
     `w2n (n2w (type_memory_size dtv) : bytes32) = type_memory_size dtv` by
       (simp[wordsTheory.w2n_n2w] >>
        irule arithmeticTheory.LESS_MOD >>
        simp[wordsTheory.dimword_def] >> gvs[]) >>
     metis_tac[]) >>
  `not_local_ptr c ee.scopes p` by
    metis_tac[local_ptrs_reserved_not_live] >>
  suspend "copy_application"
QED

Resume intcall_annassign_forced_initializer_run[copy_application]:
  `!lbl. op <> Label lbl` by
    (drule lower_compile_expr_not_label >>
     disch_then (qspec_then `env` mp_tac) >>
     simp[expr_body_pre_def,expr_sim_inv_def] >>
     fs[expr_body_pre_def,expr_sim_inv_def]) >>
  `sA.cs_next_var <= sB.cs_next_var /\ sA.cs_next_id <= sB.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sB p` by metis_tac[not_fresh_at_mono] >>
  `st.cs_next_id < sA.cs_next_id` by
    (drule emit_inst_extends >> simp[]) >>
  `intcall_expr_res fp c env (ee with gas_obs := []) sB t /\
   ~t.vs_halted /\ t.vs_current_bb = sB.cs_current_bb /\
   t.vs_inst_idx = LENGTH sB.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `alloca_inv t /\ local_ptrs_rel fp.jc_func c ee.scopes t /\
   alloca_room fp.jc_ctx fp.jc_func t` by
    fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def] >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (`w2n w + type_memory_size dtv <= t.vs_alloca_next` by
       metis_tac[alloca_inv_def,alloca_next_valid_def] >>
     fs[alloca_room_def] >> decide_tac) >>
  suspend "disjoint_application"
QED

Resume intcall_annassign_forced_initializer_run[disjoint_application]:
  `!name a n. local_region c ee.scopes t name a n ==>
    a+n <= w2n w \/ w2n w + type_memory_size dtv <= a` by
    (rpt strip_tac >>
     `(mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes ce ty))] [p]).inst_outputs = [p]` by
       simp[mk_inst_def] >>
     `FLOOKUP t.vs_allocas (mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes ce ty))] [p]).inst_id =
        SOME (w2n w,type_memory_size dtv)` by simp[mk_inst_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n sw) t.vs_memory` by
    metis_tac[expr_val_rel_def,optionTheory.SOME_11] >>
  simp[] >>
  irule intcall_aggregate_initializer_run >>
  simp[] >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >> simp[] >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`type_memory_size dtv`,
    `mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes ce ty))] [p]`, `w2n w`] >>
  simp[mk_inst_def,eval_operand_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise intcall_annassign_forced_initializer_run
