(* Source-layout-equality preparation for the joint aggregate declaration. *)
Theory bodyFullAnnAssignOther
Ancestors
  bodySim bodySimFull bodyFullPreds bodyFullAllocaFresh bodyFullUnwrap
  bodyFullAnnAssignMemoryPost bodyInvNoDalloca gasOutcomeFullCompose
  stmtSimDeclSource gasOutcomeFullStmts gasExemptCert vyperStorageTrace
  stmtLoweringMono allocLimits exprSimAggregateLayout bodyDeclCopyMemory
  annassignRelayoutSource memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  stmtSimDeclTypedCode stmtSimDeclSourceSeparation externalNormalizePremises
  assignBasePtrBoundary
  exprOperandVar bodyPtrDefs exprSimMemDefs loweringPosts
  vyperTypeValues vyperTypeInvariants vyperTypeExprSoundness valueTypingMemoryProps
  compileEnv exprLowering stmtLowering vyperInterpreter vyperState
  vyperValue vyperAST finite_map list
Libs monadsyntax

Theorem annassign_other_typed_layout:
  expr_body_pre ce cx env e es /\ env.type_defs = get_tenv cx /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  lowered_value_type ce e = expr_type e /\
  type_memory_bytes ce typ < 2 ** 64 ==>
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  post_value_type ce e = expr_type e /\
  type_memory_bytes ce (expr_type e) = type_memory_size stv /\
  type_memory_bytes ce typ = type_memory_size dtv /\
  0 < type_memory_size stv /\
  type_memory_size stv <= type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[normalize_return_source_kinds] >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  `type_widens_to (get_tenv cx) (expr_type e) typ` by metis_tac[] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  simp[post_value_type_lowered] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `value_runtime_typed env (expr_type e) v /\ value_runtime_typed env typ v` by
    metis_tac[memory_rhs_read_annotation_typed, memory_rhs_read_destination_typed] >>
  `value_has_type stv v /\ value_has_type dtv v` by
    gvs[value_runtime_typed_def] >>
  simp[value_has_type_memory_wf] >>
  metis_tac[normalize_nonbytes_footprint]
QED

(* Adapt the actual nonbytes RHS, including a source in a live local, to
   the shared aggregate suffix.  Source and destination widths stay distinct. *)
Theorem annassign_other_typed_rhs_resources:
  lowered_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes ce (expr_type e) = type_memory_size stv /\
  0 < type_memory_size stv /\ value_has_type stv v /\
  expr_post H ctx func ce cx e es sa sb s0 mid v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  not_local_ptr ce mid.scopes p /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  type_memory_size dtv <= sz ==>
  ?xs sw.
    op = Var xs /\ lookup_var xs s = SOME sw /\ not_fresh_at sb xs /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    (type_memory_size stv = 0 \/
      w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    expr_val_at ce cx (expr_type e) sa sb mid v (Var xs) s /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `stmt_state_rel H ctx func ce cx mid s /\
   expr_val_at ce cx (expr_type e) sa sb mid v op s` by fs[expr_post_def] >>
  drule_all normalize_source_window >> strip_tac >> gvs[] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    metis_tac[ptr_buf_ok_read_covers, arithmeticTheory.LESS_EQ_REFL] >>
  gvs[] >>
  `not_fresh_at sb xs` by metis_tac[compile_lower_value_var] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[normalize_nonbytes_footprint] >>
  `0 < val_footprint stv v` by simp[] >>
  `w2n w + type_memory_size stv <= w2n dw \/ w2n dw+sz <= w2n w` by
    metis_tac[expr_val_at_alloca_outside_interval_separate] >>
  qexists_tac `w` >>
  fs[venomStateTheory.eval_operand_def, ptr_val_ok_def, ptr_mem_ok_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED

Theorem annassign_other_typed_full_execution:
  (!(H0 : (bool # 256 word # type_value) list # num list) ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v
   n sz aid0 start lo explicit PG G tn.
    compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
      dty sty (type_memory_bytes ce dty) sa = ((),sf) /\
    ~is_word_type dty /\ ~is_word_type sty /\
    stmt_state_rel H0 ctx func ce cx mid s /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ alloca_history func s /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        len = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size dtv <= sz /\ n < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa p /\
    lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid0 = SOME (w2n dw,sz) /\ aid0 < sa.cs_next_id /\
    ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw+n < dimword (:256) /\
    w2n dw+type_memory_size dtv < dimword (:256) /\
    (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
    (src_loc = SOME LocMemory ==>
      expr_val_at ce cx sty start sa mid v (Var xs) s) /\
    (src_loc <> SOME LocMemory ==>
      w2n sw+n <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n sw) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u sm Gu tnu t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      (!(H : (bool # 256 word # type_value) list # num list).
        stmt_state_rel H ctx func ce cx mid s ==>
        stmt_state_rel H ctx func ce cx mid u) /\
      (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
        ghost_inv_at D lo d ce cx mid Gu tnu u) /\
      alloca_frame ce mid sa s ce mid u /\
      (!aid off len i.
        FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region ce mid.scopes s name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tnu.t_mem ==> i IN tn.t_mem) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      s.vs_alloca_next <= u.vs_alloca_next /\
      sa.cs_next_id <= sm.cs_next_id /\ local_ptrs_reserved ce sm /\
      (!x. not_fresh_at sa x ==>
        not_fresh_at sm x /\ lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)) /\
      lookup_var p u = SOME dw /\ ptr_covers Gu tnu p u sz /\
      typed_copy_state_frame sm (w2n dw) (type_memory_size dtv) u t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
        val_in_memory dtv v (w2n dw) mem) /\
      tf.t_stor = tnu.t_stor /\ tf.t_trans = tnu.t_trans /\ tf.t_imm = tnu.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
        (i IN tf.t_mem <=> i IN tnu.t_mem)) /\
      (!x. not_fresh_at sm x ==>
        lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
        op_taint tf (Var x) = op_taint tnu (Var x)) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)) /\
  (!(H : (bool # 256 word # type_value) list # num list) D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf
   id p sz w inst n tyv v sc rest lctx.
    new_variable id tyv v mid = (INL (),out) /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    FLOOKUP old.ce_vars id = NONE /\
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
    local_ptrs_reserved ce b /\ not_fresh_at b p /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
    n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
    val_wf tyv v /\ value_has_type tyv v /\
    typed_copy_state_frame b (w2n w) n s t /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame old es sa s0 ce mid s /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP s.vs_allocas aid = SOME ent) /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
    cenv_top_ext old ce out.scopes /\
    stmt_state_rel H ctx func ce cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce cx out Gf tf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce out t /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  env.type_defs = get_tenv cx /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  lowered_value_type cenv e = expr_type e /\
  ~is_word_type typ /\ expr_type e <> typ /\ ~is_bytestring_type typ /\
  ~(has_length_word typ /\ is_empty_value_expr e) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!H0 ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v n sz aid0 start lo explicit PG G tn.
    compile_assign_value _ _ _ _ _ _ _ _ _ _ = _ /\ _ ==> _`
    (mk_asm "dispatch") >>
  qpat_x_assum `!H D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf id p sz w inst n tyv v sc rest lctx. _`
    (mk_asm "install") >>
  `~ctx_has_dalloca ctx` by
    (drule body_inv_no_dalloca >> simp[]) >>
  `cenv.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (strip_assume_tac o PURE_REWRITE_RULE [body_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all annassign_full_prefix_parts >>
  disch_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) >>
  gnvs[] >>
  qpat_x_assum `!sa ce r ty. declare_local _ _ _ _ = _ ==> _` drule >>
  disch_then (qspec_then `expr_type e` strip_assume_tac) >>
  suspend "layout"
QED

Resume annassign_other_typed_full_execution[layout]:
  `type_memory_bytes cenv typ < 2 ** 64` by
    (qpat_assum `stmt_exprs_ok cenv (AnnAssign id typ e)`
       (strip_assume_tac o
        PURE_REWRITE_RULE [stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  `lowered_value_type cenv' e = expr_type e /\
   type_memory_bytes cenv' typ < 2 ** 64` by fs[] >>
  drule annassign_other_typed_layout >>
  disch_then (qspecl_then [`typ`,`stv`,`dtv`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  suspend "prefix"
QED

Resume annassign_other_typed_full_execution[prefix]:
  irule gas_outcome_full_initial_domain >>
  simp[] >> (conj_tac >- simp[evaluate_storage_trace_frame]) >>
  disch_tac >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `~(has_length_word typ /\ is_empty_value_expr e)` by metis_tac[] >>
  gnvs[Excl "NOT_AND"] >>
  qpat_x_assum `unwrap_value cenv' vv sv = _ /\ _` strip_assume_tac >>
  `type_memory_size dtv = type_memory_bytes cenv typ` by simp[] >>
  drule_all annassign_full_alloc_rhs_prefix >>
  disch_then (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac) >>
  suspend "compose"
QED

Resume annassign_other_typed_full_execution[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >> (conj_tac >- simp[]) >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `childQ` >> reverse conj_tac
  >- suspend "continuation" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res`
  >- fs[Abbr `childR`, exprSimDefsTheory.expr_exit_def] >>
  fs[Abbr `childR`, stmt_exit_ptr_def, exprSimDefsTheory.halt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume annassign_other_typed_full_execution[continuation]:
  FAIL_TAC "continuation"
QED

Finalise annassign_other_typed_full_execution
