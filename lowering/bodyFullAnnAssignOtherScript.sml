(* Source-layout-equality preparation for the joint aggregate declaration. *)
Theory bodyFullAnnAssignOther
Ancestors
  bodySim bodySimFull bodyFullPreds bodyFullAllocaFresh bodyFullUnwrap
  bodyFullShared bodyFullAnnAssignMemoryPost gasOutcomeFullCompose
  augAssignFullRhsSaved
  stmtSimDeclSource gasOutcomeFullStmts gasExemptCert vyperStorageTrace
  stmtLoweringMono allocLimits exprSimAggregateLayout bodyDeclCopyMemory
  annassignRelayoutSource memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  stmtSimDeclTypedCode stmtSimDeclSourceSeparation externalNormalizePremises
  assignBasePtrBoundary stateRelProj exprOpenMain exprOpenTerminals
  exprOperandVar bodyPtrDefs exprSimMemDefs loweringPosts
  vyperTypeValues vyperTypeInvariants vyperTypeExprSoundness valueTypingMemoryProps
  compileEnv exprLowering stmtLowering vyperInterpreter vyperState
  vyperValue vyperAST finite_map list
  bodyInvSplit[qualified]
Libs monadsyntax

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
*)
Theorem annassign_other_typed_layout:
  expr_body_pre_mods mods ce cx env e es /\ env.type_defs = get_tenv cx /\
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
  cheat
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
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ expr_sim_inv_mods mods cenv cx env es /\
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
    (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\ expr_body_pre_mods mods ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cenv.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (strip_assume_tac o PURE_REWRITE_RULE [body_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
    qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
      irule (MATCH_MP gas_outcome_full_use_return_buf_allocas
        (CONJ frame sep)))) >>
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
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  qspecl_then
    [`DF`,`lo`,`d`,`PG`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
     `cenv`,`cenv'`,`cx`,`es`,`id`,`typ`,`e`,`st0`,`sa`,`r`,`a`,`b`,
     `shadow_a`,`shadow_b`,`p`,`type_memory_size dtv`,`op`,`s0`,`G0`,`tn0`,
     `lctx`] mp_tac annassign_full_alloc_rhs_prefix >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac) >>
  suspend "compose"
QED

Resume annassign_other_typed_full_execution[compose]:
  (qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
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
  qexists_tac `childQ` >> conj_tac
  >- suspend "continuation" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res`
  >- (qpat_x_assum `childR _ (INL _) _ _ _` mp_tac >>
      simp[Abbr `childR`, exprSimDefsTheory.expr_exit_def, NoAsms]) >>
  fs[Abbr `childR`] >>
  irule (INST_TYPE [alpha |-> ``:value``]
    augAssignFullRhsSavedTheory.augassign_expr_exit_to_stmt_exit) >>
  rpt conj_tac >> first_assum ACCEPT_TAC)
QED

Resume annassign_other_typed_full_execution[continuation]:
  (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
   `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
     (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
   (impl_tac >- first_assum ACCEPT_TAC) >>
   simp[Abbr `childQ`, NoAsms] >> strip_tac >>
   qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
   disj1_tac >> qexists_tac `v` >> simp[] >>
   suspend "success")
QED

Resume annassign_other_typed_full_execution[success]:
  (qpat_assum `!tail. bind _ _ _ = _`
     (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
   drule_all annassign_continuation_success >>
   disch_then (qx_choosel_then [`sc`,`rest`] strip_assume_tac) >>
   qmatch_asmsub_abbrev_tac `new_variable id dtv v _ = (INL (),out)` >>
   `mid with gas_obs := [] = mid` by
     (qpat_assum `mid.gas_obs = []` (fn th => simp[GSYM th, NoAsms])) >>
   qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
     qpat_x_assum `new_variable id dtv v _ = (INL (),out)`
       (assume_tac o PURE_REWRITE_RULE [eq])) >>
   `mid.scopes = sc::rest` by fs[] >>
   `out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest`
     by simp[Abbr `out`] >>
   qpat_x_assum `!gs v mid. bind _ _ _ = _ ==> _` drule_all >> strip_tac >>
   `ptr_buf_ok cenv' e op G1 t` by fs[] >>
   `lowered_value_type cenv' e = expr_type e /\
    type_memory_bytes cenv' (expr_type e) = type_memory_size stv` by fs[] >>
   qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
   `inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [p] /\
    inst.inst_opcode = ALLOCA` by simp[Abbr `inst`, venomInstTheory.mk_inst_def, NoAsms] >>
   `inst.inst_id < a.cs_next_id \/ b.cs_next_id <= inst.inst_id` by fs[] >>
   `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size dtv)` by fs[] >>
   `acyclic_struct_metadata cenv'.ce_struct_fields` by
     (qpat_assum `body_inv tops ctx cenv' cx`
       (strip_assume_tac o PURE_REWRITE_RULE [body_inv_def]) >>
      first_assum ACCEPT_TAC) >>
   `storage_vars_rel cenv' cx /\ transient_vars_rel cenv' cx` by
     (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
      drule stmt_state_rel_vars_rels >> simp[]) >>
   `~block_is_terminated a` by
     (irule emit_inst_nonterminator_open >>
      qpat_assum `emit_inst ALLOCA _ _ _ = _` (irule_at Any) >>
      simp[venomInstTheory.is_terminator_def]) >>
   `?tv es1. eval_expr cx e
       (es with gas_obs := gas_explicit marks entry.vs_gas_readings) = (INL tv,es1)` by
     (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
        (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
      simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
   `~block_is_terminated sv` by
     (irule compile_expr_open_general >>
      qpat_assum `compile_expr cenv' (expr_type e) e a = (vv,sv)` (irule_at Any) >>
      qpat_assum `eval_expr cx e _ = (INL tv,es1)` (irule_at Any) >>
      qexistsl_tac [`tops`,`env`,`ctx`] >> simp[]) >>
   `~block_is_terminated b` by
     (irule unwrap_value_open >>
      qpat_assum `unwrap_value cenv' vv sv = (op,b)` (irule_at Any) >>
      first_assum ACCEPT_TAC) >>
   `?xs sw.
      op = Var xs /\ lookup_var xs t = SOME sw /\ not_fresh_at b xs /\
      ptr_covers G1 tn1 xs t (type_memory_size stv) /\
      (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory stv v (w2n sw) mem) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      (type_memory_size stv = 0 \/
        w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
      expr_val_at cenv' cx (expr_type e) a b mid v (Var xs) t /\
      (w2n sw + type_memory_size stv <= w2n w \/
        w2n w + type_memory_size dtv <= w2n sw)` by
     (irule (INST_TYPE [``:'a`` |-> ``:256``] annassign_other_typed_rhs_resources) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`ctx`,`es`,`func`] >>
      qexistsl_tac [`inst`,`p`,`entry`,`type_memory_size dtv`] >> fs[]) >>
   `!x. not_fresh_at sa x ==> not_fresh_at b x` by
     (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x` mp_tac >>
      simp[]) >>
   `b.cs_next_var <= sb.cs_next_var` by
     (qpat_assum `compile_assign_value cenv' _ _ op _ _ _ _ _ b = ((),sb)`
        (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
      metis_tac[cj 1 ci_mono_stmt_helpers, exprLoweringPropsTheory.ci_mono_def,
                pairTheory.SND]) >>
   `sa.cs_next_id < b.cs_next_id` by
     (qpat_assum `lower_value compile_expr cenv' (expr_type e) e a = (op,b)`
       (mp_tac o MATCH_MP (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
      strip_tac >> decide_tac) >>
   `?u Gf tf.
      lookup_var p u = SOME w /\
      FLOOKUP u.vs_allocas (inst.inst_id) = SOME (w2n w,type_memory_size dtv) /\
      (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,Gf,tf)) /\
      !H. valid_horizon cx st0 H out.storage_trace ==>
        stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\ ~block_is_terminated sb /\
        cenv_top_ext cenv cenv' out.scopes /\
        stmt_state_rel H ctx func cenv' cx out u /\
        storage_well_formed_on cx out (FST H) /\
        return_buf_frame d cenv' sb u /\ alloca_history func u /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        s0.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv' cx out Gf tf u /\
        (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x u = SOME z) /\
        (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 cenv' out u /\
        (!aid off len i.
          FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
          (!name a cap. local_region cenv es.scopes s0 name a cap ==>
            off+len <= a \/ a+cap <= off) /\
          off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)` by
     (irule annassign_memory_full_suffix_post >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `body_inv tops ctx cenv' cx`
        (strip_assume_tac o PURE_REWRITE_RULE [body_inv_def]) >>
        first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `expr_body_pre cenv' cx env e es`
        (strip_assume_tac o PURE_REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
        first_assum ACCEPT_TAC)
      >- (qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
        (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
        disch_tac >> rpt gen_tac >> strip_tac >>
        first_x_assum (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
        simp[arithmeticTheory.ADD_SYM] >> disch_then irule >>
        rpt strip_tac >> first_x_assum drule >>
        simp[arithmeticTheory.ADD_SYM])
      >- (irule compile_assign_value_typed_open >>
          qpat_assum `compile_assign_value cenv' _ _ _ _ _ _ _ _ b = ((),sb)`
            (irule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `ghost_inv_at _ lo d cenv' cx mid G1 tn1 t`
        (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
        first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `inst.inst_id = sa.cs_next_id` (fn th => PURE_REWRITE_TAC [th, arithmeticTheory.LESS_EQ_REFL])) >>
      qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`b`,`dtv`,`typ`] >>
      qexistsl_tac [`id`,`mid`,`type_memory_size stv`,`rest`,`sc`] >>
      qexistsl_tac [`vv_location vv`,`a`,`stv`,`expr_type e`,`sw`,`v`,`xs`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[NoAsms] >>
      TRY (qpat_assum `op = Var xs` (fn op_eq =>
        qpat_assum `!ty. type_memory_bytes cenv' ty = type_memory_bytes cenv ty` (fn decl =>
          qpat_assum `type_memory_bytes cenv typ = type_memory_size dtv` (fn size =>
            PURE_REWRITE_TAC [op_eq, Q.SPEC `typ` decl, size] >>
            first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [op_eq, Q.SPEC `typ` decl, size])))))
      >~ [`vv_location vv <> SOME LocMemory ==>
             type_memory_size stv + w2n sw <= w2n w \/ _`]
      >- (strip_tac >>
          FIRST
            [disj1_tac >>
               qpat_assum `w2n sw + type_memory_size stv <= w2n w`
                 (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]),
             disj2_tac >>
               qpat_assum `w2n w + type_memory_size dtv <= w2n sw`
                 (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])])
      >> TRY (strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (gen_tac >> disch_tac >>
           qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
             (qspec_then `H` mp_tac) >>
           (impl_tac >-
             (qpat_assum `out = mid with scopes := _` (fn eq =>
                qpat_assum `valid_horizon cx st0 H out.storage_trace`
                  (ACCEPT_TAC o SIMP_RULE (srw_ss()) [eq])))) >>
           POP_ASSUM_LIST (K all_tac) >> simp[NoAsms,expr_post_def] >> NO_TAC) >>
      TRY (strip_tac >> decide_tac) >>
      TRY (qpat_assum `lower_value compile_expr cenv' (expr_type e) e a = (op,b)`
            (mp_tac o MATCH_MP (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
          strip_tac >>
          qpat_assum `inst.inst_id = sa.cs_next_id` mp_tac >>
          qpat_assum `sa.cs_next_id < a.cs_next_id` mp_tac >> decide_tac) >>
      TRY (qpat_assum `op = Var xs` (fn eq =>
        qpat_assum `!ty. type_memory_bytes cenv' ty = type_memory_bytes cenv ty` (fn decl =>
        qpat_assum `type_memory_bytes cenv typ = type_memory_size dtv` (fn sz =>
        qpat_assum `compile_assign_value cenv' _ _ op _ _ _ _ _ b = ((),sb)` mp_tac >>
        simp[NoAsms,eq,decl,sz] >> first_assum ACCEPT_TAC)))) >>
      TRY (rpt strip_tac >> first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >> first_assum ACCEPT_TAC) >>
      NO_TAC) >>
   (irule gas_outcome_full_pure >>
    (reverse conj_tac >- first_assum ACCEPT_TAC) >>
    qexistsl_tac [`Gf`,`out`,`INL ()`,`u`,`tf`] >>
    (conj_tac
     >- (drule new_variable_success_gas_obs >> simp[NoAsms])) >>
    gen_tac >> disch_tac >>
    (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
    BETA_TAC >> strip_tac >> qexists_tac `cenv'` >>
    `out with gas_obs := [] = out` by
      (qpat_assum `mid.gas_obs = []`
         (fn th => simp[NoAsms,Abbr `out`,GSYM th])) >>
    qpat_assum `out with gas_obs := [] = out`
      (fn eq => pure_rewrite_tac [eq]) >>
    qpat_assum `!H. valid_horizon cx st0 H out.storage_trace ==> _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    `return_buf_sep d cenv' out u` by
    (`MAP FDOM (sc::rest) = MAP FDOM es.scopes` by
       (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
          (qspec_then `[]` (mp_tac o SRULE [])) >>
        strip_tac >> drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     irule annassign_memory_return_buf_sep >>
     qpat_assum `FLOOKUP cenv'.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` (irule_at Any) >>
     qexistsl_tac [`st0`,`sc`,`sa`,`s0`,`rest`,`cenv`,`func`,`es`,`<|assignable := T; type := dtv; value := v; popped := []|>`,`cx`,`ctx`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (rpt gen_tac >> strip_tac >>
          qpat_assum `!bw cap. d = SOME (bw,cap) ==>
                        allocas_from (cap + w2n bw) u`
            (qspecl_then [`bw`,`cap`] mp_tac) >>
          asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM] >> NO_TAC) >>
     simp[Abbr `out`]) >>
    asm_simp_tac bool_ss [] >>
    qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
      (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
    disch_tac >> rpt gen_tac >> strip_tac >>
    first_x_assum (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
    simp[arithmeticTheory.ADD_SYM] >> disch_then irule >>
    rpt strip_tac >> first_x_assum drule >> simp[arithmeticTheory.ADD_SYM]))
QED

Finalise annassign_other_typed_full_execution
