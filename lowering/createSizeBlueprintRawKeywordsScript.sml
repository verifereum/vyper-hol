Theory createSizeBlueprintRawKeywords
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec gasExplicitSites gasSummary venomExecSemantics
  venomState vyperCreate vyperState relation list words pair bodyFullIfExpReach arithmetic
  exprLowering vfmConstants compileEnv exprLoweringProps exprBodyPreProps vyperStorageTrace
  rich_list exprSimHypsDefs vyperTypeSystem exprSimHyps bodyPtrDefs loweringPosts vyperAST
  vyperStorageFootprint vyperValue integer_word loweringStateRelDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizeCopyReplay createSizeBlueprintRawScalars
  createSizeBlueprintRawCopyReplay createSizeOperandPre

(* Join the two raw-payload replays at the input of the fixed MLOAD/ADD
   suffix.  The source continuation already contains the read address. *)
Theorem create_blueprint_raw_keyword_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint T) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint T) hs args) /\
  e = HD ctors /\ later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cprep fnc /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  create_expr_prefix cu cl (gas_explicit_sites ctx shctx) ctx fnc u ml b /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  create_expr_prefix cl cprep (gas_explicit_sites ctx shctx) ctx fnc b ma t /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ (ml ++ ma ++ rest)))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?bs q G tn.
    ctors = [e] /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(BytesV bs::kvs))) q = (res,out) /\
    valid_horizon cx st0 H q.storage_trace /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op t = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cprep /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    return_buf_frame d ce cprep t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
    t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?k. ctors = [e] /\ expr_type e = BaseT (BytesT (Dynamic k))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> fs[well_typed_expr_def,create_arg_types_ok_def,MAP_EQ_CONS] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `e = HD ctors` kall_tac >>
  `create_operand_completed_ok cx e` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     qpat_assum `ctors = [e]` (fn th => pure_rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >> Cases_on `hs` >> simp[create_operand_order_def]) >>
  `expr_body_pre ce cx env e p` by
    (irule create_call_operand_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
     SOME (BaseTV (BytesT (Dynamic k)))` by
    (`well_typed_expr env e` by (drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
     drule_all expr_sim_inv_type_evaluates >>
     simp[evaluate_type_def] >> reverse IF_CASES_TAC >> simp[]) >>
  `fn_has_code cu cl fnc` by
    metis_tac[fn_has_code_split,exprSimAccountsTheory.emit_op_extends_next_var] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >>
     `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
     drule_all body_inv_no_phi >> simp[]) >>
  `compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep)` by
    (qpat_x_assum `later = _` kall_tac >>
     qpat_x_assum `expr_type e = _` kall_tac >>
     simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def]) >>
  qabbrev_tac `kont = \v. bind (eval_exprs cx later)
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::v::vs))` >>
  `!v. storage_trace_frame (kont v)` by
    simp[Abbr `kont`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  `bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out)` by
    fs[Abbr `kont`,create_copy_source_cons] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?bs q G tn.
     kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
     q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail /\
     expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
     eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
     expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cu /\
     (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     return_buf_frame d ce cu u /\ alloca_history fnc u /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
     (!h. valid_horizon cx st0 h q.storage_trace ==>
       stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
       ghost_inv_at (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted` by
    (Cases_on `exprs_can_mutate ce later`
     >- (drule_all blueprint_raw_copied_at_cut >> strip_tac
         >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
         disj2_tac >> qexistsl_tac [`bs`,`q`,`G`,`tn`] >>
         rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)
     >> drule_all blueprint_raw_retained_at_cut >> strip_tac
     >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
     disj2_tac >> qexistsl_tac [`bs`,`q`,`G'`,`tn'`] >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  pop_assum strip_assume_tac >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all blueprint_raw_finish_at_cut >> strip_tac >>
  disj2_tac >> qexistsl_tac [`bs`,`q`,`G`,`tn`] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `later = _` SUBST_ALL_TAC >> fs[Abbr `kont`]) >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED
