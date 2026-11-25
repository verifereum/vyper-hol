Theory createSizeBlueprintAbiEmptyMods
Ancestors
  bodyFullPostsMods exprSimHypsDefs loweringStateRelDefs bodyPtrDefs
  exprLowering compileEnv venomExecSemantics venomState vyperCreate
  vyperInterpreter vyperStorageTrace vyperStorageFootprint gasSummary
  loweringPosts ptrDiscipline fragExec

Theorem create_blueprint_abi_empty_keyword_entry_mods:
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op (St 0) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv_mods mods ce cx env p0 /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  compile_create_blueprint_args compile_expr ce F later [] (C 0) = ((data,len),en) /\
  t = St 0 /\ R 0 = rest /\
  bind (eval_exprs cx ([] ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail ==>
  ?cvs p G tn.
    LENGTH cvs = LENGTH [] /\ eval_exprs cx [] p0 = (INL cvs,p) /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
    valid_horizon cx st0 H p.storage_trace /\
    (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ([]:expr list)) cvs = SOME bs /\
      eval_operand len t = SOME (n2w (LENGTH bs))) /\
    (!x. len = Var x ==> not_fresh_at en x) /\
    eval_operand target_op t = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at en x) /\
    expr_sim_inv_mods mods ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\
      immutable_frame_mods func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind _ _ _ = (_,_)` (mp_then Any irule valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all,
          storage_trace_frame_create_operands]) >>
  gvs[compile_create_blueprint_args_def,comp_return_def] >>
  qexistsl [`p0`,`G0`,`tn0`] >>
  simp[encode_create_ctor_args_def,cj 1 eval_operand_def,listTheory.REV_DEF,
       cj 49 evaluate_def,vyperStateTheory.return_def] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K _ ==> _ /\ _` drule >> simp[]
QED
