Theory createSizeRawPayloadEmptyMods
Ancestors
  bodyFullPostsMods exprSimHypsDefs loweringStateRelDefs bodyPtrDefs
  compileEnv venomState vyperCreate vyperInterpreter vyperStorageTrace
  vyperStorageFootprint gasSummary loweringPosts ptrDiscipline fragExec

Theorem create_raw_payload_empty_at_cuts_mods:
  bind (eval_exprs cx (av::(if hs then [saltE] else [])))
    (\vs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv_mods mods ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\ local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  cv = C 0 /\ uval = St 0 /\ size_op = lenop /\ R 0 = kwmarks ==>
  ?cvs payload ee G tn.
    LENGTH cvs = LENGTH ([]:expr list) /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ([]:expr list)) cvs = SOME payload /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(cvs ++ kvs))) ee = (res,out) /\
    valid_horizon cx st0 H ee.storage_trace /\
    ee.gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env ee /\ return_buf_frame d ce cv uval /\ alloca_history func uval /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp uval) /\
    (!f i z. frag_reachable ctx func uval f i z ==> dalloca_fmp_headroom i z) /\
    ~uval.vs_halted /\ uval.vs_current_bb = cv.cs_current_bb /\
    uval.vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved ce cv /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee uval /\
      immutable_frame_mods func ce cx ee uval /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx ee G tn uval) /\
    payload = [] /\ size_op = lenop /\ cv = C 0 /\ uval = St 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind _ _ _ = (_,_)` (mp_then Any irule valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all,
          storage_trace_frame_create_operands]) >>
  qexistsl [`[]`,`[]`,`p0`,`G0`,`tn0`] >>
  simp[encode_create_ctor_args_def,listTheory.REV_DEF] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K _ ==> _ /\ _` drule >> simp[]
QED
