Theory bodyPtrSubscriptSeamArrayMemorySuffix
Ancestors
  bodyPtrSubscriptSeamArrayMemoryBounds bodyPtrSubscriptSeamArrayMemoryReject
  bodyPtrSubscriptSeamArrayMemoryAddress bodyPtrSubscriptReadOnly
  exprLowering exprLoweringProps emitHelperProps freshWrites emitHelper compileEnv
  ptrDiscipline bodyPtrDefs venomState venomInst words fragExec fragGasPathPtr
  loweringPosts finite_map appendStorageGhostPtr
Libs
  pairLib

Theorem static_selector_emissions:
  compile_array_subscript base_op idx F cnt ws elem_size sgn loader sa = (op,sb) ==>
  ?negflag lt oob invalid valid offset out sk sm sn sp sq sr st.
    op = Var out /\
    (if sgn then emit_op SLT [idx;Lit 0w] sa = (negflag,sk)
     else negflag = Lit 0w /\ sk = sa) /\
    emit_op LT [idx;Lit (n2w cnt)] sk = (Var lt,sm) /\
    emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
    emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
    emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
    emit_void ASSERT [Var valid] sq = ((),sr) /\
    emit_op MUL [idx;Lit (n2w elem_size)] sr = (Var offset,st) /\
    emit_op ADD [base_op;Var offset] st = (Var out,sb)
Proof
  Cases_on `sgn` >>
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >> metis_tac[]
QED

Theorem static_bounds_prefix_counted:
  (if sgn then emit_op SLT [idx;Lit 0w] sa = (negflag,sk)
   else negflag = Lit 0w /\ sk = sa) /\
  emit_op LT [idx;Lit len] sk = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ (sgn ==> 0 <= w2i a) /\ w2n a < w2n len /\
  op_taint tn idx = {} /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  Cases_on `sgn` >> simp[] >> disch_then (CONJUNCTS_THEN assume_tac)
  >- (qpat_assum `emit_op SLT _ _ = _`
        (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >> gvs[] >>
      irule signed_literal_bounds_counted >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   op_prov G (Lit 0w) = NONE /\
   (!q. Lit 0w = Var q ==> not_fresh_at sa q) /\ (!l. Lit 0w <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all checked_literal_bounds_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Theorem static_selector_counted:
  compile_array_subscript (Var p) idx F cnt ws elem_size sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ (!q. idx = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l) /\ ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\
  (sgn ==> 0 <= w2i (n2w i:bytes32)) /\
  w2n (n2w i:bytes32) < w2n (n2w cnt:bytes32) /\
  i * elem_size + child_sz <= parent_sz /\
  w2n a + i * elem_size < dimword (:256) ==>
  ?Gf tnf sf out.
    op = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >> drule static_selector_emissions >> strip_tac >> gnvs[] >>
  `ci_mono sa sk` by (Cases_on `sgn` >> gvs[] >>
    metis_tac[ci_mono_refl, ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono sk sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq /\
   ci_mono sr st /\ ci_mono st sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sr` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `sa.cs_next_var <= sr.cs_next_var` by (gvs[ci_mono_def] >> decide_tac) >>
  `cs_extends sa sr /\ cs_extends sr sb` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sr func /\ fn_has_code sr sb func` by
    metis_tac[fn_has_code_split] >>
  `w2n (n2w i:bytes32) < w2n (n2w cnt:bytes32)` by simp[] >>
  drule_all static_bounds_prefix_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {}` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def]) >>
  `ptr_covers G1 tn1 p s1 parent_sz` by
    (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_var p s1 = SOME a /\ not_fresh_at sr p` by
    (conj_tac >- metis_tac[] >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> gvs[ci_mono_def] >> decide_tac) >>
  `i * elem_size + child_sz <= parent_sz /\
   w2n a + i * elem_size < dimword (:256)` by simp[] >>
  drule_all literal_mul_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> `not_fresh_at sr q` by
        metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  rpt strip_tac >> `local_ptrs_reserved cenv sr` by
    metis_tac[local_ptrs_reserved_next_var] >> metis_tac[]
QED

Theorem static_bounds_prefix_rejects_counted:
  (if sgn then emit_op SLT [idx;Lit 0w] sa = (negflag,sk)
   else negflag = Lit 0w /\ sk = sa) /\
  emit_op LT [idx;Lit len] sk = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ ~((sgn ==> 0 <= w2i a) /\ w2n a < w2n len) /\
  op_taint tn idx = {} /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Cases_on `sgn` >> simp[] >> disch_then (CONJUNCTS_THEN assume_tac)
  >- (qpat_assum `emit_op SLT _ _ = _`
        (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >> gvs[] >>
      irule signed_literal_bounds_rejects_counted >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   op_prov G (Lit 0w) = NONE /\
   (!q. Lit 0w = Var q ==> not_fresh_at sa q) /\ (!l. Lit 0w <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `~((0w:bytes32) = 0w /\ w2n a < w2n len)` by simp[] >>
  drule_all literal_bounds_rejects_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Theorem static_selector_rejects_counted:
  compile_array_subscript base_op idx F cnt ws elem_size sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\
  ~((sgn ==> 0 <= w2i a) /\ w2n a < w2n (n2w cnt:bytes32)) /\
  op_taint tn idx = {} /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule static_selector_emissions >> strip_tac >>
  `ci_mono sa sk` by (Cases_on `sgn` >> gvs[] >>
    metis_tac[ci_mono_refl, ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono sk sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq /\
   ci_mono sr st /\ ci_mono st sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sr` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa sr /\ cs_extends sr sb` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sr func` by metis_tac[fn_has_code_split] >>
  drule_all static_bounds_prefix_rejects_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >> simp[]
QED
