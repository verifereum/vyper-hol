Theory bodyPtrTypeBuiltinsExtract32Prefix
Ancestors
  bodyPtrTypeBuiltinsExtract32SourceBind bodyPtrTypeBuiltinsExtract32OffsetBind
  bodyPtrTypeBuiltinsExtract32Prepare exprSimExtract32Post
  exprSimExtract32Source exprSimSource gasSummaryComposePtr gasExemptCert
  wordOperandsPtr exprBopSimProps exprLoweringProps bodyPtrDefs bodyPtrPreds
  vyperState loweringPosts compileEnv loweringStateRelDefs vyperValue rawCallBufferPtr exprOperandVar
  gasSummary fragGasMode fragGasPath freshWrites exprSimHyps exprSimHypsDefs vyperAST

Theorem extract32_operands_ptr_prefix:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\ is_uint_type (expr_type off) /\
  lower_value compile_expr cenv (expr_type src) src sa = (srcop,sm) /\
  compile_bytestring_src srcop sm = ((lenop,dataop),sb) /\
  lower_value compile_expr cenv ty off sb = (offop,sc) /\
  compile_extract32_load lenop dataop offop sc = (raw,sd) /\
  compile_clamp_basetype raw typ sd = (result,se) /\
  fn_has_code sa se func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx (TypeBuiltin ann Extract32 typ [src;off])) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!left right bs i mid fin G tn t H th u J un v sv len data p.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (vyperState$bind (eval_expr cx src) (read_result cx))
      (es,s0,G0,tn0) left (INL (BytesV bs)) mid G tn (OK t) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 H th (OK u) /\
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (vyperState$bind (eval_expr cx off) (read_result cx))
      (mid with gas_obs := [],u,H,th) right (INL (IntV i)) fin J un (OK v) /\
    LENGTH bs <= m /\ 0 <= i /\
    expr_post ctx func cenv cx src es sa sb s0
      (mid with gas_obs := []) (BytesV bs) srcop u /\
    expr_post ctx func cenv cx off (mid with gas_obs := []) sb sc u
      (fin with gas_obs := []) (IntV i) offop v /\
    srcop = Var sv /\ lenop = Var len /\ dataop = Var data /\
    not_fresh_at sb sv /\ not_fresh_at sb len /\ not_fresh_at sb data /\
    ptr_mem_ok cx (expr_type src) (BytesV bs) srcop J un v /\
    eval_operand srcop v = SOME (n2w p) /\
    eval_operand lenop v = SOME (n2w (LENGTH bs)) /\
    eval_operand dataop v = SOME (n2w (p+32)) /\
    op_taint un srcop = {} /\ op_taint un lenop = {} /\
    op_prov J lenop = NONE /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers J un data v n) /\
    v.vs_current_bb = sc.cs_current_bb /\ v.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ghost_inv d cenv cx (fin with gas_obs := []) J un v /\
    ptr_val_ok cx (post_value_type cenv off) (IntV i) offop J un v /\
    ghost_kept cenv es sa G0 tn0 s0 J un ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (vyperState$bind
        (lift_sum (evaluate_type_builtin cx Extract32 typ
          [expr_type src;expr_type off] [BytesV bs;IntV i])) (\w. return (Value w)))
      (fin with gas_obs := [],v,J,un) Q (\res ee gt r. expr_exit res r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (TypeBuiltin ann Extract32 typ [src;off]))
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all extract32_stage_cuts >> strip_tac >>
  `gas_admissible (vyperState$bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (metis_tac[extract32_vv_first_admissible]) >>
  once_rewrite_tac[eval_expr_extract32_vv_bind] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_source_ptr_bind) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
  qexistsl_tac [`ann`,`cenv`,`d`,`env`,`off`,`srcop`,`sa`,`sm`,`tops`,`ty`,`typ`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >> suspend "normal"
QED

Resume extract32_operands_ptr_prefix[normal]:
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv src = expr_type src` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn t /\
   op_taint tn srcop = {}` by gvs[ptr_val_ok_def, is_word_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (`expr_body_pre cenv cx env src es` by
       (irule expr_body_pre_type_builtin_arg >> conj_tac
        >- gvs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `expr_body_pre _ _ _ src _` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `?p. eval_operand srcop t = SOME (n2w p)` by
    (drule_all extract32_source_post_view >> metis_tac[]) >>
  drule_all ptr_mem_ok_dynamic_bytes_site >> strip_tac >> gvs[] >>
  `not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  drule (GEN_ALL (SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO]
    extract32_prepare_ptr_counted)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  suspend "offset"
QED

Resume extract32_operands_ptr_prefix[offset]:
  `gas_admissible (vyperState$bind (eval_expr cx off) (read_result cx)) expr_res_ok
     (mid with gas_obs := [])` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) u` by
    gvs[expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_offset_ptr_bind) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
  suspend "suffix"
QED

Resume extract32_operands_ptr_prefix[suffix]:
  qpat_assum `expr_sim_ptr _ _ _ _ _ _ _ off _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ src _ _ sb _ _ _ _ u` (irule_at Any) >>
  simp[] >> qexistsl_tac [`p'`,`len`,`env`,`data`] >> simp[] >>
  reverse conj_tac >- gvs[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >> rpt gen_tac >> strip_tac >>
  suspend "finish"
QED

Resume extract32_operands_ptr_prefix[finish]:
  `ghost_kept cenv es sa G0 tn0 s0 H' th'` by
    (`wb_frame cenv es sa s0 u` by
       metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
     `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
       (qpat_assum `gas_marked_exec_ptr _ _ _ _ (es,s0,G0,tn0) _ _ _ _ _ _`
          (mp_tac o MATCH_MP gas_marked_exec_ptr_exec) >>
        disch_then (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV) bop_marked_scopes_dom)) >> simp[]) >>
     irule wordOperandsPtrTheory.ghost_kept_trans >>
     qpat_assum `ghost_kept cenv es sa G0 tn0 s0 H th` (irule_at Any) >>
     qpat_assum `ghost_kept _ _ sb H th u H' th'` (irule_at Any) >> simp[] >>
     qexists_tac `func` >> conj_tac
     >- gvs[stmt_state_rel_def, state_rel_def] >>
     qpat_assum `lower_value _ _ _ src sa = _` (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     strip_tac >>
     qspecl_then [`Var x`,`sm`] mp_tac ci_mono_compile_bytestring_src >>
     simp[ci_mono_def] >> strip_tac >> decide_tac) >>
  first_x_assum (irule o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qpat_assum `gas_marked_exec_ptr _ _ _ _ (es,s0,G0,tn0) _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec_ptr _ _ _ _ (_ ,u,H,th) _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexists_tac `p'` >>
  `p' < dimword(:256) /\ p'+32 < dimword(:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD]
QED

Finalise extract32_operands_ptr_prefix
