(* Compiler-facing memory encoder boundary shared by raise and assert. *)
Theory reasonMemoryEncoderPtr
Ancestors reasonMemoryPtr reasonFinishCode reasonPrefixPtr reasonResourcesPtr
  bodyPtrDefs loweringPosts exprSimProps exprLoweringProps emitHelperProps
  loweringHalt fragExec fragGasPathPtr stmtLowering exprLowering context emitHelper
  compileEnv venomState
Libs wordsLib intLib

Theorem reason_emit_op_cs_extends:
  emit_op opc args ca = (out,cb) ==> cs_extends ca cb
Proof
  strip_tac >> mp_tac (Q.SPECL [`opc`, `args`, `ca`] ci_mono_emit_op) >>
  simp[ci_mono_def]
QED

Theorem reason_emit_void_cs_extends:
  emit_void opc args ca = ((),cb) ==> cs_extends ca cb
Proof
  strip_tac >> mp_tac (Q.SPECL [`opc`, `args`, `ca`] ci_mono_emit_void) >>
  simp[ci_mono_def]
QED

Theorem reason_encode_finish_extends:
  reason_encode_finish outer payload tuple slot sa = ((),sb) ==>
  cs_extends sa sb
Proof
  simp[reason_encode_finish_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_inst_def, emit_def] >>
  strip_tac >> gvs[cs_extends_def] >>
  simp[listTheory.APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem reason_memory_encoder_path_ptr:
  compile_revert_with_reason cenv vv (expr_type e) m cc = ((),se) /\
  fn_has_code cc se func /\
  (!st. unwrap_value cenv vv st = (Var src,st)) /\
  expr_post ctx func cenv cx e es sa sb s0 ee (StringV str) (Var src) s /\
  ptr_val_ok cx (expr_type e) (StringV str) (Var src) G tn s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  ~is_word_type (expr_type e) /\ val_wf (BaseTV (StringT cap)) (StringV str) /\
  m = type_memory_bytes cenv (BaseT (StringT cap)) /\
  type_alloc_ok cenv (BaseT (StringT cap)) /\ 64+m < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  local_ptrs_reserved cenv cc /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= cc.cs_next_var /\ sa.cs_next_id <= cc.cs_next_id /\
  sb.cs_next_id <= cc.cs_next_id /\ not_fresh_at cc src /\
  post_value_type cenv e = expr_type e ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >> drule compile_revert_reason_finish_split >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[] >> strip_tac >>
  `?outer payloadvar tuplevar lenvar rounded0var roundedvar cntvar slotvar.
    buf.buf_operand = Var outer /\ payload = Var payloadvar /\
    tuple.buf_operand = Var tuplevar /\ len = Var lenvar /\
    rounded0 = Var rounded0var /\ rounded = Var roundedvar /\
    cnt = Var cntvar /\ slot.buf_operand = Var slotvar` by suspend "operands" >>
  `fn_has_code cc c1 func /\ fn_has_code c3 c4 func /\ fn_has_code cc c4 func /\
   fn_has_code c5 c6 func /\ fn_has_code c6 c7 func /\ fn_has_code c7 c8 func /\
   fn_has_code c8 c9 func /\ fn_has_code c9 c10 func /\ fn_has_code c10 c11 func /\
   fn_has_code c11 c12 func /\ fn_has_code c12 se func` by suspend "code" >>
  suspend "compose"
QED

Resume reason_memory_encoder_path_ptr[operands]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Resume reason_memory_encoder_path_ptr[code]:
  qpat_x_assum `fn_has_code cc se func` mp_tac >>
  qpat_x_assum `c4 = c5` mp_tac >>
  qpat_x_assum `reason_encode_finish _ _ _ _ _ = _` mp_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  imp_res_tac reason_emit_op_cs_extends >> imp_res_tac reason_emit_void_cs_extends >>
  imp_res_tac reason_encode_finish_extends >>
  qpat_x_assum `c4 = c5` SUBST_ALL_TAC >>
  `cs_extends c11 se` by (irule cs_extends_trans >> qexists_tac `c12` >> simp[]) >>
  `cs_extends c10 se` by (irule cs_extends_trans >> qexists_tac `c11` >> simp[]) >>
  `cs_extends c9 se` by (irule cs_extends_trans >> qexists_tac `c10` >> simp[]) >>
  `cs_extends c8 se` by (irule cs_extends_trans >> qexists_tac `c9` >> simp[]) >>
  `cs_extends c7 se` by (irule cs_extends_trans >> qexists_tac `c8` >> simp[]) >>
  `cs_extends c6 se` by (irule cs_extends_trans >> qexists_tac `c7` >> simp[]) >>
  `cs_extends c5 se` by (irule cs_extends_trans >> qexists_tac `c6` >> simp[]) >>
  `cs_extends c3 se` by (irule cs_extends_trans >> qexists_tac `c5` >> simp[]) >>
  `cs_extends c2 se` by (irule cs_extends_trans >> qexists_tac `c3` >> simp[]) >>
  `cs_extends c1 se` by (irule cs_extends_trans >> qexists_tac `c2` >> simp[]) >>
  qspecl_then [`cc`,`c1`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c1`,`c2`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c2`,`c3`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c3`,`c5`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c5`,`c6`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c6`,`c7`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c7`,`c8`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c8`,`c9`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c9`,`c10`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c10`,`c11`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`c11`,`c12`,`se`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  `cs_extends cc c3` by (irule cs_extends_trans >> qexists_tac `c1` >> simp[] >>
    irule cs_extends_trans >> qexists_tac `c2` >> simp[]) >>
  `cs_extends cc c5` by (irule cs_extends_trans >> qexists_tac `c3` >> simp[]) >>
  qspecl_then [`cc`,`c5`,`se`,`func`] mp_tac fn_has_code_split >> simp[]
QED

Resume reason_memory_encoder_path_ptr[compose]:
  `?ow. eval_operand (Var src) s = SOME ow` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `ptr_mem_ok cx (expr_type e) (StringV str) (Var src) G tn s /\
   op_taint tn (Var src) = {}` by fs[ptr_val_ok_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (StringT cap)) (StringV str) (w2n ow) mem` by
    (qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >> simp[ptr_mem_ok_def]) >>
  `32 <= 64+m /\ m < dimword (:256)` by decide_tac >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] reason_encoder_prefix_path_ptr) >>
  disch_then (drule_at (Pat `emit_void MSTORE [_;Lit 0x08c379a0w] _ = _`)) >>
  rpt (disch_then drule) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `D`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `Var src = msg` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  fs[] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  drule_at (Pat `reason_encode_finish _ _ _ _ _ = _`)
    (REWRITE_RULE [GSYM AND_IMP_INTRO]
      (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [] reason_memory_suffix_path_ptr)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `not_fresh_at _ _`)) >>
  rpt (disch_then drule) >>
  qpat_assum `buf.buf_operand = _` (fn th => disch_then (mp_tac o REWRITE_RULE [th])) >>
  rpt (disch_then drule) >>
  qpat_assum `tuple.buf_operand = _` (fn th => disch_then (mp_tac o REWRITE_RULE [th])) >>
  rpt (disch_then drule) >>
  `(i2w (-32) : bytes32) = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w` by EVAL_TAC >>
  qpat_assum `(i2w (-32) : bytes32) = _`
    (fn th => disch_then (mp_tac o REWRITE_RULE [th])) >>
  rpt (disch_then drule) >>
  qpat_assum `slot.buf_operand = _` (fn th => disch_then (mp_tac o REWRITE_RULE [th])) >>
  rpt (disch_then drule) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 G4 tn4 (OK t)` mp_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G4 tn4 t 0 Gf tnf (Abort Revert_abort sf)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise reason_memory_encoder_path_ptr
