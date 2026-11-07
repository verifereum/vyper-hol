Theory bodyPtrBopResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list compileEnv
  bodyPtrBopHashCompile bodyPtrBopCompareCompile bodyPtrBopOperandContract
  bodyPtrBopEntry bodyPtrBopTypedSource exprPtrUnwrap exprSimBopBytestring
  exprBopLowering exprLowering emitHelper exprLoweringProps
  bodyPtrBopHashSuffix exprSimOperators exprSimLiteralWord bytestringHashProps
  bodyPtrBopSelectedHash exprBopDigestProps bodyPtrBopCompareSuffix

Theorem bop_bytestring_forced_ptr[local]:
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  body_expr_ptr_ok cx e1 /\
  ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==> body_expr_ptr_ok cx e2) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn` by (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >> gvs[]) >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_type e1 = expr_type e2 /\ ann = BaseT BoolT` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >>
     gvs[vyperTypeSystemTheory.well_typed_binop_def]) >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
    compile_builtin_dispatch_body_def, lower_value_child_call] >>
  `is_bytestring_type (expr_type e2)` by metis_tac[] >>
  simp[ETA_AX] >>
  pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >>
  qpat_x_assum `(\(h2,st4). _) _ = _` mp_tac >>
  pairarg_tac >> gnvs[] >> strip_tac >>
  strip_tac >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `cs_extends sa st2 /\ sa.cs_next_var <= st2.cs_next_var /\
   sa.cs_next_id <= st2.cs_next_id` by
    (qpat_x_assum `_ = (h1,st2)` mp_tac >>
     disch_then (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) bop_selected_hash_grows)) >> simp[]) >>
  `cs_extends st2 st4 /\ st2.cs_next_var <= st4.cs_next_var /\
   st2.cs_next_id <= st4.cs_next_id` by
    (qpat_x_assum `_ = (h2,st4)` mp_tac >>
     disch_then (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) bop_selected_hash_grows)) >> simp[]) >>
  `cs_extends st4 sb /\ st4.cs_next_var <= sb.cs_next_var /\
   st4.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >>
     gvs[as_stack_val_def, unwrap_value_def, is_word_type_def,
       emit_op_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  once_rewrite_tac[REWRITE_RULE [ETA_AX] exprBopSimPropsTheory.eval_expr_bop_bind] >>
  irule bop_selected_hash_outcome_ptr >>
  (conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])) >>
  (conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gnvs[])) >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`\rr ee. ?gs. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gs) = (rr,ee)`, `sa`, `cenv`, `st2`, `d`, `env`, `h1`, `tops`] >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  reverse conj_tac
  >- (conj_tac >- (qpat_x_assum `_ = (h1,st2)` mp_tac >>
        CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
      conj_tac >- metis_tac[body_expr_ptr_ok_def] >>
      simp[bop_operand_entry_def] >>
      conj_tac >- (metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_trans, cs_extends_refl]) >>
      metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_expr_ptr_ok cx e2` by
    (qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
     qpat_x_assum `?gs. _` strip_assume_tac >>
     gvs[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule_all bop_typed_source_witness >> simp[]) >>
  `expr_body_pre cenv cx env e2 ee` by
    (drule_all bop_typed_source_witness >> strip_tac >> metis_tac[]) >>
  irule bop_selected_hash_outcome_ptr >>
  (conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])) >>
  (conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gnvs[])) >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`\rr ee'. ?gs. bind (eval_expr cx e2) (read_result cx)
    (ee with gas_obs := gs) = (rr,ee')`, `st2`, `cenv`, `st4`, `d`, `env`, `h2`, `tops`] >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  reverse conj_tac
  >- (conj_tac >- (qpat_x_assum `_ = (h2,st4)` mp_tac >>
        CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
      conj_tac >- metis_tac[body_expr_ptr_ok_def] >>
      simp[bop_operand_entry_def] >>
      conj_tac >- metis_tac[fragExecTheory.fn_has_code_mid] >>
      conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
      conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand h1 t' = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
   op_prov H' h1 = NONE /\ op_taint un' h1 = {}` by
    (Cases_on `h1` >>
     fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, ghost_kept_def] >>
     metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `wb_frame cenv es sa s0 t'` by
    metis_tac[exprSimWordArgsTheory.wb_frame_trans] >>
  `ghost_kept cenv es sa G0 tn0 s0 H' un'` by
    metis_tac[wordArgsPtrTheory.ghost_kept_wb_trans] >>
  `MAP FDOM ee.scopes = MAP FDOM ee'.scopes /\
   ?tv. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv /\
     value_has_type tv v /\ value_has_type tv v'` by
    (qpat_assum `expr_body_pre _ _ _ e1 es` mp_tac >>
     disch_then (mp_then Any mp_tac bop_typed_source_witness) >>
     disch_then (qspecl_then [`v`, `ee`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `expr_body_pre _ _ _ e2 ee` mp_tac >>
     disch_then (mp_then Any mp_tac bop_typed_source_witness) >>
     disch_then (qspecl_then [`v'`, `ee'`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `expr_type e1 = expr_type e2` SUBST_ALL_TAC >>
     gnvs[] >> metis_tac[]) >>
  `!ss. bop_result cx (BaseT BoolT) bop [expr_type e2;expr_type e2] v v' ss =
    INL (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
       word_of_bytes_be (Keccak_256_w64 contents') else
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
       word_of_bytes_be (Keccak_256_w64 contents')))` by
    (irule comparison_source_result >>
     simp[] >>
     (conj_tac >-
       (qpat_x_assum `is_bytestring_type (expr_type e2)` mp_tac >>
        Cases_on `expr_type e2` >> simp[is_bytestring_type_def] >>
        rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def] >>
        rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def])) >>
     gnvs[byteTheory.word_of_bytes_be_def] >> metis_tac[]) >>
  `compile_compare bop h1 h2 (expr_type e2) st4 = (op,sb)` by
    (qpat_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >>
     Cases_on `emit_op EQ [h1;h2] st4` >>
     gnvs[compile_compare_def, comp_bind_def,
       vyperASTTheory.expr_type_def, as_stack_val_def, is_word_type_def]
     >- (qpat_x_assum `StackValue _ _ = _ /\ _` strip_assume_tac >>
         gnvs[unwrap_value_def, comp_return_def]) >>
     Cases_on `emit_op ISZERO [q] r` >> gnvs[as_stack_val_def, is_word_type_def] >>
     qpat_x_assum `StackValue _ _ = _ /\ _` strip_assume_tac >>
     gnvs[unwrap_value_def, comp_return_def]) >>
  `?u. run_inst_seq (emitted_insts st4 sb) t' = OK u /\
    eval_operand op u = SOME (bool_to_word (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
       word_of_bytes_be (Keccak_256_w64 contents') else
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
       word_of_bytes_be (Keccak_256_w64 contents')))` by
    (qpat_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >>
     gnvs[compile_compare_def, comp_bind_def]
     >- metis_tac[bop_eq_emit_run] >>
     pairarg_tac >> gnvs[] >>
     drule_all bop_eq_emit_run >> strip_tac >>
     drule_all bop_iszero_emit_run >> strip_tac >>
     `emitted_insts st4 sb = emitted_insts st4 cs'' ++ emitted_insts cs'' sb` by
       (imp_res_tac bop_compare_emit_layout >>
        irule emitted_insts_append >> fs[emitHelperPropsTheory.inst_extends_def]) >>
     asm_rewrite_tac[bop_run_inst_seq_append_ok] >> simp[] >>
     goal_assum (drule_at Any) >>
     Cases_on `(word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
       word_of_bytes_be (Keccak_256_w64 contents')` >>
     fs[venomExecSemanticsTheory.bool_to_word_def]) >>
  `fn_has_code st4 sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `local_ptrs_reserved cenv st4` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st4 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st4 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all bop_compile_compare_endpoint >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `wb_frame cenv es sa s0 (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> (reverse conj_tac >- metis_tac[]) >>
     qexistsl_tac [`ee'`, `st4`, `t'`] >> simp[] >> decide_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 H'' un''` by
    (qpat_assum `ghost_kept cenv ee' st4 _ _ _ _ _` mp_tac >>
     disch_then (mp_then (Pos last) mp_tac wordArgsPtrTheory.ghost_kept_wb_trans) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  `bop_operand_post d ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) es sa sb op s0 G0 tn0
    (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
       word_of_bytes_be (Keccak_256_w64 contents') else
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
       word_of_bytes_be (Keccak_256_w64 contents'))) ee'
    (u with vs_inst_idx := LENGTH sb.cs_current_insts) H'' un''` by
    (irule bop_bool_parent_post >>
     simp[vyperASTTheory.expr_type_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  irule bodyPtrHashBuiltinsSummaryTheory.hash_zero_mark_summary >>
  qexistsl_tac [`H''`, `ee'`, `INL (BoolV (if bop = Eq then
    (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
     word_of_bytes_be (Keccak_256_w64 contents') else
    (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
     word_of_bytes_be (Keccak_256_w64 contents')))`,
    `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `un''`] >>
  gnvs[bop_operand_post_def, vyperASTTheory.expr_type_def]
QED

(* RESIDUAL: dynamic bytestring Eq/NotEq; held with S1's compile_bop_bytestring_eqne_case *)
Theorem bop_bytestring_expr_ptr_residual:
  !cx ty bop e1 e2.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH [e1;e2]) ==>
     body_exprs_ptr_ok cx [e1;e2]) /\
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])
Proof
  cheat
QED
