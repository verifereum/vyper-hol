Theory bodyPtrBopResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list compileEnv
  bodyPtrBopHashCompile bodyPtrBopCompareCompile bodyPtrBopOperandContract
  bodyPtrBopEntry bodyPtrBopTypedSource exprPtrUnwrap exprSimBopBytestring
  exprBopLowering exprLowering emitHelper exprLoweringProps
  bodyPtrBopHashSuffix exprSimOperators exprSimLiteralWord bytestringHashProps
  bodyPtrBopSelectedHash exprBopDigestProps bodyPtrBopCompareEndpoint
Libs pairLib

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
  `bop <> In /\ bop <> NotIn` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >> gvs[]) >>
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
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  qpat_x_assum `(\(h2,st4). _) _ = _` mp_tac >>
  pairarg_tac >> gnvs[] >> strip_tac >> strip_tac >>
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
  irule bop_selected_hash_outcome_ptr_frame >>
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
  irule bop_selected_hash_outcome_ptr_frame >>
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
   op_prov HG' h1 = NONE /\ op_taint un' h1 = {}` by
    (Cases_on `h1` >>
     fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, ghost_kept_def] >>
     metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `wb_frame cenv es ee' sa s0 t'` by
    metis_tac[exprSimWordArgsTheory.wb_frame_trans] >>
  `ghost_kept cenv es sa G0 tn0 s0 HG' un'` by
    metis_tac[wordArgsPtrTheory.ghost_kept_wb_trans] >>
  `~expr_has_effect e1 /\ ~expr_has_effect e2 ==>
    pure_frame cenv func es sa s0 t'` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 t /\ pure_frame cenv func ee st2 t t'` by simp[] >>
     `(!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP t'.vs_allocas aid = SOME b) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w)` by
       metis_tac[loweringPostsTheory.wb_frame_def] >>
     drule_all exprSimPropsTheory.pure_frame_trans >> simp[]) >>
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
    (irule comparison_source_result >> simp[] >>
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
  `(if bop = Eq then emit_op EQ [h1;h2] st4
    else (\(q,sm). emit_op ISZERO [q] sm) (emit_op EQ [h1;h2] st4)) = (op,sb)` by
    (gvs[compile_compare_def, comp_bind_def]) >>
  drule_all (SRULE [LET_THM] exprBopSimPropsTheory.comparison_digest_run) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 sb) t' = OK u` >>
  `fn_has_code st4 sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `local_ptrs_reserved cenv st4` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st4 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st4 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all bop_compile_compare_endpoint >>
  disch_then (qspecl_then [`PG`, `cx_dead H cx`] strip_assume_tac) >>
  `wb_frame cenv es ee' sa s0 (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`u.vs_memory = t'.vs_memory /\ u.vs_allocas = t'.vs_allocas` by
       (qpat_x_assum `(u with vs_vars := _) = t'` mp_tac >>
        simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
     irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`st4`, `t'`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!z. not_fresh_at st4 z ==> lookup_var z u = _`
       (drule_then mp_tac) >>
     simp[venomStateTheory.lookup_var_def]) >>
  `ghost_kept cenv es sa G0 tn0 s0 HG'' un''` by
    (qpat_assum `ghost_kept cenv ee' st4 _ _ _ _ _` mp_tac >>
     disch_then (mp_then (Pos last) mp_tac wordArgsPtrTheory.ghost_kept_wb_trans) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  `~expr_has_effect (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) ==>
    pure_frame cenv func es sa s0 (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[] >> strip_tac >>
     irule exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `t'` >> simp[] >>
     qpat_x_assum `(u with vs_vars := _) = t'` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `bop_operand_post d ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) es sa sb op s0 G0 tn0
    (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
       word_of_bytes_be (Keccak_256_w64 contents') else
      (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
       word_of_bytes_be (Keccak_256_w64 contents'))) ee'
    (u with vs_inst_idx := LENGTH sb.cs_current_insts) HG'' un''` by
    (irule bop_bool_parent_post >>
     simp[vyperASTTheory.expr_type_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  irule bodyPtrHashBuiltinsSummaryTheory.hash_zero_mark_summary >>
  qexistsl_tac [`HG''`, `ee'`, `INL (BoolV (if bop = Eq then
    (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) =
     word_of_bytes_be (Keccak_256_w64 contents') else
    (word_of_bytes_be (Keccak_256_w64 contents) : bytes32) <>
     word_of_bytes_be (Keccak_256_w64 contents')))`,
    `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `un''`] >>
  gnvs[bop_operand_post_def, vyperASTTheory.expr_type_def]
QED

Theorem bop_bytestring_expr_ptr_residual:
  !cx ty bop e1 e2.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH [e1;e2]) ==>
     body_exprs_ptr_ok cx [e1;e2]) /\
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])
Proof
  rpt gen_tac >> strip_tac >>
  `body_expr_ptr_ok cx e1 /\
   ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==> body_expr_ptr_ok cx e2)` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> _` mp_tac >>
     simp[builtin_args_length_ok_def, body_exprs_ptr_ok_def] >> metis_tac[]) >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (Bop bop) [e1;e2]) es` by
    (irule bop_bytestring_forced_ptr >> simp[] >> metis_tac[]) >>
  gvs[] >> irule exprPtrUnwrapTheory.expr_vv_sim_ptr_stack >>
  simp[compile_bop_stack] >> metis_tac[eval_expr_builtin_value]
QED
