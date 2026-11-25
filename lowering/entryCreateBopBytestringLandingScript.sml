Theory entryCreateBopBytestringLanding
Ancestors
  entryCreateCompletedCut entryCreateFocusSpec exprSimFullBundleProps
  bodyFullBopBytestringFinalPost bodyPtrBopTypedSource bodyMemBopHeldFacts
  exprSimWordArgs vyperStorageTrace vyperStorageFootprint
  bodyPtrDefs loweringPosts venomState venomInst ptrDiscipline
  vyperInterpreter vyperState exprBopSimDefs exprSimHypsDefs exprLoweringProps
  loweringShapeDefs bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullBopBytestringDigest exprBopDigestProps fragGasOriginPtr gasSummary
  compileEnv emitHelper vyperAST vyperTypeSystem vyperValue loweringStateRelDefs
  byte keccak fragExec

Theorem digest_preserved_by_read[local]:
  wb_frame cenv mid ee sh1 t u /\
  ghost_kept_at lo cenv mid sh1 G1 tn1 t G2 tn2 /\
  eval_operand h t = SOME w /\ op_prov G1 h = NONE /\ op_taint tn1 h = {} /\
  (!z. h = Var z ==> not_fresh_at sh1 z) /\ (!l. h <> Label l) ==>
  eval_operand h u = SOME w /\ op_prov G2 h = NONE /\ op_taint tn2 h = {}
Proof
  Cases_on `h` >>
  simp[eval_operand_def, op_prov_def, op_taint_def, wb_frame_def, ghost_kept_at_def] >>
  metis_tac[]
QED

Theorem read_horizon_back[local]:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
    (INL v, ee with gas_obs := tail)) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  qpat_assum `bind (eval_expr cx e) _ _ = _`
    (mp_then Any mp_tac valid_horizon_frame) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
QED

Theorem digest_read_type[local]:
  expr_body_pre cenv cx env e es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
    (INL v,ee with gas_obs := tail)) ==>
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v`, `ee with gas_obs := []`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* The two source endpoints are the normalized states handed to the next
   continuation by the scoped bind.  The only new machine run is the comparison. *)
Theorem bop_bytestring_digest_scoped_landing:
  well_typed_binop (BaseT BoolT) bop (expr_type e1) (expr_type e2) /\
  is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq) /\
  expr_body_pre cenv cx env e1 es /\ expr_body_pre cenv cx env e2 mid /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := xs1 ++ tail) =
     (INL v1,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := xs2 ++ tail) =
     (INL v2,ee with gas_obs := tail)) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ?contents.
    (v1 = BytesV contents \/ ?str. v1 = StringV str /\ contents = MAP (n2w o ORD) str) /\
    eval_operand h1 t = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    op_prov G1 h1 = NONE /\ op_taint tn1 h1 = {} /\
    (!z. h1 = Var z ==> not_fresh_at sh1 z) /\ (!l. h1 <> Label l) /\
    stmt_state_rel H ctx func cenv cx mid t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\ ~t.vs_halted /\
    t.vs_current_bb = sh1.cs_current_bb /\ t.vs_inst_idx = LENGTH sh1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv es mid sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    (~expr_has_effect e1 ==> pure_frame cenv func es sa s0 t)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ?contents.
    (v2 = BytesV contents \/ ?str. v2 = StringV str /\ contents = MAP (n2w o ORD) str) /\
    eval_operand h2 u = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    op_prov G2 h2 = NONE /\ op_taint tn2 h2 = {} /\
    (!z. h2 = Var z ==> not_fresh_at sh2 z) /\ (!l. h2 <> Label l) /\
    stmt_state_rel H ctx func cenv cx ee u /\
    ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\ ~u.vs_halted /\
    u.vs_current_bb = sh2.cs_current_bb /\ u.vs_inst_idx = LENGTH sh2.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
    wb_frame cenv mid ee sh1 t u /\ ghost_kept_at lo cenv mid sh1 G1 tn1 t G2 tn2 /\
    (~expr_has_effect e2 ==> pure_frame cenv func mid sh1 t u)) /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sh1.cs_next_var /\ sh1.cs_next_var <= sh2.cs_next_var /\
  sa.cs_next_id <= sh1.cs_next_id /\ fn_inst_ids_distinct func /\
  fn_has_code sh2 sb func /\
  (if bop = Eq then emit_op EQ [h1;h2] sh2
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] sh2)]
                       (SND (emit_op EQ [h1;h2] sh2))) = (op,sb) /\
  (!raw. create_operand_at sh2 u /\ ~u.vs_halted /\
      run_inst_seq (emitted_insts sh2 sb) u = OK raw ==>
      create_operand_full_scope sh2 sb explicit ctx func u []
        (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
  (!H. valid_horizon cx st0 H mid.storage_trace /\ storage_well_formed_on cx es (FST H) ==>
      storage_well_formed_on cx mid (FST H)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx mid (FST H) ==>
      storage_well_formed_on cx ee (FST H)) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 sh2 sb
    (\ss. (bop_result cx (BaseT BoolT) bop [expr_type e1;expr_type e1] v1 v2 ss,ss))
    (ee,u,G2,tn2)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx
      (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) (es,sa,sb,s0,op,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> disch_tac >> irule read_horizon_back >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >> irule read_horizon_back >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ?contents. _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `contents2` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?contents. _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- metis_tac[]) >> disch_then (qx_choose_then `contents1` (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand h1 u = SOME (word_of_bytes_be (Keccak_256_w64 contents1)) /\
   op_prov G2 h1 = NONE /\ op_taint tn2 h1 = {}` by
    (irule digest_preserved_by_read >> metis_tac[]) >>
  `!z. h1 = Var z ==> not_fresh_at sh2 z` by metis_tac[not_fresh_at_mono] >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  drule_all bop_bytestring_digest_operational >>
  disch_then (qspecl_then [`explicit`, `PG`] (qx_choose_then `raw`
    (qx_choose_then `final` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))))) >>
  drule_all held_bytestring_eqne_types >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(?ty1. evaluate_type (get_tenv cx) (expr_type e1) = SOME ty1 /\ value_has_type ty1 v1) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (irule digest_read_type >> metis_tac[]) >>
  `(?ty2. evaluate_type (get_tenv cx) (expr_type e2) = SOME ty2 /\ value_has_type ty2 v2) /\
   MAP FDOM mid.scopes = MAP FDOM ee.scopes` by
    (irule digest_read_type >> metis_tac[]) >>
  qabbrev_tac `w1 = word_of_bytes_be (Keccak_256_w64 contents1) : bytes32` >>
  qabbrev_tac `w2 = word_of_bytes_be (Keccak_256_w64 contents2) : bytes32` >>
  qabbrev_tac `b = (if bop = Eq then w1 = w2 else w1 <> w2)` >>
  `!ss. bop_result cx (BaseT BoolT) bop [expr_type e1;expr_type e1] v1 v2 ss =
        INL (BoolV b)` by
    (simp[Abbr `b`, Abbr `w1`, Abbr `w2`, word_of_bytes_be_def] >>
     irule comparison_source_result >>
     metis_tac[optionTheory.SOME_11]) >>
  `create_operand_full_scope sh2 sb explicit ctx func u [] (OK final)` by
    (qpat_assum `final = _` SUBST1_TAC >> simp[create_operand_at_def]) >>
  qpat_x_assum `final = _` (mk_asm "landing_pc") >>
  pure_rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL (BoolV b)`,`ee`,`OK final`,`Gf`,`tnf`] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[gas_explicit_def, exit_result_def] >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  `stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)` by simp[] >>
  `storage_well_formed_on cx mid (FST H)` by simp[] >>
  `storage_well_formed_on cx ee (FST H)` by simp[] >>
  `stmt_state_rel H ctx func cenv cx ee u /\ ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ?contents. _`
      (qspec_then `H` mp_tac) >> simp[] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sh2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh2 x` by
     metis_tac[not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh2 x` by
     metis_tac[not_fresh_at_mono] >>
  SIMP_TAC bool_ss [expr_sim_full_post_def, expr_sim_full_endpoint_def, post_value_type_def,
    sumTheory.INL_11, UNWIND_THM2] >>
  qmatch_abbrev_tac `post /\ bound /\ bb /\ pc /\ hist /\ bump /\ fmp /\ rest` >>
  `post /\ bound /\ bb /\ pc /\ hist /\ fmp /\ bump /\ rest` suffices_by simp[] >>
  map_every qunabbrev_tac [`post`,`bound`,`bb`,`pc`,`hist`,`bump`,`fmp`,`rest`] >>
  irule (PURE_REWRITE_RULE [post_value_type_def] bop_bytestring_final_post) >>
  asm "landing_pc" assume_tac >> simp[] >>
  qexistsl_tac [`G1`,`G2`,`mid`,`h1`,`h2`,`raw`,`raw`,`sh1`,`sh2`,`t`,`tn1`,`tn2`,`u`] >>
  simp[] >>
  asm "landing_pc" (fn th => REWRITE_TAC [GSYM th]) >> simp[]
QED
