Theory createSizeExitBlueprint
Ancestors
  createSizeIndexedRun
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  s1PrefixDefs venomExecSemantics venomInst venomState vyperCreate vyperInterpreter
  vyperState relation list words pair builtinCreate arithmetic exprLowering vfmConstants
  loweringShapeRules compileEnv createSizeItinerary exprLoweringProps exprBodyPreProps
  freshWrites rich_list exprSimHypsDefs createSizeBlueprintOffset bodyPtrDefs loweringPosts
  context vyperAST vyperStorageFootprint allocLimits createSizeStraightPrefix
  ghostPcTransportPtr integer_word createCtorSegmentArrival loweringStateRelDefs
  ptrDiscipline emitHelperProps dallocaBlueprintArgs bodySim loweringShapeDefs
  createSizeBlueprintExtent createOperandSizeReject createExprSizeExitDefs
  createSizeBlueprintKeywordReplay createSizeBlueprintKeywords
  createSizeBlueprintRawKeywords createSizeBlueprintAbiKeywords createSizeBlueprintDispatch
  createSizeOperandPre createSizePrefixReplay

Theorem blueprint_append_cut_geometry[local]:
  create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz /\
  n = j+4+LENGTH app /\
  (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
  C n = sc ==>
  ?ca1 ca2 ca3.
    emit_op ADD [code;len] cf = (sz,ca1) /\
    compile_alloc_dynamic sz ca1 = (offop,ca2) /\
    emit_void EXTCODECOPY [target_op;offop;offset_op;code] ca2 = ((),ca3) /\
    C (j+5) = ca1 /\ j+5 <= n /\
    (if len = Lit 0w then sc = ca3 else
       ?args_dest ca4. emit_op ADD [offop;code] ca3 = (args_dest,ca4) /\
         compile_copy_memory_dynamic args_dest data len ca4 = ((),sc))
Proof
  strip_tac >>
  qpat_assum `create_blueprint_append_itinerary _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_blueprint_append_itinerary_def]) >>
  rename [`emit_op ADD [code;len] cf = (sz,ca1)`,
    `compile_alloc_dynamic sz ca1 = (offop,ca2)`,
    `emit_void EXTCODECOPY _ ca2 = ((),ca3)`] >>
  qexistsl_tac [`ca1`,`ca2`,`ca3`] >>
  Cases_on `len = Lit 0w` >>
  FIRST (map (fn pat => qpat_assum pat (fn h =>
    qpat_assum `if len = Lit 0w then app = _ else _`
      (strip_assume_tac o REWRITE_RULE[h,COND_CLAUSES])))
    [`len = Lit 0w`,`len <> Lit 0w`]) >>
  `LENGTH app = 3 \/ LENGTH app = 5` by simp[] >>
  `0 < LENGTH app /\ LENGTH app - 1 < LENGTH app /\
    j + 5 + (LENGTH app - 1) = n /\ j + 5 <= n` by decide_tac >>
  `C (j+5) = ca1` by
    (qpat_assum `!i. i < LENGTH app ==> C (j+5+i) = EL i app`
      (qspec_then `0` (drule_then mp_tac)) >>
     qpat_assum `app = ca1::ca2::ca3::_` (fn th => simp_tac (srw_ss()) [th])) >>
  `C n = EL (LENGTH app - 1) app` by
    (qpat_assum `!i. i < LENGTH app ==> C (j+5+i) = EL i app`
       (qspec_then `LENGTH app - 1` mp_tac) >> simp_tac bool_ss [] >>
     disch_then drule >> disch_then (fn th =>
       qpat_assum `j + 5 + (LENGTH app - 1) = n` (ACCEPT_TAC o C (REWRITE_RULE o single) th))) >>
  `sc = EL (LENGTH app - 1) app` by
    (qpat_assum `C n = sc` (fn th => pop_assum (ACCEPT_TAC o REWRITE_RULE[th]))) >>
  qpat_assum `app = ca1::ca2::ca3::_` (fn th =>
    pop_assum (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  FIRST (map (fn pat => qpat_assum pat (pure_rewrite_tac o single))
    [`len = Lit 0w`,`len <> Lit 0w`]) >>
  simp_tac bool_ss [COND_CLAUSES] >>
  (first_assum ACCEPT_TAC ORELSE
   (goal_assum (drule_at Any) >> qpat_assum `sc = _` (pure_rewrite_tac o single) >>
    first_assum ACCEPT_TAC))
QED

Theorem blueprint_raw_payload_result[local]:
  (
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
    ?bs qp Gp tnp. ctors = [raw_e] /\
      bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
        (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
          (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::BytesV bs::kvs)) qp = (res,srcout) /\
      valid_horizon cx st0 H qp.storage_trace /\
      eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
      (!x. len = Var x ==> not_fresh_at cprep x) /\
      eval_operand target_op (Obs j) = SOME aw /\
      (!x. target_op = Var x ==> not_fresh_at cprep x) /\
      expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
      (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
      (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
      (!h. valid_horizon cx st0 h qp.storage_trace ==>
        stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
        ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
      ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
      (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
      qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
  ) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs bs qp Gp tnp.
    LENGTH cvs = LENGTH ctors /\
    cvs = [BytesV bs] /\
    bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
    eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op (Obs j) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
    (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h qp.storage_trace ==>
      stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
      ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
    qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
Proof
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`bytes`,`paystate`,`payG`,`paytn`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac [`[BytesV bytes]`,`bytes`,`paystate`,`payG`,`paytn`] >>
  simp_tac (srw_ss()) [COND_CLAUSES, APPEND, LENGTH] >>
  conj_tac >- (qpat_assum `ctors = [raw_e]` (simp_tac (srw_ss()) o single)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem blueprint_abi_payload_result[local]:
  (
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
    ?cvs ps g tn1.
      LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p = (INL cvs,ps) /\
      bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
        (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
          (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) ps = (res,srcout) /\
      valid_horizon cx st0 H ps.storage_trace /\
      (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
        eval_operand len (Obs j) = SOME (n2w (LENGTH bs))) /\
      (!x. len = Var x ==> not_fresh_at cprep x) /\
      eval_operand target_op (Obs j) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cprep x) /\
      expr_sim_inv ce cx env ps /\ local_ptrs_reserved ce cprep /\
      (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
      (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
      (!h. valid_horizon cx st0 h ps.storage_trace ==>
        stmt_state_rel h ctx func ce cx ps (Obs j) /\ storage_well_formed_on cx ps (FST h) /\
        ghost_inv_at (DF h) lo depr ce cx ps g tn1 (Obs j)) /\
      ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
      (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
      ps.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
  ) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs bs qp Gp tnp.
    LENGTH cvs = LENGTH ctors /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
    bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
    eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op (Obs j) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
    (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h qp.storage_trace ==>
      stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
      ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
    qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
Proof
  disch_then (DISJ_CASES_THEN2 assume_tac
   (qx_choosel_then [`cvs`,`ps`,`g`,`tn1`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?bs. encode_create_ctor_args _ _ cvs = SOME bs /\ _`
    (qx_choose_then `bytes` (map_every assume_tac o CONJUNCTS)) >>
  disj2_tac >> qexistsl_tac [`cvs`,`bytes`,`ps`,`g`,`tn1`] >>
  simp_tac bool_ss [COND_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem create_size_exit_blueprint:
  !cx ty raw hs rof ks args d.
    EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) ==>
    create_expr_size_exit cx (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d)
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[create_expr_size_exit_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_blueprint_payload_inputs_at_dispatch >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (disj2_tac >> first_assum ACCEPT_TAC) >>
  rename [`body_inv tops ctx ce cx`, `shadow_body_inv tops ctx shctx`,
          `eval_operand offset_word s = SOME w`, `valid_horizon cx st0 H out.storage_trace`,
          `C (j+3) = cb`, `Obs n = s`] >>
  suspend "dispatch"
QED

Resume create_size_exit_blueprint[dispatch]:
  rename [`valid_horizon cx st0 H out.storage_trace`,
    `args = target::amount::((if hs then [salt_e] else []) ++ off_e::ctors)`,
    `C j = cprep`, `C (SUC j) = cm`,
    `C (j+2) = cn`, `C (j+4) = cf`, `C n = sc`,
    `eval_operand target_op (Obs 1) = SOME aw`,
    `create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz`,
    `p.gas_obs = gas_explicit (R 1) _ ++ tail`,
    `later = amount::_`, `bind _ (\vs. _ (av::vs)) p = _`] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`1`,`1 <= n`),(`j`,`j <= n`),(`SUC j`,`SUC j <= n`),
     (`j+2`,`j+2 <= n`),(`j+3`,`j+3 <= n`),(`j+4`,`j+4 <= n`)] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i < n ==> (C i).cs_next_id <= _ /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`j`,`j < n`),(`SUC j`,`SUC j < n`),(`j+2`,`j+2 < n`),(`j+3`,`j+3 < n`)] >>
  `SUC (SUC j) = j+2 /\ SUC (j+2) = j+3 /\ SUC (j+3) = j+4` by decide_tac >>
  `R j = M j ++ (M (SUC j) ++ (M (j+2) ++ R (j+3)))` by
    (qpat_assum `R j = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `R (SUC j) = _` (pure_once_rewrite_tac o single) >>
     `SUC (SUC j) = j+2` by decide_tac >>
     qpat_assum `SUC (SUC j) = j+2` (pure_once_rewrite_tac o single) >>
     qpat_assum `R (j+2) = _` (pure_once_rewrite_tac o single) >> simp[arithmeticTheory.ADD1]) >>
  suspend "payload_join"
QED

Resume create_size_exit_blueprint[payload_join]:
  rename [`eval_expr cx (Call ty _ args d) _ = (res,srcout)`,
    `p.gas_obs = gas_explicit (R 1) _ ++ tail`, `return_buf_frame depr ce ca (Obs 1)`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?cvs bs qp Gp tnp.
     LENGTH cvs = LENGTH ctors /\
     (if raw then cvs = [BytesV bs] else
        encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs) /\
     bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
       (\kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
         (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
     eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
     (!x. len = Var x ==> not_fresh_at cprep x) /\
     eval_operand target_op (Obs j) = SOME aw /\
     (!x. target_op = Var x ==> not_fresh_at cprep x) /\
     expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
     (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
     (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
     (!h. valid_horizon cx st0 h qp.storage_trace ==>
       stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
       ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
     qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail`
    suffices_by
      (disch_then (DISJ_CASES_THEN2 assume_tac
        (qx_choosel_then [`cvs`,`payload`,`paystate`,`Gp`,`tnp`]
          (map_every assume_tac o CONJUNCTS)))
       >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "keywords") >>
  Cases_on `raw` >- suspend "raw_payload" >> suspend "abi_payload"
QED

Resume create_size_exit_blueprint[keywords]:
  map_every (fn q => qpat_assum q (fn th => rule_assum_tac (REWRITE_RULE[th]) >> assume_tac th))
    [`SUC (SUC j) = j+2`,`SUC (j+2) = j+3`,`SUC (j+3) = j+4`,
     `C j = cprep`,`C (SUC j) = cm`,`C (j+2) = cn`,`C (j+3) = cb`,`C (j+4) = cf`] >>
  `?sop. if hs then
      lower_value compile_expr ce (expr_type salt_e) salt_e cm = (sop,cn) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt_e) (gas_shadow_expr salt_e) scm = (sop,scn) /\
      expr_sim_full_code (ctx,shctx,func,shadow_func) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx func (Obs (SUC j)) (M (SUC j)) (Obs (j+2)) /\
      (Obs (j+2)).vs_current_bb = cn.cs_current_bb /\ (Obs (j+2)).vs_inst_idx = LENGTH cn.cs_current_insts
    else cn = cm /\ scn = scm /\ Obs (j+2) = Obs (SUC j) /\ M (SUC j) = []` by
    (qpat_assum `if hs then ?sop. salt_op = SOME sop /\ _ else _` mp_tac >>
     Cases_on `hs` >> simp_tac bool_ss [COND_CLAUSES]
     >- (disch_then (qx_choose_then `sop` (map_every assume_tac o CONJUNCTS)) >>
         qexists_tac `sop` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `cm = cn` by (sym_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `cm = cn ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(?oty i. origin_fold_value off_e = Literal oty (IntL i) /\
       offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn /\ Obs (j+3) = Obs (j+2) /\ M (j+2) = []) \/
     lower_value compile_expr ce (expr_type off_e) off_e cn = (offset_op,cb) /\
     lower_value compile_expr (gas_shadow_env T ce) (expr_type off_e) (gas_shadow_expr off_e) scn = (offset_op,scb) /\
     expr_sim_full_code (ctx,shctx,func,shadow_func) (cn,cb,scn,scb) /\
     create_expr_prefix cn cb (gas_explicit_sites ctx shctx) ctx func (Obs (j+2)) (M (j+2)) (Obs (j+3)) /\
     (Obs (j+3)).vs_current_bb = cb.cs_current_bb /\ (Obs (j+3)).vs_inst_idx = LENGTH cb.cs_current_insts`
    suffices_by (disch_then assume_tac >> suspend "keyword_apply") >>
  qpat_assum `(?oty i. origin_fold_value off_e = _ /\ _) \/ _` strip_assume_tac
     >- (`cn = cb` by (sym_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `cn = cb ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
         disj1_tac >>
         qmatch_asmsub_rename_tac `origin_fold_value off_e = Literal lit_ty (IntL lit_i)` >>
         qexistsl_tac [`lit_ty`,`lit_i`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> conj_tac
  >- qpat_assum `lower_value compile_expr ce (expr_type off_e) off_e cn = (offset_op,cb)` ACCEPT_TAC >>
  conj_tac
  >- qpat_assum `lower_value compile_expr (gas_shadow_env T ce) _ (gas_shadow_expr off_e) scn = (offset_op,scb)` ACCEPT_TAC >>
  conj_tac >- qpat_assum `expr_sim_full_code (ctx,shctx,func,shadow_func) (cn,cb,scn,scb)` ACCEPT_TAC >>
  conj_tac >- qpat_assum `create_expr_prefix cn cb _ ctx func (Obs (j+2)) (M (j+2)) (Obs (j+3))` ACCEPT_TAC >>
  conj_tac >- qpat_assum `(Obs (j+3)).vs_current_bb = cb.cs_current_bb` ACCEPT_TAC >>
  qpat_assum `(Obs (j+3)).vs_inst_idx = LENGTH cb.cs_current_insts` ACCEPT_TAC
QED
Resume create_size_exit_blueprint[keyword_apply]:
  qpat_assum `R j = M j ++ (M (SUC j) ++ _)` (fn schedule =>
    qpat_assum `paystate.gas_obs = _`
      (assume_tac o PURE_ONCE_REWRITE_RULE [schedule])) >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?kvs q ops ow.
    eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])) paystate = (INL kvs,q) /\
    eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) q = (res,srcout) /\
    dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow) /\
    eval_operand target_op (Obs (j+3)) = SOME aw /\ eval_operand offset_op (Obs (j+3)) = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) (Obs (j+3)).vs_accounts).code /\
    (!x w. not_fresh_at cprep x /\ lookup_var x (Obs j) = SOME w ==>
       lookup_var x (Obs (j+3)) = SOME w)` suffices_by
    (disch_then (DISJ_CASES_THEN2 assume_tac
        (qx_choosel_then [`kvs`,`qs`,`ops`,`ow`] (map_every assume_tac o CONJUNCTS)))
     >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "extent") >>
  irule create_blueprint_keywords_at_cuts >> suspend "keyword_premises"
QED
Resume create_size_exit_blueprint[keyword_premises]:
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qexistsl_tac [`ctors`,`target`] >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  qexistsl_tac [`DF`,`Gp`,`H`,`value`,`ty`,`ce`,`cm`,`cn`,`ctx`,`depr`,`d`,`es`,`env`] >>
  qexistsl_tac [`func`,`ks`,`lo`,`Obs (SUC j)`,`M j`,`M (j+2)`,`M (SUC j)`,`Obs (j+2)`,`R (j+3)`] >>
  qexistsl_tac [`sop`,`scprep`,`scb`,`scm`,`scn`,`shctx`,`shadow_func`,`st0`,`tail`,`tnp`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[extent]:
  qpat_assum `create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz`
    (fn itinerary => qpat_assum `n = j+4+LENGTH app` (fn length =>
      qpat_assum `!i. i < LENGTH app ==> C (j+5+i) = EL i app` (fn cuts =>
        qpat_assum `C n = sc` (fn last =>
          mp_tac (MATCH_MP blueprint_append_cut_geometry
            (LIST_CONJ [itinerary,length,cuts,last])))))) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `C (j+5) = ca1` >>
  qmatch_asmsub_rename_tac `compile_alloc_dynamic sz ca1 = (offop,ca2)` >>
  qmatch_asmsub_rename_tac `emit_void EXTCODECOPY _ ca2 = ((),ca3)` >>
  suspend "extent_geometry"
QED
Resume create_size_exit_blueprint[extent_geometry]:
  `cf.cs_current_bb = cb.cs_current_bb /\
   cf.cs_current_insts = cb.cs_current_insts ++ emitted_insts cb cf /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts cb cf)` by
    (qpat_assum `compile_create_blueprint_check _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `is_int_literal (origin_fold_value off_e)` >>
     rewrite_tac [compile_create_blueprint_check_def] >>
     simp[emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[mk_inst_def,is_terminator_def]) >>
  `ca1.cs_current_bb = cf.cs_current_bb /\
   ca1.cs_current_insts = cf.cs_current_insts ++ emitted_insts cf ca1 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts cf ca1)` by
    (qpat_assum `emit_op ADD [code;len] cf = (sz,ca1)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule emitted_insts_emit_op >> drule emit_op_facts >>
     strip_tac >> simp[mk_inst_def,is_terminator_def]) >>
  `sc.cs_current_bb = ca1.cs_current_bb /\
   sc.cs_current_insts = ca1.cs_current_insts ++ emitted_insts ca1 sc /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts ca1 sc)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`if len = Lit 0w then sc = ca3 else _`,
        `emit_void EXTCODECOPY _ ca2 = ((),ca3)`, `compile_alloc_dynamic sz ca1 = (offop,ca2)`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `len = Lit 0w` >> simp[compile_alloc_dynamic_def,compile_copy_memory_dynamic_def,
       emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,fresh_var_def,emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[mk_inst_def,is_terminator_def]) >>
  suspend "extent_runs"
QED
Resume create_size_exit_blueprint[extent_runs]:
  `!i k a b. i <= k /\ k <= n /\ C i = a /\ C k = b /\
    b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
    EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
      (emitted_insts a b) ==>
    run_inst_seq (emitted_insts a b) (Obs i) = OK ((Obs k) with vs_inst_idx := (Obs i).vs_inst_idx)`
    suffices_by (disch_then assume_tac >> suspend "extent_apply") >>
  qx_genl_tac [`i`,`k`,`a0`,`b0`] >> strip_tac >>
  map_every (fn idx =>
    qpat_assum `!r. r <= n ==> ~(Obs r).vs_halted /\ _`
      (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
    disch_then (map_every assume_tac o CONJUNCTS)) [`i`,`k`] >>
  qpat_assum `!l r. l <= r /\ r <= n ==> ci_mono (C l) (C r) /\ _`
    (qspecl_then [`i`,`k`] mp_tac) >> (impl_tac >- decide_tac) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?x. ctor_segment_fetch func (Obs k) = SOME x /\ _`
    (qx_choose_then `x_end` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `lookup_block (Obs k).vs_current_bb func.fn_blocks`
  >- (qpat_assum `lookup_block (Obs k).vs_current_bb func.fn_blocks = NONE` (fn block =>
        qpat_assum `ctor_segment_fetch func (Obs k) = SOME x_end`
          (mp_tac o REWRITE_RULE [ctor_segment_fetch_def,block,optionTheory.OPTION_BIND_def])) >>
      simp[NoAsms]) >>
  rename1 `lookup_block (Obs k).vs_current_bb func.fn_blocks = SOME bb_end` >>
  `get_instruction bb_end (Obs k).vs_inst_idx = SOME x_end` by
    (qpat_assum `lookup_block (Obs k).vs_current_bb func.fn_blocks = SOME bb_end` (fn block =>
       qpat_assum `ctor_segment_fetch func (Obs k) = SOME x_end`
         (ACCEPT_TAC o BETA_RULE o REWRITE_RULE [ctor_segment_fetch_def,block,optionTheory.OPTION_BIND_def]))) >>
  mp_tac (Q.INST [`i` |-> `i`, `k` |-> `k`, `C` |-> `C`, `Obs` |-> `Obs`,
    `a` |-> `a0`, `b` |-> `b0`, `fn` |-> `func`, `ctx` |-> `ctx`,
    `explicit` |-> `gas_explicit_sites ctx shctx`,
    `end_bb` |-> `bb_end`, `inst` |-> `x_end`, `marks` |-> `M`] create_indexed_straight_run) >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qx_gen_tac `r` >> strip_tac >>
        `r < n` by
          (qpat_assum `k <= n` mp_tac >> qpat_assum `r < k` mp_tac >>
           rpt (pop_assum kall_tac) >> decide_tac) >>
        qpat_assum `!l. l < n ==> (C l).cs_next_id <= _ /\ _`
          (qspec_then `r` (drule_then (map_every assume_tac o CONJUNCTS))) >>
        map_every (fn (a,b) => qpat_assum `!l h. l <= h /\ h <= n ==> ci_mono (C l) (C h) /\ _`
          (qspecl_then [a,b] mp_tac) >> (impl_tac >- decide_tac) >>
          disch_then (assume_tac o REWRITE_RULE[ci_mono_def] o cj 1))
          [(`i`,`r`),(`SUC r`,`k`)] >>
        qpat_assum `C i = a0` (pure_rewrite_tac o single o SYM) >>
        qpat_assum `C k = b0` (pure_rewrite_tac o single o SYM) >>
        asm_rewrite_tac[]) >>
     map_every (fn pat => qpat_assum pat (fn th => rule_assum_tac (REWRITE_RULE[th])))
       [`C i = a0`,`C k = b0`] >>
     asm_rewrite_tac[]) >>
  simp[]
QED
Resume create_size_exit_blueprint[extent_apply]:
  map_every (fn (i,k,a,b) =>
    qpat_assum `!i k a b. _ ==> run_inst_seq (emitted_insts a b) (Obs i) = _`
      (qspecl_then [i,k,a,b] mp_tac) >>
    (impl_tac >- (conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac)
    [(`j+3`,`j+4`,`cb`,`cf`),(`j+4`,`j+5`,`cf`,`ca1`),(`j+5`,`n`,`ca1`,`sc`)] >>
  qabbrev_tac `tchk = (Obs (j+4)) with vs_inst_idx := (Obs (j+3)).vs_inst_idx` >>
  qabbrev_tac `pre = (Obs (j+5)) with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  qabbrev_tac `tf = s with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  `run_inst_seq (emitted_insts ca1 sc) pre = OK tf` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca1 sc)` by
       (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) (emitted_insts ca1 sc)` mp_tac >>
        simp_tac (srw_ss()) [EVERY_MEM]) >>
     simp_tac bool_ss [Abbr `pre`, Abbr `tf`] >>
     simp[run_inst_seq_inst_idx,instIdxIndepTheory.exec_result_map_def]) >>
  suspend "extent_len"
QED
Resume create_size_exit_blueprint[extent_len]:
  `(Obs (j+3)).vs_labels = (Obs j).vs_labels` by
    (map_every (fn (prefix,q) => q by
         qpat_assum prefix (ACCEPT_TAC o MATCH_MP create_prefix_labels))
       [(`create_expr_prefix _ _ _ _ _ (Obs j) _ (Obs (SUC j))`,
         `(Obs (SUC j)).vs_labels = (Obs j).vs_labels`),
        (`create_expr_prefix _ _ _ _ _ (Obs (SUC j)) _ (Obs (j+2))`,
         `(Obs (j+2)).vs_labels = (Obs (SUC j)).vs_labels`),
        (`create_expr_prefix _ _ _ _ _ (Obs (j+2)) _ (Obs (j+3))`,
         `(Obs (j+3)).vs_labels = (Obs (j+2)).vs_labels`)] >>
     asm_rewrite_tac[]) >>
  `eval_operand len (Obs (j+3)) = SOME (n2w (LENGTH payload))` by
    (irule blueprint_eval_operand_frame >> qexistsl_tac [`cprep`,`Obs j`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. len = Var x ==> not_fresh_at cb x` by
    (qpat_assum `!l r. l <= r /\ r <= n ==> ci_mono (C l) (C r) /\ _`
       (qspecl_then [`j`,`j+3`] mp_tac) >>
     (impl_tac >- (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC)) >>
     map_every (fn q => qpat_assum q (pure_rewrite_tac o single)) [`C j = cprep`,`C (j+3) = cb`] >>
     rewrite_tac[ci_mono_def] >> strip_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cprep` >>
     simp[]) >>
  `eval_operand len (Obs (j+4)) = SOME (n2w (LENGTH payload))` suffices_by
    (disch_then assume_tac >> suspend "extent_reject") >>
  `(eval_operand len tchk = eval_operand len (Obs (j+4)))` by
    simp[Abbr `tchk`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  qpat_assum `eval_operand len tchk = _` (pure_rewrite_tac o single o SYM) >>
  map_every (fn q => qpat_assum q mp_tac)
    [`eval_operand len (Obs (j+3)) = _`, `!x. len = Var x ==> not_fresh_at cb x`,
     `run_inst_seq (emitted_insts cb cf) (Obs (j+3)) = OK tchk`,
     `compile_create_blueprint_check _ _ _ _ = _`] >>
  rpt (pop_assum kall_tac) >>
  suspend "extent_len_check"
QED
Resume create_size_exit_blueprint[extent_len_check]:
  rpt strip_tac >>
  `EVERY (\i. (i.inst_opcode = EXTCODESIZE \/ fresh_write_op i.inst_opcode) /\
        !x. not_fresh_at cb x ==> ~MEM x i.inst_outputs) (emitted_insts cb cf)` by
    (qpat_x_assum `compile_create_blueprint_check _ _ _ _ = _` mp_tac >>
     Cases_on `is_int_literal (origin_fold_value off_e)` >>
     simp[compile_create_blueprint_check_def,emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_void_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[mk_inst_def,fresh_write_op_def,not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD,arithmeticTheory.LESS_EQ_REFL]) >>
  `tchk = (Obs (j+3)) with vs_vars := tchk.vs_vars /\
   !x. not_fresh_at cb x ==> FLOOKUP tchk.vs_vars x = FLOOKUP (Obs (j+3)).vs_vars x` by
    (match_mp_tac (Q.SPECL [`emitted_insts cb cf`, `not_fresh_at cb`,
      `Obs (j+3)`, `tchk`] run_inst_seq_protected_frame) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `EVERY _ (emitted_insts cb cf)`
       (qspec_then `i` (drule_then (CONJUNCTS_THEN2 assume_tac assume_tac o BETA_RULE)) o
        REWRITE_RULE [EVERY_MEM]) >>
     `t = s with vs_vars := t.vs_vars /\
      !x. ~MEM x i.inst_outputs ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x` by
       (Cases_on `i.inst_opcode = EXTCODESIZE`
        >- (qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
            asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
            simp_tac (srw_ss()) [exec_read1_def] >>
            rpt (BasicProvers.PURE_TOP_CASE_TAC >> simp_tac (srw_ss()) []) >>
            strip_tac >>
            qpat_assum `update_var _ _ s = t` (SUBST1_TAC o SYM) >>
            qpat_assum `i.inst_outputs = [_]` (fn outputs =>
              simp_tac (srw_ss()) [outputs,update_var_def,finite_mapTheory.FLOOKUP_UPDATE,
                venom_state_component_equality])) >>
        match_mp_tac (Q.SPECL [`i`,`s`,`t`] step_pure_opcode_frame) >>
        qpat_assum `i.inst_opcode = EXTCODESIZE \/ fresh_write_op i.inst_opcode`
          (mp_tac o REWRITE_RULE [fresh_write_op_def]) >>
        asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!x. ~MEM x i.inst_outputs ==> _` (irule o SPEC_ALL) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  Cases_on `len` >> fs[eval_operand_def,lookup_var_def] >>
  qpat_assum `tchk = (Obs (j+3)) with vs_vars := tchk.vs_vars`
    (once_rewrite_tac o single) >>
  asm_simp_tac (srw_ss()) []
QED
Resume create_size_exit_blueprint[extent_reject]:
  `blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off_e)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`args = target::amount::_`, `expr_body_pre ce cx env _ es`, `body_inv tops ctx ce cx`] >>
     rpt (pop_assum kall_tac) >> metis_tac[create_blueprint_offset_bridge]) >>
  qabbrev_tac `xs = create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))` >>
  `dest_create_args (CreateFromBlueprint F) hs xs = SOME ops` by
    (qpat_assum `dest_create_args (CreateFromBlueprint raw) hs xs = SOME ops` mp_tac >>
     simp_tac (srw_ss()) [dest_create_args_def]) >>
  `eval_operand code (Obs (j+4)) = eval_operand code tchk` by
    simp[Abbr `tchk`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  `?code_n w'.
     blueprint_prefix_size hs (is_int_literal (origin_fold_value off_e)) xs (Obs (j+3)).vs_accounts = SOME code_n /\
     eval_operand sz tf = SOME w' /\ w2n w' <= code_n + LENGTH payload` suffices_by
    (disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >> suspend "source_reject") >>
  irule create_blueprint_pre_dispatch_extent >>
  qexistsl_tac [`aw`,`offop`,`len`,`data`,`cb`,`cf`,`code`,`offset_op`,`ops`,`ow`,
    `pre`,`Obs (j+3)`,`cf`,`sc`,`ca3`,`ca1`,`ca2`,`tchk`,`target_op`,`Obs (j+4)`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)
QED
Resume create_size_exit_blueprint[source_reject]:
  rename [`blueprint_prefix_size hs _ xs (Obs (j+3)).vs_accounts = SOME code_n`,
    `eval_operand sz tf = SOME w'`] >>
  `w' = w` by
    (qpat_assum `eval_operand sz tf = SOME w'` mp_tac >>
     simp_tac (srw_ss()) [Abbr `tf`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
     qpat_assum `eval_operand sz s = SOME w` (fn th => simp_tac (srw_ss()) [th])) >>
  `2 * max_code_size < code_n + LENGTH payload` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`w' = w`, `w2n w' <= code_n + LENGTH payload`,`2 * max_code_size < w2n w`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `blueprint_prefix_size hs (blueprint_literal_offset cx hs args) xs qs.accounts = SOME code_n` by
    (qpat_assum `blueprint_prefix_size hs _ xs (Obs (j+3)).vs_accounts = SOME code_n` mp_tac >>
     map_every (fn q => qpat_assum q (fn th => simp_tac bool_ss [th]))
       [`blueprint_literal_offset cx hs args = _`] >>
     pure_rewrite_tac[blueprint_prefix_size_def] >>
     map_every (fn q => qpat_assum q (fn th => simp_tac (srw_ss()) [th]))
       [`dest_create_args (CreateFromBlueprint F) hs xs = SOME ops`,
        `ops.co_code_src = _`,`ops.co_code_offset = _`,
        `(lookup_account (w2w aw) qs.accounts).code = _`]) >>
  `create_arg_ctor_types (CreateFromBlueprint raw) hs (MAP expr_type args) = SOME (MAP expr_type ctors)` by
    (qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
     Cases_on `hs` >> simp_tac (srw_ss()) [create_arg_ctor_types_def]) >>
  `eval_create_operands cx (CreateFromBlueprint raw) hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) qs =
      (INR (Error (RuntimeError "create initcode too large")),qs)` by
    (irule blueprint_operands_size_reject >>
     qexistsl_tac [`MAP expr_type ctors`,`code_n`,`ops`,`payload`,`xs`] >>
     rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE simp[Abbr `xs`])) >>
     qpat_assum `ops.co_ctor_args = cvs` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  disj1_tac >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ _ qs = (res,srcout)` mp_tac >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ _ qs = (INR _,qs)`
    (fn th => simp_tac (srw_ss()) [th])
QED
Resume create_size_exit_blueprint[raw_payload]:
  qpat_x_assum `if T then _ else _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o REWRITE_RULE[COND_CLAUSES]) >>
  rename [`ctors = [raw_e]`, `C 2 = c0`, `C 3 = c1`, `C 4 = c2`, `C 5 = c3`] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`2`,`2 <= n`),(`3`,`3 <= n`),(`4`,`4 <= n`),(`5`,`5 <= n`)] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i < n ==> (C i).cs_next_id <= _ /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS) o SIMP_RULE (srw_ss()) [])))
    [(`1`,`1 < n`),(`2`,`2 < n`),(`3`,`3 < n`),(`4`,`4 < n`),(`5`,`5 < n`)] >>
  `raw_e = HD ctors` by simp[] >>
  `p.gas_obs = gas_explicit (M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j))))
    (Obs 1).vs_gas_readings ++ tail` by
    (qpat_assum `p.gas_obs = _` (pure_rewrite_tac o single) >>
     qpat_assum `R 1 = M 1 ++ (M 2 ++ _)` (pure_once_rewrite_tac o single) >> REFL_TAC) >>
  `C 6 = cprep /\ Obs 6 = Obs j` by
    (qpat_assum `j = 6` (pure_rewrite_tac o single o SYM) >> simp[]) >>
  map_every (fn q => qpat_assum q (fn th =>
      rule_assum_tac (REWRITE_RULE[th])))
    [`C 1 = ca`,`C 2 = c0`,`C 3 = c1`,`C 4 = c2`,`C 5 = c3`,`C 6 = cprep`,`C j = cprep`,`Obs 6 = Obs j`] >>
  pure_rewrite_tac[COND_CLAUSES] >>
  match_mp_tac (Q.INST [`H` |-> `H`, `raw_e` |-> `raw_e`] (SPEC_ALL blueprint_raw_payload_result)) >>
  qpat_assum `expr_body_pre ce cx env (Call _ (CreateTarget (CreateFromBlueprint T) _ _ _) args _) _`
    (mp_then (Pos (el 3)) mp_tac create_blueprint_raw_keyword_entry) >>
  disch_then (fn entry =>
    qpat_assum `args = target::amount::((if hs then [salt_e] else []) ++ off_e::ctors)`
      (mp_then (Pat `args = _::_::_`) irule entry)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`Obs 5`,`ca`,`c3`,`c0`,`c1`,`c2`,`data`,`later`,
    `Obs 2`,`M 5`,`M 1`,`M 4`,`M 2`,`M 3`,`p`,`Obs 3`,`raw_op`,`Obs 1`,
    `saved`,`sca`,`h0`,`h1`,`h2`,`shctx`,`shadow_func`,`ssaved`,`tn`,`Obs 4`,`v`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_payload]:
  qpat_x_assum `if F then _ else _` (assume_tac o REWRITE_RULE[COND_CLAUSES]) >>
  Cases_on `ctors = []` >- suspend "abi_empty" >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) < dimword (:256)` by
    (`EVERY (\e. expr_body_pre ce cx env e es) ctors` by
       (simp[EVERY_MEM] >> rpt strip_tac >>
        `MEM e args` by
          (qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
           simp[MEM_APPEND]) >>
        irule create_call_operand_body_pre >>
        qpat_assum `expr_body_pre ce cx env (Call _ _ args d) es` (irule_at Any) >>
        drule expr_body_pre_static_facts >> simp[]) >>
     drule dallocaBlueprintArgsTheory.create_ctor_args_abi_bound >> disch_tac >>
     `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type ctors)) < 2 ** 64` by
       (drule expr_body_pre_static_facts >> disch_then (mp_tac o cj 3) >>
        qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
        Cases_on `hs` >> simp[alloc_limits_expr_def,ext_call_alloc_ok_def]) >>
     qpat_x_assum `_ < 2 ** 64` mp_tac >>
     qpat_x_assum `abi_size_bound _ _ <= abi_size_bound _ _` mp_tac >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `ctors <> []` (fn ne =>
    qpat_x_assum `if ctors = [] then _ else _`
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
       REWRITE_RULE[ne,COND_CLAUSES])) >>
  suspend "abi_apply"
QED
Resume create_size_exit_blueprint[abi_empty]:
  qpat_assum `ctors = []` (fn empty =>
    qpat_x_assum `if ctors = [] then _ else _`
      (mp_tac o SIMP_RULE bool_ss [empty,COND_CLAUSES])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disj2_tac >> qexistsl_tac [`[]`,`[]`,`p`,`G`,`tn`] >>
  qpat_assum `j = 1` (pure_rewrite_tac o single) >>
  qpat_assum `cprep = ca` (pure_rewrite_tac o single) >>
  qpat_assum `len = Lit 0w` (pure_rewrite_tac o single) >>
  qpat_assum `ctors = []` (pure_rewrite_tac o single) >>
  simp_tac (srw_ss()) [encode_create_ctor_args_def,eval_operand_def,LET_THM,listTheory.REV_DEF] >>
  conj_tac
  >- (qpat_assum `ctors = []` (fn empty =>
       qpat_assum `later = _` (fn lat =>
         qpat_assum `bind (eval_exprs cx (ctors ++ later)) _ p = _`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [empty,lat]))) ) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_apply]:
  pure_rewrite_tac[COND_CLAUSES] >>
  match_mp_tac (Q.INST [`H` |-> `H`] (SPEC_ALL blueprint_abi_payload_result)) >>
  irule create_blueprint_abi_keyword_entry >> suspend "abi_premises"
QED
Resume create_size_exit_blueprint[abi_premises]:
  `fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions` by
    (qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
     disch_then (fn pre => ACCEPT_TAC (CONJ (cj 12 pre) (cj 8 pre)))) >>
  `LENGTH vals = LENGTH ctors` by fs[create_itinerary_ctor_rows_def] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qexists_tac `target` >> first_assum ACCEPT_TAC))) >>
  conj_tac
  >- (qexistsl_tac [
       `\i. C (1 + 2*i)`, `\i. M (1 + 2*i)`, `G`,
       `\i. C (SUC (1 + 2*i))`, `\i. Obs (SUC (1 + 2*i))`,
       `\i. R (1 + 2*i)`, `\i. EL i hmid`, `\i. EL i hcs`,
       `\i. M (SUC (1 + 2*i))`, `\i. Obs (1 + 2*i)`, `\i. EL i vvs`,
       `a`, `M q`, `s`, `bb`, `buf`, `\i. C (j+i)`,
       `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors))`,
       `\i. M (j+i)`, `data`, `inst`, `M (SUC q)`, `later`, `n-j`, `offop`,
       `\i. Obs (j+i)`, `Obs q`, `salt`, `k`, `shctx`, `shadow_func`,
       `Obs (SUC q)`, `vals`, `sz`, `tn`, `value`, `w`] >>
     BETA_TAC >> simp_tac (srw_ss()) [arithmeticTheory.MULT_CLAUSES] >>
     qpat_assum `C 1 = ca` (pure_rewrite_tac o single) >>
     qpat_assum `q = 1 + 2 * LENGTH ctors` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `C q = k` (pure_rewrite_tac o single) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     suspend "abi_rows_and_tail") >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ty`,`d`,`es`,`ks`] >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_rows_and_tail]:
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >>
      `1 + (2 + 2*i) = 1 + 2*SUC i /\
       SUC (SUC (1 + 2*i)) = 1 + 2*SUC i /\ SUC (1 + 2*i) < n` by decide_tac >>
      map_every (fn idx =>
        qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
          (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [`SUC (1 + 2*i)`,`1 + 2*SUC i`] >>
      map_every (fn idx =>
        qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
          (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [`1 + 2*i`,`SUC (1 + 2*i)`] >>
      map_every (fn (l,r) =>
        qpat_assum `!a b. a <= b /\ b <= n ==> ci_mono (C a) (C b) /\ _`
          (qspecl_then [l,r] mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [(`1`,`1 + 2*i`),(`SUC (1 + 2*i)`,`1 + 2*SUC i`)] >>
      qpat_assum `create_itinerary_ctor_rows ce ctors vals ca k cs mid vvs`
        (strip_assume_tac o REWRITE_RULE[create_itinerary_ctor_rows_def]) >>
      qpat_assum `!k. k < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      qpat_assum `!k. k < LENGTH ctors ==> C (SUC _) = EL k mid /\ _`
        (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      map_every (fn idx => qpat_assum `!k. k <= LENGTH ctors ==> C (1+2*k) = EL k cs`
        (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >> disch_tac)
        [`i`,`SUC i`] >>
      map_every (fn pat => qpat_assum pat (fn th =>
        rule_assum_tac (REWRITE_RULE[th]) >> pure_rewrite_tac[th]))
        [`1 + (2 + 2*i) = 1 + 2*SUC i`,`SUC (SUC (1+2*i)) = 1+2*SUC i`,
         `C 1 = ca`, `C (1+2*i) = EL i cs`, `C (1+2*SUC i) = EL (SUC i) cs`,
         `C (SUC (1+2*i)) = EL i mid`] >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  qpat_assum `C 1 = ca` (fn th => rule_assum_tac (REWRITE_RULE[th])) >>
  simp_tac (srw_ss()) [] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "abi_suffix"
QED
Resume create_size_exit_blueprint[abi_suffix]:
  conj_tac
  >- (strip_tac >>
      map_every (fn (l,r) =>
        qpat_assum `!a b. a <= b /\ b <= n ==> ci_mono (C a) (C b) /\ _`
          (qspecl_then [l,r] mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [(`q`,`SUC q`),(`SUC q`,`j`)] >>
      qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
        (qspec_then `SUC q` mp_tac) >> (impl_tac >- decide_tac) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      map_every (fn idx => qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
        (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS)) [`q`,`SUC q`] >>
      `SUC (SUC q) = j /\ j + (n-j) = n` by decide_tac >>
      qpat_assum `abi_size_bound _ _ < dimword (:256)`
        (assume_tac o SIMP_RULE (srw_ss()) [wordsTheory.dimword_def]) >>
      map_every (fn pat => qpat_assum pat (fn th =>
        rule_assum_tac (REWRITE_RULE[th]) >> pure_rewrite_tac[th]))
        [`SUC (SUC q) = j`,`C q = k`,`C (SUC q) = a`,`C j = cprep`] >>
      qpat_assum `j + (n-j) = n` (pure_rewrite_tac o single) >>
      simp_tac bool_ss [] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qx_gen_tac `i` >> strip_tac >>
          qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
            (qspec_then `j+i` mp_tac) >> (impl_tac >- decide_tac) >>
          `SUC (j+i) = j+SUC i` by decide_tac >>
          qpat_assum `SUC (j+i) = j+SUC i` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_size_exit_blueprint
