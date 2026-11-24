(* The selected CopyOf preparation visit either belongs to one of its
   scalar children, or occurs in the installed administrative suffix. *)
Theory entryCreateCopyVisitWalk
Ancestors
  entryCreateScalarVisitBind entryCreateNativeFirstExit entryCreateReplayBind
  entryCreateAdminSequence createSizeItinerary createSizeDispatch
  createSizeCopyScalarCode createSizeStraightPrefix createSizeCopyReplay
  createSizeOperandPre createSizeCutCode exprBodyPreProps
  exprSimFullBundleProps vyperStorageTrace vyperInterpreter
  emitHelper emitHelperProps compileEnv exprLoweringProps builtinCreate
  context loweringShapeRules s1PrefixDefs vyperTypeSystem vyperAST exprLowering
  entryCreateFocusSpec vyperCreate vyperState venomInst list rich_list pair

Theorem copy_prepare_no_create[local]:
  emit_op EXTCODESIZE [target] c = (code,a1) /\
  emit_void ASSERT [code] a1 = ((),a2) /\
  emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
  emit_op ADD [code;Lit 32w] a4 = (request,a5) /\
  compile_alloc_dynamic request a5 = (alloc_ptr,a6) /\
  emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
  emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
  emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
  emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [code;Lit 11w] a10 = (len,sc) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
        (emitted_insts c sc)
Proof
  strip_tac >> fs[compile_alloc_dynamic_def, emit_op_eq, emit_void_eq] >> gvs[] >>
  SIMP_TAC pure_ss [emitted_insts_def, compile_state_accfupds,
    GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]
QED

(* Apply the shared scalar rule, leaving only its normal-return continuation.
   The first-exit and replay premises use the checked generic introduction rules. *)
fun copy_scalar_step shadow code agreement tn ghost =
  pure_once_rewrite_tac[create_copy_source_cons] >>
  irule scalar_visit_cons >>
  qpat_assum shadow (irule_at Any) >>
  qpat_assum code (irule_at Any) >>
  qpat_assum agreement (irule_at Any) >>
  qexistsl [tn,`lo`,`d`,`PG`,ghost,`DF`] >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `create_operand_at sa s0` >>
       simp[create_operand_at_def] >> NO_TAC) >>
  TRY (rpt gen_tac >> MATCH_ACCEPT_TAC create_operand_cut_bind_replay >> NO_TAC) >>
  TRY (rpt gen_tac >> strip_tac >>
       drule_all create_interior_visit_first_exit >>
       disch_then (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th)
         (fn th => disj2_tac >> strip_assume_tac th >> rpt (goal_assum (drule_at Any)))) >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `expr_sim_full_pre _ _ _ _ _ _ _ ==> _` >>
       strip_tac >> qpat_assum `!e p a m b n op s G tn. _`
         (drule_at (Pat `expr_sim_full_pre _ _ _ _ _ _ _`)) >>
       simp[] >> NO_TAC) >>
  TRY (qpat_assum `!e q. _ ==> expr_body_pre _ _ _ e q` irule >> simp[] >> NO_TAC)

Theorem copy_predispatch_visit_walk:
  let call = Call ann (CreateTarget CreateCopyOf salted rof ks) args opt in
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env call es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty call es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  (!e p a m b n op s G tn.
    MEM e args /\ expr_body_pre ce cx env e p /\
    body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e p
      (st0,a,m,b,n,op,s,G,tn) ==>
    expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (expr_type e) e p /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx fn tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (p,s)) /\
  create_call_itinerary ce CreateCopyOf salted args sa cuts value salt buf len /\
  create_itinerary_code sa cuts sc /\
  create_size_dispatch_tail rof sc sd created buf len value salt result sb /\
  create_interior_visit sa sc (gas_explicit_sites ctx shctx) ctx fn
    (p,depth,fuel) s0 (before,hit,after) ==>
  create_body_cut (gas_explicit_sites ctx shctx) tops cx st0
    (eval_expr cx call) (es,s0) (before,hit)
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!e q. MEM e args /\ expr_sim_inv ce cx env q ==> expr_body_pre ce cx env e q` by
    (rpt strip_tac >> irule create_call_operand_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) es` (irule_at Any) >> simp[]) >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (Call ann (CreateTarget CreateCopyOf salted rof ks) args opt)` by
    (drule expr_body_pre_static_facts >> simp[]) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [create_call_itinerary_def, create_kind_case_def, create_copy_itinerary_def]) >>
  rename1 `lower_value compile_expr ce (expr_type te) te sa = (target,a)` >>
  rename1 `lower_value compile_expr ce (expr_type ve) ve a = (value,b)` >>
  rename1 `create_itinerary_salt _ _ b salt c` >>
  rename1 `emit_op ADD [code; Lit 11w] _ = (len,sc1)` >>
  qabbrev_tac `salt_e = if salted then SOME (HD rest) else NONE` >>
  `salted = IS_SOME salt_e /\
   args = te::ve::(case salt_e of NONE => [] | SOME e => [e])` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     qpat_assum `args = te::ve::rest` (pure_rewrite_tac o single) >>
     Cases_on `salted` >> simp[Abbr `salt_e`,well_typed_expr_def,create_arg_types_ok_def] >>
     Cases_on `rest` >> simp[] >> rename1 `MAP expr_type rs = _ ==> _` >> Cases_on `rs` >> simp[]) >>
  `compile_create_salt compile_expr ce salt_e b = (salt,c)` by
    (qpat_x_assum `create_itinerary_salt _ _ b salt c` mp_tac >>
     qpat_assum `Abbrev (salt_e = _)`
       (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     Cases_on `salt_e` >> simp[create_itinerary_salt_def,compile_create_salt_def,
                             comp_bind_def,comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `sc1 = sc` by
    (drule create_itinerary_code_relations >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `sc1 = sc` SUBST_ALL_TAC >>
  `compile_create_dispatch buf len value salt rof sc = (result,sb)` by
    (Cases_on `salt` >> fs[create_size_dispatch_tail_def,compile_create_dispatch_def,
                           comp_bind_def,mk_inst_def]) >>
  drule_all_then assume_tac copy_prepare_no_create >>
  drule_all create_copy_preparation_code >> disch_then (strip_assume_tac o Q.SPEC `value`) >>
  `compile_create_copy target value salt rof c = (result,sb)` by
    (first_x_assum irule >> simp[]) >>
  drule_all create_copy_scalar_code >> strip_tac >>
  `create_cut_code {} sa a /\ create_cut_code {} a b /\ create_cut_code {} b c` by
    (qpat_assum `create_itinerary_code sa cuts sc` mp_tac >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >> simp[create_itinerary_code_def]) >>
  `create_cut_code {} c sc` by
    (irule (cj 5 createSizePreparationCodeTheory.create_preparation_cut_code) >>
     rpt (goal_assum (drule_at Any))) >>
  `create_cut_code {} b sc` by
    (irule create_cut_code_join >> qexists_tac `c` >> simp[]) >>
  `create_cut_code {} a sc` by
    (irule create_cut_code_join >> qexists_tac `b` >> simp[]) >>
  `fn_has_code sa sc fn` by
    (`cs_extends sa sc /\ cs_extends sc sb` by
       (conj_tac >- metis_tac[create_cut_code_def, create_cut_code_join] >>
        metis_tac[externalEntryShapeTheory.compile_create_dispatch_labels,SND]) >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  `fn_has_code a sc fn /\ fn_has_code b sc fn /\ fn_has_code c sc fn` by
    (fs[create_cut_code_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `eval_expr cx (Call ann (CreateTarget CreateCopyOf salted rof ks) args opt) =
     bind (eval_exprs cx args)
       (eval_create_operands cx CreateCopyOf salted rof (MAP expr_type args)
         (blueprint_literal_offset cx salted args))` by
    (pure_once_rewrite_tac[evaluate_def] >>
     simp[create_operand_order_def,FUN_EQ_THM,bind_def]) >>
  pop_assum (pure_once_rewrite_tac o single) >>
  qabbrev_tac `next = eval_create_operands cx CreateCopyOf salted rof
    (MAP expr_type args) (blueprint_literal_offset cx salted args)` >>
  `!vs. storage_trace_frame (next vs)` by simp[Abbr `next`,storage_trace_frame_create_operands] >>
  `create_operand_cut sa sc (gas_explicit_sites ctx shctx) ctx fn tops cx st0
     (bind (eval_exprs cx args) next) (es,s0)` suffices_by
    (simp[create_operand_cut_def] >> metis_tac[]) >>
  qpat_x_assum `args = te::ve::rest` kall_tac >>
  qpat_assum `args = te::ve::_` (pure_once_rewrite_tac o single) >>
  `expr_sim_full_code (ctx,shctx,fn,shfn) (sa,a,sha,b1) /\
   expr_sim_full_code (ctx,shctx,fn,shfn) (a,b,b1,b2) /\
   expr_sim_full_code (ctx,shctx,fn,shfn) (b,c,b2,b3)` by simp[expr_sim_full_code_def] >>
  copy_scalar_step `lower_value _ _ _ (gas_shadow_expr te) sha = _`
    `expr_sim_full_code _ (sa,a,sha,b1)` `body_const_cells_agree _ _ env es` `tn0` `G0` >>
  map_every qx_gen_tac [`H1`,`marks1`,`v1`,`q1`,`G1`,`tn1`,`s1`] >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env (q1 with gas_obs := [])` by simp[] >>
  copy_scalar_step `lower_value _ _ _ (gas_shadow_expr ve) b1 = _`
    `expr_sim_full_code _ (a,b,b1,b2)` `body_const_cells_agree _ _ env (q1 with gas_obs := [])` `tn1` `G1` >>
  map_every qx_gen_tac [`H2`,`marks2`,`v2`,`q2`,`G2`,`tn2`,`s2`] >> strip_tac >>
  Cases_on `salt_e`
  >- (gvs[compile_create_salt_def,comp_return_def] >>
      simp[cj 49 evaluate_def,bind_return] >> irule create_admin_sequence_cut >> simp[]) >>
  rename1 `compile_create_salt compile_expr ce (SOME se) b = _` >>
  `?op. lower_value compile_expr ce (expr_type se) se b = (op,c) /\
        lower_value compile_expr (gas_shadow_env T ce) (expr_type se) (gas_shadow_expr se) b2 = (op,b3)` by
    (Cases_on `lower_value compile_expr ce (expr_type se) se b` >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type se) (gas_shadow_expr se) b2` >>
     gvs[compile_create_salt_def,comp_bind_def,comp_return_def,optionTheory.OPTION_MAP_DEF]) >>
  simp_tac bool_ss [optionTheory.option_case_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env (q2 with gas_obs := [])` by simp[] >>
  copy_scalar_step `lower_value _ _ _ (gas_shadow_expr se) b2 = _`
    `expr_sim_full_code _ (b,c,b2,b3)` `body_const_cells_agree _ _ env (q2 with gas_obs := [])` `tn2` `G2` >>
  rpt gen_tac >> strip_tac >>
  simp[cj 49 evaluate_def,bind_return] >> irule create_admin_sequence_cut >> simp[]
QED
