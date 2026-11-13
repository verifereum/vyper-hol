Theory bodyFullBuiltinEnvHashCompose
Ancestors
 bodyFullPreds bodySimFull gasOutcomeFullCompose bodyFullGhostFrame
 gasShadowCompileStmtHelpers gasShadowState exprSimSource exprSimHypsDefs
 exprSimWordBuiltins exprSimUnopComposeProps exprSimUnopProps exprUnopSimDefs exprSimWordArgs exprSimProps exprSimOperands
 exprLoweringProps exprLowering exprBopLowering loweringPosts valueEncoding
 bodyPtrDefs ptrDiscipline ptrSafeRun loweringStateRelDefs
 vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperTypeSystem
 builtinProps builtinSimple compileEnv emitHelperProps allocaHistory
 codegenRel contextCodegenRel fragExec list pair finite_map

Theorem hash_builtin_value_from_suffixes:
 (!arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i.
 compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb func /\
 fn_inst_ids_distinct func /\ storage_trace_domain cx st0 mid.storage_trace /\
 local_ptrs_reserved cenv sa /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 0 <= i /\ i < 2 ** 256 /\
 eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
 op_taint tn arg = {} /\ op_prov G arg = NONE /\
 (!p. arg = Var p ==> not_fresh_at sa p) /\ ~ctx_has_dalloca ctx /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid s /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn s) ==>
 ?r G' tn'.
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
   case unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
          [BaseT (UintT 256)] (IntV i) mid of
   | INL v => ?t. r = OK t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       expr_val_rel cx (BaseT (BytesT (Fixed 32))) v op t /\
       op_taint tn' op = {} /\ op_prov G' op = NONE /\
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G' tn' t /\
       alloca_history func t /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       t.vs_alloca_next = s.vs_alloca_next /\
       tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
       tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
       (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
          FLOOKUP G' p = FLOOKUP G p /\
          op_taint tn' (Var p) = op_taint tn (Var p))
   | INR ex => expr_exit (INR ex) r)) /\
 (!arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i.
 emit_op BLOBHASH [arg] sa = (op,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 storage_trace_domain cx st0 mid.storage_trace /\
 0 <= i /\ i < 2 ** 256 /\ local_ptrs_reserved cenv sa /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
 op_taint tn arg = {} /\ op_prov G arg = NONE /\ ~ctx_has_dalloca ctx /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx mid G tn s)
 ==>
 ?t G' tn'.
 unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash [BaseT (UintT 256)] (IntV i) mid =
   INL (evaluate_blob_hash cx.txn (Num i)) /\
 ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
 t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
 alloca_history func t /\ t.vs_memory = s.vs_memory /\
 t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
 tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
   FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
 (!rb. return_buf_frame rb cenv sa s ==> return_buf_frame rb cenv sb t) /\
 expr_val_rel cx (BaseT (BytesT (Fixed 32))) (evaluate_blob_hash cx.txn (Num i)) op t /\
 op_taint tn' op = {} /\ op_prov G' op = NONE /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
 gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
 stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx mid G' tn' t)) ==>
 !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
 (bt = BlockHash \/ bt = BlobHash) /\
 builtin_args_length_ok bt (LENGTH args) /\ body_exprs_full_ok cx args /\
 body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (Builtin a bt args) es ==>
 expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
   cenv cx ty (Builtin a bt args) es
Proof
 strip_tac >> rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
 `?e. args = [e] /\ a = BaseT (BytesT (Fixed 32)) /\
       expr_type e = BaseT (UintT 256)` by
   (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
    Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
 gnvs[body_exprs_full_ok_def] >>
 `expr_body_pre cenv cx env e es` by
   (irule expr_body_pre_builtin_arg >>
    conj_tac >- gvs[expr_body_pre_def] >>
    qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `[e]`, `bt`, `es`] >>
    simp[] >> Cases_on `bt = BlockHash` >> gvs[expr_body_pre_def]) >>
 `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
   metis_tac[body_expr_full_ok_def] >>
 rewrite_tac[expr_sim_full_def] >> rpt gen_tac >>
 disch_then (CONJUNCTS_THEN assume_tac) >>
 RULE_L_ASSUM_TAC CONJUNCTS >>
 `?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\
   (if bt = BlockHash then compile_blockhash x else emit_op BLOBHASH [x]) sm = (op,sb)` by
   (qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) sa = _` mp_tac >>
    Cases_on `bt = BlockHash` >> gvs[] >>
    simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
    simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
         compile_builtin_dispatch_body_def] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def, builtinMiscTheory.compile_blobhash_def]) >>
 `?shadow_sm. lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
    gas_shadow_state sm shadow_sm` by
   (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e`] gas_shadow_stmt_lower_value) >>
    rewrite_tac[gas_shadow_compiles_def] >>
    disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
 `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
   metis_tac[cj 2 compile_expr_grows] >>
 `cs_extends sm sb` by
   (`cs_appends (if bt = BlockHash then compile_blockhash x else emit_op BLOBHASH [x])` by
      (Cases_on `bt = BlockHash` >> simp[builtinMiscTheory.compile_blockhash_def, cs_appends_emit_helpers] >>
       rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
            rw[cs_appends_emit_helpers]) >>
       simp[cs_appends_emit_helpers]) >>
    metis_tac[cs_appends_def]) >>
 `fn_has_code sa sm func /\ fn_has_code sm sb func` by
   metis_tac[fn_has_code_mid, cs_extends_refl] >>
 `(if bt = BlockHash then compile_blockhash x else emit_op BLOBHASH [x]) shadow_sm = (op,shadow_sb)` by
   (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
    Cases_on `bt = BlockHash` >> gvs[] >>
    simp[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
    simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
    simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)), compile_builtin_dispatch_body_def] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def, builtinMiscTheory.compile_blobhash_def]) >>
 `cs_extends shadow_sa shadow_sm` by metis_tac[cj 2 compile_expr_grows] >>
 `cs_extends shadow_sm shadow_sb` by
   (`cs_appends (if bt = BlockHash then compile_blockhash x else emit_op BLOBHASH [x])` by
      (Cases_on `bt = BlockHash` >> simp[builtinMiscTheory.compile_blockhash_def, cs_appends_emit_helpers] >>
       rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >> rw[cs_appends_emit_helpers]) >>
       simp[cs_appends_emit_helpers]) >> metis_tac[cs_appends_def]) >>
 `fn_has_code shadow_sa shadow_sm shadow_func` by
   metis_tac[fn_has_code_mid, cs_extends_refl] >>
 `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
   (irule unop_operand_admissible >>
    qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `bt`] >>
    Cases_on `bt = BlockHash` >> gvs[precompile_builtin_def]) >>
 qpat_x_assum `expr_sim_full _ _ _ _ e es` mp_tac >>
 rewrite_tac[expr_sim_full_def] >>
 disch_then drule >>
 simp[] >>
 disch_then (qspec_then `st0` mp_tac) >>
 disch_then (qspecl_then [`shadow_sa`, `shadow_sm`] mp_tac) >>
 disch_then (qspecl_then [`s0`, `G0`, `tn0`] mp_tac) >>
 simp[] >> disch_tac >>
 qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
 `bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 32))) bt [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. (unop_result cx (BaseT (BytesT (Fixed 32))) bt [expr_type e] v es, es))` by
   (irule eval_expr_unop_action_general >> Cases_on `bt = BlockHash` >> gvs[precompile_builtin_def]) >>
 pop_assum SUBST1_TAC >>
 irule gas_outcome_full_bind_all >>
 conj_tac
 >- (gen_tac >> Cases_on `bt = BlockHash` >> gvs[] >>
     simp[storage_trace_frame_def, unop_result_def]) >>
 conj_tac
 >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`, `t`, `v`] >> gnvs[]) >>
 conj_tac
 >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
 conj_tac
 >- (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
 qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
 conj_tac >- suspend "suffix" >>
 irule gas_outcome_full_post_source >>
 qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
 conj_tac >- simp[] >>
 simp[Abbr `childR`] >> rpt strip_tac >>
 Cases_on `res` >- fs[exprSimDefsTheory.expr_exit_def] >> simp[]
QED

Resume hash_builtin_value_from_suffixes[suffix]:
 rpt gen_tac >> BETA_TAC >> strip_tac >>
 `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
   fs[storage_trace_domain_def] >>
 qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
 (impl_tac >- first_assum ACCEPT_TAC) >>
 qunabbrev_tac `childQ` >> BETA_TAC >> strip_tac >>
 qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
 `expr_result_typed env e (Value v)` by
   (qpat_assum `!tail. _` (qspec_then `[]` assume_tac) >>
    `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
    drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
 `?i. v = IntV i /\ 0 <= i /\ i < 2 ** 256` by
   (gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
    Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >> intLib.COOPER_TAC) >>
 gnvs[] >>
 `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
 `eval_operand x t = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
  op_taint tn1 x = {} /\ op_prov G1 x = NONE` by
   (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    gvs[expr_post_def, expr_val_rel_def, ptr_val_ok_def, is_word_type_def,
        vyperValueTheory.evaluate_type_def]) >>
 `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
   metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
 `!p. x = Var p ==> not_fresh_at sm p` by
   (qpat_assum `lower_value compile_expr cenv ty e sa = (x,sm)`
      (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
    simp[is_word_type_def] >> disch_then drule >> simp[]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
   (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> simp[expr_post_def]) >>
 Cases_on `bt = BlockHash`
 >- (gvs[] >> qpat_assum `!arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i. compile_blockhash _ _ = _ /\ _ ==> _`
       (drule_at Any) >> FAIL_TAC "block apply") >>
 FAIL_TAC "blob apply"
QED

Finalise hash_builtin_value_from_suffixes

