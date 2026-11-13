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
    rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
 cheat
QED
