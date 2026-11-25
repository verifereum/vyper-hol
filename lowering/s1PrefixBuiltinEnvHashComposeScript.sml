(* Request-prefix companion to bodyFullBuiltinEnvHashCompose. *)
Theory s1PrefixBuiltinEnvHashCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinEnvHashCompose s1PrefixDefs s1PrefixOfVV
  exprBodyPreProps exprSimBuiltins externalEntryShape exprSimSource
  exprLoweringProps fragExec gasShadowCompileStmtHelpers gasShadowState
  exprSimUnopComposeProps vyperContext vyperInterpreter vyperState

Theorem hash_builtin_value_prefix_from_suffixes:
  (!arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i.
   compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\ storage_trace_domain cx st0 mid.storage_trace /\
   local_ptrs_reserved cenv sa /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
   0 <= i /\ i < 2 ** 256 /\
   eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
   op_taint tn arg = {} /\ op_prov G arg = NONE /\
   (!p. arg = Var p ==> not_fresh_at sa p) /\
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
     | INR ex => expr_exit (INR ex) r /\ halt_exit H cx mid (INR ex) r)) /\
   (!arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i.
   emit_op BLOBHASH [arg] sa = (op,sb) /\
   fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
   storage_trace_domain cx st0 mid.storage_trace /\
   0 <= i /\ i < 2 ** 256 /\ local_ptrs_reserved cenv sa /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
   eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
   op_taint tn arg = {} /\ op_prov G arg = NONE /\
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
  builtin_args_length_ok bt (LENGTH args) /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a bt args) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a bt args) es
Proof
  (* A request can only arise in the operand, so no suffix post is needed. *)
  disch_tac >> pop_assum kall_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `?e. args = [e]` by
    (Cases_on `bt = BlockHash` >> gvs[builtin_args_length_ok_def] >>
     Cases_on `args` >> gvs[] >> rename1 `LENGTH rest = 0` >> gvs[]) >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  `body_expr_prefix_ok cx e` by fs[body_exprs_prefix_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`a`, `[e]`, `bt`, `es`] >>
     Cases_on `bt = BlockHash` >> gvs[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `body_expr_prefix_ok _ _`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\
    (if bt = BlockHash then compile_blockhash x else emit_op BLOBHASH [x]) sm = (op,sb)` by
    (Cases_on `bt = BlockHash` >> gvs[] >>
     metis_tac[lower_value_blockhash, lower_value_blobhash]) >>
  `?x' sm'. lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr e) shadow_sa = (x',sm') /\
    (if bt = BlockHash then compile_blockhash x' else emit_op BLOBHASH [x']) sm' =
      (op,shadow_sb)` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     Cases_on `bt = BlockHash` >>
     gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
     metis_tac[lower_value_blockhash, lower_value_blobhash]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa sm'` by metis_tac[compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends sm' shadow_sb` by
    (Cases_on `bt = BlockHash` >> gvs[] >>
     metis_tac[compile_blockhash_labels, emit_op_labels, pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sm' shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_shadow_compiles (lower_value compile_expr cenv ty e)
     (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    irule gas_shadow_stmt_lower_value_env >>
  `x' = x /\ gas_shadow_state sm sm'` by
    (qpat_x_assum `gas_shadow_compiles _ _`
      (qspecl_then [`sa`, `shadow_sa`] mp_tac o REWRITE_RULE[gas_shadow_compiles_def]) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `sm'`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> disch_tac >>
  (* Neither hash changes the source state after its operand has been read. *)
  `!qe. SND (bind (eval_expr cx (Builtin a bt [e])) (read_result cx) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (`bind (eval_expr cx (Builtin a bt [e])) (read_result cx) =
      bind (bind (eval_expr cx e) (read_result cx))
        (\v ee. (unop_result cx a bt [expr_type e] v ee,ee))` by
       (irule eval_expr_unop_action_general >> Cases_on `bt = BlockHash` >>
        gvs[builtin_args_length_ok_def, precompile_builtin_def,
            vyperContextTheory.is_self_codesize_def]) >>
     pop_assum SUBST1_TAC >> gen_tac >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
  drule gas_prefix_full_state_cong >> metis_tac[]
QED
