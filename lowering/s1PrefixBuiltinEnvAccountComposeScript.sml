(* Request-prefix companion to bodyFullBuiltinEnvAccountCompose. *)
Theory s1PrefixBuiltinEnvAccountCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinEnvAccountCompose s1PrefixDefs
  s1PrefixFrame s1PrefixOfVV exprBodyPreProps exprSimUnopComposeProps
  vyperContext vyperTypeSystem vyperStorageTrace vyperState exprSimSource
  gasShadow exprLoweringProps compileEnv fragExec gasShadowCompileStmtHelpers
Libs
  pairLib

Theorem account_prefix_from_suffix:
  (!item bs ee cx v x sa op sb func st0 cenv s ctx G tn DF lo d explicit PG.
      item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed ee.accounts /\
      unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
        (BytesV bs) ee = INL v /\
      (case item of
         Balance => emit_op BALANCE [x]
       | Codesize => emit_op EXTCODESIZE [x]
       | Codehash => emit_op EXTCODEHASH [x]
       | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                          (\c. emit_op GT [c; Lit 0w])
       | Address => comp_return x | Code => comp_return x) sa = (op,sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      storage_trace_domain cx st0 ee.storage_trace /\ local_ptrs_reserved cenv sa /\
      (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
      (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
      eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
      op_taint tn x = {} /\ op_prov G x = NONE /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee s /\
        storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn s) ==>
      ?t G' tn'.
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        local_ptrs_reserved cenv sb /\ alloca_history func t /\
        t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
        t.vs_alloca_next = s.vs_alloca_next /\
        tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
        tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
        (!p. not_fresh_at sa p ==>
          lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
          op_taint tn' (Var p) = op_taint tn (Var p)) /\
        op_taint tn' op = {} /\ op_prov G' op = NONE /\
        (!tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
          eval_operand op t = SOME (typed_val_to_w256 tv v)) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) [] (OK t,G',tn') /\
          stmt_state_rel H ctx func cenv cx ee t /\
          storage_well_formed_on cx ee (FST H) /\
          ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty item e es.
  item <> Code /\
  expr_type e = BaseT AddressT /\
  body_exprs_full_ok cx [e] /\
  body_exprs_prefix_ok cx [e] /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
        (Builtin (account_item_type item) (Acc item) [e]) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
        (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  (* The suffix changes the value but cannot contribute a request. *)
  disch_then kall_tac >> rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `is_self_codesize (Acc item) [e]`
  >- (Cases_on `item` >> gvs[is_self_codesize_def, account_item_type_def] >>
      irule gas_prefix_full_no_outcome >>
      simp[exprSimAccountsTheory.self_codesize_source_bind_all_tails,
           storage_trace_frame_bind, cj 5 evaluate_storage_trace_frame,
           storage_trace_frame_read_result]) >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`account_item_type item`, `[e]`, `Acc item`, `es`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT AddressT) e es` by
    (qpat_x_assum `body_exprs_prefix_ok _ [e]` mp_tac >>
     simp[body_exprs_prefix_ok_def] >>
     disch_then (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  drule_all exprSimAccountsTheory.lower_value_acc >> strip_tac >>
  rename1 `lower_value _ _ _ e sa = (x,s1)` >>
  `~is_self_codesize (Acc item) [gas_shadow_expr e]` by
    fs[is_self_codesize_def, gasShadowCompileHelpersTheory.gas_shadow_self_addr] >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ (Acc _) _)) _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  disch_then (mp_then Any mp_tac exprSimAccountsTheory.lower_value_acc) >>
  simp[] >> strip_tac >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (sx,ss1)` >>
  `cs_extends sa s1 /\ cs_extends shadow_sa ss1` by
    metis_tac[compile_expr_grows] >>
  `cs_extends s1 sb /\ cs_extends ss1 shadow_sb` by
    (qpat_x_assum `_ s1 = (op,sb)` mp_tac >>
     qpat_x_assum `_ ss1 = (op,shadow_sb)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `item` >> simp[comp_return_def, cs_extends_refl, comp_bind_def] >>
     rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code shadow_sa ss1 shadow_func` by
    metis_tac[fn_has_code_split] >>
  `sx = x /\ gas_shadow_state s1 ss1` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = (x,s1)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _`
       (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`ss1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> disch_tac >>
  `!qe. SND (bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e]))
                    (read_result cx) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (`bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e]))
           (read_result cx) =
       bind (bind (eval_expr cx e) (read_result cx))
         (\v ee. (unop_result cx (account_item_type item) (Acc item)
           [expr_type e] v ee,ee))` by
       (irule eval_expr_unop_action_general >> simp[builtin_args_length_ok_def]) >>
     simp[] >> gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
  drule gas_prefix_full_state_cong >> metis_tac[]
QED
