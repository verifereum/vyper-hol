(* Request-prefix companion to bodyFullBuiltinWordPowCompose. *)
Theory s1PrefixBuiltinWordPowCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinWordPowCompose s1PrefixDefs

Theorem pow_mod256_sim_prefix_from_suffix:
  (!DF lo explicit ctx func PG d cenv cx st0 ee sm sb x y op t G1 tn1 ann ts (va:bytes32) (vb:bytes32).
      compile_pow_mod256 x y sm = (op,sb) /\
      eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
      op_taint tn1 x = {} /\ op_taint tn1 y = {} /\
      fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ local_ptrs_reserved cenv sm /\
      (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
      storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           stmt_state_rel H ctx func cenv cx ee t /\
           ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
      ?t' G2 tn2.
        builtin_result cx ee.accounts ann PowMod256 ts
          [IntV (&w2n va); IntV (&w2n vb)] =
          INL (IntV (&w2n (word_exp va vb))) /\
        eval_operand op t' = SOME (word_exp va vb) /\
        op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
        ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t' /\
        t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
        t'.vs_fmp = t.vs_fmp /\
        t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
        t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
        t'.vs_immutables = t.vs_immutables /\
        t'.vs_gas_readings = t.vs_gas_readings /\
        tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
        tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
        (!z. not_fresh_at sm z ==>
           lookup_var z t' = lookup_var z t /\
           FLOOKUP G2 z = FLOOKUP G1 z /\
           op_taint tn2 (Var z) = op_taint tn1 (Var z)) /\
        ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2 /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
             (t,G1,tn1) [] (OK t',G2,tn2) /\
           stmt_state_rel H ctx func cenv cx ee t' /\
           ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t')) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a args es.
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
         (~is_word_type (expr_type e) ==>
          !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                  SOME tvt ==> type_memory_size tvt = 0) /\
         expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
           cenv cx ty e es /\
         (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
         (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
         expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
           cenv cx ty e es) /\
  (builtin_args_length_ok PowMod256 (LENGTH args) ==> body_exprs_full_ok cx args) /\
  (builtin_args_length_ok PowMod256 (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a PowMod256 args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (Builtin a PowMod256 args) es /\
      expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (Builtin a PowMod256 args) es
Proof
  cheat
QED
