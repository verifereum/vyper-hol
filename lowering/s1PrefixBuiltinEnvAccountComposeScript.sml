(* Request-prefix companion to bodyFullBuiltinEnvAccountCompose. *)
Theory s1PrefixBuiltinEnvAccountCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinEnvAccountCompose s1PrefixDefs

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
  cheat
QED
