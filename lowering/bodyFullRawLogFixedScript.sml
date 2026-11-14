(* Fixed bytes32 RawLog continuation, discharging the concrete endpoints. *)
Theory bodyFullRawLogFixed
Ancestors bodyFullRawLogFixedCompose bodyFullRawLogFixedAlloc bodyFullRawLogFixedTail

Theorem raw_log_fixed_data_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx data es sd data_op sm
      shadow_sd shadow_sm sa shadow_sa s0 G0 tn0 st0 vals ops ann es_call dflt
      buf s1 sb ret_ty ty topics call_sa vv call_sb env es0.
    expr_body_pre cenv cx env (Call ann RawLog es_call dflt) es0 /\
    MEM data es_call /\ expr_sim_inv cenv cx env es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type data) data es /\
    lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
    lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)
      shadow_sd = (data_op,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_state sd shadow_sd /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sd func /\ fn_has_code sd sm func /\
    fn_has_code shadow_sa shadow_sd shadow_func /\ fn_has_code shadow_sd shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_admissible
      (bind (bind (eval_expr cx data) (read_result cx))
        (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
                type_check (LENGTH vals <= 4) "raw_log too many topics";
                push_log (encode_raw_event_values cx.txn.target vals bs);
                return NoneV od)) expr_res_ok es /\
    LENGTH vals <= 4 /\ LENGTH ops = LENGTH vals /\ LENGTH ops < dimword (:256) /\
    EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn0 op = {}) ops) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\
    post_value_type cenv data = expr_type data /\
    evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    compile_alloc_buffer 32 sa = (buf,sd) /\
    compile_alloc_buffer 32 shadow_sa = (buf,shadow_sd) /\
    emit_inst MSTORE [buf.buf_operand;data_op] [] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    fn_has_code sm sb func /\
    compile_call compile_expr cenv ret_ty ty RawLog [topics;data] dflt call_sa = (vv,call_sb) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (bind (eval_expr cx data) (read_result cx))
        (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
                type_check (LENGTH vals <= 4) "raw_log too many topics";
                push_log (encode_raw_event_values cx.txn.target vals bs);
                return NoneV od)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post H ctx func cenv cx (Call ann RawLog es_call dflt)
          es sa sb s0 ee v (Lit 0w) t /\
        expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) v (Lit 0w) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) v (Lit 0w) G tn t /\
        (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
          ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  mp_tac (INST_TYPE [``:'c`` |-> ``:'a``]
    raw_log_fixed_data_full_from_endpoints) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_log_fixed_alloc_full)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_log_fixed_tail_full)) >>
  disch_tac >> rpt gen_tac >> first_x_assum MATCH_ACCEPT_TAC
QED
