Theory bodyFullExtCallComposeProof
Ancestors
  bodyFullExtCallStep bodyFullExtCallReturn bodyInvNoDalloca
  bodySimFull bodyFullPreds vyperInterpreter vyperAST list exprSimSource gasOutcomeFull
Libs
  bodyFullExtCallComposeProofLib

val _ = Parse.hide "body";

(* Exact Request proposition as an ordinary, discharged local hypothesis.
   No Request theory or canonical Compose theory is imported. *)
Theorem extcall_compose_validation[local]:
  (!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   is_static skip fname arg_types ret_type opts args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types /\
       eval_exprs cx (TAKE nargs (DROP 1 args)) s'3' =
         (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) args)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 args))) /\
    body_exprs_full_ok cx (TAKE 1 args) ==>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 Q.
      compile_expr cenv ty
        (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
           args dflt) sa = (vv, sb) /\
      compile_expr cenv ty
        (gas_shadow_expr
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) shadow_sa = (vv, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible
        (eval_expr cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) expr_vv_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!sp sr u result_op addr_op value_op gas_op buf_op call_offset call_len
        has_default default_op default_ty target_v rest target value_opt
        calldata ee t G tn.
         comp_ignore_bind
           (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
            else comp_return ())
           (comp_bind
              (if is_static then
                 emit_op STATICCALL
                   [gas_op; addr_op; call_offset; call_len; buf_op;
                    Lit (n2w (abi_size_bound cenv.ce_struct_fields
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))]
               else
                 emit_op CALL
                   [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
                    Lit (n2w (abi_size_bound cenv.ce_struct_fields
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))])
           (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
            comp_bind (fresh_label "extcall_cont") (\cont_lbl.
            comp_ignore_bind
              (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
            (comp_ignore_bind (new_block fail_lbl)
            (comp_bind (emit_op RETURNDATASIZE []) (\rds.
            comp_bind (compile_alloc_buffer 0) (\fail_buf.
            comp_ignore_bind
              (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
            (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
               (new_block cont_lbl)))))))))) sp = (u, sr) /\
         (if ret_type = NoneT then comp_return (Lit 0w)
          else if has_default then
            comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
              (\r. compile_default_return_path cenv ret_type default_ty
                     buf_op r.buf_operand default_op addr_op skip
                     (abi_static_size cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type))
                     (abi_size_bound cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type))
                     (type_to_abi_dec_info cenv.ce_struct_fields cenv
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type)))
          else
            comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
              (\r. comp_bind (compile_return_value_decode
                          (abi_static_size cenv.ce_struct_fields
                             (if needs_external_call_wrap ret_type
                              then TupleT [ret_type] else ret_type))
                          (abi_size_bound cenv.ce_struct_fields
                             (if needs_external_call_wrap ret_type
                              then TupleT [ret_type] else ret_type)))
              (\hi_op. comp_ignore_bind
                 (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
                    buf_op hi_op
                    (type_to_abi_dec_info cenv.ce_struct_fields cenv
                       (if needs_external_call_wrap ret_type
                        then TupleT [ret_type] else ret_type)))
                 (comp_return r.buf_operand)))) sr = (result_op, sb) /\
         vv = (if ret_type = NoneT then StackValue ann result_op
               else LocatedValue ann (mk_ptr result_op LocMemory)) /\
         fn_has_code sp sr func /\ fn_has_code sr sb func /\
         LENGTH rest = LENGTH arg_types + LENGTH opts /\
         ext_call_opts_ok is_static opts /\
         dest_AddressV target_v = SOME target /\
         value_opt =
           (if is_static then NONE
            else case ext_call_kwarg EKValue opts
                        (DROP (LENGTH arg_types) rest) of
                   NONE => SOME 0
                 | SOME v => dest_NumV v) /\
         build_ext_calldata (get_tenv cx) fname arg_types
           (TAKE (LENGTH arg_types) rest) = SOME calldata /\
         extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp
           is_static addr_op value_op gas_op buf_op call_offset call_len
           (abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap ret_type
               then TupleT [ret_type] else ret_type))
           target value_opt calldata has_default default_op default_ty
           (ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)) ee t /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         (!H. valid_horizon cx st0 H ee.storage_trace ==>
            ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
         EVERY (\op. op_taint tn op = {})
           [addr_op; value_op; gas_op; buf_op; call_offset; call_len;
            default_op] /\
         (?ao az. eval_operand call_offset t = SOME ao /\
            eval_operand call_len t = SOME az /\
            (w2n az <> 0 ==> w2n ao + w2n az <= t.vs_alloca_next) /\
            (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
            (w2n az <> 0 ==>
             ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                      b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
         (!dv. ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest) =
            SOME dv /\ ~is_word_type default_ty ==>
            ptr_mem_ok cx default_ty dv default_op G tn t /\
            (type_memory_bytes cenv default_ty <> 0 ==>
             ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
               eval_operand default_op t = SOME w /\ b <= w2n w /\
               w2n w + type_memory_bytes cenv default_ty <= b + sz /\
               w2n w + type_memory_bytes cenv default_ty <= t.vs_alloca_next)) /\
         (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type) <> 0 ==>
          ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
            w2n ro + abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap ret_type
               then TupleT [ret_type] else ret_type) <= b + sz) ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (eval_ext_call cx is_static skip (fname,arg_types,ret_type) opts
              (target_v :: rest)) (ee, t, G, tn)
           Q (\H res ee gt r. expr_exit res r)) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (eval_expr cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt)) (es, s0, G0, tn0)
        Q (\H res ee gt r. expr_exit res r)) ==>
  (!cx ann is_static skip sig opts args dflt
   DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 args)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) args)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 args))) /\
    body_exprs_full_ok cx (TAKE 1 args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip sig opts) args dflt) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann (ExtCall is_static skip sig opts) args dflt) es)
Proof
  disch_tac >> pop_assum bodyFullExtCallComposeProofLib.compose_tac >>
  bodyFullExtCallComposeProofLib.request_finish_tac >>
  bodyFullExtCallComposeProofLib.source_tac >>
  bodyFullExtCallComposeProofLib.call_tac >>
  bodyFullExtCallComposeProofLib.call_finish_tac >>
  bodyFullExtCallComposeProofLib.return_tac >>
  bodyFullExtCallComposeProofLib.return_finish_tac
QED
