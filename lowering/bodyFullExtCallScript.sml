(*
 * The external-call case of the full body induction: target, positional
 * arguments and keyword arguments over the finite-horizon joint judgment.
 *
 * Admitted until its providers (the S1 extcall seams, bodyMemExtCall,
 * exprSimExtCallCase and the external-call gas shadow) are on the
 * finite-horizon base.
 *
 * TOP-LEVEL:
 *   extcall_expr_full_ok
 *)
Theory bodyFullExtCall
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull exprSimExtCallCase bodyPtrDefs
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  vyperInterpreter vyperAST list

val _ = Parse.hide "body";

(* ===== The three stages over the joint judgment ===== *)

(* (1) Operands and request, at (DF H, lo): the operand judgments run the
   lowering up to the extcodesize check against the source up to the built
   calldata, on one witness; whatever runs the rest of eval_ext_call from a
   ready request (source, memory and pointer facts at t), with the lowered
   call step at sp and the return handling at sr, runs the whole call.
   The pointer side of a ready request: the call's operands are untainted,
   the calldata bytes are untainted and lie inside the site call_offset
   points into, and the return buffer lies inside the site buf_op points
   into. *)
Theorem extcall_request_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   is_static skip fname arg_types ret_type opts args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types /\
       eval_expr_results cx (TAKE nargs (DROP 1 args)) s'3' =
         (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) args)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH arg_types ==>
       body_results_full_ok cx (TAKE nargs (DROP 1 args))) /\
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
         (* the lowered call step, sp to sr *)
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
         (* the lowered return handling, sr to sb *)
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
         (* the source's request *)
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
         (* source and memory at t *)
         extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp
           is_static addr_op value_op gas_op buf_op call_offset call_len
           (abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap ret_type
               then TupleT [ret_type] else ret_type))
           target value_opt calldata has_default default_op default_ty
           (ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)) ee t /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         (* pointer at t *)
         (!H. valid_horizon cx st0 H ee.storage_trace ==>
            ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
         EVERY (\op. op_taint tn op = {})
           [addr_op; value_op; gas_op; buf_op; call_offset; call_len;
            default_op] /\
         (?ao az. eval_operand call_offset t = SOME ao /\
            eval_operand call_len t = SOME az /\
            (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
            (w2n az <> 0 ==>
             ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                      b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
         (!dv. ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest) =
            SOME dv /\ ~is_word_type default_ty ==>
            ptr_mem_ok cx default_ty dv default_op G tn t /\
            ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
              eval_operand default_op t = SOME w /\ b <= w2n w /\
              w2n w + type_memory_bytes cenv default_ty <= b + sz) /\
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
        Q (\H res ee gt r. expr_exit res r)
Proof
  cheat
QED

(* (2) The call step, at (DF H, lo).  From a ready request at sp (source,
   memory and pointer facts at t): the extcodesize check against the
   source's precheck, the CALL or STATICCALL as an oracle step, a failed
   call's returndata copy and REVERT; a successful call reaches sr with
   the returndata in the buffer and the pointer facts kept. *)
Theorem extcall_call_full:
  !DF lo d explicit ctx PG func cenv cx es st0 sa s0 G0 tn0 sp sr u
   is_static skip ret_type addr_op value_op gas_op buf_op call_offset
   call_len cap target value_opt calldata gas has_default default_op
   default_ty default_opt ee t G tn k Q.
    comp_ignore_bind
      (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
       else comp_return ())
      (comp_bind
         (if is_static then
            emit_op STATICCALL
              [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
          else
            emit_op CALL
              [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
               Lit (n2w cap)])
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
    fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
    MEM func ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\op. op_taint tn op = {})
      [addr_op; value_op; gas_op; buf_op; call_offset; call_len; default_op] /\
    (?ao az. eval_operand call_offset t = SOME ao /\
       eval_operand call_len t = SOME az /\
       (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
       (w2n az <> 0 ==>
        ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                 b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
    (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
       ptr_mem_ok cx default_ty dv default_op G tn t /\
       ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
         eval_operand default_op t = SOME w /\ b <= w2n w /\
         w2n w + type_memory_bytes cenv default_ty <= b + sz) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz) /\
    (!returnData ee' t' G' tn'.
       extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op
         buf_op cap target has_default default_op default_ty default_opt
         returnData ee' t' /\
       alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
       (!H. valid_horizon cx st0 H ee'.storage_trace ==>
          ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t') /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
       EVERY (\op. op_taint tn' op = {}) [addr_op; buf_op; default_op] /\
       (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
          ptr_mem_ok cx default_ty dv default_op G' tn' t' /\
          ?x b sz w. default_op = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
            eval_operand default_op t' = SOME w /\ b <= w2n w /\
            w2n w + type_memory_bytes cenv default_ty <= b + sz) /\
       (cap <> 0 ==>
        ?v b sz ro. buf_op = Var v /\ FLOOKUP G' v = SOME (b,sz) /\
          eval_operand buf_op t' = SOME ro /\ b <= w2n ro /\
          w2n ro + cap <= b + sz /\
          (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
              i NOTIN tn'.t_mem)) ==>
       gas_outcome_full (DF, lo, explicit, ctx, func, PG) (cx_tops cx) cx st0
         (k returnData) (ee', t', G', tn') Q
         (\H res ee gt r. expr_exit res r)) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) (cx_tops cx) cx st0
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          value_opt' <- frame_call_value cx value_opt;
          returnData <- eval_ext_call_effects cx target calldata value_opt'
                          gas accounts;
          k returnData
       od) (ee, t, G, tn) Q (\H res ee gt r. expr_exit res r)
Proof
  cheat
QED

(* (3) Return handling, at (DF H, lo).  From sr after a successful call
   (source, memory and pointer facts at t): void, the default on empty
   returndata and the bounded memory decode reach the joint vv post of the
   whole call at sb. *)
Theorem extcall_return_full:
  !DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    cap = abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap ret_type
             then TupleT [ret_type] else ret_type) /\
    (if ret_type = NoneT then comp_return (Lit 0w)
     else if has_default then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. compile_default_return_path cenv ret_type default_ty
                buf_op r.buf_operand default_op addr_op skip
                (abi_static_size cenv.ce_struct_fields
                   (if needs_external_call_wrap ret_type
                    then TupleT [ret_type] else ret_type))
                cap
                (type_to_abi_dec_info cenv.ce_struct_fields cenv
                   (if needs_external_call_wrap ret_type
                    then TupleT [ret_type] else ret_type)))
     else
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
         (\r. comp_bind (compile_return_value_decode
                     (abi_static_size cenv.ce_struct_fields
                        (if needs_external_call_wrap ret_type
                         then TupleT [ret_type] else ret_type)) cap)
         (\hi_op. comp_ignore_bind
            (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
               buf_op hi_op
               (type_to_abi_dec_info cenv.ce_struct_fields cenv
                  (if needs_external_call_wrap ret_type
                   then TupleT [ret_type] else ret_type)))
            (comp_return r.buf_operand)))) sr = (result_op, sb) /\
    vv = (if ret_type = NoneT then StackValue ann result_op
          else LocatedValue ann (mk_ptr result_op LocMemory)) /\
    fn_has_code sr sb func /\ fn_inst_ids_distinct func /\
    MEM func ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
      cap target has_default default_op default_ty default_opt returnData ee t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
    (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
       ptr_mem_ok cx default_ty dv default_op G tn t /\
       ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
         eval_operand default_op t = SOME w /\ b <= w2n w /\
         w2n w + type_memory_bytes cenv default_ty <= b + sz) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz /\
       (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
            i NOTIN tn.t_mem)) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) (cx_tops cx) cx st0
      (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
              return (Value default_v)
           od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od) (ee, t, G, tn)
      (\H res ee' G' tn' t'. ?tv. res = INL tv /\
         vv_post H ctx func cenv cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt) es sa sb s0 ee' tv vv t' /\
         vv_store_bound cx
           (expr_type
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt))
           (lowered_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) ee' tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t' /\
         ptr_vv_ok cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) tv vv ee' G' tn' t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee' = (INL val, ee') /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv
                            (Call ann (ExtCall is_static skip
                               (fname,arg_types,ret_type) opts) args dflt)) =
                         SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn'.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!t'' op. vv = StackValue t'' op /\
            ~is_word_type (post_value_type cenv
               (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                  opts) args dflt)) ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt) op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt) p.ptr_operand G' t') /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
      (\H res ee gt r. expr_exit res r)
Proof
  cheat
QED

Theorem extcall_expr_full_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_full_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_full_ok cx (TAKE 1 es) ==>
    body_expr_full_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED
