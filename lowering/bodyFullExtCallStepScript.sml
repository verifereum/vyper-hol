(*
 * The extcall full case's call step over the finite-horizon joint judgment.
 *
 * TOP-LEVEL:
 *   extcall_call_full
 *)
Theory bodyFullExtCallStep
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull exprSimExtCallCase bodyPtrDefs
  oracleCallOriginPtr gasOutcomeFullCompose
  bodyFullExtCallPrefix bodyFullExtCallCallGhost bodyFullExtCallCallPath
  bodyFullExtCallExit bodyFullExtCallSuccess bodyFullExtCallBoundary
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  vyperInterpreter vyperAST list

val _ = Parse.hide "body";

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
       (type_memory_bytes cenv default_ty <> 0 ==>
        ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
          eval_operand default_op t = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz) /\
    (!returnData. storage_trace_frame (k returnData)) /\
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
          (type_memory_bytes cenv default_ty <> 0 ==>
           ?x b sz w. default_op = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
             eval_operand default_op t' = SOME w /\ b <= w2n w /\
             w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
       (cap <> 0 ==>
        ?v b sz ro. buf_op = Var v /\ FLOOKUP G' v = SOME (b,sz) /\
          eval_operand buf_op t' = SOME ro /\ b <= w2n ro /\
          w2n ro + cap <= b + sz /\
          (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
              i NOTIN tn'.t_mem)) ==>
       ?res r G'' tn''.
         (!tail. k returnData (ee' with gas_obs := tail) =
           (res, ee' with gas_obs := tail)) /\
         (!H. valid_horizon cx st0 H ee'.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (t', G', tn') [] (r, G'', tn'') /\
           ((?t''. r = OK t'' /\
               Q H res (ee' with gas_obs := []) G'' tn'' t'') \/
            (exit_result r /\ expr_exit res r)))) ==>
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
  rpt gen_tac >> strip_tac >>
  drule extcall_call_layout >> strip_tac >>
  drule_all extcall_suffix_code >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  drule_all extcall_check_code_split >> strip_tac >>
  `fn_has_code s1 s2 func /\ fn_has_code s4 s5 func` by metis_tac[] >>
  Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`
  >- cheat >>
  cheat
QED
