Theory bodyFullExtCallReturnVoid
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFullCompose exprSimExtCallCase bodyPtrDefs
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  extcallReturnCallerReject extcallReturnDefaultDecode
  extcallReturnDefaultResources extcallReturnDefaultOwnership
  extcallReturnDefaultIntervals extcallReturnDefaultStore
  vyperInterpreter vyperAST list

val _ = Parse.hide "body";

Theorem extcall_return_step_void:
  !DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    ret_type = NoneT /\
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
    local_ptrs_reserved cenv sa /\
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
       (type_memory_bytes cenv default_ty <> 0 ==>
        ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
          eval_operand default_op t = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz /\
       (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
            i NOTIN tn.t_mem)) ==>
    ?res r G' tn'.
      (!tail.
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
           od) (ee with gas_obs := tail) =
          (res, ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
          (t, G, tn) [] (r, G', tn') /\
        ((?t'. r = OK t' /\ ?tv. res = INL tv /\
         vv_post H ctx func cenv cx
           (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
              args dflt) es sa sb s0 (ee with gas_obs := []) tv vv t' /\
         vv_store_bound cx
           (expr_type
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt))
           (lowered_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) (ee with gas_obs := []) tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' t' /\
         ptr_vv_ok cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
                 args dflt)) tv vv (ee with gas_obs := []) G' tn' t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv (ee with gas_obs := []) = (INL val, (ee with gas_obs := [])) /\
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
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ expr_exit res r)))
Proof
  rpt gen_tac >> strip_tac >>
  drule extcallReturnInterfaceTheory.extcall_return_type_bounds >> strip_tac >>
  gvs[extcall_returned_def, extcall_default_ready_def, compileEnvTheory.comp_return_def] >>
  simp[vyperABITheory.evaluate_abi_decode_return_def,
       vyperABITheory.needs_external_call_wrap_def,
       vyperABITheory.evaluate_abi_decode_returndata_def,
       vyperABITheory.vyper_abi_size_bound_def,
       vyperABITheory.vyper_valid_enc_returndata_def,
       vyperABITheory.decode_abi_value_def,
       vyperABITheory.vyper_is_dynamic_def,
       vyperABITheory.vyper_decode_valid_enc_def] >>
  qexistsl_tac [`INL (Value NoneV)`, `OK t`, `G`, `tn`] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.lift_sum_runtime_def] >>
  gen_tac >> disch_tac >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
       contextTheory.vv_location_def, expr_type_def,
       compileEnvTheory.is_word_type_def, ptr_vv_ok_def, ptr_val_ok_def,
       exprSimMemDefsTheory.vv_store_bound_def] >>
  simp[lowered_value_type_def, ptr_buf_ok_def, ptr_mem_ok_def,
       compileEnvTheory.type_memory_bytes_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       venomStateTheory.eval_operand_def,
       valueEncodingDefsTheory.val_in_memory_def] >>
  simp[expr_type_def, exprSimPropsTheory.val_store_size_def,
       loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def,
       op_taint_def, compileEnvTheory.type_memory_bytes_def] >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, loweringPostsTheory.post_value_type_def,
       expr_type_def, loweringPostsTheory.wb_frame_def] >>
  gvs[loweringPostsTheory.wb_frame_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def,
      loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
      venomStateTheory.eval_operand_def, compileEnvTheory.is_word_type_def,
      valueEncodingDefsTheory.val_in_memory_def,
      loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def,
      valueEncodingDefsTheory.val_wf_def] >>
  metis_tac[]
QED

Theorem extcall_return_full_void:
  !DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    ret_type = NoneT /\
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
    local_ptrs_reserved cenv sa /\
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
       (type_memory_bytes cenv default_ty <> 0 ==>
        ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
          eval_operand default_op t = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
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
  rpt gen_tac >> strip_tac >>
  drule_all extcall_return_step_void >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (irule gas_outcome_full_intro >>
      qexistsl_tac [`G'`, `ee`, `[]`, `r`, `res`, `tn'`] >>
      simp[gasSummaryTheory.gas_explicit_def] >>
      rpt strip_tac >> res_tac >> gvs[]) >>
  irule gas_outcome_full_bad_nil >>
  fs[extcall_returned_def] >> gen_tac >> simp[]
QED
