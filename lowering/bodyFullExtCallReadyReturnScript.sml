(* Compose the request-ready external call with its counted return. *)
Theory bodyFullExtCallReadyReturn
Ancestors
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullExtCallCallStage exprSimExtCallCase exprSimHypsDefs loweringPosts
  exprLowering compileEnv context venomState venomInst vyperInterpreter vyperState
  bodyPtrDefs loweringStateRelDefs[qualified,ignore_grammar] fragGasOriginPtr
  gasOutcomeFullCompose vyperABI vyperAST words finite_map pred_set list
  gasOutcomeFullMods[qualified]

Theorem extcall_ready_return_outcome:
  (!DF lo d explicit ctx PG func cenv cx env es ann is_static skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sr result_op vv
   addr_op buf_op cap target has_default default_op default_ty default_opt
   returnData ee t G tn.
    expr_body_pre_mods mods cenv cx env
      (Call ann (ExtCall is_static skip (fname,arg_types,ret_type) opts)
         args dflt) es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
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
    MEM func ctx.ctx_functions /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
      cap target has_default default_op default_ty default_opt returnData ee t /\
    (IS_SOME default_opt /\ ~is_word_type default_ty ==>
      ?w aid tv. eval_operand default_op t = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sr.cs_next_id) /\
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
          w2n w + type_memory_bytes cenv default_ty <= b + sz /\
          w2n w + type_memory_bytes cenv default_ty <= t.vs_alloca_next)) /\
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
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                 opts) args dflt) op G' t') /\
         (!t'' p. vv = LocatedValue t'' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                 opts) args dflt) p.ptr_operand G' t') /\
         vv_own cenv cx
           (post_value_type cenv
              (Call ann (ExtCall is_static skip (fname,arg_types,ret_type)
                 opts) args dflt)) sa sb (ee with gas_obs := []) tv vv t' /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
         (exit_result r /\ create_size_exit_ok ctx res r /\ expr_exit res r)))) ==>
  !DF lo d explicit ctx PG func cenv cx env es ann stat skip fname
   arg_types ret_type opts args dflt st0 sa sb s0 G0 tn0 sp sr u result_op vv
   addr value gas buf off len cap target target_v rest value_opt calldata
   source_gas has_default default_op default_ty default_opt ee s G tn.
  LENGTH rest = LENGTH arg_types + LENGTH opts /\
  ext_call_opts_ok stat opts /\
  dest_AddressV target_v = SOME target /\
  value_opt =
    (if stat then NONE
     else case ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) of
            NONE => SOME 0
          | SOME v => dest_NumV v) /\
  build_ext_calldata (get_tenv cx) fname arg_types
    (TAKE (LENGTH arg_types) rest) = SOME calldata /\
  source_gas = ext_call_kwarg EKGas opts (DROP (LENGTH arg_types) rest) /\
  default_opt = ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest) /\
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
     else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w cap)]
       else emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand;rds] [])
         (new_block cont_lbl)))))))))) sp = (u,sr) /\
  fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op s = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  (!gw g. eval_operand gas s = SOME gw /\ OPTION_BIND source_gas dest_NumV = SOME g ==>
          g = w2n gw) /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off s = SOME ao /\ eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p s (w2n az)) /\
                  w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  cap = abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty
              buf r.buf_operand default_op addr skip
              (abi_static_size cenv.ce_struct_fields
                (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type))
              cap
              (type_to_abi_dec_info cenv.ce_struct_fields cenv
                (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
   else
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. comp_bind (compile_return_value_decode
              (abi_static_size cenv.ce_struct_fields
                (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) cap)
       (\hi_op. comp_ignore_bind
          (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi_op
            (type_to_abi_dec_info cenv.ce_struct_fields cenv
              (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)))
          (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  vv = (if ret_type = NoneT then StackValue ann result_op
        else LocatedValue ann (mk_ptr result_op LocMemory)) /\
  fn_has_code sr sb func /\ local_ptrs_reserved cenv sa /\
  MEM func ctx.ctx_functions /\ (!H. dead_lo_ok H (DF H) lo cenv cx) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (eval_ext_call cx stat skip (fname,arg_types,ret_type) opts (target_v::rest))
    (ee,s,G,tn)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx
        (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)
        es sa sb s0 ee tv vv t /\
      vv_store_bound cx
        (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt))
        (lowered_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx
        (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) /\
          ~is_bytestring_type (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) ==>
        vv_own cenv cx (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv
            (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)) ==>
        ptr_buf_ok cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv
          (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  disch_then (mk_asm "counted") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stat <=> value_opt = NONE` by
    (qhdtm_assum `extcall_request_ready` (mp_tac o REWRITE_RULE [extcall_request_ready_def]) >>
     simp[]) >>
  drule_all_then (pure_rewrite_tac o single) eval_ext_call_request >>
  qpat_x_assum `source_gas = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `default_opt = _` (SUBST_ALL_TAC o SYM) >>
  ho_match_mp_tac extcall_call_stage_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_x "counted"
    (drule_at_then (Pat `extcall_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       (drule_all_then (qspecl_then [`explicit`,`PG`]
          (qx_choose_then `res_f` (qx_choose_then `r_f`
             (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))))))) >>
  qexistsl [`res_f`,`r_f`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac)
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> goal_assum (drule_at (Pat `r_f = OK _`)) >>
      goal_assum (drule_at (Pat `res_f = INL _`)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rewrite_tac [post_value_type_def] >> first_assum ACCEPT_TAC)
      >- first_assum (ACCEPT_TAC o MATCH_MP
        bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
        CONJUNCT1 o REWRITE_RULE [vv_post_def]) >>
      rpt gen_tac >> disch_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `vv = _` SUBST1_TAC >> POP_ASSUM_LIST kall_tac >>
      Cases_on `ret_type = NoneT` >> simp[mk_ptr_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
