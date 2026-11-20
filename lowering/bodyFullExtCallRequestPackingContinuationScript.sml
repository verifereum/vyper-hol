Theory bodyFullExtCallRequestPackingContinuation
Ancestors
  bodyFullExtCallCallStage gasExplicitSites gasOutcomeFullStmts

(* The empty-mark packing path and the call continuation share one endpoint,
   including the physical gas operand and the original ghost frame. *)
Theorem extcall_request_packing_continuation:
  (\addr value gas buf off len.
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
      (comp_bind
        (if stat then
           emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w
             (abi_size_bound cenv.ce_struct_fields
               (if needs_external_call_wrap rt then TupleT [rt] else rt)))]
         else
           emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w
             (abi_size_bound cenv.ce_struct_fields
               (if needs_external_call_wrap rt then TupleT [rt] else rt)))])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
         comp_bind (fresh_label "extcall_cont") (\cont_lbl.
         comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
         (comp_ignore_bind (new_block fail_lbl)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
         comp_bind (compile_alloc_buffer 0) (\fb.
         comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
           (new_block cont_lbl)))))))))))
    addr value gas buf off len sp = (u,sr) /\
  (\addr buf hasdef def dt.
    if rt = NoneT then comp_return (Lit 0w)
    else if hasdef then
      comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
        compile_default_return_path cenv rt dt buf r.buf_operand def addr skip
          (abi_static_size cenv.ce_struct_fields
            (if needs_external_call_wrap rt then TupleT [rt] else rt))
          (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap rt then TupleT [rt] else rt))
          (type_to_abi_dec_info cenv.ce_struct_fields cenv
            (if needs_external_call_wrap rt then TupleT [rt] else rt)))
    else
      comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
        comp_bind (compile_return_value_decode
          (abi_static_size cenv.ce_struct_fields
            (if needs_external_call_wrap rt then TupleT [rt] else rt))
          (abi_size_bound cenv.ce_struct_fields
            (if needs_external_call_wrap rt then TupleT [rt] else rt))) (\hi.
        comp_ignore_bind
          (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi
            (type_to_abi_dec_info cenv.ce_struct_fields cenv
              (if needs_external_call_wrap rt then TupleT [rt] else rt)))
          (comp_return r.buf_operand))))
    addr buf hasdef def dt sr = (result,sb) /\
  vv = (if rt = NoneT then StackValue ann result
        else LocatedValue ann (mk_ptr result LocMemory)) /\
  fn_has_code sp sr func /\ fn_has_code sr sb func /\
  LENGTH vs = LENGTH ats /\ LENGTH kws = LENGTH opts /\ ext_call_opts_ok stat opts /\
  dest_AddressV v = SOME target /\
  value_opt = (if stat then NONE else
    case ext_call_kwarg EKValue opts kws of NONE => SOME 0 | SOME x => dest_NumV x) /\
  (?calldata t Gf tf.
    build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas buf off len (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then
        TupleT [rt] else rt)) target value_opt calldata
      hasdef def dt (ext_call_kwarg EKDefault opts kws) ke t /\
    (IS_SOME (ext_call_kwarg EKDefault opts kws) /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (zg,Gg,tng) [] (OK t,Gf,tf)) /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx ke Gf tf t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
    eval_operand gas t = SOME gw /\
    (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tf p = {}) [addr;value;gas;buf;off;len;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tf.t_mem)) /\
    ((abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt)) <> 0
      ==> ?p. buf = Var p /\ ptr_covers Gf tf p t (abi_size_bound cenv.ce_struct_fields (if
      needs_external_call_wrap rt then TupleT [rt] else rt))) /\
    (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def Gf tf t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))) /\
  (!sp sr u result addr value gas buf off len hasdef def dt v vs kws target value_opt
     calldata ee t G tn.
    (\addr value gas buf off len.
      comp_ignore_bind
        (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
        (comp_bind
          (if stat then
             emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w
               (abi_size_bound cenv.ce_struct_fields
                 (if needs_external_call_wrap rt then TupleT [rt] else rt)))]
           else
             emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w
               (abi_size_bound cenv.ce_struct_fields
                 (if needs_external_call_wrap rt then TupleT [rt] else rt)))])
          (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
           comp_bind (fresh_label "extcall_cont") (\cont_lbl.
           comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
           (comp_ignore_bind (new_block fail_lbl)
           (comp_bind (emit_op RETURNDATASIZE []) (\rds.
           comp_bind (compile_alloc_buffer 0) (\fb.
           comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
           (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
             (new_block cont_lbl)))))))))))
      addr value gas buf off len sp = (u,sr) /\
    (\addr buf hasdef def dt.
      if rt = NoneT then comp_return (Lit 0w)
      else if hasdef then
        comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
          compile_default_return_path cenv rt dt buf r.buf_operand def addr skip
            (abi_static_size cenv.ce_struct_fields
              (if needs_external_call_wrap rt then TupleT [rt] else rt))
            (abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap rt then TupleT [rt] else rt))
            (type_to_abi_dec_info cenv.ce_struct_fields cenv
              (if needs_external_call_wrap rt then TupleT [rt] else rt)))
      else
        comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
          comp_bind (compile_return_value_decode
            (abi_static_size cenv.ce_struct_fields
              (if needs_external_call_wrap rt then TupleT [rt] else rt))
            (abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap rt then TupleT [rt] else rt))) (\hi.
          comp_ignore_bind
            (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi
              (type_to_abi_dec_info cenv.ce_struct_fields cenv
                (if needs_external_call_wrap rt then TupleT [rt] else rt)))
            (comp_return r.buf_operand))))
      addr buf hasdef def dt sr = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    fn_has_code sp sr func /\ fn_has_code sr sb func /\
    LENGTH vs = LENGTH ats /\ LENGTH kws = LENGTH opts /\ ext_call_opts_ok stat opts /\
    dest_AddressV v = SOME target /\
    value_opt = (if stat then NONE else
      case ext_call_kwarg EKValue opts kws of NONE => SOME 0 | SOME x => dest_NumV x) /\
    build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas buf off len (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then
        TupleT [rt] else rt)) target value_opt calldata hasdef def dt
      (ext_call_kwarg EKDefault opts kws) ee t /\
    (IS_SOME (ext_call_kwarg EKDefault opts kws) /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    (!gw g. eval_operand gas t = SOME gw /\
      OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
    ((abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt)) <> 0
      ==> ?p. buf = Var p /\ ptr_covers G tn p t (abi_size_bound cenv.ce_struct_fields (if
      needs_external_call_wrap rt then TupleT [rt] else rt))) /\
    (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def G tn t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers G tn p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
          w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next))) ==>
    gas_outcome_full ((DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)) (cx_tops cx) cx st0
      (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
      (ee,t,G,tn) Q (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full ((DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)) (cx_tops cx) cx st0
    (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
    (ke,zg,Gg,tng) Q (\H res ee gt r. expr_exit res r)
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `?calldata t Gf tf. _`
    (qx_choosel_then [`calldata`,`t`,`Gf`,`tf`]
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `!gw' g. eval_operand gas t = SOME gw' /\
     OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw'` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!g. OPTION_BIND _ _ = SOME g ==> _` drule >>
     disch_then SUBST1_TAC >>
     qpat_assum `eval_operand gas t = SOME gw` (fn th =>
       qpat_assum `eval_operand gas t = SOME gw'` (mp_tac o PURE_REWRITE_RULE [th])) >>
     simp[NoAsms]) >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl [`Gf`,`t`,`tf`] >>
  conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!sp sr u result. _` irule >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
