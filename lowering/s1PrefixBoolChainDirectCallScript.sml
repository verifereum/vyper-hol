(* A checked native-call producer for the Boolean-chain request cut. *)
Theory s1PrefixBoolChainDirectCall
Ancestors
  s1PrefixExtCallCallStage s1PrefixDefs s1PrefixProps
  bodyFullExtCallCallStage bodyFullExtCallPrecheck bodyFullExtCallDispatch
  bodyFullRawCallCallOrigin fragGasOriginPtr fragExec vyperStorageFootprint
  vyperCallOutcome vyperCallOutcomeProps vyperInterpreter vyperState bodyPtrDefs
  contextCodegenRelProps gasSummary gasEvents stateRelProj abiCallerAllocation
  instMemFrontier gasOutcomeFull exprSafeOperand list rich_list words
  ptrDiscipline

(* The Boolean-chain cut uses the static-call branch.  All premises below
   describe the actual emitted call instruction and its source request; no
   prefix predicate for the enclosing test is assumed. *)
Theorem bool_chain_direct_bool_extcall_prefix:
  stat = T /\
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
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  (!gw g. eval_operand gas s = SOME gw /\
          OPTION_BIND source_gas dest_NumV = SOME g ==>
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
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        framed <- frame_call_value cx value_opt;
        eval_ext_call_effects cx target calldata framed source_gas accounts
     od) (ee,s,G,tn)
Proof
  strip_tac >> qpat_x_assum `stat = T` SUBST_ALL_TAC >>
  irule extcall_call_stage_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexistsl_tac [`G0`,`addr`,`buf`,`cap`,`cenv`,`d`,`default_op`,`default_opt`,
    `default_ty`,`es`,`gas`,`has_default`,`len`,`off`,`s0`,`sa`,`sp`,`sr`,
    `T`,`tn0`,`u`,`value`]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[EVERY_DEF, optionTheory.OPTION_BIND_EQUALS_OPTION]
QED
