Theory bodyPtrBytestringBuiltinsCalldataReserved
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice exprSimWordBuiltins exprLoweringProps
  venomState venomExecSemantics emitHelper compileEnv context fragExec
  words list rich_list venomInst emitHelperProps
  stmtSimAppendStorageCompose stateFrame

(* Unlike global runtime freshness, reservation of the named start operand
   is guaranteed by lower_value_word_shape. Unrelated frontier variables
   may already be populated. *)
Theorem calldata_size_reserved_runtime:
  emit_op CALLDATASIZE [] sa = (limit,sb) /\
  (!z. start = Var z ==> not_fresh_at sa z) ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s /\
    eval_operand limit u = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    eval_operand start u = eval_operand start s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `limit = Var (STRING #"%" (toString sa.cs_next_var)) /\
   emitted_insts sa sb = [mk_inst sa.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s` >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE []
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    (irule external_size_step >> simp[]) >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >>
  conj_tac
  >- (irule eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem stmt_state_rel_reserved_vars_update:
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  t = s with vs_vars := t.vs_vars /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >>
  `state_frame t = state_frame s` by
    (qpat_x_assum `t = _` SUBST1_TAC >> simp[state_frame_def]) >>
  irule stmt_state_rel_reserved_frame >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
