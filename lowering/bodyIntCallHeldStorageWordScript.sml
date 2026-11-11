(* Nonallocating storage loads at the held argument endpoint. *)
Theory bodyIntCallHeldStorageWord
Ancestors
  bodyIntCallHeldRead stmtSimDeclPath exprSimUnwrap exprSimAggregateSource
  context venomExecSemantics venomInst finite_map venomState compileEnv
  emitHelper

Theorem held_storage_word_load_path:
  emit_op (if tr then TLOAD else SLOAD) [src] sm = (op,sn) /\
  eval_operand src s = SOME a /\ fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME (if tr then tload a s else sload a s) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w)
Proof
  strip_tac >>
  qabbrev_tac `w = if tr then tload a s else sload a s` >>
  qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var)) w s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qunabbrev_tac `t` >> irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[src]`, `if tr then TLOAD else SLOAD`,
       `[STRING #"%" (toString sm.cs_next_var)]`,
       `sm with cs_next_var := sm.cs_next_var + 1`, `sn`] >>
     Cases_on `tr` >>
     gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def, emit_inst_def, Abbr `w`, step_inst_base_def,
       exec_read1_def, mk_inst_def, is_terminator_def,
       fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]) >>
  qexists_tac `t` >> simp[] >>
  gvs[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def, mk_inst_def, Abbr `t`, Abbr `w`, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality, not_fresh_at_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem held_storage_word_read:
  storage_holds cx tr ty raw w es s /\ is_word_type ty ==>
  ?v. read_result cx raw es = (INL v,es) /\
    !tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
      (if tr then tload w s else sload w s) = typed_val_to_w256 tvt v
Proof
  strip_tac >>
  `?v. read_result cx raw es = (INL v,es)` by
    metis_tac[storage_holds_materialised] >>
  `storage_holds cx tr ty (Value v) w es s` by
    gvs[loweringPostsTheory.storage_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qexists_tac `v` >> simp[] >> rpt strip_tac >>
  drule_all storage_holds_load >> simp[]
QED

Theorem intcall_held_storage_word_read:
  unwrap_value ce (LocatedValue sty p) sm = (op,sn) /\
  is_word_type sty /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t. gas_marked_exec F (ctx,func) (read_result cx raw) (es,s)
          [] (INL v) es (OK t) /\
    expr_val_rel cx ty v op t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?tr w. ty = sty /\
    eval_operand p.ptr_operand s = SOME w /\
    storage_holds cx tr ty raw w es s /\
    emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sn)` by
    (gvs[loweringPostsTheory.vv_holds_def, exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_ptr_load_def] >> metis_tac[]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  gvs[] >> drule_all held_storage_word_read >> strip_tac >>
  drule_all held_storage_word_load_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`v`, `t`] >> fs[] >> conj_tac
  >- (simp[gasSummaryTheory.gas_marked_exec_def] >>
      drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  simp[loweringPostsTheory.expr_val_rel_def] >> gvs[]
QED

Theorem intcall_held_storage_word_read_with_tail:
  unwrap_value ce (LocatedValue sty p) sm = (op,sn) /\
  is_word_type sty /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  intcall_held_args ce cx a sm es s H /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t. gas_marked_exec F (ctx,func) (read_result cx raw) (es,s)
          [] (INL v) es (OK t) /\
    expr_val_rel cx ty v op t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w) /\
    intcall_held_args ce cx a sn es t H
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all intcall_held_storage_word_read >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by
    (gvs[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ptr_load_def,
       emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def, mk_inst_def]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qexistsl_tac [`v`, `t`] >> gvs[] >>
  irule intcall_held_args_readonly_tail >> metis_tac[]
QED
