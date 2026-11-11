(* Nonallocating argument reads at the common held-value endpoint. *)
Theory bodyIntCallHeldRead
Ancestors
  bodyIntCallHeldArgs bodyIntCallHeldFrame freshWrites exprSimMemoryPath exprSimVVFrame gasSummary
  fragGasPath fragGasMode exprSimProps exprSimMemorySource exprLowering
  valueEncodingProps venomState compileEnv loweringPosts

Theorem intcall_held_nonallocating_read:
  unwrap_value ce vv sm = (op,sn) /\
  ((?sty arg. vv = StackValue sty arg) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  vv_holds ce cx ty raw vv es s /\
  fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
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
  Cases_on `vv` >> simp[] >> strip_tac
  >- (gvs[unwrap_value_def, comp_return_def, vv_holds_def] >>
      qexistsl_tac [`v`, `s`] >> simp[] >>
      simp[gas_marked_exec_def] >>
      conj_tac
      >- (conj_tac >- (drule read_result_gas_obs >> simp[]) >>
          simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]) >>
      simp[venom_state_component_equality]) >>
  rename1 `LocatedValue sty p` >>
  `(is_word_type sty <=> is_word_type ty) /\
   ?w v. eval_operand p.ptr_operand s = SOME w /\
     read_result cx raw es = (INL v,es) /\
     (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
       val_in_memory tvt v (w2n w) s.vs_memory /\
       (is_word_type ty ==> mem_word_at (w2n w) s.vs_memory =
          typed_val_to_w256 tvt v))` by
    gvs[vv_holds_def, valueCopyBytesTheory.is_bytestring_word_type] >>
  gvs[unwrap_memory_compile] >> Cases_on `is_word_type sty`
  >- (gvs[] >> qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var))
        (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
      `eval_operand op t = SOME (mload (w2n w) s) /\
       t.vs_current_bb = sn.cs_current_bb /\
       t.vs_inst_idx = LENGTH sn.cs_current_insts /\
       (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
          lookup_var x t = SOME w') /\
       t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory` by
        (qunabbrev_tac `t` >> irule emit_mload_endpoint >>
         simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
      qexistsl_tac [`v`, `t`] >> simp[] >>
      conj_tac
      >- (simp[gas_marked_exec_def] >> conj_tac
          >- (drule read_result_gas_obs >> simp[]) >>
          drule_all emit_mload_marked_path >> simp[Abbr `t`]) >>
      conj_tac
      >- (simp[expr_val_rel_def] >> rpt strip_tac >>
          fs[GSYM mem_word_at_eq_mload]) >>
      gvs[Abbr `t`, update_var_def, venom_state_component_equality]) >>
  gvs[comp_return_def] >> qexistsl_tac [`v`, `s`] >> simp[] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- (drule read_result_gas_obs >> simp[]) >>
      simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]) >>
  simp[expr_val_rel_def, venom_state_component_equality]
QED

Theorem intcall_held_args_read_frame:
  intcall_held_args ce cx a sm es s H /\
  wb_frame ce es sm s t /\ local_ptrs_reserved ce sm /\
  local_ptrs_rel func ce es.scopes s /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  t.vs_labels = s.vs_labels /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var ==>
  intcall_held_args ce cx a sn es t H
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> irule exprSimSubscriptArrayFrameTheory.local_region_wb_frame >>
     metis_tac[]) >>
  simp[intcall_held_args_def, listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> disch_tac >> rename1 `MEM (ty,raw,vv) H` >>
  drule_all intcall_held_args_member >> strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (drule intcall_held_operand_defined >> strip_tac >>
     Cases_on `vv_operand vv` >>
     gvs[eval_operand_def, wb_frame_def] >> metis_tac[]) >>
  conj_tac >- (irule vv_holds_vars_frame >> metis_tac[]) >>
  conj_tac >- (irule vv_at_vars_frame >> metis_tac[]) >>
  conj_tac >- (irule intcall_vv_provenance_frame >> metis_tac[]) >>
  conj_tac >- (Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem intcall_held_args_readonly_tail:
  intcall_held_args ce cx a sm es s H /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var ==>
  intcall_held_args ce cx a sn es t H
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_labels = s.vs_labels /\
   contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[contract_storage_def, contract_transient_def]) >>
  `wb_frame ce es sm s t` by
    (simp[wb_frame_def, locals_kept_mem] >> metis_tac[]) >>
  irule intcall_held_args_read_frame >> metis_tac[]
QED

Theorem intcall_held_read_with_tail:
  unwrap_value ce vv sm = (op,sn) /\
  ((?sty arg. vv = StackValue sty arg) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  vv_holds ce cx ty raw vv es s /\ intcall_held_args ce cx a sm es s H /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
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
  drule_all intcall_held_nonallocating_read >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`v`, `t`] >> simp[] >>
  irule intcall_held_args_readonly_tail >> metis_tac[]
QED
