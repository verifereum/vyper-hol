Theory bodyIntCallStoreRun
Ancestors
  bodyIntCallStorePost bodyIntCallReturnLayout intCallResult loweringSlice localPtrsProps
  exprSimProps compileEnv exprLoweringProps finite_map list valueEncodingProps
  venomState venomMemDefs loweringStateRelDefs

Theorem owned_memory_tail_state_rel:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce si /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s) /\
  (!a len. a + len <= b \/ b + sz <= a ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!n lb lsz. local_region ce es.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint b sz off (type_memory_size tv)) ==>
  stmt_state_rel ctx func ce cx es u
Proof
  strip_tac >> irule result_state_memory_frame >>
  reverse conj_tac
  >- (qexists_tac `s` >> simp[] >> rpt conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> metis_tac[])
      >- (rpt strip_tac >> first_x_assum irule >>
          fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >> fs[local_ptrs_reserved_def]) >>
  `u.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_data_section`) >> simp[]) >>
  fs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
  rpt strip_tac >>
  qpat_x_assum `!name tv v byte_offset. _` drule_all >> strip_tac >>
  Cases_on `ce.ce_is_ctor` >> gvs[] >>
  `mem_bytes_at byte_offset (type_memory_size tv) u.vs_memory =
   mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by
    (first_x_assum irule >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  simp[] >> irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[immutable_admissible_val_wf] >>
  qexistsl_tac [`type_memory_size tv`,`s.vs_memory`] >> simp[]
QED

Theorem stack_buffer_run_post:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  store_multi_results buf.buf_operand results 0 si = ((),sb) /\
  local_ptrs_reserved ce si /\
  buf.buf_operand = Var p /\ not_fresh_at si p /\
  (!x. MEM (Var x) results ==> not_fresh_at si x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e) /\
  intret_vals_match tv v ws /\ ws <> [] /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 es' sa s0 s /\
  sa.cs_next_var <= si.cs_next_var /\
  eval_operand buf.buf_operand s = SOME w /\
  MAP (\op. eval_operand op s) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    local_region ce es'.scopes s n lb lsz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint (w2n w) (32 * LENGTH results) off
      (type_memory_size itv)) ==>
  ?u. run_inst_seq (emitted_insts si sb) s = OK u /\
    vv_post ctx func ce cx e es0 sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) (base_ptr buf)) u /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at si x` by simp[] >>
  drule store_multi_results_run >>
  disch_then (qspecl_then [`s`,`w2n w`,`ws`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  qexists_tac `u` >> simp[] >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u with <|vs_memory := _; vs_vars := _|> = s`
      (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_allocas`) >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME w` by
    (gvs[eval_operand_def]) >>
  `stmt_state_rel ctx func ce cx es' u` by
    (irule owned_memory_tail_state_rel >>
     qexistsl_tac [`w2n w`,`s`,`si`,`32 * LENGTH results`] >>
     simp[] >> rpt conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM]
     >- metis_tac[arithmeticTheory.ADD_COMM] >>
     gvs[]) >>
  `val_in_memory tv v (w2n w) u.vs_memory` by
    (irule stack_results_val_in_memory >>
     conj_tac
     >- (qexists_tac `get_tenv cx` >> irule stack_return_value_layout >>
         goal_assum (drule_at Any) >> simp[]) >>
     simp[] >> qexists_tac `ws` >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule owned_buffer_result_post >> rpt conj_tac
  >~ [`vv_holds`]
  >- (simp[] >> irule buffer_vv_holds >> goal_assum (drule_at Any) >> simp[]) >>
  TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`aid`,`w2n w`,`s`,`si`,`32 * LENGTH results`,`tv`,`w`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
