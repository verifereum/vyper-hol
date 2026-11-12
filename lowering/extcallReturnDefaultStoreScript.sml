(* Typed default payload execution into a caller-owned return allocation. *)
Theory extcallReturnDefaultStore
Ancestors
  valueCopySource extcallReturnDefaultPath extCallSeamPrecheck bodyIntCallStoreRun exprSimWordArgs
  placeMemoryPrimitiveForward storageCopyGasPath exprSimProps
  loweringPosts context compileEnv loweringStateRelDefs venomState venomInst exprLoweringProps
  emitHelper emitHelperProps list rich_list finite_map arithmetic

Theorem return_default_store_counted:
  compile_store_memory ce src dst rt sty a = ((),b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type (get_tenv cx) rt = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  (rt = sty \/ is_bytestring_type rt /\ is_bytestring_type sty) /\
  value_has_type tv v /\ value_has_type stv v /\
  type_memory_bytes ce rt = type_memory_size tv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce a /\
  wb_frame ce es ee sa s0 s /\ sa.cs_next_var <= a.cs_next_var /\
  (!name lo sz. local_region ce ee.scopes s name lo sz ==>
     regions_disjoint (w2n dw) (type_memory_size tv) lo sz) /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
     regions_disjoint (w2n dw) (type_memory_size tv) lo sz) /\
  (!aid lo sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (lo,sz) ==>
     regions_disjoint (w2n dw) (type_memory_size tv) lo sz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
       name = SOME (itv,iv) ==>
     regions_disjoint (w2n dw) (type_memory_size tv) off (type_memory_size itv)) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx ee u /\ wb_frame ce es ee sa s0 u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\
    eval_operand dst u = SOME dw /\
    u.vs_allocas = s.vs_allocas /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. safe_operand a p ==> eval_operand p u = eval_operand p s) /\
    (!x. not_fresh_at a x ==> lookup_var x u = lookup_var x s) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_run_source_bound >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts a b)` by
    suspend "no_gas" >>
  `stmt_state_rel ctx func ce cx ee t` by suspend "state" >>
  `wb_frame ce es ee sa s0 t` by suspend "frame" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_halted = s.vs_halted /\
   t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH b.cs_current_insts))` by
    (irule straight_line_zero_gas_path >>
     goal_assum (drule_at Any) >> fs[same_blocks_def] >> metis_tac[]) >>
  `wb_frame ce es ee sa s0 (t with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (irule wb_frame_readonly_tail >> qexistsl [`sa`, `t`] >>
     simp[lookup_var_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac >- suspend "operand" >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac >- suspend "safe_operands" >>
  fs[lookup_var_def, same_blocks_def]
QED
Resume return_default_store_counted[no_gas]:
  `compile_store_memory ce src dst rt rt a = ((),b)` by
    (Cases_on `rt = sty` >> gvs[] >>
     fs[compile_store_memory_def]) >>
  drule compile_store_memory_same_type_no_gas >> simp[]
QED
Resume return_default_store_counted[state]:
  irule owned_memory_tail_state_rel >>
  goal_assum (drule_at Any) >> simp[] >>
  `MIN (type_memory_size stv) (type_memory_size tv) <= type_memory_size tv`
    by simp[] >>
  qexists_tac `a` >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED
Resume return_default_store_counted[frame]:
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `MIN (type_memory_size stv) (type_memory_size tv) <= type_memory_size tv` by simp[] >>
  qpat_x_assum `wb_frame ce es ee sa s0 s` mp_tac >>
  rewrite_tac[wb_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at a x` by
        (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `regions_disjoint (w2n dw) (type_memory_size tv) off sz` by metis_tac[] >>
      `off + sz <= w2n dw \/ w2n dw + MIN (type_memory_size stv) (type_memory_size tv) <= off`
        by (qpat_x_assum `regions_disjoint _ _ off sz` mp_tac >>
            pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists `s` >> simp[] >>
  rpt strip_tac >>
  `regions_disjoint (w2n dw) (type_memory_size tv) b' sz` by metis_tac[] >>
  `b' + sz <= w2n dw \/ w2n dw + MIN (type_memory_size stv) (type_memory_size tv) <= b'`
    by (qpat_x_assum `regions_disjoint _ _ b' sz` mp_tac >>
        pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED
Resume return_default_store_counted[operand]:
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  Cases_on `dst` >> gvs[eval_operand_def]
QED
Resume return_default_store_counted[safe_operands]:
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  Cases >> simp[exprSafeOperandTheory.safe_operand_def, eval_operand_def]
QED
Finalise return_default_store_counted

(* Optional check, at the store endpoint; no memory or allocation changes. *)
Theorem return_default_optional_check_counted:
  (if skip then comp_return () else compile_extcodesize_check addr) a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ w2w aw = target /\
  stmt_state_rel ctx func ce cx ee s /\
  accounts_runtime_well_typed ee.accounts /\ local_ptrs_reserved ce a /\
  wb_frame ce es ee sa s0 s /\ sa.cs_next_var <= a.cs_next_var ==>
  ?u. if skip \/ ext_call_has_code target ee.accounts then
    gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx ee u /\ wb_frame ce es ee sa s0 u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    (!p. safe_operand a p ==> eval_operand p u = eval_operand p s) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts
  else gas_marked_path F ctx func s 0 (Abort Revert_abort u)
Proof
  strip_tac >> Cases_on `skip`
  >- (gvs[comp_return_def] >> qexists_tac `s` >>
      simp[fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  gvs[] >>
  drule_all return_default_check_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all extcall_precheck_code_word >>
  disch_then (qspec_then `w2w aw` assume_tac) >>
  Cases_on `ext_call_has_code (w2w aw) ee.accounts`
  >- (gvs[] >>
      qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK checked)` >>
      qexists_tac `checked` >> simp[] >>
      unabbrev_all_tac >> suspend "check_frame") >>
  gvs[] >> metis_tac[]
QED
Resume return_default_optional_check_counted[check_frame]:
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `a` >> simp[]) >>
  conj_tac
  >- (irule extcall_optional_precheck_wb >>
      metis_tac[]) >>
  drule extcall_codesize_check_shape >> strip_tac >>
  simp[update_var_def] >>
  reverse conj_tac >- fs[same_blocks_def] >>
  Cases >> simp[exprSafeOperandTheory.safe_operand_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]
QED
Finalise return_default_optional_check_counted
