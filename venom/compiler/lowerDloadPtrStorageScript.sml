Theory lowerDloadPtrStorage
Ancestors
  lowerDloadPtrStoreCommon lowerDloadPtrCopy lowerDloadPtrMemoryRead lowerDloadPtrAggregate
  lowerDloadPtrJointNext lowerDloadPtrBlockEntry lowerDloadPtrPhi
  lowerDloadPtrCall lowerDloadPtrStatic lowerDloadPtrRel
  ptrDiscipline venomExecSemantics venomState venomInst venomWf
  vfmState codegenRel memLocDefs pointerConfinedDefs list pred_set
  arithmetic words finite_map contextCodegenRel

Theorem dload_shared_storage_read:
  dload_shared_store tn un s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  word_agree_except (key_taint tn.t_stor k) (sload k s) (sload k t) /\
  word_agree_except (key_taint tn.t_trans k) (tload k s) (tload k t)
Proof
  simp[dload_shared_store_def, storage_agree_except_def,
    sload_def, tload_def, contract_storage_def, contract_transient_def,
    lookup_account_def, lookup_storage_def] >> metis_tac[]
QED


Theorem dload_storage_agree_update[local]:
  storage_agree_except X a b /\ word_agree_except m x y /\
  m SUBSET {k | k < 32} ==>
  storage_agree_except (key_update X key m)
    (update_storage key x a) (update_storage key y b)
Proof
  simp[storage_agree_except_def, update_storage_def, key_taint_update] >>
  rpt strip_tac >> Cases_on `k = key` >> simp[combinTheory.APPLY_UPDATE_THM] >>
  `m INTER {b | b < 32} = m` by (gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  simp[]
QED

Theorem dload_shared_store_sstore:
  dload_shared_store tn un s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  word_agree_except m x y /\ m SUBSET {k | k < 32} ==>
  dload_shared_store
    (tn with t_stor := key_update tn.t_stor key m)
    (un with t_stor := key_update un.t_stor key m)
    (sstore key x s) (sstore key y t)
Proof
  simp[dload_shared_store_def, sstore_def, lookup_account_def] >>
  strip_tac >> gvs[] >> gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >> simp[] >>
  strip_tac >> simp[] >> conj_tac
  >- gvs[account_state_component_equality] >>
  irule dload_storage_agree_update >> simp[]
QED

Theorem dload_shared_store_tstore:
  dload_shared_store tn un s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  word_agree_except m x y /\ m SUBSET {k | k < 32} ==>
  dload_shared_store
    (tn with t_trans := key_update tn.t_trans key m)
    (un with t_trans := key_update un.t_trans key m)
    (tstore key x s) (tstore key y t)
Proof
  simp[dload_shared_store_def, tstore_def] >>
  strip_tac >> gvs[] >> gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >> simp[] >>
  strip_tac >> simp[] >> irule dload_storage_agree_update >> simp[]
QED

Theorem dload_storage_operand_prov[local]:
  MEM i.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  MEM op i.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `!v. MEM (Var v) i.inst_operands ==> v NOTIN fn_pv P f` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem storage_read_step_success[local]:
  MEM i.inst_opcode [SLOAD;TLOAD] ==>
  (step_inst fuel C i s = OK s' <=>
   ?a out x. i.inst_operands = [a] /\ i.inst_outputs = [out] /\
     eval_operand a s = SOME x /\
     s' = update_var out (if i.inst_opcode = SLOAD then sload x s else tload x s) s)
Proof
  simp[] >> strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def,
    exec_read1_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_storage_read_ghost_updates[local]:
  MEM i.inst_opcode [SLOAD;TLOAD] /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out value s) = set_prov G [out] NONE /\
  step_taint i s (update_var out value s) tn =
    tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s)
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, written_taint_def,
       FLOOKUP_DEF, taint_component_equality, EXTENSION] >>
  simp[SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops"] >> simp[] >>
  namedCases_on `ops` ["", "b ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "c ops2"] >> simp[] >>
  Cases_on `ops2` >> simp[]
QED

Theorem dload_boundary_core_storage_read:
  MEM i.inst_opcode [SLOAD;TLOAD] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule storage_read_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `op_prov G a = NONE` by
    (irule dload_storage_operand_prov >> simp[] >> metis_tac[MEM]) >>
  `op_taint tn a = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand a s = SOME x` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `a` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> strip_tac >>
     `eval_operand a s = eval_operand a t` suffices_by simp[] >>
     irule scalar_operand_equal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `tn.t_stor = un.t_stor /\ tn.t_trans = un.t_trans /\
   word_agree_except (key_taint tn.t_stor x) (sload x s) (sload x t) /\
   word_agree_except (key_taint tn.t_trans x) (tload x s) (tload x t)` by
    (drule dload_boundary_shared_store >> strip_tac >>
     drule_all dload_shared_storage_read >>
     gvs[dload_shared_store_def]) >>
  suspend "storage_read_finish"
QED

Resume dload_boundary_core_storage_read[storage_read_finish]:
  qexists `update_var out (if i.inst_opcode = SLOAD then sload x s else tload x s) s` >>
  conj_tac >- (simp[storage_read_step_success] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `out_taint tn i s = (if i.inst_opcode = SLOAD then key_taint tn.t_stor x else key_taint tn.t_trans x) /\
   out_taint un i t = (if i.inst_opcode = SLOAD then key_taint tn.t_stor x else key_taint tn.t_trans x)` by
    gvs[out_taint_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s))
    (un with t_var := set_var_taint un.t_var [out] (out_taint un i t))
    (s with <|vs_vars := (update_var out (if i.inst_opcode = SLOAD then sload x s else tload x s) s).vs_vars;
              vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out (if i.inst_opcode = SLOAD then sload x t else tload x t) t).vs_vars;
              vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >> simp[dload_value_word_def] >>
     Cases_on `i.inst_opcode = SLOAD` >> gvs[]) >>
  simp[dload_storage_read_ghost_updates, update_var_def] >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Finalise dload_boundary_core_storage_read

Theorem dload_storage_reconstruct[local]:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  tn' = (tn with <|t_stor := tn'.t_stor; t_trans := tn'.t_trans|>) /\
  un' = (un with <|t_stor := un'.t_stor; t_trans := un'.t_trans|>) /\
  s' = (s with <|vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient|>) /\
  t' = (t with <|vs_accounts := t'.vs_accounts; vs_transient := t'.vs_transient|>) /\
  dload_shared_store tn' un' s' t' ==>
  dload_boundary_core lo fs V Ws PG PH G H tn' un' s' t' cs ds
Proof
  strip_tac >>
  `dload_shared_store
    (tn with <|t_stor := tn'.t_stor; t_trans := tn'.t_trans|>)
    (un with <|t_stor := un'.t_stor; t_trans := un'.t_trans|>)
    (s with <|vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient|>)
    (t with <|vs_accounts := t'.vs_accounts; vs_transient := t'.vs_transient|>)` by metis_tac[] >>
  `dload_boundary_core lo fs V Ws PG PH G H
    (tn with <|t_stor := tn'.t_stor; t_trans := tn'.t_trans|>)
    (un with <|t_stor := un'.t_stor; t_trans := un'.t_trans|>)
    (s with <|vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient|>)
    (t with <|vs_accounts := t'.vs_accounts; vs_transient := t'.vs_transient|>) cs ds` by
    (qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_boundary_core_def, dload_vars_match_def, lookup_var_def,
       dload_memory_match_def, dload_equal_environment_def, op_taint_def,
       venom_state_component_equality] >>
     strip_tac >> simp[] >> conj_tac
     >- (qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
         simp[dload_table_stack_def] >> strip_tac >> gen_tac >> strip_tac >>
         first_x_assum (qspec_then `k` mp_tac) >> Cases_on `k` >> simp[]) >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem storage_write_step_success[local]:
  MEM i.inst_opcode [SSTORE;TSTORE] ==>
  (step_inst fuel C i s = OK s' <=>
   ?a v x y. i.inst_operands = [a;v] /\
     eval_operand a s = SOME x /\ eval_operand v s = SOME y /\
     ~s.vs_call_ctx.cc_static /\
     s' = if i.inst_opcode = SSTORE then sstore x y s else tstore x y s)
Proof
  simp[] >> strip_tac >> Cases_on `s.vs_call_ctx.cc_static` >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
      AllCaseEqs()] >>
  rw[EQ_IMP_THM] >> gvs[venomStateTheory.eval_operands_def]
QED

Theorem dload_storage_write_ghosts[local]:
  MEM i.inst_opcode [SSTORE;TSTORE] /\ i.inst_outputs = [] /\
  i.inst_operands = [a;v] /\ eval_operand a s = SOME x /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G i s' = G /\
  step_taint i s s' tn =
    if i.inst_opcode = SSTORE then tn with t_stor := key_update tn.t_stor x (op_taint tn v)
    else tn with t_trans := key_update tn.t_trans x (op_taint tn v)
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def, new_site_bytes_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    written_taint_def, FLOOKUP_DEF, taint_component_equality, EXTENSION,
    set_var_taint_def, DRESTRICT_UNIV, SF CONJ_ss]
QED

Theorem dload_boundary_core_storage_write:
  MEM i.inst_opcode [SSTORE;TSTORE] /\ i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ s.vs_labels = t.vs_labels /\
  (!v. op_taint tn (Var v) SUBSET {k | k < 32}) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb /\
    t'.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule storage_write_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `op_prov G a = NONE /\ op_prov G v = NONE` by
    (conj_tac >> irule dload_storage_operand_prov >> simp[] >> metis_tac[MEM]) >>
  `op_taint tn a = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand a s = SOME x` by
    (drule eval_operand_definedness >> disch_then (qspec_then `a` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> strip_tac >>
     `eval_operand a s = eval_operand a t` suffices_by simp[] >>
     irule scalar_operand_equal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `eval_operand v s <> NONE` by
    (drule eval_operand_definedness >> disch_then (qspec_then `v` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand v s` >- gvs[] >> rename1 `eval_operand v s = SOME ys` >>
  `dload_value_word fs (op_taint tn v) (op_prov G v) (op_prov H v) ys y` by
    (irule dload_matched_operand >> qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM]) >>
  `word_agree_except (op_taint tn v) ys y` by (Cases_on `op_prov H v` >> gvs[dload_value_word_def]) >>
  `op_taint un v = op_taint tn v` by
    (Cases_on `v` >> gvs[op_taint_def, dload_vars_match_def] >> metis_tac[]) >>
  `op_taint tn v SUBSET {k | k < 32}` by
    (Cases_on `v` >> gvs[op_taint_def]) >>
  `s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
   s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  suspend "storage_write_finish"
QED

Resume dload_boundary_core_storage_write[storage_write_finish]:
  qexists `if i.inst_opcode = SSTORE then sstore x ys s else tstore x ys s` >>
  conj_tac >- (simp[storage_write_step_success] >> metis_tac[]) >>
  conj_tac >- (gvs[lookup_var_def] >> simp[sstore_def, tstore_def]) >>
  `dload_shared_store tn un s t` by metis_tac[dload_boundary_shared_store] >>
  `step_prov PG G i (if i.inst_opcode = SSTORE then sstore x ys s else tstore x ys s) = G /\
   step_taint i s (if i.inst_opcode = SSTORE then sstore x ys s else tstore x ys s) tn =
     if i.inst_opcode = SSTORE then tn with t_stor := key_update tn.t_stor x (op_taint tn v)
     else tn with t_trans := key_update tn.t_trans x (op_taint tn v)` by
    (irule dload_storage_write_ghosts >> simp[sstore_def, tstore_def, COND_RAND] >> metis_tac[]) >>
  `step_prov PH H i (if i.inst_opcode = SSTORE then sstore x y t else tstore x y t) = H /\
   step_taint i t (if i.inst_opcode = SSTORE then sstore x y t else tstore x y t) un =
     if i.inst_opcode = SSTORE then un with t_stor := key_update un.t_stor x (op_taint un v)
     else un with t_trans := key_update un.t_trans x (op_taint un v)` by
    (irule dload_storage_write_ghosts >> simp[sstore_def, tstore_def, COND_RAND] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (Cases_on `i.inst_opcode = SSTORE`
      >- (drule_all dload_shared_store_sstore >> strip_tac >>
          simp[] >> irule dload_storage_reconstruct >>
          conj_tac >- simp[] >> qexistsl [`s`,`t`,`tn`,`un`] >> simp[sstore_def, venom_state_component_equality]) >>
      drule_all dload_shared_store_tstore >> strip_tac >> simp[] >>
      irule dload_storage_reconstruct >>
      conj_tac >- simp[] >> qexistsl [`s`,`t`,`tn`,`un`] >> simp[tstore_def, venom_state_component_equality, taint_component_equality]) >>
  simp[sstore_def, tstore_def, COND_RAND]
QED

Finalise dload_boundary_core_storage_write

Theorem storage_write_arity[local]:
  fn_inst_wf f /\ MEM i (fn_insts f) /\
  MEM i.inst_opcode [SSTORE;TSTORE] ==> i.inst_outputs = []
Proof
  simp[fn_inst_wf_def, fn_insts_def,
    o1PassContractTheory.fn_insts_blocks_MEM] >>
  strip_tac >> first_x_assum drule >> disch_then drule >>
  gvs[inst_wf_def]
QED

Theorem dload_actual_storage_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE] /\ fn_inst_wf f /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  (!v. op_taint tn (Var v) SUBSET {k | k < 32}) /\
  (!v. MEM (Var v) i.inst_operands ==> ~retpc_var f v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE))
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  `?s'. step_inst fuel C i s = OK s' /\
     (!v. v IN set (fn_ir_vars f) ==>
       (lookup_var v s' = NONE <=> lookup_var v t1 = NONE)) /\
     dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
       (step_prov PG G i s') (step_prov PH H i t1)
       (step_taint i s s' tn) (step_taint i t t1 un) s' t1 cs ds /\
     s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
     s'.vs_inst_idx = s.vs_inst_idx /\
     t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
     t1.vs_inst_idx = t.vs_inst_idx` by
    (Cases_on `MEM i.inst_opcode [SLOAD;TLOAD]`
     >- (drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_storage_read >>
         simp[] >> disch_then drule_all >>
         disch_then (qspec_then `C` strip_assume_tac) >>
         qexists `s'` >> simp[] >>
         qpat_x_assum `s' = s with vs_vars := _` mp_tac >>
         qpat_x_assum `t1 = t with vs_vars := _` mp_tac >>
         simp[venom_state_component_equality] >> metis_tac[]) >>
     `MEM i.inst_opcode [SSTORE;TSTORE]` by gvs[] >>
     `i.inst_outputs = []` by metis_tac[storage_write_arity] >>
     drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_storage_write >>
     simp[] >> disch_then drule_all >>
     disch_then (qspec_then `C` strip_assume_tac) >> metis_tac[]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
