Theory lowerDloadPtrByteStore
Ancestors
  lowerDloadPtrStoreCommon
  lowerDloadPtrMemoryWrite lowerDloadPtrMemoryRead lowerDloadPtrAggregate
  lowerDloadPtrJointNext lowerDloadPtrBlockEntry lowerDloadPtrPhi
  lowerDloadPtrCall lowerDloadPtrStatic lowerDloadPtrRel lowerDloadPtrAffine
  ptrDiscipline venomExecSemantics venomState venomInst venomWf contextCodegenRel
  codegenRel memLocDefs pointerConfinedDefs list pred_set arithmetic words finite_map

Theorem mstore8_write_memory[local]:
  mstore8 off value s = write_memory_with_expansion off [w2w value] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

Theorem mstore8_step_success[local]:
  i.inst_opcode = MSTORE8 ==>
  (step_inst fuel C i s = OK s' <=>
   ?a v x y. i.inst_operands = [a;v] /\
     eval_operand a s = SOME x /\ eval_operand v s = SOME y /\
     s' = mstore8 (w2n x) y s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
    exec_write2_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_mstore8_ghosts[local]:
  i.inst_opcode = MSTORE8 /\ i.inst_operands = [a;v] /\ i.inst_outputs = [] /\
  eval_operand a s = SOME x /\ eval_operand v s = SOME y ==>
  step_prov PG G i (mstore8 (w2n x) y s) = G /\
  step_taint i s (mstore8 (w2n x) y s) tn =
    tn with t_mem := tn.t_mem DIFF {p | w2n x <= p /\ p < w2n x+1}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
    mem_taint_def, step_writes_def, source_memory_write_ranges_def,
    fixed_source_write_range_def, written_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mstore8_def, new_site_bytes_def,
    range_bytes_def, FLOOKUP_DEF, EXTENSION, taint_component_equality,
    DRESTRICT_UNIV] >> metis_tac[]
QED

Theorem dload_boundary_core_memory_successors:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  tn' = (tn with t_mem := tn'.t_mem) /\
  un' = (un with t_mem := un'.t_mem) /\
  s' = (s with vs_memory := s'.vs_memory) /\
  t' = (t with vs_memory := t'.vs_memory) /\
  dload_memory_match lo fs tn' un' s' t' ==>
  dload_boundary_core lo fs V Ws PG PH G H tn' un' s' t' cs ds
Proof
  strip_tac >>
  `dload_memory_match lo fs (tn with t_mem := tn'.t_mem) (un with t_mem := un'.t_mem)
    (s with vs_memory := s'.vs_memory) (t with vs_memory := t'.vs_memory)` by metis_tac[] >>
  `dload_boundary_core lo fs V Ws PG PH G H
    (tn with t_mem := tn'.t_mem) (un with t_mem := un'.t_mem)
    (s with vs_memory := s'.vs_memory) (t with vs_memory := t'.vs_memory) cs ds` by
    (qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_boundary_core_def, dload_vars_match_def, lookup_var_def,
       dload_shared_store_def, dload_equal_environment_def, op_taint_def,
       venom_state_component_equality] >>
     strip_tac >> simp[] >> conj_tac
     >- (qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
         simp[dload_table_stack_def] >> strip_tac >> gen_tac >> strip_tac >>
         first_x_assum (qspec_then `k` mp_tac) >> Cases_on `k` >> simp[]) >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem dload_boundary_core_mstore8:
  i.inst_opcode = MSTORE8 /\ i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  s.vs_labels = t.vs_labels /\
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
  drule mstore8_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `eval_operand a s <> NONE` by
    (drule eval_operand_definedness >> disch_then (qspec_then `a` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  `eval_operand v s <> NONE` by
    (drule eval_operand_definedness >> disch_then (qspec_then `v` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand a s` >- gvs[] >>
  Cases_on `eval_operand v s` >- gvs[] >>
  rename1 `eval_operand a s = SOME xs` >>
  rename1 `eval_operand v s = SOME ys` >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `op_taint tn a = {} /\ op_taint tn v = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `dload_value_word fs (op_taint tn a) (op_prov G a) (op_prov H a) xs x /\
   dload_value_word fs (op_taint tn v) (op_prov G v) (op_prov H v) ys y` by
    (conj_tac >> irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `op_prov G v = NONE` by (irule dload_store_payload >> metis_tac[]) >>
  `ys = y` by
    (Cases_on `op_prov H v` >> gvs[dload_value_word_def, word_agree_except_bits] >>
     simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
  `dload_value_word fs {} (op_prov G a) (op_prov H a) xs x` by metis_tac[] >>
  Q.SUBGOAL_THEN
   `(w2n xs = w2n x /\ w2n xs + 1 <= lo) \/
    (?owner id b c n d. dload_live_site fs owner id b c n /\
      w2n xs = b+d /\ w2n x = c+d /\ d+1 <= n)` assume_tac
  >- (irule dload_store_region >> metis_tac[]) >>
  suspend "mstore8_finish"
QED

Resume dload_boundary_core_mstore8[mstore8_finish]:
  `dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs+1})
    (un with t_mem := un.t_mem DIFF {p | w2n x <= p /\ p < w2n x+1})
    (mstore8 (w2n xs) ys s) (mstore8 (w2n x) y t)` by
    (pure_asm_rewrite_tac[mstore8_write_memory] >>
     irule (SRULE [] (Q.INST [`bs` |-> `[(w2w y):word8]`] dload_memory_match_clean_write_region)) >>
     simp[] >> metis_tac[]) >>
  qexists `mstore8 (w2n xs) ys s` >>
  conj_tac >- (simp[mstore8_step_success] >> metis_tac[]) >>
  conj_tac >- (gvs[lookup_var_def] >> simp[mstore8_def, write_memory_with_expansion_def]) >>
  `step_prov PG G i (mstore8 (w2n xs) ys s) = G /\
   step_prov PH H i (mstore8 (w2n x) y t) = H` by metis_tac[dload_mstore8_ghosts] >>
  `step_taint i s (mstore8 (w2n xs) ys s) tn =
     tn with t_mem := tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs+1}` by
    metis_tac[dload_mstore8_ghosts] >>
  `step_taint i t (mstore8 (w2n x) y t) un =
     un with t_mem := un.t_mem DIFF {p | w2n x <= p /\ p < w2n x+1}` by
    metis_tac[dload_mstore8_ghosts] >>
  simp[] >> conj_tac
  >- (irule dload_boundary_core_memory_successors >> conj_tac >- metis_tac[] >>
      qexistsl [`s`,`t`,`tn`,`un`] >>
      simp[mstore8_def, write_memory_with_expansion_def]) >>
  simp[mstore8_def, write_memory_with_expansion_def]
QED

Finalise dload_boundary_core_mstore8

Theorem dload_mstore8_arity[local]:
  fn_inst_wf f /\ MEM i (fn_insts f) /\ i.inst_opcode = MSTORE8 ==>
  i.inst_outputs = []
Proof
  simp[fn_inst_wf_def, fn_insts_def,
    o1PassContractTheory.fn_insts_blocks_MEM] >>
  strip_tac >> first_x_assum drule >> disch_then drule >>
  simp[inst_wf_def]
QED

Theorem dload_actual_mstore8_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  i.inst_opcode = MSTORE8 /\ fn_inst_wf f /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
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
  `i.inst_outputs = []` by metis_tac[dload_mstore8_arity] >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_mstore8 >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
