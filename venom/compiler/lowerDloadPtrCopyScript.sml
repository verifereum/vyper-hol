Theory lowerDloadPtrCopy
Ancestors
  lowerDloadPtrBytesTransport lowerDloadPtrMemoryStore lowerDloadPtrMemoryRead
  lowerDloadPtrEnvironmentRead vfmState
  lowerDloadPtrMemoryWrite lowerDloadPtrAggregate lowerDloadPtrJointNext
  lowerDloadPtrBlockEntry lowerDloadPtrExpansionTransport lowerDloadPtrPhi
  lowerDloadPtrCall lowerDloadPtrStatic contextCodegenRel lowerDloadPtrRel
  ptrDiscipline venomExecSemantics venomState venomInst venomWf codegenRel
  memLocDefs pointerConfinedDefs list pred_set arithmetic words finite_map

Theorem external_copy_step_success[local]:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] ==>
  (step_inst fuel C i s = OK s' <=>
   ?dst off sz x a z addr address.
     i.inst_operands =
       (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz]) /\
     (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s = SOME address) /\
     eval_operand dst s = SOME x /\ eval_operand off s = SOME a /\
     eval_operand sz s = SOME z /\
     (i.inst_opcode = RETURNDATACOPY ==> w2n a + w2n z <= LENGTH s.vs_returndata) /\
     s' = write_memory_with_expansion (w2n x)
       (TAKE (w2n z) (DROP (w2n a)
          (if i.inst_opcode = CODECOPY then s.vs_code
           else if i.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
           else if i.inst_opcode = EXTCODECOPY then
             (lookup_account (w2w address) s.vs_accounts).code
           else s.vs_returndata) ++
          (if i.inst_opcode = RETURNDATACOPY then [] else REPLICATE (w2n z) 0w))) s)
Proof
  strip_tac >> gvs[MEM] >>
  (eq_tac
   >- (simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
       strip_tac >> gvs[] >> metis_tac[]) >>
   strip_tac >> gvs[] >>
   simp[step_inst_non_invoke, step_inst_base_opcode_eqs])
QED

Theorem dload_external_copy_step_fields:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C i s = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
  s'.vs_call_ctx = s.vs_call_ctx /\
  s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
  s'.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule external_copy_step_success >> simp[] >>
  strip_tac >> gvs[write_memory_with_expansion_def, write_memory_def,
    expand_memory_def]
QED

Theorem external_copy_destination_region:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  i.inst_operands =
    (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz]) /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand off s = SOME a /\
  eval_operand sz s = SOME z /\
  (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s <> NONE) /\
  access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} (op_prov G dst) q x y ==>
  w2n z = 0 \/
  (w2n x = w2n y /\ w2n x + w2n z <= lo) \/
  (?owner id b c n d.
    dload_live_site fs owner id b c n /\
    w2n x = b+d /\ w2n y = c+d /\ d+w2n z <= n)
Proof
  strip_tac >>
  `access_ok lo G fn (i with <| inst_opcode := DLOADBYTES; inst_operands := [dst;off;sz] |>) s` by
    (Cases_on `eval_operand addr s` >>
     gvs[access_ok_def, source_memory_write_ranges_def,
         sized_source_write_range_def, mem_write_ops_def,
         source_memory_read_ranges_def, mem_read_ops_def]) >>
  drule_at (Pat `access_ok _ _ _ _ _`) dloadbytes_destination_region >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem external_copy_scalar_clean:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  i.inst_operands =
    (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz]) /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s ==>
  op_prov G off = NONE /\ op_prov G sz = NONE /\
  op_taint tn dst = {} /\ op_taint tn off = {} /\ op_taint tn sz = {} /\
  (i.inst_opcode = EXTCODECOPY ==> op_prov G addr = NONE /\ op_taint tn addr = {})
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `!v. MEM (Var v) (if i.inst_opcode = EXTCODECOPY then [addr;off;sz] else [off;sz]) ==> v NOTIN fn_pv P fn` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `v` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `dst = Var v` >> gvs[FILTER] >>
     Cases_on `sz = Var v` >> gvs[] >>
     Cases_on `off = Var v` >> gvs[] >>
     Cases_on `addr = Var v` >> gvs[]) >>
  conj_tac
  >- (Cases_on `off` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `sz` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = EXTCODECOPY` >> gvs[] >>
  `op_taint tn dst = {} /\ op_taint tn off = {} /\ op_taint tn sz = {}` by
    metis_tac[MEM] >> simp[] >>
  Cases_on `addr` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem external_copy_ghosts:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  i.inst_operands =
    (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz]) /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand off s = SOME a /\
  eval_operand sz s = SOME z /\
  (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s <> NONE) ==>
  step_prov PG G i (write_memory_with_expansion (w2n x) bs s) = G /\
  step_taint i s (write_memory_with_expansion (w2n x) bs s) tn =
    tn with t_mem := tn.t_mem DIFF {j | w2n x <= j /\ j < w2n x + w2n z}
Proof
  strip_tac >>
  Cases_on `eval_operand addr s` >>
  gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  simp[step_taint_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, range_bytes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, mem_write_ops_def, written_taint_def,
       FLOOKUP_DEF, write_memory_with_expansion_def,
       taint_component_equality] >>
  simp[DRESTRICT_UNIV, EXTENSION] >> metis_tac[]
QED

Theorem dload_clean_write_reconstruct[local]:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  dload_memory_match lo fs (tn with t_mem := A) (un with t_mem := B)
    (write_memory_with_expansion x bs s) (write_memory_with_expansion y bs t) ==>
  dload_boundary_core lo fs V Ws PG PH G H
    (tn with t_mem := A) (un with t_mem := B)
    (write_memory_with_expansion x bs s) (write_memory_with_expansion y bs t) cs ds
Proof
  pure_rewrite_tac[dload_boundary_core_def] >> strip_tac >>
  simp[write_memory_with_expansion_def, dload_vars_match_def, lookup_var_def,
    dload_shared_store_def, dload_equal_environment_def] >>
  rpt conj_tac
  >- (qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
      simp[dload_table_stack_def] >> strip_tac >> gen_tac >> strip_tac >>
      qpat_x_assum `!k. _` (qspec_then `k` mp_tac) >>
      Cases_on `k` >> simp[]) >>
  gvs[dload_vars_match_def, lookup_var_def, op_taint_def, dload_shared_store_def,
    dload_equal_environment_def, write_memory_with_expansion_def,
    venom_state_component_equality] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem dload_boundary_core_external_copy:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  i.inst_outputs = [] /\
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
  drule external_copy_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `!v. MEM (Var v) [dst;off;sz] ==> v IN V /\ v IN U` by
    (Cases_on `i.inst_opcode = EXTCODECOPY` >> gvs[] >> metis_tac[MEM]) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `op_prov G off = NONE /\ op_prov G sz = NONE /\
   op_taint tn dst = {} /\ op_taint tn off = {} /\ op_taint tn sz = {} /\
   (i.inst_opcode = EXTCODECOPY ==> op_prov G addr = NONE /\ op_taint tn addr = {})` by
    (irule external_copy_scalar_clean >> simp[] >> metis_tac[]) >>
  `eval_operand off s = eval_operand off t /\
   eval_operand sz s = eval_operand sz t` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `off` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> strip_tac >>
     drule eval_operand_definedness >>
     disch_then (qspec_then `sz` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> strip_tac >>
     conj_tac >> irule scalar_operand_equal >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]) >>
  `eval_operand dst s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `dst` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand dst s` >- gvs[] >>
  rename1 `eval_operand dst s = SOME xs` >>
  `dload_value_word fs (op_taint tn dst) (op_prov G dst) (op_prov H dst) xs x` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM]) >>
  `dload_value_word fs {} (op_prov G dst) (op_prov H dst) xs x` by metis_tac[] >>
  `s.vs_code = t.vs_code /\ s.vs_call_ctx = t.vs_call_ctx /\
   s.vs_returndata = t.vs_returndata` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `(i.inst_opcode = EXTCODECOPY ==> eval_operand addr s = SOME address)` by
    (strip_tac >>
     `!v. addr = Var v ==> v IN V /\ v IN U` by metis_tac[MEM] >>
     `eval_operand addr s = NONE <=> eval_operand addr t = NONE` by
       (irule eval_operand_definedness >> metis_tac[]) >>
     `eval_operand addr s = eval_operand addr t` by
       (irule scalar_operand_equal >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  `!a. (lookup_account a s.vs_accounts).code =
        (lookup_account a t.vs_accounts).code` by
    (`dload_shared_store tn un s t` by metis_tac[dload_boundary_core_def] >>
     drule dload_shared_store_lookup_account >> strip_tac >> qx_gen_tac `ad` >>
     first_x_assum (qspec_then `ad` mp_tac) >>
     simp[vfmStateTheory.account_state_component_equality]) >>
  suspend "copy_write"
QED

Resume dload_boundary_core_external_copy[copy_write]:
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n x) bs t` >>
  `LENGTH bs = w2n z` by
    (simp[Abbr `bs`] >> Cases_on `i.inst_opcode = RETURNDATACOPY` >>
     simp[LENGTH_TAKE_EQ] >> gvs[]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by
    metis_tac[dload_boundary_core_def] >>
  `w2n z = 0 \/
   (w2n xs = w2n x /\ w2n xs + w2n z <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     w2n xs = b+d /\ w2n x = c+d /\ d+w2n z <= n)` by
    (irule external_copy_destination_region >> conj_tac
     >- (goal_assum (drule_at Any)) >>
     first_assum (irule_at (Pat `access_ok _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `dload_value_word _ _ _ _ _ _`)) >>
     qexistsl [`sz`,`off`,`addr`,`a`] >> simp[] >> metis_tac[]) >>
  `dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs + LENGTH bs})
    (un with t_mem := un.t_mem DIFF {p | w2n x <= p /\ p < w2n x + LENGTH bs})
    (write_memory_with_expansion (w2n xs) bs s)
    (write_memory_with_expansion (w2n x) bs t)` by
    (Cases_on `w2n z = 0`
     >- (irule dload_memory_match_clean_write >> simp[]) >>
     irule dload_memory_match_clean_write_region >> gvs[] >> metis_tac[]) >>
  (qexists `write_memory_with_expansion (w2n xs) bs s` >>
  conj_tac
  >- (simp[external_copy_step_success] >>
      qexistsl [`dst`,`off`,`sz`,`xs`,`a`,`z`,`addr`,`address`] >> simp[Abbr `bs`]) >>
  conj_tac >- (gvs[lookup_var_def] >> simp[write_memory_with_expansion_def]) >>
  `step_prov PG G i (write_memory_with_expansion (w2n xs) bs s) = G /\
   step_taint i s (write_memory_with_expansion (w2n xs) bs s) tn =
     tn with t_mem := tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs + w2n z}` by
    (irule external_copy_ghosts >> simp[] >>
     qexistsl [`a`,`addr`,`dst`,`off`,`sz`] >> simp[]) >>
  `step_prov PH H i (write_memory_with_expansion (w2n x) bs t) = H /\
   step_taint i t (write_memory_with_expansion (w2n x) bs t) un =
     un with t_mem := un.t_mem DIFF {p | w2n x <= p /\ p < w2n x + w2n z}` by
    (irule external_copy_ghosts >> simp[] >>
     qexistsl [`a`,`addr`,`dst`,`off`,`sz`] >> simp[]) >>
  `dload_boundary_core lo fs V Ws PG PH G H
    (tn with t_mem := tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs + w2n z})
    (un with t_mem := un.t_mem DIFF {p | w2n x <= p /\ p < w2n x + w2n z})
    (write_memory_with_expansion (w2n xs) bs s)
    (write_memory_with_expansion (w2n x) bs t) cs ds` by
    (irule dload_clean_write_reconstruct >> metis_tac[]) >>
  gvs[] >> simp[write_memory_with_expansion_def])
QED

Finalise dload_boundary_core_external_copy

Theorem external_copy_arity[local]:
  fn_inst_wf f /\ MEM i (fn_insts f) /\
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] ==>
  i.inst_outputs = []
Proof
  simp[fn_inst_wf_def, fn_insts_def,
    o1PassContractTheory.fn_insts_blocks_MEM] >>
  strip_tac >> first_x_assum drule >> disch_then drule >>
  gvs[inst_wf_def]
QED

Theorem dload_actual_external_copy_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\ fn_inst_wf f /\
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
  `i.inst_outputs = []` by metis_tac[external_copy_arity] >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_external_copy >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
