Theory lowerDloadPtrMCopy
Ancestors
  lowerDloadPtrMemoryRead lowerDloadPtrMemoryWrite lowerDloadPtrRel
  lowerDloadPtrAffine lowerDloadPtrRegion lowerDloadPtrByteStore
  lowerDloadPtrJointNext lowerDloadPtrBlockEntry lowerDloadPtrAggregate
  lowerDloadPtrCall lowerDloadPtrStatic lowerDloadPtrPhi venomWf
  ptrDiscipline venomExecSemantics venomState venomInst pointerConfinedDefs
  memLocDefs finite_map
  contextCodegenRel codegenRel vfmTypes list rich_list pred_set arithmetic words

Theorem dload_snapshot_byte[local]:
  k < len ==>
  EL k (TAKE len (DROP src mem ++ REPLICATE len 0w)) =
    read_byte (src+k) mem
Proof
  strip_tac >>
  simp[EL_TAKE, EL_APPEND, EL_DROP, EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem dload_memory_match_mcopy_region:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\
  ((src = tsrc /\ src + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     src = b+d /\ tsrc = c+d /\ d+len <= n)) /\
  ((dst = tdst /\ dst + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     dst = b+d /\ tdst = c+d /\ d+len <= n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := (tn.t_mem DIFF {p | dst <= p /\ p < dst+len})
      UNION {dst+k | k < len /\ src+k IN tn.t_mem})
    (un with t_mem := (un.t_mem DIFF {p | tdst <= p /\ p < tdst+len})
      UNION {tdst+k | k < len /\ tsrc+k IN un.t_mem})
    (mcopy dst src len s) (mcopy tdst tsrc len t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < len ==>
    (src+k IN tn.t_mem <=> tsrc+k IN un.t_mem) /\
    (src+k NOTIN tn.t_mem ==>
      read_byte (src+k) s.vs_memory = read_byte (tsrc+k) t.vs_memory)` by
    (match_mp_tac dload_memory_read_bytes >> metis_tac[]) >>
  `{k | k < len /\ src+k IN tn.t_mem} =
   {k | k < len /\ tsrc+k IN un.t_mem}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  `{tdst+k | k < len /\ tsrc+k IN un.t_mem} =
   {tdst+k | k < len /\ src+k IN tn.t_mem}` by
    (simp[EXTENSION] >> metis_tac[ADD_COMM]) >>
  mp_tac (Q.INST
    [`bs` |-> `TAKE len (DROP src s.vs_memory ++ REPLICATE len 0w)`,
     `bt` |-> `TAKE len (DROP tsrc t.vs_memory ++ REPLICATE len 0w)`,
     `M` |-> `{k | k < len /\ src+k IN tn.t_mem}`,
     `a` |-> `dst`, `z` |-> `tdst`]
    (SPEC_ALL dload_memory_match_masked_write_region)) >>
  simp[LENGTH_TAKE_EQ, SUBSET_DEF, dload_snapshot_byte, mcopy_def] >>
  metis_tac[ADD_COMM]
QED

Theorem mcopy_step_success[local]:
  i.inst_opcode = MCOPY ==>
  (step_inst fuel C i s = OK s' <=>
   ?dst src sz x y z. i.inst_operands = [dst;src;sz] /\
     eval_operand dst s = SOME x /\ eval_operand src s = SOME y /\
     eval_operand sz s = SOME z /\ s' = mcopy (w2n x) (w2n y) (w2n z) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
    AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_mcopy_size_clean:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s ==>
  op_prov G sz = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\ op_taint tn sz = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `!u. sz = Var u ==> u NOTIN fn_pv P f` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> rpt strip_tac >>
     qpat_x_assum `!v. _` (qspec_then `u` mp_tac) >>
     gvs[] >> Cases_on `dst = Var u` >> Cases_on `src = Var u` >>
     gvs[] >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `sz` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dload_mcopy_contained:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME dx /\ eval_operand src s = SOME sx /\
  eval_operand sz s = SOME z /\ w2n z <> 0 /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  ((a = dst /\ x = dx) \/ (a = src /\ x = sx)) ==>
  (lo < w2n x + w2n z \/ op_prov G a <> NONE) ==>
  ?b n. op_prov G a = SOME (b,n) /\
    b <= w2n x /\ w2n x + w2n z <= b+n
Proof
  strip_tac >>
  gvs[access_ok_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def, sized_source_write_range_def,
      mem_write_ops_def, mem_read_ops_def] >>
  strip_tac >>
  qpat_x_assum `(_ ==> _) ==> _` drule >>
  strip_tac >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem dload_memory_match_mcopy_zero[local]:
  dload_memory_match lo fs tn un s t ==>
  dload_memory_match lo fs tn un (mcopy dst src 0 s) (mcopy tdst tsrc 0 t)
Proof
  simp[mcopy_def] >> strip_tac >>
  `!a p:num. (a <= p /\ p < a) = F` by decide_tac >>
  mp_tac (Q.INST [`bs` |-> `[]`, `a` |-> `dst`, `z` |-> `tdst`]
    (SPEC_ALL dload_memory_match_clean_write)) >>
  simp[taint_component_equality]
QED

Theorem dload_mcopy_memory[local]:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME dx /\ eval_operand src s = SOME sx /\
  eval_operand sz s = SOME z /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  dload_live_layout lo sf tf fs /\ dload_memory_match lo fs tn un s t /\
  dload_value_word fs {} (op_prov G dst) pd dx tx /\
  dload_value_word fs {} (op_prov G src) ps sx ty ==>
  dload_memory_match lo fs
    (tn with t_mem := (tn.t_mem DIFF {p | w2n dx <= p /\ p < w2n dx+w2n z})
      UNION {w2n dx+k | k < w2n z /\ w2n sx+k IN tn.t_mem})
    (un with t_mem := (un.t_mem DIFF {p | w2n tx <= p /\ p < w2n tx+w2n z})
      UNION {w2n tx+k | k < w2n z /\ w2n ty+k IN un.t_mem})
    (mcopy (w2n dx) (w2n sx) (w2n z) s)
    (mcopy (w2n tx) (w2n ty) (w2n z) t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `w2n z = 0`
  >- (simp[] >> irule dload_memory_match_mcopy_zero >> simp[]) >>
  `(lo < w2n dx + w2n z \/ op_prov G dst <> NONE) ==>
    ?b n. op_prov G dst = SOME (b,n) /\ b <= w2n dx /\
      w2n dx + w2n z <= b+n` by
    (metis_tac[dload_mcopy_contained]) >>
  `(lo < w2n sx + w2n z \/ op_prov G src <> NONE) ==>
    ?b n. op_prov G src = SOME (b,n) /\ b <= w2n sx /\
      w2n sx + w2n z <= b+n` by
    (metis_tac[dload_mcopy_contained]) >>
  irule dload_memory_match_mcopy_region >>
  conj_tac
  >- (qpat_x_assum `dload_value_word _ _ _ ps _ _` kall_tac >>
      qpat_x_assum `lo < w2n sx + _ \/ _ ==> _` kall_tac >>
      drule_all dload_value_contained_region >> simp[]) >>
  qpat_x_assum `dload_value_word _ _ _ pd _ _` kall_tac >>
  qpat_x_assum `lo < w2n dx + _ \/ _ ==> _` kall_tac >>
  drule_all dload_value_contained_region >> simp[] >> metis_tac[]
QED

Theorem dload_mcopy_ghosts[local]:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand src s = SOME y /\
  eval_operand sz s = SOME z ==>
  step_prov PG G i (mcopy (w2n x) (w2n y) (w2n z) s) = G /\
  step_taint i s (mcopy (w2n x) (w2n y) (w2n z) s) tn =
    tn with t_mem := (tn.t_mem DIFF {p | w2n x <= p /\ p < w2n x+w2n z})
      UNION {w2n x+k | k < w2n z /\ w2n y+k IN tn.t_mem}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
    mem_taint_def, step_writes_def, source_memory_write_ranges_def,
    sized_source_write_range_def, written_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mcopy_def, write_memory_with_expansion_def,
    new_site_bytes_def, range_bytes_def, FLOOKUP_DEF, EXTENSION,
    taint_component_equality, DRESTRICT_UNIV] >> metis_tac[]
QED

Theorem dload_boundary_core_mcopy:
  i.inst_opcode = MCOPY /\ i.inst_outputs = [] /\
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
  drule mcopy_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `!a. MEM a i.inst_operands ==> (eval_operand a s = NONE <=> eval_operand a t = NONE)` by
    (drule eval_operand_definedness >> simp[] >> metis_tac[]) >>
  `eval_operand dst s <> NONE /\ eval_operand src s <> NONE /\
   eval_operand sz s <> NONE` by (gvs[] >> metis_tac[]) >>
  Cases_on `eval_operand dst s` >- gvs[] >>
  Cases_on `eval_operand src s` >- gvs[] >>
  Cases_on `eval_operand sz s` >- gvs[] >>
  rename1 `eval_operand dst s = SOME xs` >>
  rename1 `eval_operand src s = SOME ys` >>
  rename1 `eval_operand sz s = SOME zs` >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `op_prov G sz = NONE /\ op_taint tn dst = {} /\
   op_taint tn src = {} /\ op_taint tn sz = {}` by
    metis_tac[dload_mcopy_size_clean] >>
  `eval_operand sz s = eval_operand sz t` by
    (irule scalar_operand_equal >> metis_tac[MEM]) >>
  `zs = z` by gvs[] >> gvs[] >>
  `dload_value_word fs (op_taint tn dst) (op_prov G dst) (op_prov H dst) xs x /\
   dload_value_word fs (op_taint tn src) (op_prov G src) (op_prov H src) ys y` by
    (conj_tac >> irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  suspend "mcopy_finish"
QED

Resume dload_boundary_core_mcopy[mcopy_finish]:
  `step_taint i s (mcopy (w2n xs) (w2n ys) (w2n z) s) tn =
    tn with t_mem := (tn.t_mem DIFF {p | w2n xs <= p /\ p < w2n xs+w2n z})
      UNION {w2n xs+k | k < w2n z /\ w2n ys+k IN tn.t_mem}` by
    metis_tac[dload_mcopy_ghosts] >>
  `step_taint i t (mcopy (w2n x) (w2n y) (w2n z) t) un =
    un with t_mem := (un.t_mem DIFF {p | w2n x <= p /\ p < w2n x+w2n z})
      UNION {w2n x+k | k < w2n z /\ w2n y+k IN un.t_mem}` by
    metis_tac[dload_mcopy_ghosts] >>
  `dload_memory_match lo fs
    (step_taint i s (mcopy (w2n xs) (w2n ys) (w2n z) s) tn)
    (step_taint i t (mcopy (w2n x) (w2n y) (w2n z) t) un)
    (mcopy (w2n xs) (w2n ys) (w2n z) s)
    (mcopy (w2n x) (w2n y) (w2n z) t)` by
    (pure_asm_rewrite_tac[] >> irule dload_mcopy_memory >>
     gvs[] >> metis_tac[]) >>
  qexists `mcopy (w2n xs) (w2n ys) (w2n z) s` >>
  conj_tac >- (simp[mcopy_step_success] >> metis_tac[]) >>
  conj_tac >- (gvs[lookup_var_def] >> simp[mcopy_def, write_memory_with_expansion_def]) >>
  `step_prov PG G i (mcopy (w2n xs) (w2n ys) (w2n z) s) = G /\
   step_prov PH H i (mcopy (w2n x) (w2n y) (w2n z) t) = H` by
    metis_tac[dload_mcopy_ghosts] >>
  simp[] >> conj_tac
  >- (irule dload_boundary_core_memory_successors >> conj_tac >- gvs[] >>
      qexistsl [`s`,`t`,`tn`,`un`] >>
      simp[mcopy_def, write_memory_with_expansion_def] >>
      metis_tac[dload_mcopy_ghosts]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Finalise dload_boundary_core_mcopy

Theorem dload_mcopy_arity[local]:
  fn_inst_wf f /\ MEM i (fn_insts f) /\ i.inst_opcode = MCOPY ==>
  i.inst_outputs = []
Proof
  simp[fn_inst_wf_def, fn_insts_def,
    o1PassContractTheory.fn_insts_blocks_MEM] >>
  strip_tac >> first_x_assum drule >> disch_then drule >>
  simp[inst_wf_def]
QED

Theorem dload_actual_mcopy_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  i.inst_opcode = MCOPY /\ fn_inst_wf f /\
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
  `i.inst_outputs = []` by metis_tac[dload_mcopy_arity] >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_mcopy >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
