Theory lowerDloadPtrMemoryRead
Ancestors
  lowerDloadPtrRel lowerDloadPtrAffine lowerDloadPtrExpansionTransport
  lowerDloadPtrBlockEntry lowerDloadPtrJointNext lowerDloadPtrAggregate lowerDloadPtrPhi
  ptrDiscipline venomExecSemantics venomState venomMemProps vfmTypes codegenRel
  lowerDloadPtrStatic lowerDloadPtrCall pointerConfinedDefs venomInst
  contextCodegenRel memLocDefs list rich_list pred_set arithmetic words finite_map

Theorem dload_memory_read_bytes:
  dload_memory_match lo fs tn un s t /\
  ((a = z /\ a + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+len <= n)) ==>
  !k. k < len ==>
    (a+k IN tn.t_mem <=> z+k IN un.t_mem) /\
    (a+k NOTIN tn.t_mem ==>
      read_byte (a+k) s.vs_memory = read_byte (z+k) t.vs_memory)
Proof
  simp[dload_memory_match_def] >> strip_tac >> rpt strip_tac
  >- (`a+k < lo` by decide_tac >>
      qpat_x_assum `!i. i < lo ==> _` (qspec_then `a+k` mp_tac) >>
      gvs[ADD_COMM])
  >- (`a+k < lo` by decide_tac >>
      qpat_x_assum `!i. i < lo ==> _` (qspec_then `a+k` mp_tac) >>
      gvs[ADD_COMM]) >>
  `d+k < n` by decide_tac >>
  first_x_assum (qspecl_then [`owner`,`id`,`b`,`c`,`n`,`d+k`] mp_tac) >>
  `b+(d+k) = a+k /\ c+(d+k) = k+z` by decide_tac >>
  asm_rewrite_tac[] >> strip_tac >> gvs[]
QED

Theorem dload_mload_byte:
  k < 32 ==>
  EL k (word_to_bytes (mload a s) T) = read_byte (a+k) s.vs_memory
Proof
  strip_tac >>
  `word_to_bytes (mload a s) T =
    TAKE 32 (DROP a s.vs_memory ++ REPLICATE 32 0w)` by
    (irule (INST_TYPE [alpha |-> ``:256``] venomMemPropsTheory.word_of_bytes_be_inj) >>
     simp[byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE_EQ,
       word_to_bytes_word_of_bytes_256, mload_def] >> EVAL_TAC) >>
  simp[EL_TAKE, EL_APPEND, EL_DROP, EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem dload_memory_read_word:
  dload_memory_match lo fs tn un s t /\
  ((a = z /\ a + 32 <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+32 <= n)) ==>
  mem_word_taint tn.t_mem a = mem_word_taint un.t_mem z /\
  word_agree_except (mem_word_taint tn.t_mem a) (mload a s) (mload z t)
Proof
  disch_then (mp_tac o MATCH_MP dload_memory_read_bytes) >> strip_tac >> conj_tac
  >- (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
      Cases_on `x < 32` >> simp[] >>
      first_x_assum (qspec_then `x` mp_tac) >> simp[ADD_COMM]) >>
  simp[word_agree_except_def, mem_word_taint_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >>
  simp[dload_mload_byte, ADD_COMM]
QED

Theorem mload_step_success[local]:
  MEM i.inst_opcode [MLOAD; ILOAD] ==>
  (step_inst fuel C i s = OK s' <=>
   ?a out x. i.inst_operands = [a] /\ i.inst_outputs = [out] /\
     eval_operand a s = SOME x /\
     s' = update_var out (mload (w2n x) s) s)
Proof
  simp_tac pure_ss [MEM] >> strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
    exec_read1_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_mload_region[local]:
  MEM i.inst_opcode [MLOAD; ILOAD] /\ i.inst_operands = [a] /\
  eval_operand a s = SOME x /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} (op_prov G a) q x y ==>
  (w2n x = w2n y /\ w2n x + 32 <= lo) \/
  (?owner id b c n d. dload_live_site fs owner id b c n /\
    w2n x = b+d /\ w2n y = c+d /\ d+32 <= n)
Proof
  simp_tac pure_ss [MEM] >> strip_tac >> (
  gvs[access_ok_def, source_memory_read_ranges_def,
      mem_read_ops_def] >>
  qpat_x_assum `!off len. _` kall_tac >>
  Cases_on `op_prov G a`
  >- (Cases_on `q` >>
      gvs[dload_value_word_def, word_agree_except_bits] >>
      disj1_tac >> conj_tac
      >- (simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
      spose_not_then assume_tac >>
      `lo < w2n x + 32` by decide_tac >>
      qpat_x_assum `lo < _ ==> _` drule >>
      strip_tac >> gvs[op_prov_def]) >>
  PairCases_on `x'` >>
  qpat_x_assum `(_ ==> _) ==> _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[op_prov_def] >>
  Cases_on `q` >> gvs[dload_value_word_def] >>
  PairCases_on `x'` >> gvs[dload_pointer_word_def] >>
  `dload_pointer_word fs (b,sz) (x'0,sz) x
     (x - n2w b + n2w x'0)` by
    (simp[dload_pointer_word_def] >> metis_tac[]) >>
  `w2n x <= b+sz` by decide_tac >>
  drule_all dload_pointer_word_interval >> strip_tac >>
  disj2_tac >> qexistsl [`owner`,`id`,`b`,`x'0`,`sz`,`w2n x-b`] >>
  simp[] >> decide_tac)
QED

Theorem dload_boundary_core_mload:
  MEM i.inst_opcode [MLOAD; ILOAD] /\
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
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule mload_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `eval_operand a s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `a` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand a s` >- gvs[] >>
  rename1 `eval_operand a s = SOME xs` >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `op_taint tn a = {}` by (gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `dload_value_word fs (op_taint tn a) (op_prov G a) (op_prov H a) xs x` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by
    metis_tac[dload_boundary_core_def] >>
  qpat_x_assum `dload_value_word _ _ _ _ _ _` mp_tac >>
  simp[] >> disch_then assume_tac >>
  drule_all (SRULE [MEM] dload_mload_region) >> disch_then assume_tac >>
  `mem_word_taint tn.t_mem (w2n xs) = mem_word_taint un.t_mem (w2n x) /\
   word_agree_except (mem_word_taint tn.t_mem (w2n xs))
     (mload (w2n xs) s) (mload (w2n x) t)` by
    (match_mp_tac dload_memory_read_word >> simp[]) >>
  qexists `update_var out (mload (w2n xs) s) s` >>
  conj_tac >- (simp[mload_step_success] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `out_taint tn i s = mem_word_taint tn.t_mem (w2n xs) /\
   out_taint un i t = mem_word_taint un.t_mem (w2n x)` by
    simp[out_taint_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s))
    (un with t_var := set_var_taint un.t_var [out] (out_taint un i t))
    (s with <|vs_vars := (update_var out (mload (w2n xs) s) s).vs_vars;
              vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out (mload (w2n x) t) t).vs_vars;
              vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >> simp[dload_value_word_def] >>
     metis_tac[]) >>
  qpat_x_assum `i.inst_opcode = MLOAD \/ i.inst_opcode = ILOAD` strip_assume_tac >>
  simp[dload_read_ghost_updates, update_var_def] >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_actual_mload_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [MLOAD; ILOAD] /\
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
       lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venomStateTheory.venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_mload >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
