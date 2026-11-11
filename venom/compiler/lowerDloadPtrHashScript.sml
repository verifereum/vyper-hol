Theory lowerDloadPtrHash
Ancestors
  lowerDloadPtrMemoryRead lowerDloadPtrRegion lowerDloadPtrRel
  lowerDloadPtrAggregate lowerDloadPtrJointNext lowerDloadPtrBlockEntry
  lowerDloadPtrPhi lowerDloadPtrCall lowerDloadPtrStatic lowerDloadPtrScalar
  ptrDiscipline venomExecSemantics venomState venomInst venomWf
  pointerConfinedDefs contextCodegenRel codegenRel memLocDefs
  finite_map list rich_list pred_set arithmetic words

Theorem dload_memory_clean_slice:
  dload_memory_match lo fs tn un s t /\
  ((a=z /\ a+len<=lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
      a=b+d /\ z=c+d /\ d+len<=n)) /\
  (!k. k<len ==> a+k NOTIN tn.t_mem) ==>
  TAKE len (DROP a s.vs_memory ++ REPLICATE len 0w) =
  TAKE len (DROP z t.vs_memory ++ REPLICATE len 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < len ==>
    (a+k IN tn.t_mem <=> z+k IN un.t_mem) /\
    (a+k NOTIN tn.t_mem ==>
      read_byte (a+k) s.vs_memory = read_byte (z+k) t.vs_memory)` by
    (match_mp_tac dload_memory_read_bytes >> metis_tac[]) >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  simp[EL_TAKE, EL_APPEND, EL_DROP, EL_REPLICATE, read_byte_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem sha3_step_success[local]:
  i.inst_opcode = SHA3 ==>
  (step_inst fuel C i s = OK s' <=>
   ?a sz out x z. i.inst_operands = [a;sz] /\ i.inst_outputs = [out] /\
     eval_operand a s = SOME x /\ eval_operand sz s = SOME z /\
     s' = update_var out
       (word_of_bytes T (0w:bytes32) (Keccak_256_w64
         (TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w)))) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_sha3_size_clean[local]:
  i.inst_opcode = SHA3 /\ i.inst_operands = [a;sz] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s ==>
  op_prov G sz = NONE /\ op_taint tn a = {} /\ op_taint tn sz = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `!u. sz = Var u ==> u NOTIN fn_pv P f` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> rpt strip_tac >>
     qpat_x_assum `!v. _` (qspec_then `u` mp_tac) >>
     gvs[] >> Cases_on `a = Var u` >> gvs[] >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `sz` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dload_sha3_slice[local]:
  i.inst_opcode = SHA3 /\ i.inst_operands = [a;sz] /\
  eval_operand a s = SOME x /\ eval_operand sz s = SOME z /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  taint_ok f tn i s /\ ~about_to_revert f i s /\
  dload_live_layout lo sf tf fs /\ dload_memory_match lo fs tn un s t /\
  dload_value_word fs {} (op_prov G a) q x y ==>
  TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w) =
  TAKE (w2n z) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n z) 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `w2n z = 0` >- simp[] >>
  `(lo < w2n x + w2n z \/ op_prov G a <> NONE) ==>
    ?b n. op_prov G a = SOME (b,n) /\ b <= w2n x /\
      w2n x + w2n z <= b+n` by
    (gvs[access_ok_def, source_memory_read_ranges_def, mem_read_ops_def,
         memory_range_of_operands_def] >>
     strip_tac >> qpat_x_assum `(_ ==> _) ==> _` drule >>
     strip_tac >> gvs[op_prov_def] >> metis_tac[]) >>
  `((w2n x = w2n y /\ w2n x + w2n z <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     w2n x = b+d /\ w2n y = c+d /\ d+w2n z <= n))` by
    (drule_all dload_value_contained_region >> simp[]) >>
  `!k. k < w2n z ==> w2n x+k NOTIN tn.t_mem` by
    (gvs[taint_ok_def, source_memory_read_ranges_def, mem_read_ops_def,
         memory_range_of_operands_def] >>
     rpt strip_tac >> qpat_x_assum `!i'. _` (qspec_then `w2n x+k` mp_tac) >>
     simp[ADD_COMM]) >>
  match_mp_tac dload_memory_clean_slice >> metis_tac[]
QED

Theorem dload_sha3_ghosts[local]:
  i.inst_opcode = SHA3 /\ i.inst_operands = [a;sz] /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    (simp[out_taint_def, written_taint_def] >>
     Cases_on `eval_operand a s` >> simp[]) >>
  simp[step_prov_def, out_prov_def, step_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_sha3:
  i.inst_opcode = SHA3 /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  ~about_to_revert f i s /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\ t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule sha3_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (drule eval_operand_definedness >> simp[] >> metis_tac[]) >>
  `eval_operand a s <> NONE /\ eval_operand sz s <> NONE` by
    (gvs[] >> metis_tac[]) >>
  Cases_on `eval_operand a s` >- gvs[] >>
  Cases_on `eval_operand sz s` >- gvs[] >>
  rename1 `eval_operand a s = SOME xs` >>
  rename1 `eval_operand sz s = SOME zs` >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `op_prov G sz = NONE /\ op_taint tn a = {} /\ op_taint tn sz = {}` by
    metis_tac[dload_sha3_size_clean] >>
  `eval_operand sz s = eval_operand sz t` by
    (irule scalar_operand_equal >> metis_tac[MEM]) >>
  `zs = z` by gvs[] >> gvs[] >>
  `dload_value_word fs (op_taint tn a) (op_prov G a) (op_prov H a) xs x` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `TAKE (w2n z) (DROP (w2n xs) s.vs_memory ++ REPLICATE (w2n z) 0w) =
   TAKE (w2n z) (DROP (w2n x) t.vs_memory ++ REPLICATE (w2n z) 0w)` by
    (irule dload_sha3_slice >> simp[] >> metis_tac[]) >>
  suspend "sha3_finish"
QED

Resume dload_boundary_core_sha3[sha3_finish]:
  qmatch_goalsub_abbrev_tac `update_var out hash t` >>
  qexists `update_var out hash s` >>
  conj_tac >- (simp[sha3_step_success, Abbr `hash`] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule update_var_definedness >> qexists `U` >> simp[]) >>
  `step_prov PG G i (update_var out hash s) = set_prov G [out] NONE /\
   step_taint i s (update_var out hash s) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule dload_sha3_ghosts >> simp[]) >>
  `step_prov PH H i (update_var out hash t) = set_prov H [out] NONE /\
   step_taint i t (update_var out hash t) un =
     un with t_var := set_var_taint un.t_var [out] {}` by
    (irule dload_sha3_ghosts >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    (s with <|vs_vars := (update_var out hash s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out hash t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >>
     simp[dload_value_word_def, word_agree_except_def]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Finalise dload_boundary_core_sha3

Theorem dload_actual_sha3_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\ i.inst_opcode = SHA3 /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  ~about_to_revert f i s /\
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
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_sha3 >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
