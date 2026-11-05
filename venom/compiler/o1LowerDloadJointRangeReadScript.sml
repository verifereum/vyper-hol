(* Relocated normal-path word and slice reads. *)
Theory o1LowerDloadJointRangeRead
Ancestors
  o1LowerDloadJointRangeCopy o1LowerDloadJointMemoryRead
  o1LowerDloadRangeTransport o1LowerDloadJointAssign
  o1LowerDloadJointShift o1LowerDloadEnvironment venomInst codegenRel
  ptrDiscipline venomExecSemantics venomState words list pred_set unitShapeDefs
  pointerConfinedDefs o1PassContract rich_list o1LowerDloadJointScalar
  finite_map o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadOpaque
  o1LowerDloadRelocationKernel contextCodegenRel memLocDefs

Theorem ld_mload_range_masked:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ((p=q /\ p+32<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+32<=z /\
                    p=b+j /\ q=c+j)) ==>
  word_agree_except (mem_word_taint mask p) (mload p s) (mload q t)
Proof
  strip_tac
  >- (gvs[] >> irule ld_mload_masked_bytes >> rpt strip_tac >>
      irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`,`mask`,`sites`] >>
      gvs[mem_word_taint_def] >> decide_tac) >>
  gvs[] >> irule ld_mload_site_masked >> metis_tac[]
QED

Theorem ld_joint_iload_read:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [p] /\
  eval_operand p s = SOME x ==>
  ?y. eval_operand p t = SOME y /\
    word_agree_except (mem_word_taint tn.t_mem (w2n x))
      (mload (w2n x) s) (mload (w2n y) t)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?y. eval_operand p t = SOME y /\
    (32=0 \/ (w2n x=w2n y /\ w2n x+32<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+32<=z /\
                    w2n x=b+j /\ w2n y=c+j))` by
    (drule ld_joint_read_operand_range >>
     disch_then (qspecl_then [`x`,`<|iao_ofst := p; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`,`p`,`32`] mp_tac) >>
     simp[mem_read_ops_def] >> disch_then irule >> simp[] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def, eval_operand_def,
          retpc_use_ok_def] >> metis_tac[]) >>
  qexists_tac `y` >> simp[] >> irule ld_mload_range_masked >>
  qexistsl_tac [`lo`,`sites`] >> fs[ld_joint_boundary_def] >> metis_tac[]
QED

Theorem ld_joint_iload_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = ILOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[exec_read1_def, AllCaseEqs()] >> strip_tac >>
  rename1 `eval_operand p s = SOME x` >>
  `?y. eval_operand p t = SOME y /\
    word_agree_except (mem_word_taint tn.t_mem (w2n x))
      (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ld_joint_iload_read >> metis_tac[]) >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`, `value`, `mload (w2n y) t`] >> simp[] >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  conj_tac >- gvs[out_taint_def, Abbr `value`] >>
  metis_tac[ld_joint_environment]
QED

Theorem ld_memory_agree_clean_slice:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  (len=0 \/ (p=q /\ p+len<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                  p=b+j /\ q=c+j)) /\
  (!k. k<len ==> p+k NOTIN mask) ==>
  read_memory p len s = read_memory q len t
Proof
  rpt gen_tac >> disch_tac >>
  irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_joint_sha3_length:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [addr;sz] ==>
  eval_operand sz s = eval_operand sz t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn sz = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  drule ld_joint_nonaddress_operand >> disch_then irule >>
  gvs[is_pointer_preserving_op_def, retpc_use_ok_def] >>
  Cases_on `addr = sz` >>
  simp[mem_read_ops_def, mem_write_ops_def]
QED

Theorem ld_joint_sha3_read:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [p;sz] /\
  eval_operand p s = SOME x /\ eval_operand sz s = SOME l ==>
  ?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t
Proof
  strip_tac >>
  `eval_operand sz s = eval_operand sz t` by
    (irule ld_joint_sha3_length >> metis_tac[]) >>
  `eval_operand sz t = SOME l` by metis_tac[] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {}` by
    (qpat_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `?y. eval_operand p t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n x=b+j /\ w2n y=c+j))` by
    (drule ld_joint_read_operand_range >>
     disch_then (qspecl_then [`x`,`<|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|>`,`p`,`w2n l`] mp_tac) >>
     simp[mem_read_ops_def] >> disch_then irule >> simp[retpc_use_ok_def]) >>
  `!k. k<w2n l ==> w2n x+k NOTIN tn.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x+k /\ w2n x+k < w2n x+w2n l` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl_tac [`w2n x`,`w2n l`,`w2n x+k`] >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `y` >> simp[] >> irule ld_memory_agree_clean_slice >>
  qexistsl_tac [`lo`,`tn.t_mem`,`sites`] >> simp[] >>
  gvs[ld_joint_boundary_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_joint_sha3_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = SHA3 /\ step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[] >> rename1 `inst.inst_operands = [p;sz]` >>
  rename1 `eval_operand p s = SOME x` >>
  rename1 `eval_operand sz s = SOME l` >>
  `?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t` by
    (irule ld_joint_sha3_read >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`,`value`,`value`] >> simp[] >> conj_tac
  >- (simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      gvs[Abbr `value`, read_memory_def]) >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  conj_tac >- simp[out_taint_def, word_agree_except_def] >>
  metis_tac[ld_joint_environment]
QED

Theorem ld_joint_range_read_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ILOAD;SHA3] /\ ~in_revert_forward fn s /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)` by
    (gvs[] >> metis_tac[ld_joint_iload_step, ld_joint_sha3_step]) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `update_var out y t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`y`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  gvs[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED
