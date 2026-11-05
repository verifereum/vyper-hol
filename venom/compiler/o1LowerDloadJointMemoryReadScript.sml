(* Source-indexed masked memory reads. *)
Theory o1LowerDloadJointMemoryRead
Ancestors
  o1LowerDloadMemoryConsumer o1LowerDloadJointShift
  o1LowerDloadRelocationKernel o1LowerDloadEnvironment o1LowerDloadOccurrence
  ptrDiscipline venomState venomExecSemantics list rich_list byte words
  finite_map pred_set vfmTypes codegenRel o1LowerDloadJointRelation
  o1LowerDloadJointScalar unitShapeDefs memLocDefs o1LowerDloadAddressArithmetic
  venomInst o1LowerDloadJointAssign

Theorem ld_mload_masked_bytes:
  (!k. k < 32 /\ k NOTIN m ==>
    read_byte (a+k) s.vs_memory = read_byte (b+k) t.vs_memory) ==>
  word_agree_except m (mload a s) (mload b t)
Proof
  strip_tac >> simp[word_agree_except_def, mload_def] >> rpt strip_tac >>
  simp[word_to_bytes_def, EL_word_to_bytes_aux,
    get_byte_word_of_bytes_be, LENGTH_TAKE_EQ, first_byte_at_0w, dimword_def] >>
  simp[EL_TAKE, EL_APPEND_EQN, EL_DROP, EL_REPLICATE] >>
  first_x_assum (qspec_then `b'` mp_tac) >> simp[read_byte_def] >>
  Cases_on `a+b' < LENGTH s.vs_memory` >>
  Cases_on `b+b' < LENGTH t.vs_memory` >> simp[]
QED

Theorem ld_mload_site_masked:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z ==>
  word_agree_except (mem_word_taint mask (b+j)) (mload (b+j) s) (mload (c+j) t)
Proof
  strip_tac >> irule ld_mload_masked_bytes >> rpt strip_tac >>
  `b+j+k NOTIN mask` by gvs[mem_word_taint_def] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule ld_memory_agree_site_byte >>
  qexistsl_tac [`id`, `lo`, `mask`, `sites`, `z`] >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem ld_step_mload_masked_transfer:
  ld_env_agree sites fn H tn s t /\
  ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
  b+j < dimword (:256) /\ c+j < dimword (:256) /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [p] /\ inst.inst_outputs = [out] /\
  eval_operand p s = SOME (n2w (b+j)) /\
  eval_operand p t = SOME (n2w (c+j)) ==>
  step_inst fuel C inst s = OK (update_var out (mload (b+j) s) s) /\
  step_inst fuel C' inst t = OK (update_var out (mload (c+j) t) t) /\
  ld_env_agree sites fn
    (occurrence_step a0 HP H inst (update_var out (mload (b+j) s) s))
    (step_taint inst s (update_var out (mload (b+j) s) s) tn)
    (update_var out (mload (b+j) s) s) (update_var out (mload (c+j) t) t)
Proof
  strip_tac >> conj_tac >- (irule ld_step_mload >> metis_tac[]) >>
  conj_tac >- (irule ld_step_mload >> metis_tac[]) >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  simp[out_taint_def] >> irule ld_mload_site_masked >> metis_tac[]
QED

Theorem ld_joint_mload_read:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [p] /\
  eval_operand p s = SOME x ==>
  ?y. eval_operand p t = SOME y /\
    word_agree_except (mem_word_taint tn.t_mem (w2n x))
      (mload (w2n x) s) (mload (w2n y) t)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. p = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var, MEM] >>
  `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
  `!v. p = Var v ==> ~retpc_var fn v` by
    metis_tac[ld_active_operand_non_retpc, MEM] >>
  `?y. eval_operand p t = SOME y /\
    ld_value_agree sites (op_prov H p) (op_taint tn p) x y` by
    (irule ld_joint_operand_value >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\
   ld_joint_erasure sites B /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U) /\
   ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  drule occurrence_op_erasure >> disch_then (qspec_then `p` assume_tac) >>
  qexists_tac `y` >> simp[] >>
  `lo < w2n x + 32 \/ op_prov G p <> NONE ==>
    ?v b z. p = Var v /\ FLOOKUP G v = SOME (b,z) /\
      b <= w2n x /\ w2n x+32 <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, contextCodegenRelTheory.source_memory_read_ranges_def,
       mem_read_ops_def] >> metis_tac[]) >>
  Cases_on `op_prov H p`
  >- (gvs[occurrence_param_ok_def] >>
      `x = y` by metis_tac[ld_value_agree_clean] >> gvs[] >>
      `w2n x+32 <= lo` by
        (Cases_on `lo < w2n x+32` >> gvs[op_prov_def]) >>
      irule ld_mload_masked_bytes >> rpt strip_tac >>
      irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`, `tn.t_mem`, `sites`] >>
      gvs[mem_word_taint_def] >> decide_tac) >>
  gvs[occurrence_param_ok_def, ld_value_agree_pointer] >>
  gvs[op_prov_def] >>
  `FLOOKUP B x' = SOME (b,z)` by
    (drule ld_joint_erasure_lookup >> metis_tac[]) >>
  gvs[] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    metis_tac[ld_joint_geometry_def] >>
  `w2n (x + n2w c - n2w b) = c + (w2n x - b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  `w2n x = b + (w2n x-b)` by decide_tac >>
  `(w2n x-b)+32 <= z` by decide_tac >>
  metis_tac[ld_mload_site_masked]
QED

Theorem ld_joint_mload_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >>
  rename1 `eval_operand p s = SOME x` >>
  `?y. eval_operand p t = SOME y /\
    word_agree_except (mem_word_taint tn.t_mem (w2n x))
      (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ld_joint_mload_read >> metis_tac[]) >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`, `value`, `mload (w2n y) t`] >> simp[] >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  conj_tac >- gvs[out_taint_def, Abbr `value`] >>
  metis_tac[ld_joint_environment]
QED

Theorem ld_joint_mload_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = MLOAD /\ ~in_revert_forward fn s /\
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
  strip_tac >> drule_all ld_joint_mload_step >> strip_tac >>
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
