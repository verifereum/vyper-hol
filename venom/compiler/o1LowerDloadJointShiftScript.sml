(* Mask-changing scalar execution at the joint boundary. *)
Theory o1LowerDloadJointShift
Ancestors
  o1LowerDloadJointScalar o1LowerDloadEnvironment o1LowerDloadOccurrence
  o1LowerDloadRelocationKernel ptrDiscipline venomState finite_map
  pointerConfinedDefs memLocDefs o1LowerDloadJointRelation unitShapeDefs list
  venomInst venomExecSemantics o1LowerDloadJointAssign

Theorem ld_joint_shift_operands:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\ inst.inst_operands = [amount; data] /\
  eval_operand amount s = SOME k /\ eval_operand data s = SOME x ==>
  ?y. eval_operand amount t = SOME k /\ eval_operand data t = SOME y /\
    word_agree_except (op_taint tn data) x y
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_prov H op = NONE` by
    (drule ld_joint_scalar_no_provenance >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn amount = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var] >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==> ~retpc_var fn v` by
    metis_tac[ld_active_operand_non_retpc] >>
  `eval_operand amount s = eval_operand amount t` by
    (irule ld_joint_operand_clean >> metis_tac[MEM]) >>
  `?y. eval_operand data t = SOME y /\
    ld_value_agree sites (op_prov H data) (op_taint tn data) x y` by
    (irule ld_joint_operand_value >> metis_tac[MEM]) >>
  qexists_tac `y` >> gvs[ld_value_agree_scalar]
QED

Theorem ld_joint_shift_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\ step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >>
  rename1 `eval_operand op1 s = SOME arg1` >>
  rename1 `eval_operand op2 s = SOME arg2` >>
  `?y. eval_operand op1 t = SOME arg1 /\ eval_operand op2 t = SOME y /\
     word_agree_except (op_taint tn op2) arg2 y` by
    (irule ld_joint_shift_operands >> metis_tac[MEM]) >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`,`value`] >>
  FIRST [qpat_assum `Abbrev (value = word_lsl arg2 (w2n arg1))` kall_tac >>
           qexists_tac `word_lsl y (w2n arg1)`,
         qpat_assum `Abbrev (value = word_lsr arg2 (w2n arg1))` kall_tac >>
           qexists_tac `word_lsr y (w2n arg1)`,
         qpat_assum `Abbrev (value = word_asr arg2 (w2n arg1))` kall_tac >>
           qexists_tac `word_asr y (w2n arg1)`] >>
  simp[] >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  conj_tac
  >- (simp[out_taint_def, Abbr `value`] >>
      metis_tac[word_agree_except_shl, word_agree_except_shr, word_agree_except_sar]) >>
  metis_tac[ld_joint_environment])
QED

Theorem ld_joint_shift_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [SHL; SHR; SAR] /\
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
  strip_tac >> drule_all ld_joint_shift_step >> strip_tac >>
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
  fs[MEM] >>
  (gvs[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[])
QED
