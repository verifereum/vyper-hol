(* Affine ADD/SUB operands at the joint semantic boundary. *)
Theory o1LowerDloadJointArithmetic
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointScalar o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadGhost o1LowerDloadOpaque o1LowerDloadEnvironment
  ptrDiscipline pointerConfinedDefs unitShapeDefs o1PassContract
  venomExecSemantics venomInst finite_map list pred_set contextCodegenRel
  venomState o1LowerDloadRelocationKernel words o1LowerDloadJointAssign
  venomExecProps memLocDefs

Theorem ld_joint_arithmetic_operand_taint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands ==>
  op_taint tn op = {}
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_arithmetic_operand_value:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ ld_value_agree sites (op_prov H op) {} x y
Proof
  strip_tac >>
  `op_taint tn op = {}` by metis_tac[ld_joint_arithmetic_operand_taint] >>
  `!v. op = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> irule ld_active_operand_non_retpc >>
     simp[] >> qexistsl_tac [`inst`,`s`] >> gvs[retpc_use_ok_def] >> metis_tac[]) >>
  drule_all ld_joint_operand_value >> simp[]
QED

Theorem ld_joint_arithmetic_affine:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ADD; SUB] /\
  inst.inst_operands = [op1;op2] ==>
  (op_prov H op1 = NONE \/ op_prov H op2 = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov H op2 = NONE)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  qpat_x_assum `ptr_discipline _ _ _`
    (strip_assume_tac o MATCH_MP ptr_discipline_fn_ptr_ok) >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `affine_pointer_ops fn (ptr_roots P fn)` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op1` assume_tac) >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op2` assume_tac) >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (fs[active_inst_def] >> metis_tac[MEM_EL]) >>
  qpat_x_assum `affine_pointer_ops _ _`
    (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
  disch_then (qspecl_then [`bb`,`inst`,`op1`,`op2`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[op_prov_def, occurrence_param_ok_def, fn_pv_def] >>
  gvs[FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_env_value_update:
  ld_env_agree sites fn H tn s t /\ inst.inst_outputs = [out] /\
  ld_value_agree sites (occurrence_out a HP H inst (update_var out x s))
    (out_taint tn inst s) x y ==>
  ld_env_agree sites fn
    (occurrence_step a HP H inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn)
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, step_taint_def, set_var_taint_def, op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `v = out` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `v = out` >>
  Cases_on `occurrence_out a HP H inst (update_var out x s)` >>
  gvs[ld_env_agree_def, set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      update_var_def, op_taint_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_value_agree_add:
  ld_value_agree sites h1 {} x1 y1 /\ ld_value_agree sites h2 {} x2 y2 /\
  (h1 = NONE \/ h2 = NONE) ==>
  ld_value_agree sites (case h1 of NONE => h2 | SOME id => h1) {}
    (x1 + x2) (y1 + y2)
Proof
  Cases_on `h1` >> Cases_on `h2` >> simp[] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_scalar, ld_value_agree_pointer, word_agree_except_def] >>
  qexistsl_tac [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ld_value_agree_sub:
  ld_value_agree sites h {} x1 y1 /\ ld_value_agree sites NONE {} x2 y2 ==>
  ld_value_agree sites h {} (x1 - x2) (y1 - y2)
Proof
  strip_tac >> imp_res_tac ld_value_agree_clean >> gvs[] >>
  Cases_on `h` >> imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_scalar, ld_value_agree_pointer, word_agree_except_def] >>
  qexistsl_tac [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ld_joint_arithmetic_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADD; SUB] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
   strip_tac >> gvs[] >>
   rename1 `eval_operand op1 s = SOME x1` >>
   rename1 `eval_operand op2 s = SOME x2` >>
   `?y1. eval_operand op1 t = SOME y1 /\
     ld_value_agree sites (op_prov H op1) {} x1 y1` by
     (metis_tac[ld_joint_arithmetic_operand_value, MEM]) >>
   `?y2. eval_operand op2 t = SOME y2 /\
     ld_value_agree sites (op_prov H op2) {} x2 y2` by
     (metis_tac[ld_joint_arithmetic_operand_value, MEM]) >>
   `(op_prov H op1 = NONE \/ op_prov H op2 = NONE) /\
    (inst.inst_opcode = SUB ==> op_prov H op2 = NONE)` by
     metis_tac[ld_joint_arithmetic_affine, MEM] >>
   (qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexistsl_tac [`out`,`value`,
     `if inst.inst_opcode = ADD then y1 + y2 else y1 - y2`] >> simp[] >>
   irule ld_env_value_update >> simp[] >>
   conj_tac
   >- (simp[occurrence_out_def, out_prov_def, first_prov_def, out_taint_def,
            Abbr `value`] >>
       Cases_on `op_prov H op1` >> Cases_on `op_prov H op2` >> gvs[] >>
       imp_res_tac ld_value_agree_add >> gvs[] >>
       metis_tac[SRULE [] ld_value_agree_sub]) >>
   drule ld_joint_environment >> simp[]))
QED

Theorem ld_joint_arithmetic_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ADD; SUB] /\
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
  strip_tac >> drule_all ld_joint_arithmetic_step >> strip_tac >>
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
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[])
QED
