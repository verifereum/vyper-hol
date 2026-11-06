(* Comparison transport uses same positive-size occurrence, not global order. *)
Theory o1LowerDloadJointCompare
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointScalar o1LowerDloadJointGeometry o1LowerDloadJointAssign
  o1LowerDloadAddressArithmetic o1LowerDloadJointRelation
  finite_map words arithmetic ptrDiscipline o1LowerDloadOccurrence
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel venomState
  list pred_set pointerConfinedDefs memLocDefs unitShapeDefs
  o1LowerDloadGhost o1PassContract venomInst contextCodegenRel
  venomExecSemantics venomExecProps

Theorem ld_joint_geometry_positive_source_unique:
  ld_joint_geometry sites X lo owners /\
  FLOOKUP sites id = SOME (b,c,z) /\
  FLOOKUP sites jd = SOME (b,d,z) /\ 0 < z ==>
  id = jd /\ c = d
Proof
  strip_tac >>
  `id = jd` by
    (spose_not_then assume_tac >>
     fs[ld_joint_geometry_def] >>
     first_x_assum (qspecl_then [`id`,`jd`,`b`,`c`,`z`,`b`,`d`,`z`] mp_tac) >>
     simp[] >> decide_tac) >>
  gvs[]
QED

Theorem ld_joint_compare_operand_results:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y ==>
  ?x' y'. eval_operand p t = SOME x' /\ eval_operand q t = SOME y' /\
    (w2n x < w2n y <=> w2n x' < w2n y') /\
    (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {} /\ op_taint tn q = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def, MEM] >>
  `?x'. eval_operand p t = SOME x' /\
     ld_value_agree sites (op_prov H p) (op_taint tn p) x x'` by
    (irule ld_joint_operand_value >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  `?y'. eval_operand q t = SOME y' /\
     ld_value_agree sites (op_prov H q) (op_taint tn q) y y'` by
    (irule ld_joint_operand_value >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  qexistsl_tac [`x'`,`y'`] >> simp[] >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\
   ld_joint_erasure sites B /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  `op_prov G p = OPTION_BIND (op_prov H p) (FLOOKUP B) /\
   op_prov G q = OPTION_BIND (op_prov H q) (FLOOKUP B)` by
    (drule occurrence_op_erasure >>
     disch_then (fn th => mp_tac (Q.SPEC `p` th) >> mp_tac (Q.SPEC `q` th)) >>
     simp[occurrence_param_ok_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `op_prov H p = NONE /\ op_prov H q = NONE`
  >- (gvs[] >> `x = x' /\ y = y'` by metis_tac[ld_value_agree_clean] >> gvs[]) >>
  `op_prov G p <> NONE \/ op_prov G q <> NONE` by
    (drule occurrence_op_erasure >>
     disch_then (fn th => mp_tac (Q.SPEC `p` th) >> mp_tac (Q.SPEC `q` th)) >>
     simp[occurrence_param_ok_def] >> rpt strip_tac >> gvs[]) >>
  `?P. FDOM G SUBSET fn_pv P fn /\ ptr_use_ok P (fn_pv P fn) inst` by
    (qpat_assum `ptr_discipline _ _ _`
       (strip_assume_tac o MATCH_MP ptr_discipline_fn_ptr_ok) >>
     drule frame_reachable_prov_support >>
     disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
     qexists_tac `P` >> simp[] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
        metis_tac[MEM_EL]) >>
     gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `?u w. p = Var u /\ q = Var w /\
     (u IN FDOM G \/ w IN FDOM G)` by
    (Cases_on `p` >> Cases_on `q` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_ok_def,
         mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM] >>
     metis_tac[]) >>
  gvs[] >>
  `?b z. FLOOKUP G u = SOME (b,z) /\ FLOOKUP G w = SOME (b,z) /\
     0 < z /\ b <= w2n x /\ w2n x <= b+z /\
     b <= w2n y /\ w2n y <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, MEM] >> metis_tac[]) >>
  `?id jd. FLOOKUP H u = SOME id /\ FLOOKUP H w = SOME jd /\
      FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (b,z)` by
    (qpat_assum `FLOOKUP G u = _` mp_tac >>
     qpat_assum `FLOOKUP G w = _` mp_tac >>
     qpat_assum `occurrence_env_ok _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[occurrence_env_ok_def] >> rpt strip_tac >>
     `u IN FDOM H /\ w IN FDOM H` by
       gvs[FLOOKUP_DEF] >>
     `?id. FLOOKUP H u = SOME id` by (Cases_on `FLOOKUP H u` >> gvs[FLOOKUP_DEF]) >>
     `?jd. FLOOKUP H w = SOME jd` by (Cases_on `FLOOKUP H w` >> gvs[FLOOKUP_DEF]) >>
     qexistsl_tac [`id`,`jd`] >> simp[] >> metis_tac[]) >>
  `?c. FLOOKUP sites id = SOME (b,c,z)` by
    (drule ld_joint_erasure_lookup >> metis_tac[]) >>
  `?d. FLOOKUP sites jd = SOME (b,d,z)` by
    (drule ld_joint_erasure_lookup >> metis_tac[]) >>
  `id = jd /\ c = d` by
    metis_tac[ld_joint_geometry_positive_source_unique] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    metis_tac[ld_joint_geometry_def] >>
  `x' = x + n2w c - n2w b /\ y' = y + n2w c - n2w b` by
    gvs[op_prov_def, ld_value_agree_pointer] >>
  `w2n x' = c + (w2n x-b)` by
    (qpat_assum `x' = _` SUBST1_TAC >>
     irule lower_dload_translate_endpoint >> simp[] >> qexists_tac `z` >> simp[]) >>
  `w2n y' = c + (w2n y-b)` by
    (qpat_assum `y' = _` SUBST1_TAC >>
     irule lower_dload_translate_endpoint >> simp[] >> qexists_tac `z` >> simp[]) >>
  pure_once_rewrite_tac[GSYM w2n_11] >>
  qpat_x_assum `x' = _` kall_tac >> qpat_x_assum `y' = _` kall_tac >>
  decide_tac
QED

Theorem ld_joint_compare_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [LT; GT; EQ] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `?p q out x y. inst.inst_operands = [p;q] /\ inst.inst_outputs = [out] /\
     eval_operand p s = SOME x /\ eval_operand q s = SOME y` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all ld_joint_compare_operand_results >> strip_tac >>
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  fs[MEM] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_pure2_def, GREATER_DEF] >> strip_tac >>
   qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexistsl_tac [`out`,`value`] >> simp[] >>
   irule ld_env_clean_update >> simp[] >>
   conj_tac >- simp[out_taint_def] >>
   conj_tac >- simp[occurrence_out_def, out_prov_def] >>
   metis_tac[ld_joint_environment])
QED

Theorem ld_joint_compare_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [LT; GT; EQ] /\
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
  strip_tac >> drule_all ld_joint_compare_step >> strip_tac >>
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
  qexists_tac `update_var out x t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`x`] >>
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
