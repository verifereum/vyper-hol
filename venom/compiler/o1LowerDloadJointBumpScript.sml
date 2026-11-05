(* Scalar BUMP writes two variables in operational order. *)
Theory o1LowerDloadJointBump
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointVarsUpdate
  o1LowerDloadJointRelation ptrDiscipline pointerConfinedDefs memLocDefs
  unitShapeDefs venomInst list o1LowerDloadEnvironment
  o1LowerDloadOccurrence venomState finite_map pred_set
  o1LowerDloadRelocationKernel venomExecSemantics venomExecProps

Theorem ld_joint_bump_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = BUMP ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
    mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_env_bump_update:
  ld_env_agree sites fn H tn s t /\ inst.inst_opcode = BUMP /\
  inst.inst_outputs = [p;q] ==>
  ld_env_agree sites fn
    (occurrence_step a HP H inst (update_var q y (update_var p x s)))
    (step_taint inst s (update_var q y (update_var p x s)) tn)
    (update_var q y (update_var p x s))
    (update_var q y (update_var p x t))
Proof
  strip_tac >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, occurrence_out_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       set_prov_def, FLOOKUP_DRESTRICT, op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `q = v` >> Cases_on `p = v` >>
      gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `q = v` >> Cases_on `p = v` >>
  gvs[ld_env_agree_def, ld_value_agree_scalar, word_agree_except_def] >>
  rpt strip_tac >> gvs[op_taint_def]
QED

Theorem ld_bump_success_iff:
  inst.inst_opcode = BUMP ==>
  (step_inst fuel C inst s = OK s1 <=>
   ?bop sop p q base sz.
     inst.inst_operands = [bop;sop] /\ inst.inst_outputs = [p;q] /\
     eval_operand bop s = SOME base /\ eval_operand sop s = SOME sz /\
     s1 = update_var q (base + sz) (update_var p base s))
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_joint_bump_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = BUMP /\
  step_inst fuel C inst s = OK s1 ==>
  ?p q base sz. inst.inst_outputs = [p;q] /\
    s1 = update_var q (base + sz) (update_var p base s) /\
    step_inst fuel C' inst t = OK (update_var q (base + sz) (update_var p base t)) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1
      (update_var q (base + sz) (update_var p base t))
Proof
  strip_tac >>
  `?bop sop p q base sz.
     inst.inst_operands = [bop;sop] /\ inst.inst_outputs = [p;q] /\
     eval_operand bop s = SOME base /\ eval_operand sop s = SOME sz /\
     s1 = update_var q (base + sz) (update_var p base s)` by
    (qpat_x_assum `step_inst fuel C inst s = OK s1` mp_tac >>
     simp[ld_bump_success_iff]) >>
  rename1 `eval_operand bop s = SOME bval` >>
  drule ld_joint_bump_operands_clean >> simp[] >> strip_tac >>
  `eval_operand bop t = SOME bval /\ eval_operand sop t = SOME sz` by
    metis_tac[MEM] >>
  qexistsl_tac [`bval`,`sz`] >> simp[] >> conj_tac
  >- (simp[ld_bump_success_iff] >> metis_tac[]) >>
  irule ld_env_bump_update >> simp[] >>
  metis_tac[ld_joint_environment]
QED

Theorem ld_joint_bump_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = BUMP /\
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
  strip_tac >> drule_all ld_joint_bump_step >> strip_tac >>
  rename1 `s1 = update_var q (bval + sz) (update_var p bval s)` >>
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
  qexists_tac `update_var q (bval + sz) (update_var p bval t)` >> simp[] >>
  irule ld_joint_vars_update_next >> simp[] >>
  conj_tac >- (qexists_tac `(s.vs_vars |+ (p,bval)) |+ (q,bval + sz)` >>
               simp[update_var_def]) >>
  conj_tac >- (qexists_tac `(t.vs_vars |+ (p,bval)) |+ (q,bval + sz)` >>
               simp[update_var_def]) >>
  qpat_assum `s1 = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[] >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  qpat_x_assum `step_inst fuel C inst s = OK s1` mp_tac >>
  simp[ld_bump_success_iff] >> rpt strip_tac >>
  gvs[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
      imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
      step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      range_bytes_def, FLOOKUP_DEF, SF CONJ_ss]
QED
