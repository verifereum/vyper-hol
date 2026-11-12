Theory o1LowerDloadFreshNext
Ancestors
  o1LowerDloadAllocationBoundary o1LowerDloadJointAllocation
  o1LowerDloadJointRelation o1LowerDloadJointAssign
  o1LowerDloadOccurrence o1LowerDloadPairedAllocation
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadRelocationKernel ptrDiscipline
  venomExecSemantics venomState codegenRel finite_map words list pred_set arithmetic
  o1PassContract venomWf venomInst contextCodegenRel

Theorem ld_alloca_fresh_annotations[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s1 ==>
  occurrence_sites_step a B inst s1 =
    B |+ ((a,inst.inst_id),(s.vs_alloca_next,w2n amount)) /\
  occurrence_step a HP H inst s1 = H |+ (out,(a,inst.inst_id)) /\
  step_taint inst s s1 tn = tn with
    <|t_var := tn.t_var |+ (out,{});
      t_mem := tn.t_mem UNION {s.vs_alloca_next+j | j < w2n amount}|>
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (Q.ISPEC `amount:bytes32`
    (Q.GEN `amount` (SPEC_ALL lower_dload_alloca_fresh))) >>
  disch_then (qspec_then `amount` strip_assume_tac) >> gvs[] >>
  simp[occurrence_sites_step_def, occurrence_step_def, occurrence_out_def,
       set_prov_def, update_var_def, FLOOKUP_UPDATE,
       step_taint_def, mem_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def] >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by gvs[FLOOKUP_DEF] >>
  simp[] >>
  simp[taint_component_equality, EXTENSION] >>
  rpt gen_tac >> eq_tac
  >- (rpt strip_tac >> gvs[] >> Cases_on `inst.inst_id = aid` >>
      gvs[FLOOKUP_DEF] >> disj2_tac >>
      qexists_tac `x - s.vs_alloca_next` >> decide_tac) >>
  rpt strip_tac >> gvs[] >> disj2_tac >>
  qexistsl_tac [`inst.inst_id`, `s.vs_alloca_next`, `w2n amount`] >>
  simp[] >> decide_tac
QED

Theorem ld_joint_alloca_fresh_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  mem_inv dload_headroom_ok C vs /\ callee_first names C.ctx_functions /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  MEM inst.inst_id (fn_ir_inst_ids fn) /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U (occurrence_sites_step a B inst s1) HP
      (occurrence_step a HP H inst s1)
      (sites |+ ((a,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n amount))) X ts
Proof
  (* P4a in progress *) cheat
QED
