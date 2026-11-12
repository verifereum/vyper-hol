(* Whole-boundary modular ternary arithmetic preservation. *)
Theory o1LowerDloadJointTernary
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadEnvironment ptrDiscipline
  venomExecSemantics venomExecProps venomInst venomState list finite_map
  memLocDefs pointerConfinedDefs o1LowerDloadOpaque o1PassContract unitShapeDefs

Theorem ld_joint_ternary_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADDMOD; MULMOD] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
    mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_ternary_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADDMOD; MULMOD] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[ld_joint_ternary_operands_clean] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`,`value`] >> simp[] >>
  conj_tac
  >- (simp[Abbr `value`] >> metis_tac[MEM]) >>
  irule ld_env_clean_update >> simp[] >>
  conj_tac >- simp[out_taint_def] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  metis_tac[ld_joint_environment])
QED

Theorem ld_joint_ternary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ADDMOD; MULMOD] /\
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
  (* P4a in progress *) cheat
QED
