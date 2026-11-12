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
  (* P4a in progress *) cheat
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
  (* P4a in progress *) cheat
QED
