Theory requestCutFmpOperand
Ancestors
  fmpStageOpBase
  concretizePtrOperationalOpcodes
  fmpStageRel ptrStaticDiscipline ptrDiscipline o1PassContract
  fmpStepBridge fmpLowerDefs fmpWfDefs livenessProofs cfgHelpers pred_set
  contextCodegenRel venomExecSemantics venomInst list
  fmpStageOpBaseRoot fmpStageOpBaseActual o1LowerDloadGhost finite_map

Theorem fmp_env_operand_at:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def, op_prov_def, op_taint_def,
      fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
      word_agree_except_def]
  >- (gvs[venomStateTheory.lookup_var_def] >>
      `MEM s' (live_vars_at (liveness_analyze fn)
                 s.vs_current_bb s.vs_inst_idx)` by
        metis_tac[stage_operand_live] >>
      qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
      simp[fmp_env_rel_def] >>
      disch_then (qspec_then `s'` mp_tac) >> simp[op_taint_def] >>
      strip_tac >> qexists `y` >>
      gvs[fmp_value_rel_def,
          o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
          word_agree_except_def])
QED
