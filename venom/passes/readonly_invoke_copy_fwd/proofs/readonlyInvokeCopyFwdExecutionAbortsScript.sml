Theory readonlyInvokeCopyFwdExecutionAborts
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadOpaque frameRel taintAgree internalReturnCopyFwdSim
  ptrDiscipline venomExecSemantics venomState venomInst
  finite_map list pred_set words

Theorem ricf_execution_static_effect_abort:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG;SELFDESTRUCT;CREATE;CREATE2] /\
  s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s) ==>
  step_inst fuel Ct inst t =
    Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  `t.vs_call_ctx = s.vs_call_ctx /\
   (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t))` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_call_ctx >> drule taint_agree_labels >>
     drule taint_agree_operand_defined >>
     simp[ricf_opaque_view_def] >> rpt strip_tac >>
     Cases_on `op` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_FMAP_MAP2,
       optionTheory.IS_SOME_MAP, FLOOKUP_DEF] >>
     rpt (IF_CASES_TAC >> simp[])) >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
  fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem ricf_execution_invalid_abort:
  inst.inst_opcode = INVALID ==>
  step_inst fuel Ct inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
