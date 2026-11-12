Theory fmpStageTermSimJump
Ancestors
  fmpStageOpBase fmpStageRel ptrStaticDiscipline ptrDiscipline
  o1PassContract frameViewFacts unitShapeDefs passSimulationDefs
  o1LowerDloadRelocationKernel venomExecSemantics venomState venomInst
  frameRelocationGuardedValues pointerConfinedDefs memLocDefs finite_map pred_set list

Theorem jump_operand_clean[local]:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  MEM i (fn_insts f) /\ fn_static_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P f) i` by
    metis_tac[fn_static_ptr_ok_def] >>
  gvs[MEM, ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem jump_operand_transport[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  drule_all fmp_stage_prov_support >> strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (irule jump_operand_clean >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     conj_tac >- gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     qexists_tac `inst` >> gvs[MEM]) >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  drule_all fmp_stage_operand >>
  simp[MEM] >> strip_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_scalar] >>
  metis_tac[word_agree_except_empty]
QED

Theorem jump_success_transport[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  ~s.vs_halted /\ ~t.vs_halted /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst k C inst s = r /\ terminates r ==>
  ?lbl. r = OK (jump_to lbl s) /\
        !k'. step_inst k' C' inst t = OK (jump_to lbl t)
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[terminates_def] >>
  metis_tac[MEM]
QED

Theorem fmp_stage_jump_result:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?lbl. r = OK (jump_to lbl s) /\
        !k'. step_inst k' C' inst t = OK (jump_to lbl t)
Proof
  strip_tac >>
  `~t.vs_halted` by gvs[fmp_stage_rel_def] >>
  irule jump_success_transport >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule jump_operand_transport >> metis_tac[]) >>
  metis_tac[]
QED
