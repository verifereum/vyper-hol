Theory concretizeLayoutLocalReturn
Ancestors concretizeLayoutHaltExit concretizeLayoutSupplement frameRelocationLocal codegenRel
  ptrDiscipline venomExecSemantics venomState list rich_list pred_set

Theorem return_execution_envelope[local]:
  inst.inst_opcode = RETURN /\ step_inst_base inst s = Halt post ==>
  ?opd opn off sz.
    inst.inst_operands = [opd;opn] /\
    eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
    post = halt_state (set_returndata
      (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w)) s)
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

(* Return payloads need agreement only outside their source memory taint. *)
Theorem concretize_return_payload:
  inst.inst_opcode = RETURN /\ inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
    codegenRel$read_byte (w2n off+i) s.vs_memory =
    codegenRel$read_byte (w2n offT+i) t.vs_memory) ==>
  ?post post'. step_inst_base inst s = Halt post /\
    step_inst_base inst t = Halt post' /\
    LENGTH post.vs_returndata = LENGTH post'.vs_returndata /\
    (!i. i < LENGTH post.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
      EL i post.vs_returndata = EL i post'.vs_returndata)
Proof
  strip_tac >>
  qexistsl_tac [
    `halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w)) s)`,
    `halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n offT) t.vs_memory ++ REPLICATE (w2n sz) 0w)) t)`] >>
  simp[step_inst_base_def, halt_state_def, set_returndata_def,
       LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP, ret_taint_def] >>
  qx_gen_tac `j` >> strip_tac >>
  `codegenRel$read_byte (w2n off+j) s.vs_memory =
   codegenRel$read_byte (w2n offT+j) t.vs_memory` by metis_tac[arithmeticTheory.ADD_COMM] >>
  fs[codegenRelTheory.read_byte_def] >> simp[EL_TAKE] >>
  Cases_on `w2n off+j < LENGTH s.vs_memory` >>
  Cases_on `w2n offT+j < LENGTH t.vs_memory` >>
  gvs[EL_APPEND1, EL_APPEND2, LENGTH_DROP, EL_DROP, EL_REPLICATE] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[]
QED

Theorem concretize_return_observation:
  inst.inst_opcode = RETURN /\ step_inst_base inst s = Halt post /\
  inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
    codegenRel$read_byte (w2n off+i) s.vs_memory =
    codegenRel$read_byte (w2n offT+i) t.vs_memory) /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  taint_within D C vs0 /\
  final_taint vs0 C post (step_taint inst s post tn) (ret_taint tn inst s) ==>
  ?post'. step_inst_base inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  strip_tac >>
  drule_all return_execution_envelope >> strip_tac >> gvs[] >>
  drule_all (SRULE[arithmeticTheory.ADD_COMM] concretize_return_payload) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst t = Halt _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[] >> strip_tac >> gvs[] >>
  irule concretize_supplement_halt_exit >>
  gvs[halt_state_def, set_returndata_def] >>
  `s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[concretize_local_obs_def, dead_result_rel_def] >>
  simp[] >>
  goal_assum (drule_at (Pat `final_taint _ _ _ _ _`)) >> simp[] >>
  gvs[concretize_supplement_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def, halt_state_def, set_returndata_def]
QED

val _ = export_theory();
