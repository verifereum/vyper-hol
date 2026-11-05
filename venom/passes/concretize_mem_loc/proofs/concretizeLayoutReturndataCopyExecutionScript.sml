Theory concretizeLayoutReturndataCopyExecution
Ancestors concretizeLayoutLocalReturndataSize
  venomExecSemantics venomInst venomState ptrDiscipline

Theorem returndatacopy_execution:
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;len] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\
  eval_operand dst t = SOME d' /\ eval_operand src t = SOME a /\
  eval_operand len t = SOME n /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  step_inst_base inst s = OK post ==>
  post = write_memory_with_expansion (w2n d)
    (TAKE (w2n n) (DROP (w2n a) s.vs_returndata)) s /\
  step_inst_base inst t = OK (write_memory_with_expansion (w2n d')
    (TAKE (w2n n) (DROP (w2n a) t.vs_returndata)) t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> simp[] >>
  Cases_on `w2n a + w2n n > LENGTH t.vs_returndata` >> gvs[]
QED

(* A local calculation only: no claim that these states satisfy the entire
   frozen producer antecedent. Length agreement does not give slice agreement. *)
Theorem returndatacopy_distinct_dead_slices:
  LENGTH ([0w]:word8 list) = LENGTH ([1w]:word8 list) /\
  TAKE 1 (DROP 0 ([0w]:word8 list)) <> TAKE 1 (DROP 0 ([1w]:word8 list)) /\
  read_memory 0 1
    (write_memory_with_expansion 0 [0w] (s with vs_memory := [])) = [0w] /\
  read_memory 0 1
    (write_memory_with_expansion 0 [1w] (s with vs_memory := [])) = [1w]
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

(* The frozen producer uses an empty returndata observation mask, not D.d_ret.
   This boundary applies regardless of trace demand or revert exemption. *)
Theorem dead_result_rel_empty_ret:
  dead_result_rel D (Halt s) (Halt t) /\ D.d_ret s.vs_returndata = {} ==>
  s.vs_returndata = t.vs_returndata
Proof
  simp[dead_result_rel_def] >> strip_tac >>
  irule listTheory.LIST_EQ >> simp[]
QED

Theorem local_rel_empty_ret:
  local_rel H L B R (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  D.d_ret s.vs_returndata = {} ==>
  s.vs_returndata = t.vs_returndata
Proof
  strip_tac >> irule dead_result_rel_empty_ret >>
  qexists_tac `D` >> simp[] >>
  drule frameRelocationLocalTheory.local_rel_observation >> simp[]
QED
