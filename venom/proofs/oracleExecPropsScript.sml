(* Only non-CALL/non-STATICCALL primitives preserve the oracle lists.
 * Activated-call counterexamples live in venomCallActivationRegression.
 * INVOKE transport remains the calleeTransport boundary. *)
Theory oracleExecProps
Ancestors
  venomState venomInst venomExecSemantics oracleStateProps

(* Index the exported equations once; rewrite only the known opcode branch. *)
val step_inst_base_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun rewrite_step_inst_base_opcode eq = let
  val (_, rewrite) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq)))
    step_inst_base_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP rewrite eq] end;

val step_inst_base_opcode_tac =
  qpat_assum `inst.inst_opcode = _` rewrite_step_inst_base_opcode;

Theorem step_inst_base_oracle:
  inst.inst_opcode <> CALL /\ inst.inst_opcode <> STATICCALL /\
  step_inst_base inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

Theorem step_inst_noninvoke_oracle:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> CALL /\
  inst.inst_opcode <> STATICCALL /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  simp[Once step_inst_def] >> strip_tac >> gvs[] >>
  drule step_inst_base_oracle >> simp[]
QED
