(* Delegate calls use the frame's observed message-call outcomes. *)
Theory asmFrameDelegateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp

(* Check the delegated request boundary without equating its zero value
   with the inherited EVM message value. *)
Theorem asm_delegate_request_fields[local]:
  s.contexts = (c,rb)::rest /\ next_opcode c = SOME DelegateCall ==>
  (request_of s).cr_kind = DelegateMessageCall /\
  (request_of s).cr_value = 0 /\
  (request_of s).cr_static = c.msgParams.static /\
  ~computed_precompile (request_of s)
Proof
  simp[request_of_def, computed_precompile_def]
QED

Theorem asm_delegate_outcome_view[local]:
  outcome_of DelegateMessageCall s n m = outcome_of MessageCall s n m
Proof
  simp[outcome_of_def]
QED

(* A delegated child runs the parent's identities and value, not the
   request's target/value pair.  This is an entry-interface diagnostic. *)
Theorem asm_delegate_enter_view[local]:
  s.contexts = (parent,prb)::rest /\
  ~fIN address precompile_addresses /\
  proceed_call DelegateCall sender address 0 ao az code stipend (Memory mr) s =
    (INL (),t) ==>
  ?child. t.contexts = (child,s.rollback)::(parent,prb)::rest /\
    child.msgParams.callee = sender /\
    child.msgParams.caller = parent.msgParams.caller /\
    child.msgParams.value = parent.msgParams.value /\
    child.msgParams.static = parent.msgParams.static /\
    child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
    t.rollback = s.rollback
Proof
  strip_tac >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, push_context_def,
       get_current_context_def, return_def] >>
  strip_tac >>
  gvs[vfmContextTheory.initial_context_def,
      vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_frame_delegate_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp "DELEGATECALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
