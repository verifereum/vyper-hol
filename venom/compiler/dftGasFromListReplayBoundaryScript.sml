Theory dftGasFromListReplayBoundary
Ancestors
  dftGasFromListRestore dftGasFromListTraceDefs gasOracleReplay list

(* State restoration commutations are already exported as gas_eval_operands,
   gas_setup_callee, gas_merge_callee, gas_adopt_return, gas_bind_outputs. *)

Theorem trace_agrees_append[simp]:
  trace_agrees orc (xs ++ ys) <=>
  trace_agrees orc xs /\ trace_agrees orc ys
Proof
  simp[trace_agrees_def, trace_gas_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem trace_agrees_cons:
  trace_agrees orc ((e,fn,inst,s)::xs) <=>
  (inst.inst_opcode = GAS ==>
    orc e = (case s.vs_gas_readings of [] => 0w | w::_ => w)) /\
  trace_agrees orc xs
Proof
  Cases_on `inst.inst_opcode = GAS` >>
  simp[trace_agrees_def, trace_gas_def, visit_gas_def]
QED

Theorem trace_agrees_nil[simp]:
  trace_agrees orc []
Proof
  simp[trace_agrees_def, trace_gas_def]
QED
