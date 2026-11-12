Theory entryAllocationCapacityProbe
Ancestors context vyperCompiler allocaBudgetProps actualAllocCredit
  venomInst venomState words list arithmetic finite_map
Libs wordsLib

(* Literal emission preserves only the residue, not the natural capacity. *)
Theorem allocation_capacity_wrap_probe:
  emit_op ALLOCA [Lit ((n2w (dimword (:256))):bytes32)] =
    emit_op ALLOCA [Lit 0w] /\
  alloca_size (inst with inst_operands := [Lit (n2w (dimword (:256)))]) = 0
Proof
  `((n2w (dimword (:256))):bytes32) = 0w` by EVAL_TAC >>
  simp[alloca_size_def]
QED

Theorem retained_alloca_charge_bound:
  MEM func ctx.ctx_functions /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ unit_alloca_budget ctx < dimword (:256) ==>
  alloca_size inst < dimword (:256)
Proof
  strip_tac >>
  `inst.inst_id NOTIN FDOM (s with vs_allocas := FEMPTY).vs_allocas` by simp[] >>
  drule_all remaining_alloca_budget_member >> strip_tac >>
  drule remaining_alloca_budget_unit >>
  disch_then (qspec_then `s with vs_allocas := FEMPTY` mp_tac) >>
  gvs[] >> decide_tac
QED
