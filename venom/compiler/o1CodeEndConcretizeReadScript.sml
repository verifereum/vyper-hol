Theory o1CodeEndConcretizeRead
Ancestors
  concretizePtrObservationInterface lowerDloadSafetyPublicCopy
  concretizePtrOpaqueRetpc ptrDiscipline venomState venomInst
  contextCodegenRel codegenRel list finite_map pred_set

(* CODECOPY's external source is a scalar, not the relocated destination. *)
Theorem code_end_concretize_read_value:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ taint_ok fn tn inst s /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; off; sz] /\
  ptr_ledger_erases dyn births TG G /\ FDOM G SUBSET fn_pv P fn /\
  ptr_mixed_vars births positions TG tn fn ft s t /\
  s.vs_labels = t.vs_labels ==>
  eval_operand off s = eval_operand off t
Proof
  strip_tac >>
  `!v. off = Var v ==> v NOTIN fn_pv P fn` by
    (metis_tac[ld_public_copy_scalar_nonpointer, MEM]) >>
  `op_prov G off = NONE` by
    (Cases_on `off` >> gvs[op_prov_def] >>
     metis_tac[flookup_thm, SUBSET_DEF]) >>
  `op_taint tn off = {}` by
    (gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `ptr_nonopaque_operand fn off` by gvs[] >>
  drule_all ptr_mixed_scalar_eval >> simp[]
QED
