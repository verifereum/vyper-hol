Theory concretizeLayoutOperandCleanliness
Ancestors frameRelocationCleanOperands frameRelocationReachableSupport
  ptrDiscipline pointerConfinedDefs memLocDefs finite_map list

Theorem nonpointer_operand_clean:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  ~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
  mem_write_ops inst = NONE /\ mem_read_ops inst = NONE ==>
  !w. MEM (Var w) inst.inst_operands ==> clean_scalar (retpc_var fn) rv tn w
Proof
  rpt strip_tac >>
  `FLOOKUP rv w = NONE` by
    (spose_not_then assume_tac >>
     `w IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by
       (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     fs[ptr_use_ok_def] >>
     qpat_x_assum `!v. MEM (Var v) _ /\ _ ==> _`
       (qspec_then `w` mp_tac) >> simp[]) >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by fs[] >>
  drule_all disciplined_clean_scalar >> simp[]
QED
