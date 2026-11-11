(* The O1 pipeline keeps a leaf entry function's opcode absences: when the
 * entry function has no INVOKE, pruning keeps only it, and no O1 pass
 * introduces a RETURNDATACOPY or an INVOKE.
 * TOP-LEVEL: o1_pipeline_leaf_entry_no_returndatacopy (used by
 * deploy_frame_gas_sufficient; admitted until proved).
 *)
Theory o1OpcodeAbsence
Ancestors
  o1PipelineCorrect venomPassDispatcherProps fcgPruning fcgDefs venomInst

Theorem o1_pipeline_leaf_entry_no_returndatacopy:
  !rpolicy unit out efn.
    o1_pipeline rpolicy unit = SOME out /\
    unit.cu_context.ctx_entry = SOME efn.fn_name /\
    lookup_function efn.fn_name unit.cu_context.ctx_functions = SOME efn /\
    (!inst. MEM inst (fn_insts efn) ==>
            inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> INVOKE)
    ==>
    !fn inst. MEM fn out.po_unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) ==>
              inst.inst_opcode <> RETURNDATACOPY
Proof
  cheat
QED
