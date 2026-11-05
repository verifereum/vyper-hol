(* Memory checks for the storage pop fragment, including exiting ASSERT. *)
Theory bodyMemPopToplevelPath
Ancestors
  exprSimPopStorage fragExecMem instMemFrontier
  exprLoweringProps memSafeRun venomInst list

Theorem dynarray_pop_storage_mem_ok:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  Cases_on `tr` >>
  simp[emitted_insts_def, DROP_APPEND, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def]
QED

Theorem dynarray_pop_storage_opcodes:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  Cases_on `tr` >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED
