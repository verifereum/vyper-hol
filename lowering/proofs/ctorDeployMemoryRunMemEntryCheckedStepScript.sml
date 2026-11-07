Theory ctorDeployMemoryRunMemEntryCheckedStep
Ancestors
  fragGasPathMem gasCount memSafeRun venomExecSemantics venomState
  venomInst arithmetic

Theorem ctor_checked_step:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode /\ ~t.vs_halted /\
  mem_safe_step fuel ctx inst s /\
  gas_count_step fuel ctx inst s = 0 ==>
  gas_path_mem ctx fn s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_mem_edge ctx fn s 0
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_path_mem_edge_def] >>
     qexists `fuel` >> simp[]) >>
  `gas_path_mem ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx) 0
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  metis_tac[gas_path_mem_rules, ADD_0]
QED

Theorem ctor_checked_path_append:
  gas_path_mem ctx fn s n (OK t) /\ gas_path_mem ctx fn t m r ==>
  gas_path_mem ctx fn s (n + m) r
Proof
  metis_tac[gas_path_mem_then]
QED
