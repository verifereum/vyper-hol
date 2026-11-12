(* Clean S1 runs transported to the same actual, memory-counted path. *)
Theory rawCallCountedRun
Ancestors
  varsExt freshWrites fragGasSeqMem fragExecMem exprLoweringProps
  venomExecSemantics venomState venomInst list rich_list

Theorem clean_run_counted_mem:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> GAS) code /\
  run_inst_seq code (drop_fresh sa s) = OK t0 /\
  run_inst_seq_mem_ok code s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. run_inst_seq code s = OK t /\ vars_ext t0 t /\
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  `vars_ext_result (run_inst_seq code (drop_fresh sa s))
     (run_inst_seq code s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> impl_tac >- fs[EVERY_MEM] >> metis_tac[]
QED
