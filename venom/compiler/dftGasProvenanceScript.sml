Theory dftGasProvenance
Ancestors
  dftEdgeReadiness dftOriginalScheduleRuntime dftGasOrdinaryTrace dftMixedCrossing
  dftProtectedRuntime dftWf allocaRemapSSA venomWf venomInst list sorting

Theorem dft_original_indexed_block:
  dft_original_context C A /\ fi < LENGTH A.ctx_functions /\
  bi < LENGTH (EL fi A.ctx_functions).fn_blocks ==>
  dft_original_block (EL fi C.ctx_functions)
    (EL bi (EL fi C.ctx_functions).fn_blocks)
    (EL bi (EL fi A.ctx_functions).fn_blocks)
Proof
  simp[dft_original_context_def, dft_original_function_def, LIST_REL_EL_EQN] >>
  metis_tac[]
QED

Theorem dft_original_gas_shape:
  dft_original_block f b q /\ MEM gas q.bb_instructions /\
  gas.inst_opcode = GAS ==> ?v. gas.inst_outputs = [v]
Proof
  strip_tac >>
  `EVERY inst_wf q.bb_instructions` by
    (fs[dft_original_block_def] >> metis_tac[dft_original_schedule_instructions_wf]) >>
  `inst_wf gas` by metis_tac[EVERY_MEM] >>
  fs[inst_wf_def] >>
  Cases_on `gas.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem dft_original_adjacent_outputs_disjoint:
  dft_original_block f b q /\ q.bb_instructions = pre ++ [x;y] ++ post ==>
  !v. MEM v x.inst_outputs ==> ~MEM v y.inst_outputs
Proof
  strip_tac >>
  `wf_ssa f /\ wf_function f /\ MEM b f.fn_blocks` by
    fs[dft_original_block_def, dft_original_schedule_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) q.bb_instructions)` by
    metis_tac[dft_original_block_perm, PERM_MAP, ALL_DISTINCT_PERM] >>
  `x <> y` by (gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `MEM x b.bb_instructions /\ MEM y b.bb_instructions` by
    (drule dft_original_block_mem >> simp[] >> metis_tac[]) >>
  `MEM x (fn_insts f) /\ MEM y (fn_insts f)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     conj_tac >> qexists `b` >> simp[]) >>
  fs[wf_ssa_def] >>
  metis_tac[ssa_unique_output]
QED

Theorem dft_indexed_gas_shape:
  dft_original_context C A /\ fi < LENGTH A.ctx_functions /\
  bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
  MEM gas (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions /\
  gas.inst_opcode = GAS ==> ?v. gas.inst_outputs = [v]
Proof
  strip_tac >> drule_all dft_original_indexed_block >>
  metis_tac[dft_original_gas_shape]
QED

Theorem dft_indexed_adjacent_outputs_disjoint:
  dft_original_context C A /\ fi < LENGTH A.ctx_functions /\
  bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
  (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post ==>
  !v. MEM v x.inst_outputs ==> ~MEM v y.inst_outputs
Proof
  strip_tac >> drule_all dft_original_indexed_block >>
  metis_tac[dft_original_adjacent_outputs_disjoint]
QED

Theorem dft_indexed_adjacent_forward_nonuse:
  dft_original_context C A /\ fi < LENGTH A.ctx_functions /\
  bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
  (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  ~dft_must_order x y /\ ~is_pseudo x.inst_opcode ==>
  !v. MEM v x.inst_outputs ==> ~MEM (Var v) y.inst_operands
Proof
  strip_tac >> drule_all dft_original_indexed_block >>
  metis_tac[dft_original_mixed_operands_disjoint]
QED

Theorem dft_indexed_adjacent_backward_nonuse:
  dft_original_context C A /\ fi < LENGTH A.ctx_functions /\
  bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
  (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  ~dft_must_order x y /\ ~is_pseudo x.inst_opcode ==>
  !v. MEM v y.inst_outputs ==> ~MEM (Var v) x.inst_operands
Proof
  strip_tac >> drule_all dft_original_indexed_block >>
  metis_tac[dft_original_mixed_operands_disjoint]
QED
