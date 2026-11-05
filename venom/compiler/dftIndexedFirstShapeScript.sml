Theory dftIndexedFirstShape
Ancestors
  dftIndexedFirstCut dftShapeBoundary dftLocalOrdinaryClosure
  dftOriginalScheduleRuntime unitLabelMapIdentity venomInst list

Theorem dft_original_indexed_instruction_mem[local]:
  dft_original_context Corig E /\ fi < LENGTH E.ctx_functions /\
  bi < LENGTH (EL fi E.ctx_functions).fn_blocks /\
  MEM inst (EL bi (EL fi E.ctx_functions).fn_blocks).bb_instructions ==>
  MEM (EL fi Corig.ctx_functions) Corig.ctx_functions /\
  MEM inst (fn_insts (EL fi Corig.ctx_functions))
Proof
  strip_tac >>
  `fi < LENGTH Corig.ctx_functions /\
   dft_original_function (EL fi Corig.ctx_functions) (EL fi E.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `bi < LENGTH (EL fi Corig.ctx_functions).fn_blocks /\
   dft_original_block (EL fi Corig.ctx_functions)
     (EL bi (EL fi Corig.ctx_functions).fn_blocks)
     (EL bi (EL fi E.ctx_functions).fn_blocks)` by
    (fs[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `MEM inst (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions` by
    metis_tac[dft_original_block_mem] >>
  conj_tac
  >- (simp[MEM_EL] >> qexists_tac `fi` >> simp[]) >>
  simp[fn_insts_MEM] >>
  qexists_tac `EL bi (EL fi Corig.ctx_functions).fn_blocks` >>
  simp[] >> simp[MEM_EL] >> qexists_tac `bi` >> simp[]
QED

Theorem dft_rooted_indexed_first_no_error:
  dft_original_context Corig E /\ ctx_labels_bound Corig L /\
  fi < LENGTH E.ctx_functions /\
  bi < LENGTH (EL fi E.ctx_functions).fn_blocks /\
  (EL bi (EL fi E.ctx_functions).fn_blocks).bb_instructions = pre ++ [inst;y] ++ post /\
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  MEM rootfn E.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  c = FUNPOW (dft_occ_oracle_next w E) m
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) /\
  c.dft_occ_core = DftOpen
    (DftAt (EL fi E.ctx_functions) k (EL bi (EL fi E.ctx_functions).fn_blocks) s)
    stack n /\ s.vs_inst_idx = LENGTH pre /\
  o1_ctx_shape Corig /\ inst.inst_opcode <> GAS /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) ==>
  !e. step_inst_base inst s <> Error e
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v` by
    (rpt strip_tac >> irule dft_rooted_indexed_first_operands >>
     goal_assum drule >> simp[] >> metis_tac[]) >>
  `MEM (EL fi Corig.ctx_functions) Corig.ctx_functions /\
   MEM inst (fn_insts (EL fi Corig.ctx_functions))` by
    (irule dft_original_indexed_instruction_mem >> goal_assum drule >> simp[MEM_APPEND] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT; DJMP; OFFSET]` by
    (irule dft_ctx_instruction_excluded >> goal_assum drule >> simp[] >> metis_tac[]) >>
  irule dft_shaped_ordinary_no_error >> gvs[] >> metis_tac[]
QED
