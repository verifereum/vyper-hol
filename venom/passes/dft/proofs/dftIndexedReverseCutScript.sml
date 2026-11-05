Theory dftIndexedReverseCut
Ancestors
  dftIndexedOriginalRuntime dftOriginalOperands dftOriginalOrbit
  dftOriginalScheduleRuntime dftProtectedRuntime dftPositionalEdit
  dftOccurrenceOrdinaryClosure dftOccurrenceReplay dftOccurrenceMachine
  dftOpenMachine dftRunRel unitLabelMapIdentity venomInst venomState list
  finite_map arithmetic

Theorem dft_original_context_labels:
  dft_original_context Corig D /\ ctx_labels_bound Corig L ==>
  ctx_labels_bound D L
Proof
  simp[ctx_labels_bound_def] >> rpt strip_tac >>
  `?f. MEM f Corig.ctx_functions /\ dft_original_function f fn` by
    (fs[dft_original_context_def] >> metis_tac[LIST_REL_MEM_IMP_R]) >>
  `?q. MEM q fn.fn_blocks /\ MEM inst q.bb_instructions` by
    metis_tac[fn_insts_MEM] >>
  `?b. MEM b f.fn_blocks /\ dft_original_block f b q` by
    (fs[dft_original_function_def] >> metis_tac[LIST_REL_MEM_IMP_R]) >>
  `MEM inst b.bb_instructions` by metis_tac[dft_original_block_mem] >>
  `MEM inst (fn_insts f)` by metis_tac[fn_insts_MEM] >> metis_tac[]
QED

Theorem dft_indexed_instruction_labels[local]:
  ctx_labels_bound D L /\ fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  MEM x (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions /\
  x.inst_opcode <> INVOKE /\ ~is_terminator x.inst_opcode /\
  ~is_pseudo x.inst_opcode ==>
  !l. MEM (Label l) x.inst_operands ==> l IN FDOM L
Proof
  strip_tac >>
  `MEM (EL fi D.ctx_functions) D.ctx_functions` by (simp[MEM_EL] >> qexists_tac `fi` >> simp[]) >>
  `MEM x (fn_insts (EL fi D.ctx_functions))` by
    (simp[fn_insts_MEM] >>
     qexists_tac `EL bi (EL fi D.ctx_functions).fn_blocks` >> simp[MEM_EL] >>
     qexists_tac `bi` >> simp[]) >>
  fs[ctx_labels_bound_def] >> metis_tac[]
QED

Theorem dft_indexed_reverse_operands:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;call] ++ post /\
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo call.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator call.inst_opcode /\
  call.inst_opcode = INVOKE /\ x.inst_opcode <> INVOKE /\
  ctx_labels_bound Corig L /\ MEM rootfn D.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  c = FUNPOW (dft_occ_oracle_next w D) m
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) /\
  c.dft_occ_core = DftOpen
    (DftAt (EL fi D.ctx_functions) k (EL bi (EL fi D.ctx_functions).fn_blocks) s)
    stack n /\ s.vs_inst_idx = LENGTH pre ==>
  !op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >>
  `dft_all_original_ready c` by
    metis_tac[dft_all_original_root, dft_all_original_iter] >>
  `dft_source_provenance D L c` by
    metis_tac[dft_source_root, dft_source_run] >>
  `s.vs_labels = L` by metis_tac[dft_source_active_at] >>
  `ctx_labels_bound D L` by metis_tac[dft_original_context_labels] >>
  `fi < LENGTH D.ctx_functions /\
   bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
   (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions = pre ++ [call;x] ++ post` by
    (simp[dft_pos_edit_ctx_def, dft_pos_edit_fn_def, dft_pos_replace_el] >>
     metis_tac[]) >>
  `dft_original_cut (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks) s` by
    (irule dft_all_original_indexed_at >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `dft_original_function (EL fi Corig.ctx_functions) (EL fi D.ctx_functions) /\
   dft_original_function (EL fi Corig.ctx_functions) (EL fi C.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi D.ctx_functions).fn_blocks) /\
   dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi C.ctx_functions).fn_blocks)` by
    (fs[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `?done. pre = FILTER (\i. is_pseudo i.inst_opcode)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions ++ done` by
    (irule dft_original_crossing_cut >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels` by
    (simp[] >> rpt strip_tac >> irule dft_indexed_instruction_labels >>
     qexistsl_tac [`D`, `bi`, `fi`, `x`] >> simp[]) >>
  rpt strip_tac >> irule dft_original_before_operands >> goal_assum drule >> simp[] >>
  fs[dft_original_block_def, dft_original_schedule_def] >> metis_tac[]
QED
