Theory dftIndexedFirstCut
Ancestors
  dftIndexedReverseCut dftIndexedOriginalRuntime dftOriginalOperands
  dftOriginalOrbit dftOriginalScheduleRuntime dftProtectedRuntime
  dftOccurrenceOrdinaryClosure dftOccurrenceReplay dftOccurrenceMachine
  dftOpenMachine dftRunRel unitLabelMapIdentity venomInst venomState list
  finite_map arithmetic

Theorem dft_rooted_indexed_first_operands:
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
    stack n /\ s.vs_inst_idx = LENGTH pre ==>
  !op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >>
  `dft_all_original_ready c` by
    metis_tac[dft_all_original_root, dft_all_original_iter] >>
  `dft_source_provenance E L c` by
    metis_tac[dft_source_root, dft_source_run] >>
  `s.vs_labels = L` by metis_tac[dft_source_active_at] >>
  `ctx_labels_bound E L` by metis_tac[dft_original_context_labels] >>
  `dft_original_cut (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi E.ctx_functions).fn_blocks) s` by
    (irule dft_all_original_indexed_at >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `dft_original_function (EL fi Corig.ctx_functions) (EL fi E.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks)
    (EL bi (EL fi E.ctx_functions).fn_blocks)` by
    (fs[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `?done. pre = FILTER (\i. is_pseudo i.inst_opcode)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions ++ done` by
    (irule dft_original_crossing_cut >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `!l. MEM (Label l) inst.inst_operands ==> l IN FDOM s.vs_labels` by
    (simp[] >> rpt strip_tac >>
     fs[ctx_labels_bound_def] >>
     first_x_assum irule >>
     qexists_tac `EL fi E.ctx_functions` >>
     qexists_tac `inst` >> simp[fn_insts_MEM] >> conj_tac
     >- (qexists_tac `EL bi (EL fi E.ctx_functions).fn_blocks` >>
         simp[MEM_APPEND] >> simp[MEM_EL] >> qexists_tac `bi` >> simp[]) >>
     simp[MEM_EL] >> qexists_tac `fi` >> simp[]) >>
  drule dft_original_first_operands >>
  disch_then (qspecl_then [`inst`, `y::post`,
    `FILTER (\i. is_pseudo i.inst_opcode)
      (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions`, `done`] mp_tac) >>
  simp[APPEND_ASSOC]
QED
