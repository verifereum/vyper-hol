Theory dftRecursiveOrbitReadiness
Ancestors
  dftOriginalRuntime dftRecursiveFixedOrbit dftRecursiveActivePhase
  dftOriginalScheduleRuntime dftProtectedRuntime dftOccurrenceOrdinaryClosure
  o1PassContract venomExecSemantics venomInst venomWf dftOriginalCutLifecycle
  list finite_map pred_set

Theorem dft_original_recursive_orbit_ready:
  dft_original_context Corig C /\ dft_original_label_ready C L c /\
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) ==>
  !j fn s ls n.
    (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
      DftOpen (DftAt fn 0 q s) ls n /\ s.vs_inst_idx = LENGTH pre ==>
    ?f b. dft_recursive_crossing_ready f b q pre x call post s
Proof
  rpt strip_tac >>
  `dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) j c)` by
    metis_tac[dft_original_label_iter] >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w C) j c) /\
   dft_source_provenance C L (FUNPOW (dft_occ_oracle_next w C) j c)` by
    fs[dft_original_label_ready_def] >>
  drule_all dft_source_active_at >> strip_tac >>
  drule_all dft_original_runtime_at_projection >> strip_tac >>
  `MEM x (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists `q` >> simp[]) >>
  `MEM x b.bb_instructions /\ MEM call b.bb_instructions` by
    (drule dft_original_block_mem >> simp[] >> metis_tac[]) >>
  `inst_wf x /\ inst_wf call` by
    (fs[dft_original_block_def, dft_original_schedule_def, EVERY_MEM] >> metis_tac[]) >>
  qexistsl [`f`, `b`] >> simp[dft_recursive_crossing_ready_def] >> metis_tac[]
QED

Theorem dft_original_fixed_orbit_ready:
  dft_original_context Corig C /\ dft_original_label_ready C L c /\
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) /\
  dft_fixed_phase q pre x call post c d /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) ==>
  dft_fixed_orbit_ready q pre x call post w C Corig Dorig c d
Proof
  strip_tac >> simp[dft_fixed_orbit_ready_def] >>
  metis_tac[dft_original_recursive_orbit_ready]
QED

Theorem dft_original_label_entry_root:
  dft_original_function f fn /\ MEM fn C.ctx_functions /\
  fn_entry_label fn = SOME s.vs_current_bb /\ s.vs_labels = L ==>
  dft_original_label_ready C L
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  strip_tac >>
  `fn_entry_label f = SOME s.vs_current_bb` by
    metis_tac[dft_original_function_entry] >>
  `fn_reachable f s.vs_current_bb` by
    (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  `strict_dom_vars_defined f s` by metis_tac[dft_original_root_dom] >>
  irule dft_original_label_root >> simp[] >> qexists `f` >> simp[]
QED
