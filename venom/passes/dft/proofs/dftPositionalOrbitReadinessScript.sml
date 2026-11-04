Theory dftPositionalOrbitReadiness
Ancestors
  dftPositionalOrbit dftRecursiveOrbitReadiness dftPositionalRuntime
  dftPositionalPhase dftOriginalRuntime venomExecSemantics venomInst
  venomWf list finite_map pred_set

Theorem dft_original_pos_orbit_ready:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_original_label_ready C L l /\
  dft_pos_phase C D fi bi pre x call post l r /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i lbl. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label lbl) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> lbl IN FDOM L) ==>
  dft_pos_orbit_ready fi bi pre x call post w C D Corig Dorig l r
Proof
  strip_tac >>
  `!j fn s ls n.
    (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
      DftOpen (DftAt fn 0 (EL bi (EL fi C.ctx_functions).fn_blocks) s) ls n /\
    s.vs_inst_idx = LENGTH pre ==>
    ?f b. dft_recursive_crossing_ready f b
      (EL bi (EL fi C.ctx_functions).fn_blocks) pre x call post s` by
    (rpt strip_tac >> irule dft_original_recursive_orbit_ready >>
     fs[dft_pos_runtime_ready_def] >> metis_tac[]) >>
  simp[dft_pos_orbit_ready_def] >> rpt strip_tac >>
  fs[dft_pos_slot_def] >> metis_tac[]
QED

Theorem dft_original_pos_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_original_label_ready C L l /\
  dft_pos_phase C D fi bi pre x call post l r /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i lbl. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label lbl) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> lbl IN FDOM L) ==>
  ?A B. dft_pos_orbit_cuts fi bi pre x call post w C D l r A B
Proof
  strip_tac >> irule dft_pos_orbit_segments >>
  drule_all dft_original_pos_orbit_ready >> metis_tac[]
QED
