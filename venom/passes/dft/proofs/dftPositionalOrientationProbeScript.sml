Theory dftPositionalOrientationProbe
Ancestors
  dftPositionalOrientation dftPositionalOrbitReadiness dftOriginalRuntime
  dftPositionalPhase dftPositionalPendingClosure venomInst venomWf venomEffects dftScheduleOrder
  finite_map pred_set list

(* The exclusion and label readiness here are deliberately on D, the
   ordinary-first context. Static reversal alone does not supply them. *)
Theorem dft_reverse_ordinary_orbit_readiness_probe:
  D = dft_pos_edit_ctx fi bi pre call x post C /\
  dft_pos_runtime_ready C fi bi pre call x post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_original_label_ready D L r /\
  dft_pos_phase D C fi bi pre x call post r l /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i lbl. MEM fn D.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label lbl) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> lbl IN FDOM L) ==>
  dft_pos_orbit_ready fi bi pre x call post w D C Dorig Corig r l
Proof
  strip_tac >>
  `C = dft_pos_edit_ctx fi bi pre x call post D` by
    (irule dft_pos_edit_ctx_reverse >> metis_tac[]) >>
  `dft_pos_runtime_ready D fi bi pre x call post` by
    (irule dft_pos_runtime_ready_reverse >> metis_tac[]) >>
  irule dft_original_pos_orbit_ready >> metis_tac[]
QED

Theorem dft_no_invoke_invoke_edge_probe:
  x.inst_opcode = INVOKE /\ y.inst_opcode = INVOKE ==>
  dft_must_order x y
Proof
  simp[dft_must_order_def, read_effects_def, write_effects_def,
       all_effects_def, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

(* GAS has a total oracle update, so this reverse interface needs no
   ordinary-operand readiness. The annotated phase is still a premise. *)
Theorem dft_reverse_gas_call_closure_probe:
  D = dft_pos_edit_ctx fi bi pre call gas post C /\
  dft_pos_runtime_ready C fi bi pre call gas post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  ~MEM v call.inst_outputs /\
  dft_pos_pending_aligned_phase w D C fi bi pre gas call post zs H r l ==>
  ?a b zs' H'. 0 < a /\ a <= 2 /\ 0 < b /\ b <= 2 /\
    dft_pos_pending_aligned_phase w D C fi bi pre gas call post zs' H'
      (FUNPOW (dft_occ_oracle_next w D) a r)
      (FUNPOW (dft_occ_oracle_next w C) b l) /\
    pending_segment_account D C w a b r l
      (dft_pos_pending_gas_events zs ++ H)
      (dft_pos_pending_gas_events zs' ++ H') /\
    (!e. MEM e H ==> MEM e H')
Proof
  strip_tac >>
  `C = dft_pos_edit_ctx fi bi pre gas call post D` by
    (irule dft_pos_edit_ctx_reverse >> metis_tac[]) >>
  `dft_pos_runtime_ready D fi bi pre gas call post` by
    (irule dft_pos_runtime_ready_reverse >> metis_tac[]) >>
  irule dft_pending_bounded_closed_retired >> metis_tac[]
QED
