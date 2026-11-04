Theory dftGasOrdinaryTrace
Ancestors
  dftOriginalOrbit dftOriginalRuntime dftOriginalOperands dftOriginalSegment
  dftOriginalScheduleRuntime dftProtectedRuntime dftOrdinaryEventTrace
  dftMixedCrossing dftMixedEventTrace dftOccurrenceOrdinaryClosure
  dftScheduleOrder dftCorrectness pred_set
  dftOccurrenceGasEdit dftOrdinarySwap dftScheduleEdits dftOccurrenceOrdinaryStop
  dftOccurrenceMachine dftOccurrenceOrdinaryEdit dftOpenMachine dftOpenErase venomInst list arithmetic

Definition dft_gas_ordinary_pair_def:
  dft_gas_ordinary_pair x y <=>
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    ((x.inst_opcode = GAS /\ y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE) \/
     (y.inst_opcode = GAS /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE))
End

Definition dft_original_gas_ordinary_environment_def:
  dft_original_gas_ordinary_environment Corig C L q pre x y post <=>
    dft_original_context Corig C /\
    q.bb_instructions = pre ++ [x;y] ++ post /\
    dft_gas_ordinary_pair x y /\ ~dft_must_order x y /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    x.inst_opcode <> ALLOCA /\ y.inst_opcode <> ALLOCA /\
    ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
    ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
    (!f b. dft_original_block f b q ==>
      schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) /\
    (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
      MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> l IN FDOM L)
End

(* Aborting cuts may have consumed different numbers of GAS readings. *)
Definition dft_gas_ordinary_stopped_def:
  dft_gas_ordinary_stopped c d <=>
    ?a s t n m.
      c.dft_occ_core = DftOpen (DftDone (Abort a s)) [] n /\
      d.dft_occ_core = DftOpen (DftDone (Abort a t)) [] m
End

Definition dft_gas_ordinary_endpoint_def:
  dft_gas_ordinary_endpoint q pre x y post c d <=>
    dft_ordinary_sync q pre x y post c d \/ dft_gas_ordinary_stopped c d
End

Theorem dft_gas_ordinary_outside_segment:
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_sync q pre x y post c d /\
  ~dft_edit_before q (LENGTH pre) c ==>
  dft_gas_ordinary_endpoint q pre x y post
    (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C) d) /\
  dft_original_label_ready C L (dft_occ_oracle_next w C c) /\
  dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
    (dft_gas_edit_ctx q pre x y post C) c d 1 1 /\
  dft_segment_gas_cover w C (dft_gas_edit_ctx q pre x y post C) c d 1 1
Proof
  strip_tac >>
  `q.bb_instructions = pre ++ [x;y] ++ post /\
   x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\ x.inst_opcode <> INVOKE` by
    (fs[dft_original_gas_ordinary_environment_def, dft_gas_ordinary_pair_def] >>
     metis_tac[is_pseudo_def]) >>
  conj_tac
  >- (simp[dft_gas_ordinary_endpoint_def] >> disj1_tac >>
      irule dft_ordinary_sync_outside >> simp[]) >>
  conj_tac
  >- (fs[dft_original_gas_ordinary_environment_def] >>
      metis_tac[dft_original_label_next]) >>
  conj_tac
  >- (irule dft_ordinary_sync_outside_cover >> simp[]) >>
  drule_all dft_ordinary_sync_outside_gas_cover >> simp[]
QED

(* A dropped event is tied to the crossed GAS instruction and to this
   activation, not to an arbitrary address exempted by the consumer. *)
Definition dft_mixed_segment_events_def:
  dft_mixed_segment_events w CL CR x y c d k j <=>
    dft_segment_gas_cover w CL CR c d k j \/
    (dft_gas_ordinary_stopped
      (FUNPOW (dft_occ_oracle_next w CL) k c)
      (FUNPOW (dft_occ_oracle_next w CR) j d) /\
     ((x.inst_opcode = GAS /\
       (!i a. (?h. h < k /\ dft_occ_gas_event i a
          (FUNPOW (dft_occ_oracle_next w CL) h c)) <=>
          i = x /\ a = c.dft_occ_path ++ [(c.dft_occ_visit,x.inst_id)]) /\
       (!h i a. h < j ==> ~dft_occ_gas_event i a
          (FUNPOW (dft_occ_oracle_next w CR) h d))) \/
      (y.inst_opcode = GAS /\
       (!i a. (?h. h < j /\ dft_occ_gas_event i a
          (FUNPOW (dft_occ_oracle_next w CR) h d)) <=>
          i = y /\ a = c.dft_occ_path ++ [(c.dft_occ_visit,y.inst_id)]) /\
       (!h i a. h < k ==> ~dft_occ_gas_event i a
          (FUNPOW (dft_occ_oracle_next w CL) h c)))))
End

Theorem dft_gas_ordinary_stopped_next:
  dft_gas_ordinary_stopped c d ==>
  dft_gas_ordinary_stopped (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w C' d)
Proof
  simp[dft_gas_ordinary_stopped_def] >> rpt strip_tac >>
  qexistsl_tac [`a`, `s`, `t`, `n`, `m`] >>
  metis_tac[dft_occ_abort_clear]
QED

Theorem dft_gas_ordinary_stopped_segment:
  dft_original_context Corig C /\ dft_original_label_ready C L c /\
  dft_gas_ordinary_stopped c d ==>
  dft_gas_ordinary_stopped (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w C' d) /\
  dft_original_label_ready C L (dft_occ_oracle_next w C c) /\
  dft_ordinary_prefix_cover fm w C C' c d 1 1 /\
  dft_mixed_segment_events w C C' x y c d 1 1
Proof
  strip_tac >> conj_tac
  >- metis_tac[dft_gas_ordinary_stopped_next] >>
  conj_tac >- metis_tac[dft_original_label_next] >>
  conj_tac
  >- fs[dft_gas_ordinary_stopped_def, dft_ordinary_prefix_cover_def,
        dft_open_observe_def] >>
  simp[dft_mixed_segment_events_def] >> disj1_tac >>
  fs[dft_gas_ordinary_stopped_def, dft_segment_gas_cover_def] >>
  metis_tac[dft_done_no_gas_event]
QED

Theorem dft_original_mixed_crossing_labels:
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n ==>
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels)
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ s.vs_labels = L` by
    (fs[dft_original_label_ready_def] >> metis_tac[dft_source_active_at]) >>
  `MEM q fn.fn_blocks` by
    (fs[dft_original_label_ready_def] >>
     drule_all dft_original_runtime_at_projection >> simp[]) >>
  `MEM x (fn_insts fn) /\ MEM y (fn_insts fn)` by
    (fs[dft_original_gas_ordinary_environment_def] >>
     simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     conj_tac >> qexists `q` >> simp[]) >>
  `x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE` by
    (fs[dft_original_gas_ordinary_environment_def, dft_gas_ordinary_pair_def] >>
     gvs[]) >>
  fs[dft_original_gas_ordinary_environment_def, dft_gas_ordinary_pair_def] >>
  metis_tac[]
QED

Theorem dft_original_mixed_crossing_operands:
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  inst_wf x /\ inst_wf y /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v)
Proof
  strip_tac >>
  `?f b. dft_original_block f b q /\ dft_original_cut f b q s` by
    (fs[dft_original_label_ready_def] >>
     drule_all dft_original_runtime_at_projection >> metis_tac[]) >>
  `?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ done` by
    (irule dft_original_crossing_cut >>
     fs[dft_original_gas_ordinary_environment_def] >> metis_tac[]) >>
  `MEM x b.bb_instructions /\ MEM y b.bb_instructions` by
    (drule dft_original_block_mem >>
     fs[dft_original_gas_ordinary_environment_def] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `inst_wf x /\ inst_wf y` by
    (fs[dft_original_block_def, dft_original_schedule_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all dft_original_mixed_crossing_labels >> strip_tac >> simp[] >>
  conj_tac
  >- (drule dft_original_first_operands >>
      disch_then (qspecl_then [`x`, `y::post`,
        `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions`, `done`] mp_tac) >>
      fs[dft_original_gas_ordinary_environment_def, APPEND_ASSOC]) >>
  rpt strip_tac >> irule dft_original_before_operands >>
  fs[dft_original_gas_ordinary_environment_def, dft_gas_ordinary_pair_def] >>
  metis_tac[]
QED

(* Non-call instructions do not inspect the function table. This is the
   context boundary needed to reuse local crossing equations. *)
Theorem dft_mixed_noninvoke_context:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> INVOKE ==>
  dft_occ_oracle_next w C c = dft_occ_oracle_next w C' c
Proof
  strip_tac >>
  simp[dftOccurrenceReplayTheory.dft_occ_oracle_next_def,
       dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def]
QED

Theorem dft_mixed_success_prefix_context:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME gas /\ gas.inst_opcode = GAS ==>
  FUNPOW (dft_occ_oracle_next w C) 2 c =
  FUNPOW (dft_occ_oracle_next w C') 2 c
Proof
  strip_tac >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C'`] assume_tac) >>
  simp[FUNPOW_2] >>
  irule dft_mixed_noninvoke_context >>
  qexistsl_tac [`bb`, `fn`, `gas`, `n`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`, `stack`] >> simp[]
QED

Theorem dft_mixed_distinct_output_lists[local]:
  !xs x y v. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    MEM x xs /\ MEM y xs /\ x <> y /\ MEM v x.inst_outputs ==>
    ~MEM v y.inst_outputs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem dft_original_mixed_outputs_disjoint:
  dft_original_block f b q /\ q.bb_instructions = pre ++ [x;y] ++ post /\
  dft_gas_ordinary_pair x y ==>
  !v. MEM v x.inst_outputs ==> ~MEM v y.inst_outputs
Proof
  strip_tac >>
  `ssa_form f /\ MEM b f.fn_blocks` by
    fs[dft_original_block_def, dft_original_schedule_def,
       venomWfTheory.wf_ssa_def] >>
  `MEM x b.bb_instructions /\ MEM y b.bb_instructions` by
    (drule dft_original_block_mem >> simp[] >> metis_tac[]) >>
  `MEM x (fn_insts f) /\ MEM y (fn_insts f)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     conj_tac >> qexists `b` >> simp[]) >>
  `x <> y` by (fs[dft_gas_ordinary_pair_def] >> metis_tac[]) >>
  fs[venomWfTheory.ssa_form_def] >>
  metis_tac[dft_mixed_distinct_output_lists]
QED

Theorem dft_original_mixed_operands_disjoint:
  dft_original_block f b q /\ q.bb_instructions = pre ++ [x;y] ++ post /\
  ~dft_must_order x y /\ ~is_pseudo x.inst_opcode ==>
  (!v. MEM v x.inst_outputs ==> ~MEM (Var v) y.inst_operands) /\
  (!v. MEM v y.inst_outputs ==> ~MEM (Var v) x.inst_operands)
Proof
  strip_tac >> conj_tac
  >- (fs[dft_must_order_def, inst_defs_def, inst_uses_def,
         DISJOINT_DEF, EXTENSION, MEM_operand_vars_iff] >> metis_tac[]) >>
  `!v. MEM (Var v) x.inst_operands ==> ~MEM v y.inst_outputs` by
    (gen_tac >> disch_tac >> irule dft_original_future_outputs_disjoint >>
     qexistsl_tac [`b`, `f`, `[]`, `post`, `pre`, `q`] >>
     fs[dft_original_block_def]) >>
  metis_tac[]
QED
