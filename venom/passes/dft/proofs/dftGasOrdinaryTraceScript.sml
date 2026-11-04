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

Theorem dft_mixed_gas_next:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] ==>
  dft_occ_oracle_next w C c = c with
    <| dft_occ_core := DftOpen (DftAt fn 0 bb
       ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
         with vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC n);
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[dftOccurrenceReplayTheory.dft_occ_oracle_next_def, dft_occ_next_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       is_terminator_def, dft_erase_def, dft_occ_update_def,
       dftOccurrenceReplayTheory.dft_occ_address_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

(* Full-record successors retain the occurrence address and saved callers. *)
Theorem dft_mixed_gas_first_success:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  FUNPOW (dft_occ_oracle_next w C) 2 c = c with
    <| dft_occ_core := DftOpen (DftAt fn 0 bb
      ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)
        with vs_inst_idx := SUC (SUC s.vs_inst_idx))) stack (SUC n);
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >>
  `step_inst_base inst (update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s) =
   OK (update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)` by
    metis_tac[dftMixedResidualProbeTheory.dft_gas_value_ordinary_frame] >>
  `step_inst_base inst ((update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
       with vs_inst_idx := SUC s.vs_inst_idx) =
   OK ((update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)
       with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  drule_all dft_mixed_gas_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[FUNPOW_2] >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
  `mid.dft_occ_core = DftOpen (DftAt fn 0 bb
     ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
       with vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC n)` by
    simp[Abbr `mid`] >>
  qpat_assum `mid.dft_occ_core = _` (mp_then Any mp_tac dft_occ_ordinary_next) >>
  simp[venomExecSemanticsTheory.update_var_inst_idx] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  simp[Abbr `mid`, venomExecSemanticsTheory.update_var_inst_idx] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

Theorem dft_mixed_gas_second_success:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  FUNPOW (dft_occ_oracle_next w C) 2 c = c with
    <| dft_occ_core := DftOpen (DftAt fn 0 bb
      ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)
        with vs_inst_idx := SUC (SUC s.vs_inst_idx))) stack (SUC n);
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >> drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[FUNPOW_2] >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
  `mid.dft_occ_core = DftOpen (DftAt fn 0 bb
      (t with vs_inst_idx := SUC s.vs_inst_idx)) stack n` by simp[Abbr `mid`] >>
  qpat_assum `mid.dft_occ_core = _`
    (mp_then Any mp_tac dft_mixed_gas_next) >>
  simp[Abbr `mid`] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  simp[venomStateTheory.update_var_def] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

Theorem dft_mixed_safe_fill:
  dft_edit_safe c /\ c.dft_occ_core = DftOpen ctl stack n ==>
  MAP (dft_fill_frame 0) stack = stack
Proof
  strip_tac >> fs[dft_edit_safe_def, dft_edit_safe_core_def] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  `dft_edit_frame_safe (EL x stack)` by metis_tac[EVERY_EL] >>
  Cases_on `EL x stack` >> gvs[dft_edit_frame_safe_def, dft_fill_frame_def]
QED

Theorem dft_mixed_fill_edit_stack:
  MAP (dft_fill_frame 0) stack = stack ==>
  MAP (dft_fill_frame 0) (MAP (dft_edit_frame fm bm) stack) =
    MAP (dft_edit_frame fm bm) stack
Proof
  `!f. dft_fill_frame 0 (dft_edit_frame fm bm f) =
       dft_edit_frame fm bm (dft_fill_frame 0 f)` by
    (Cases >> simp[dft_fill_frame_def, dft_edit_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem dft_mixed_gas_first_sync_success:
  q.bb_instructions = pre ++ [gas;inst] ++ post /\
  dft_ordinary_sync q pre gas inst post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  dft_ordinary_sync q pre gas inst post
    (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (FUNPOW (dft_occ_oracle_next w
      (dft_gas_edit_ctx q pre gas inst post C)) 2 d)
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `MAP (dft_fill_frame 0) stack = stack` by
    (irule dft_mixed_safe_fill >> qexistsl_tac [`c`, `DftAt fn 0 q s`, `n`] >>
     fs[dft_ordinary_sync_def]) >>
  drule dft_mixed_fill_edit_stack >>
  disch_then (qspecl_then [`dft_gas_edit_fn q pre gas inst post`,
    `dft_gas_edit_block q pre gas inst post`] assume_tac) >>
  drule_all dft_mixed_gas_first_success >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_mixed_gas_second_success >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx q pre gas inst post C`] assume_tac) >>
  simp[dft_ordinary_sync_def] >> conj_tac
  >- (fs[dft_ordinary_sync_def] >> metis_tac[dft_gas_edit_safe_next, FUNPOW_2]) >>
  conj_tac >- simp[dft_edit_cut_def] >>
  fs[dft_ordinary_sync_def, dft_edit_occ_def, dft_edit_core_def,
     dft_edit_control_def] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

Theorem dft_mixed_gas_second_sync_success:
  q.bb_instructions = pre ++ [inst;gas] ++ post /\
  dft_ordinary_sync q pre inst gas post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  dft_ordinary_sync q pre inst gas post
    (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (FUNPOW (dft_occ_oracle_next w
      (dft_gas_edit_ctx q pre inst gas post C)) 2 d)
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `MAP (dft_fill_frame 0) stack = stack` by
    (irule dft_mixed_safe_fill >> qexistsl_tac [`c`, `DftAt fn 0 q s`, `n`] >>
     fs[dft_ordinary_sync_def]) >>
  drule dft_mixed_fill_edit_stack >>
  disch_then (qspecl_then [`dft_gas_edit_fn q pre inst gas post`,
    `dft_gas_edit_block q pre inst gas post`] assume_tac) >>
  drule_all dft_mixed_gas_second_success >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_mixed_gas_first_success >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx q pre inst gas post C`] assume_tac) >>
  simp[dft_ordinary_sync_def] >> conj_tac
  >- (fs[dft_ordinary_sync_def] >> metis_tac[dft_gas_edit_safe_next, FUNPOW_2]) >>
  conj_tac >- simp[dft_edit_cut_def] >>
  fs[dft_ordinary_sync_def, dft_edit_occ_def, dft_edit_core_def,
     dft_edit_control_def] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

Theorem dft_mixed_gas_first_abort:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_core =
    DftOpen (DftDone (Abort a
      ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)
        with vs_inst_idx := SUC s.vs_inst_idx))) stack (SUC n)
Proof
  strip_tac >>
  `!y. MEM (Var y) inst.inst_operands ==> v <> y` by metis_tac[] >>
  drule_all dftCommutationTheory.step_inst_base_frame >>
  disch_then (qspecl_then [`s`,
    `w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])`] mp_tac) >>
  simp[dftCommutationTheory.map_result_state_def] >> strip_tac >>
  `step_inst_base inst ((update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
       with vs_inst_idx := SUC s.vs_inst_idx) =
   Abort a ((update_var v
     (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) t)
       with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  drule_all dft_mixed_gas_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[FUNPOW_2] >>
  qmatch_goalsub_abbrev_tac `(dft_occ_oracle_next w C mid).dft_occ_core` >>
  `mid.dft_occ_core = DftOpen (DftAt fn 0 bb
     ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
       with vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC n)` by
    simp[Abbr `mid`] >>
  qpat_assum `mid.dft_occ_core = _` (mp_then Any mp_tac dft_occ_ordinary_abort) >>
  simp[venomExecSemanticsTheory.update_var_inst_idx] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >> simp[]
QED

Theorem dft_mixed_abort_endpoint:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR m /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w ctxL) 3 l)
    (FUNPOW (dft_occ_oracle_next w ctxR) 2 r)
Proof
  strip_tac >> drule_all dft_mixed_gas_first_abort >>
  disch_then (qspecl_then [`w`, `ctxL`] assume_tac) >>
  drule_all dft_occ_ordinary_abort >>
  disch_then (qspecl_then [`w`, `ctxR`] assume_tac) >>
  `?u. (FUNPOW (dft_occ_oracle_next w ctxL) 3 l).dft_occ_core =
     DftOpen (DftDone (Abort a u)) [] (SUC n)` by
    (qpat_assum `(FUNPOW _ 2 l).dft_occ_core = _`
       (mp_then Any mp_tac dft_occ_abort_clear) >>
     disch_then (qspecl_then [`w`, `ctxL`] mp_tac) >>
     `3 = SUC 2` by decide_tac >> metis_tac[FUNPOW_SUC]) >>
  ` (FUNPOW (dft_occ_oracle_next w ctxR) 2 r).dft_occ_core =
     DftOpen (DftDone (Abort a t)) [] m` by
    (simp[FUNPOW_2] >> irule dft_occ_abort_clear >> metis_tac[]) >>
  simp[dft_gas_ordinary_stopped_def] >> metis_tac[]
QED

Theorem dft_mixed_gas_first_events:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\ inst.inst_opcode <> GAS ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
     (FUNPOW (dft_occ_oracle_next w C) h c)) <=>
   i = gas /\ a = c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])
Proof
  strip_tac >> drule_all dft_mixed_gas_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  `!h:num. h < 2 <=> h = 0 \/ h = 1` by decide_tac >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM, FUNPOW] >>
  gvs[dft_occ_gas_event_def,
      dft_occ_event_def,
      dftOccurrenceReplayTheory.dft_occ_address_def,
      venomExecSemanticsTheory.update_var_inst_idx] >> metis_tac[]
QED

Theorem dft_mixed_success_gas_cover:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR m /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  dft_segment_gas_cover w ctxL ctxR l r 2 2
Proof
  strip_tac >>
  `!i a. (?h. h < 2 /\ dft_occ_gas_event i a
     (FUNPOW (dft_occ_oracle_next w ctxL) h l)) <=>
     i = gas /\ a = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]` by
    (rpt gen_tac >> irule dft_mixed_gas_first_events >> metis_tac[]) >>
  `!i a. (?h. h < 2 /\ dft_occ_gas_event i a
     (FUNPOW (dft_occ_oracle_next w ctxR) h r)) <=>
     i = gas /\ a = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]` by
    (rpt gen_tac >> irule dft_ordinary_first_prefix_events >> metis_tac[]) >>
  simp[dft_segment_gas_cover_def] >> metis_tac[]
QED

Theorem dft_mixed_abort_gas_events:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR m /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  (!i addr. (?h. h < 3 /\ dft_occ_gas_event i addr
     (FUNPOW (dft_occ_oracle_next w ctxL) h l)) <=>
     i = gas /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) /\
  (!h i addr. h < 2 ==> ~dft_occ_gas_event i addr
     (FUNPOW (dft_occ_oracle_next w ctxR) h r))
Proof
  strip_tac >> drule_all dft_mixed_gas_first_abort >>
  disch_then (qspecl_then [`w`, `ctxL`] assume_tac) >>
  drule_all dft_occ_ordinary_abort >>
  disch_then (qspecl_then [`w`, `ctxR`] assume_tac) >>
  conj_tac
  >- (rpt gen_tac >>
      `!h:num. h < 3 <=> h < 2 \/ h = 2` by decide_tac >>
      simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      `~dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w ctxL) 2 l)` by
        metis_tac[dft_done_no_gas_event] >> simp[] >>
      irule dft_mixed_gas_first_events >> metis_tac[]) >>
  rpt strip_tac >> `h = 0 \/ h = 1` by decide_tac
  >- (gvs[FUNPOW] >> metis_tac[dft_at_no_gas_event]) >>
  gvs[FUNPOW] >> metis_tac[dft_done_no_gas_event]
QED
