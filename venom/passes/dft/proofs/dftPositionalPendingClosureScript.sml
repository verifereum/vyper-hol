Theory dftPositionalPendingClosure
Ancestors
  dftPositionalPendingGas dftPositionalSegment dftPositionalStep
  dftPositionalReturn dftOccurrenceMachine dftOccurrenceReplay
  dftOpenMachine dftOpenErase dftOriginalRuntime dftPositionalPhase
  dftOccurrenceSuspended dftPositionalEdit dftPositionalRuntime
  dftPositionalGasSegment dftPositionalGasCall dftPositionalGasReturn
  contextRawReachable venomExecSemantics venomInst venomState list arithmetic

Definition dft_pending_segment_hits_def:
  dft_pending_segment_hits C w a l inst addr =
    SUM (GENLIST (\j. if dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j l) then 1 else 0) a)
End

Definition dft_pending_ledger_hits_def:
  dft_pending_ledger_hits B inst addr =
    LENGTH (FILTER (\e. e = (inst,addr)) B)
End

Definition pending_segment_account_def:
  pending_segment_account C D w a b l r B B' <=>
    (!inst addr.
      dft_pending_segment_hits C w a l inst addr +
        dft_pending_ledger_hits B inst addr =
      dft_pending_segment_hits D w b r inst addr +
        dft_pending_ledger_hits B' inst addr) /\
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) +
      dft_occ_count r + LENGTH B =
    dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) +
      dft_occ_count l + LENGTH B' /\
    (!j f inst s. j < a /\
      dft_open_observe f inst s
        (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      inst_mem_ranges inst s <> [] ==>
      ?k g t. k < b /\ dft_pos_functions C D f g /\
        dft_open_observe g inst t
          (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s) /\
    (!k g inst t. k < b /\
      dft_open_observe g inst t
        (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      inst_mem_ranges inst t <> [] ==>
      ?j f s. j < a /\ dft_pos_functions C D f g /\
        dft_open_observe f inst s
          (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s)
End

Theorem dft_pending_segment_hits_small[simp]:
  dft_pending_segment_hits C w 0 l inst addr = 0 /\
  dft_pending_segment_hits C w 1 l inst addr =
    (if dft_occ_gas_event inst addr l then 1 else 0) /\
  dft_pending_segment_hits C w 2 l inst addr =
    (if dft_occ_gas_event inst addr l then 1 else 0) +
    (if dft_occ_gas_event inst addr (dft_occ_oracle_next w C l) then 1 else 0)
Proof
  simp[dft_pending_segment_hits_def, GENLIST, SUM]
QED

Theorem dft_pending_ledger_hits_small[simp]:
  dft_pending_ledger_hits [] inst addr = 0 /\
  dft_pending_ledger_hits (e::B) inst addr =
    (if e = (inst,addr) then 1 else 0) + dft_pending_ledger_hits B inst addr /\
  dft_pending_ledger_hits (B ++ B') inst addr =
    dft_pending_ledger_hits B inst addr + dft_pending_ledger_hits B' inst addr
Proof
  simp[dft_pending_ledger_hits_def, FILTER_APPEND_DISTRIB] >>
  Cases_on `e = (inst,addr)` >> simp[]
QED

Theorem dft_pending_account_zero:
  pending_segment_account C D w 0 0 l r B B
Proof simp[pending_segment_account_def, ADD_COMM]
QED

Theorem dft_pending_account_one_transfer:
  dft_pos_segment_account C D w 1 1 l r /\
  dft_occ_count (dft_occ_oracle_next w C l) + dft_occ_count r =
    dft_occ_count (dft_occ_oracle_next w D r) + dft_occ_count l ==>
  pending_segment_account C D w 1 1 l r B B
Proof
  simp[dft_pos_segment_account_def, pending_segment_account_def] >>
  rpt strip_tac >> simp[]
QED

Theorem dft_pending_account_phase_transfer:
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs' H'
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  dft_pos_pending_gas_events zs ++ H = dft_pos_pending_gas_events zs' ++ H' /\
  dft_pos_segment_account C D w 1 1 l r ==>
  pending_segment_account C D w 1 1 l r
    (dft_pos_pending_gas_events zs ++ H) (dft_pos_pending_gas_events zs' ++ H')
Proof
  strip_tac >>
  `dft_occ_count l = dft_occ_count r +
      LENGTH (dft_pos_pending_gas_events zs ++ H) /\
   dft_occ_count (dft_occ_oracle_next w C l) =
     dft_occ_count (dft_occ_oracle_next w D r) +
      LENGTH (dft_pos_pending_gas_events zs' ++ H')` by
    (fs[dft_pos_pending_aligned_phase_def] >>
     every_drule dft_pos_pending_gas_phase_count >> simp[]) >>
  `LENGTH (dft_pos_pending_gas_events zs ++ H) =
   LENGTH (dft_pos_pending_gas_events zs' ++ H')` by metis_tac[] >>
  gvs[] >> irule dft_pending_account_one_transfer >> simp[]
QED

Theorem dft_pending_enter_account:
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR ==>
  pending_segment_account C D w 1 1 l r B B
Proof
  strip_tac >>
  `dft_pos_segment_account C D w 1 1 l r` by
    (irule dft_pos_enter_account >> metis_tac[]) >>
  `dft_occ_count (dft_occ_oracle_next w C l) = nL /\
   dft_occ_count (dft_occ_oracle_next w D r) = nR` by
    metis_tac[dft_pos_enter_count] >>
  irule dft_pending_account_one_transfer >> gvs[dft_occ_count_def]
QED

Theorem dft_pending_enter_success:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb g.fn_blocks = SOME bb' /\
  eval_phis s bb.bb_instructions = OK sp /\
  eval_phis s bb'.bb_instructions = OK sp /\
  phi_prefix_length bb.bb_instructions = phi_prefix_length bb'.bb_instructions /\
  dft_pos_slot C D j k f g bb bb' /\
  ~(j = fi /\ k = bi /\ phi_prefix_length bb.bb_instructions = SUC (LENGTH pre)) ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH zs /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r /\
   dft_pos_pending_saved zs l.dft_occ_saved` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `(ls = [] ==> l.dft_occ_saved = []) /\
   (rs = [] ==> r.dft_occ_saved = [])` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def] >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >>
  qexistsl [`j`,`k`] >> simp[]
QED

Theorem dft_pending_plain_call_success:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  ~(j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm D.ctx_functions = SOME callee' /\
  dft_pos_functions C D callee callee' /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\ setup_callee callee' args s = SOME cs ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH zs /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r /\
   dft_pos_pending_saved zs l.dft_occ_saved` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `dft_pos_pending_gas_frame w C D fi bi pre gas call post NONE
    (DftCaller f 0 bb inst s) (DftCaller g 0 bb' inst s)` by
    (simp[dft_pos_pending_gas_frame_def] >> irule dft_pos_plain_frame >> metis_tac[]) >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_invoke_def,
    dft_erase_def, dft_fill_frame_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_pending_gas_stack_def, dft_pos_pending_gas_events_def,
    dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pending_plain_return_success:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H l r /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 bb' inst s::rs) nR /\
  dft_restore inst.inst_outputs ret cs s = SOME a ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `dft_pos_pending_gas_frame w C D fi bi pre gas call post NONE
     lf (DftCaller g 0 bb' inst s) /\
   dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_saved = r.dft_occ_saved /\
   LENGTH l.dft_occ_saved = SUC (LENGTH zs) /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r /\
   dft_pos_pending_saved (NONE::zs) l.dft_occ_saved` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
       dft_pos_pending_gas_stack_def, dft_pos_pending_gas_events_def] >> gvs[]) >>
  Cases_on `l.dft_occ_saved` >> gvs[] >> PairCases_on `h` >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  fs[dft_pos_pending_gas_frame_def, dft_pos_frame_def] >> gvs[] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b
      (a with vs_inst_idx := SUC s.vs_inst_idx)) ls
        (nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H);
      dft_occ_path := h0; dft_occ_visit := h1; dft_occ_saved := t|>` by
    (irule dft_suspend_pop >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt g 0 bb'
      (a with vs_inst_idx := SUC s.vs_inst_idx)) rs nR;
      dft_occ_path := h0; dft_occ_visit := h1; dft_occ_saved := t|>` by
    (irule dft_suspend_pop >> simp[]) >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pending_at_ordinary:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/ s.vs_inst_idx <> LENGTH pre) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH zs /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r /\
   dft_pos_pending_saved zs l.dft_occ_saved` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `dft_pos_functions C D f g` by
    (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `(ls = [] ==> l.dft_occ_saved = []) /\
   (rs = [] ==> r.dft_occ_saved = [])` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  `!fr. dft_fill_frame 0 (dft_fill_frame 1 fr) = dft_fill_frame 0 fr` by
    (Cases >> simp[dft_fill_frame_def]) >>
  Cases_on `step_inst_base inst s` >- suspend "ok" >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
    dft_open_continue_def, dft_erase_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >> metis_tac[]
QED

Resume dft_pending_at_ordinary[ok]:
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `v.vs_halted` >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
        dft_open_continue_def, dft_erase_def, MAP_MAP_o, combinTheory.o_DEF,
        dft_occ_update_def, SF ETA_ss] >>
      simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
        dft_pos_control_def] >>
      Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >> metis_tac[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_deliver_def,
    dft_open_continue_def, dft_erase_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >> metis_tac[]
QED
Finalise dft_pending_at_ordinary

Theorem dft_pending_at_gas:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/ SUC s.vs_inst_idx <> SUC (LENGTH pre)) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [u] ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH zs /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r /\
   dft_pos_pending_saved zs l.dft_occ_saved` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `(ls = [] ==> l.dft_occ_saved = []) /\
   (rs = [] ==> r.dft_occ_saved = [])` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 bb
      ((update_var u (w (l.dft_occ_path ++ [(l.dft_occ_visit,inst.inst_id)])) s)
        with vs_inst_idx := SUC s.vs_inst_idx)) ls (SUC nL);
      dft_occ_saved := if ls = [] then [] else l.dft_occ_saved|>` by
    (qpat_assum `l.dft_occ_core = _`
       (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_one_step) >>
     simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt g 0 bb'
      ((update_var u (w (r.dft_occ_path ++ [(r.dft_occ_visit,inst.inst_id)])) s)
        with vs_inst_idx := SUC s.vs_inst_idx)) rs (SUC nR);
      dft_occ_saved := if rs = [] then [] else r.dft_occ_saved|>` by
    (qpat_assum `r.dft_occ_core = _`
       (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_one_step) >>
     simp[]) >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def, update_var_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[] >> metis_tac[]
QED

Theorem dft_pending_at_outside_account:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs' H'
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  dft_pos_pending_gas_events zs ++ H = dft_pos_pending_gas_events zs' ++ H' ==>
  pending_segment_account C D w 1 1 l r
    (dft_pos_pending_gas_events zs ++ H) (dft_pos_pending_gas_events zs' ++ H')
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  irule dft_pending_account_phase_transfer >>
  `l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `dft_pos_segment_account C D w 1 1 l r` by
    (irule dft_pos_at_outside_account >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dft_pending_done_account:
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR ==>
  pending_segment_account C D w 1 1 l r B B
Proof
  strip_tac >> irule dft_pending_account_one_transfer >>
  `dft_pos_segment_account C D w 1 1 l r` by
    (irule dft_pos_done_one_account >> metis_tac[]) >>
  simp[] >> metis_tac[dftRecursiveFixedSegmentTheory.dft_fixed_done_count, ADD_COMM]
QED

Theorem dft_pending_plain_call_runtime:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  ~(j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `?callee'. lookup_function nm D.ctx_functions = SOME callee' /\
     dft_pos_functions C D callee callee'` by
    (metis_tac[dft_pos_edit_function_lookup, optionTheory.OPTREL_def,
       optionTheory.NOT_SOME_NONE, optionTheory.option_case_def]) >>
  `setup_callee callee' args s = SOME cs` by
    metis_tac[dft_pos_edit_setup] >>
  irule dft_pending_plain_call_success >> metis_tac[]
QED

Theorem dft_pending_enter_runtime:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb g.fn_blocks = SOME bb' /\
  eval_phis s bb.bb_instructions = OK sp /\
  dft_pos_slot C D j k f g bb bb' /\
  ~(j = fi /\ k = bi /\ phi_prefix_length bb.bb_instructions = SUC (LENGTH pre)) ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  pending_segment_account C D w 1 1 l r B B
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `dft_pos_blocks C D f g bb bb'` by
    (fs[dft_pos_slot_def, dft_pos_blocks_def] >> metis_tac[]) >>
  `eval_phis s bb.bb_instructions = eval_phis s bb'.bb_instructions /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length bb'.bb_instructions` by
    (irule dft_pos_edit_block_phis >> fs[dft_pos_runtime_ready_def] >> metis_tac[]) >>
  conj_tac >- (irule dft_pending_enter_success >> metis_tac[]) >>
  irule dft_pending_enter_account >> metis_tac[]
QED

Theorem dft_pending_plain_return:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H l r /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 bb' inst s::rs) nR /\
  dft_restore inst.inst_outputs ret cs s = SOME a ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  pending_segment_account C D w 1 1 l r
    (dft_pos_pending_gas_events (NONE::zs) ++ H)
    (dft_pos_pending_gas_events zs ++ H)
Proof
  strip_tac >> conj_tac
  >- (irule dft_pending_plain_return_success >> metis_tac[]) >>
  simp[dft_pos_pending_gas_events_def] >>
  irule dft_pending_done_account >> metis_tac[]
QED

Theorem dft_pending_at_outside_instruction:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode = GAS ==> ?u. inst.inst_outputs = [u]) ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  pending_segment_account C D w 1 1 l r
    (dft_pos_pending_gas_events zs ++ H) (dft_pos_pending_gas_events zs ++ H)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction bb' s.vs_inst_idx = SOME inst` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  `dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
    (Cases_on `inst.inst_opcode = GAS`
     >- (irule dft_pending_at_gas >> simp[] >> metis_tac[]) >>
     irule dft_pending_at_ordinary >> metis_tac[]) >>
  simp[] >> irule dft_pending_at_outside_account >> metis_tac[]
QED

Theorem dft_pending_at_outside_call:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  pending_segment_account C D w 1 1 l r
    (dft_pos_pending_gas_events zs ++ H)
    (dft_pos_pending_gas_events (NONE::zs) ++ H)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction bb' s.vs_inst_idx = SOME inst` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  `dft_pos_pending_aligned_phase w C D fi bi pre gas call post (NONE::zs) H
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
    (irule dft_pending_plain_call_runtime >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule dft_pending_at_outside_account >>
  conj_tac >- simp[dft_pos_pending_gas_events_def] >> metis_tac[]
QED

Theorem dft_pending_phase_count_balance:
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs' H'
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (FUNPOW (dft_occ_oracle_next w D) b r) ==>
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) +
    dft_occ_count r + LENGTH (dft_pos_pending_gas_events zs ++ H) =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) +
    dft_occ_count l + LENGTH (dft_pos_pending_gas_events zs' ++ H')
Proof
  strip_tac >>
  `dft_occ_count l = dft_occ_count r +
      LENGTH (dft_pos_pending_gas_events zs ++ H) /\
   dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) =
     dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) +
      LENGTH (dft_pos_pending_gas_events zs' ++ H')` by
    (fs[dft_pos_pending_aligned_phase_def] >>
     every_drule dft_pos_pending_gas_phase_count >> simp[]) >>
  decide_tac
QED

Theorem dft_pending_gas_event_unique:
  dft_occ_gas_event gas addr c ==>
  (dft_occ_gas_event inst addr' c <=> inst = gas /\ addr' = addr)
Proof
  simp[dft_occ_gas_event_def] >>
  metis_tac[dft_occ_event_deterministic]
QED

Theorem dft_pending_event_no_memory:
  dft_occ_event inst addr c /\
  (inst.inst_opcode = GAS \/ inst.inst_opcode = INVOKE) ==>
  !f x s. dft_open_observe f x s c.dft_occ_core ==> inst_mem_ranges x s = []
Proof
  simp[dft_occ_event_def, dft_open_observe_def] >> rpt strip_tac >> gvs[] >>
  simp[unitMemInvTheory.inst_mem_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem dft_pending_call_event_not_gas:
  dft_occ_event call addr c /\ call.inst_opcode = INVOKE ==>
  ~dft_occ_gas_event inst addr' c
Proof
  simp[dft_occ_gas_event_def, dft_occ_event_def] >> rpt strip_tac >> gvs[] >>
  strip_tac >> gvs[]
QED

Theorem dft_pending_entry_event_account:
  dft_occ_gas_event gas addr l /\
  dft_occ_event call ca (dft_occ_oracle_next w C l) /\
  dft_occ_event call ca r /\ call.inst_opcode = INVOKE /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) +
    dft_occ_count r + LENGTH B =
  dft_occ_count (dft_occ_oracle_next w D r) + dft_occ_count l + LENGTH ((gas,addr)::B) ==>
  pending_segment_account C D w 2 1 l r B ((gas,addr)::B)
Proof
  strip_tac >>
  `!inst ad. dft_occ_gas_event inst ad l <=> inst = gas /\ ad = addr` by
    metis_tac[dft_pending_gas_event_unique] >>
  `!inst ad. ~dft_occ_gas_event inst ad (dft_occ_oracle_next w C l) /\
             ~dft_occ_gas_event inst ad r` by
    metis_tac[dft_pending_call_event_not_gas] >>
  `!f x s. dft_open_observe f x s l.dft_occ_core ==> inst_mem_ranges x s = []` by
    (fs[dft_occ_gas_event_def] >> metis_tac[dft_pending_event_no_memory]) >>
  `!f x s. dft_open_observe f x s (dft_occ_oracle_next w C l).dft_occ_core ==>
      inst_mem_ranges x s = []` by
    (metis_tac[dft_pending_event_no_memory]) >>
  `!f x s. dft_open_observe f x s r.dft_occ_core ==> inst_mem_ranges x s = []` by
    (metis_tac[dft_pending_event_no_memory]) >>
  simp[pending_segment_account_def] >> conj_tac
  >- (simp[EQ_SYM_EQ]) >>
  conj_tac
  >- (rpt strip_tac >> `j = 0 \/ j = 1` by decide_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem dft_pending_crossing_enter:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_slot C D fi bi f g b b' /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  ~MEM v call.inst_outputs /\ s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  eval_operands ops s = SOME args /\ setup_callee calleeR args s = SOME cs ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) H
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  pending_segment_account C D w 2 1 l r (dft_pos_pending_gas_events zs ++ H)
    (dft_pos_pending_gas_events
      (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) ++ H)
Proof
  strip_tac >>
  `dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) H
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r)` by
    (irule dft_pos_pending_aligned_enter >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `b.bb_instructions = pre ++ [gas;call] ++ post /\
   b'.bb_instructions = pre ++ [call;gas] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  `l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit` by
    (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `dft_occ_gas_event gas (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) l /\
   dft_occ_event call (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)])
     (dft_occ_oracle_next w C l) /\
   dft_occ_event call (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)]) r` by
    (irule dft_pos_gas_call_events >> metis_tac[]) >>
  `dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) +
    dft_occ_count r + LENGTH (dft_pos_pending_gas_events zs ++ H) =
   dft_occ_count (dft_occ_oracle_next w D r) + dft_occ_count l +
    LENGTH (dft_pos_pending_gas_events
      (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) ++ H)` by
    (fs[dft_pos_pending_aligned_phase_def] >>
     every_drule dft_pos_pending_gas_phase_count >> simp[] >> decide_tac) >>
  simp[dft_pos_pending_gas_events_def] >>
  irule dft_pending_entry_event_account >>
  fs[dft_pos_pending_gas_events_def] >> metis_tac[]
QED

Theorem dft_pending_return_event_account:
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR /\
  dft_occ_gas_event gas addr (dft_occ_oracle_next w D r) /\
  dft_occ_count (dft_occ_oracle_next w C l) +
    dft_occ_count r + LENGTH ((gas,addr)::B) =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 2 r) + dft_occ_count l + LENGTH B ==>
  pending_segment_account C D w 1 2 l r ((gas,addr)::B) B
Proof
  strip_tac >>
  `!inst ad. dft_occ_gas_event inst ad (dft_occ_oracle_next w D r) <=>
    inst = gas /\ ad = addr` by
    metis_tac[dft_pending_gas_event_unique] >>
  `!f x s. dft_open_observe f x s (dft_occ_oracle_next w D r).dft_occ_core ==>
    inst_mem_ranges x s = []` by
    (fs[dft_occ_gas_event_def] >> metis_tac[dft_pending_event_no_memory]) >>
  `!inst ad. ~dft_occ_gas_event inst ad l /\ ~dft_occ_gas_event inst ad r` by
    simp[dft_occ_gas_event_def, dft_occ_event_def] >>
  simp[pending_segment_account_def] >> conj_tac
  >- simp[EQ_SYM_EQ] >> conj_tac
  >- (fs[] >> decide_tac) >> conj_tac
  >- simp[dft_open_observe_def] >>
  rpt strip_tac >> `k = 0 \/ k = 1` by decide_tac >> gvs[] >>
  fs[dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_pending_crossing_return:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 b' call s::rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (SOME (gas,addr)::zs) H l r /\
  dft_restore call.inst_outputs ret cs s = SOME a ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r) /\
  pending_segment_account C D w 1 2 l r
    (dft_pos_pending_gas_events (SOME (gas,addr)::zs) ++ H)
    (dft_pos_pending_gas_events zs ++ H)
Proof
  strip_tac >>
  `dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r)` by
    (irule dft_pos_pending_aligned_return >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `dft_occ_gas_event gas addr (dft_occ_oracle_next w D r)` by
    (`addr = path ++ [(visit,gas.inst_id)] /\
      dft_pos_pending_gas_frame w C D fi bi pre gas call post
        (SOME (gas,addr)) lf (DftCaller g 0 b' call s) /\
      dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
      r.dft_occ_saved = (path,visit)::saved /\ LENGTH saved = LENGTH zs` by
       (fs[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
           dft_pos_pending_gas_stack_def] >> gvs[]) >>
     `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
       metis_tac[dft_pos_pending_gas_stack_fill] >>
     `(ls = [] ==> saved = []) /\ (rs = [] ==> saved = [])` by
       metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
     fs[dft_pos_pending_gas_frame_def] >> gvs[] >>
     qpat_assum `s.vs_inst_idx = LENGTH pre`
       (fn th => drule_all (REWRITE_RULE [th] dft_pos_gas_call_return_success)) >>
     disch_then (qspecl_then [`D`,`C`] mp_tac) >> simp[]) >>
  `dft_occ_count (dft_occ_oracle_next w C l) + dft_occ_count r +
    LENGTH (dft_pos_pending_gas_events (SOME (gas,addr)::zs) ++ H) =
   dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 2 r) + dft_occ_count l +
    LENGTH (dft_pos_pending_gas_events zs ++ H)` by
    (fs[dft_pos_pending_aligned_phase_def] >>
     every_drule dft_pos_pending_gas_phase_count >> simp[] >> decide_tac) >>
  simp[dft_pos_pending_gas_events_def] >>
  irule dft_pending_return_event_account >>
  fs[dft_pos_pending_gas_events_def] >> metis_tac[]
QED
