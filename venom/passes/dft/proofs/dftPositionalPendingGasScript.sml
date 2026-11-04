Theory dftPositionalPendingGas
Ancestors
  dftPositionalGasCall dftPositionalGasReturn dftPositionalPhase dftPositionalGasSegment
  dftOriginalRuntime dftOccurrenceMachine dftOccurrenceReplay dftOpenMachine dftOpenErase venomState list arithmetic

Definition dft_pos_pending_gas_frame_def:
  dft_pos_pending_gas_frame w C D fi bi pre gas call post z l r <=>
    case z of
      NONE => dft_pos_frame C D fi bi pre gas call post NONE l r
    | SOME (inst,addr) =>
        inst = gas /\
        (?f g b b' s v.
          dft_pos_slot C D fi bi f g b b' /\
          b.bb_instructions = pre ++ [gas;call] ++ post /\
          b'.bb_instructions = pre ++ [call;gas] ++ post /\
          gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
          call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
          ~MEM v call.inst_outputs /\ s.vs_inst_idx = LENGTH pre /\
          l = DftCaller f 0 b call
            ((update_var v (w addr) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
          r = DftCaller g 0 b' call s)
End

Definition dft_pos_pending_gas_stack_def:
  (dft_pos_pending_gas_stack w C D fi bi pre gas call post [] ls rs <=>
    ls = [] /\ rs = []) /\
  (dft_pos_pending_gas_stack w C D fi bi pre gas call post (z::zs) ls rs <=>
    ?l r lt rt. ls = l::lt /\ rs = r::rt /\
      dft_pos_pending_gas_frame w C D fi bi pre gas call post z l r /\
      dft_pos_pending_gas_stack w C D fi bi pre gas call post zs lt rt)
End

Definition dft_pos_pending_gas_events_def:
  (dft_pos_pending_gas_events [] = []) /\
  (dft_pos_pending_gas_events (NONE::zs) = dft_pos_pending_gas_events zs) /\
  (dft_pos_pending_gas_events (SOME z::zs) = z::dft_pos_pending_gas_events zs)
End

Definition dft_pos_pending_gas_phase_def:
  dft_pos_pending_gas_phase w C D fi bi pre gas call post zs H c d <=>
    ?ctl ctl' ls rs nL nR.
      c.dft_occ_core = DftOpen ctl ls nL /\
      d.dft_occ_core = DftOpen ctl' rs nR /\
      dft_pos_control C D fi bi pre ctl ctl' /\
      dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
      c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
      c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH zs /\
      nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
      dft_original_ready c /\ dft_original_ready d
End

Theorem dft_pos_pending_gas_root:
  dft_pos_functions C D f g /\
  c.dft_occ_core = DftOpen (DftEnter f 0 s) [] n /\
  d.dft_occ_core = DftOpen (DftEnter g 0 s) [] n /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = [] /\ d.dft_occ_saved = [] /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_pos_pending_gas_phase w C D fi bi pre gas call post [] [] c d
Proof
  strip_tac >>
  simp[dft_pos_pending_gas_phase_def, dft_pos_pending_gas_stack_def,
    dft_pos_pending_gas_events_def, dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_pending_gas_frame_fill:
  dft_pos_pending_gas_frame w C D fi bi pre gas call post z l r ==>
  dft_fill_frame 0 l = l /\ dft_fill_frame 0 r = r
Proof
  Cases_on `z` >> simp[dft_pos_pending_gas_frame_def] >-
    (simp[dft_pos_frame_def] >> rpt strip_tac >> gvs[dft_fill_frame_def]) >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >> gvs[dft_fill_frame_def]
QED

Theorem dft_pos_pending_gas_stack_fill:
  dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs ==>
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  qid_spec_tac `rs` >> qid_spec_tac `ls` >> Induct_on `zs` >>
  simp[dft_pos_pending_gas_stack_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[dft_pos_pending_gas_frame_fill]
QED

Theorem dft_pos_pending_gas_stack_length:
  dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs ==>
  LENGTH ls = LENGTH zs /\ LENGTH rs = LENGTH zs
Proof
  qid_spec_tac `rs` >> qid_spec_tac `ls` >> Induct_on `zs` >>
  simp[dft_pos_pending_gas_stack_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_pos_pending_gas_push_count[simp]:
  LENGTH (dft_pos_pending_gas_events (NONE::zs)) =
    LENGTH (dft_pos_pending_gas_events zs) /\
  LENGTH (dft_pos_pending_gas_events (SOME z::zs)) =
    SUC (LENGTH (dft_pos_pending_gas_events zs))
Proof simp[dft_pos_pending_gas_events_def]
QED

Theorem dft_pos_pending_gas_enter_phase:
  c.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  d.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR /\
  dft_pos_functions C D f g /\
  dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH zs /\
  nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_pos_pending_gas_phase w C D fi bi pre gas call post zs H c d
Proof
  strip_tac >> simp[dft_pos_pending_gas_phase_def, dft_pos_control_def] >>
  metis_tac[]
QED

Theorem dft_pos_pending_gas_enter:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_slot C D fi bi f g b b' /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  ~MEM v call.inst_outputs /\ s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_pos_pending_gas_phase w C D fi bi pre gas call post zs H l r /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  eval_operands ops s = SOME args /\ setup_callee calleeR args s = SOME cs ==>
  dft_pos_pending_gas_phase w C D fi bi pre gas call post
    (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) H
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH zs /\
   nL = nR + LENGTH (dft_pos_pending_gas_events zs) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r` by
    (fs[dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `ls = [] ==> l.dft_occ_saved = []` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  `b.bb_instructions = pre ++ [gas;call] ++ post /\
   b'.bb_instructions = pre ++ [call;gas] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w C) 2 l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_iter, dft_original_runtime_next] >>
  drule_all dft_pos_gas_call_enter >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
  irule dft_pos_pending_gas_enter_phase >>
  simp[dft_pos_pending_gas_stack_def, dft_pos_pending_gas_events_def] >>
  conj_tac >-
    (simp[dft_pos_pending_gas_frame_def] >> metis_tac[]) >>
  Cases_on `ls = []` >> gvs[dft_pos_pending_gas_frame_def] >> metis_tac[]
QED

Theorem dft_pos_pending_gas_event_push[simp]:
  dft_pos_pending_gas_events (SOME (gas,addr)::zs) =
    (gas,addr)::dft_pos_pending_gas_events zs /\
  dft_pos_pending_gas_events (NONE::zs) = dft_pos_pending_gas_events zs
Proof simp[dft_pos_pending_gas_events_def]
QED

Theorem dft_pos_pending_gas_phase_count:
  dft_pos_pending_gas_phase w C D fi bi pre gas call post zs H c d ==>
  dft_occ_count c = dft_occ_count d +
    LENGTH (dft_pos_pending_gas_events zs) + LENGTH H
Proof
  simp[dft_pos_pending_gas_phase_def, dft_occ_count_def] >>
  rpt strip_tac >> gvs[]
QED

Definition dft_pos_pending_saved_def:
  dft_pos_pending_saved zs saved <=>
    LIST_REL (\z pv. case z of NONE => T | SOME (inst,addr) =>
      addr = FST pv ++ [(SND pv,inst.inst_id)]) zs saved
End

Definition dft_pos_pending_aligned_phase_def:
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H c d <=>
    dft_pos_pending_gas_phase w C D fi bi pre gas call post zs H c d /\
    dft_pos_pending_saved zs c.dft_occ_saved
End

Theorem dft_pos_pending_saved_cons[simp]:
  dft_pos_pending_saved [] [] /\
  (dft_pos_pending_saved (NONE::zs) (pv::saved) <=>
    dft_pos_pending_saved zs saved) /\
  (dft_pos_pending_saved (SOME (inst,addr)::zs) ((path,visit)::saved) <=>
    addr = path ++ [(visit,inst.inst_id)] /\ dft_pos_pending_saved zs saved)
Proof simp[dft_pos_pending_saved_def]
QED

Theorem dft_pos_pending_saved_head:
  dft_pos_pending_saved (SOME (inst,addr)::zs) ((path,visit)::saved) ==>
  addr = path ++ [(visit,inst.inst_id)] /\ dft_pos_pending_saved zs saved
Proof simp[]
QED

Theorem dft_pos_pending_aligned_root:
  dft_pos_functions C D f g /\
  c.dft_occ_core = DftOpen (DftEnter f 0 s) [] n /\
  d.dft_occ_core = DftOpen (DftEnter g 0 s) [] n /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = [] /\ d.dft_occ_saved = [] /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post [] [] c d
Proof
  strip_tac >> simp[dft_pos_pending_aligned_phase_def] >>
  irule dft_pos_pending_gas_root >> metis_tac[]
QED

Theorem dft_pos_pending_aligned_enter:
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
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  fs[dft_pos_pending_aligned_phase_def] >>
  `dft_pos_pending_gas_phase w C D fi bi pre gas call post
    (SOME (gas,l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])::zs) H
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r)` by
    (irule dft_pos_pending_gas_enter >> metis_tac[]) >>
  simp[dft_pos_pending_aligned_phase_def] >>
  `l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   LENGTH l.dft_occ_saved = LENGTH zs /\
   dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs` by
    (fs[dft_pos_pending_gas_phase_def] >> gvs[]) >>
  `ls = [] ==> l.dft_occ_saved = []` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  drule_all dft_pos_gas_call_enter >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `ls = []` >> gvs[]
QED

Theorem dft_pos_pending_aligned_return:
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 b' call s::rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (SOME (gas,addr)::zs) H l r /\
  dft_restore call.inst_outputs ret cs s = SOME a ==>
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r)
Proof
  strip_tac >>
  `dft_pos_pending_gas_phase w C D fi bi pre gas call post
     (SOME (gas,addr)::zs) H l r /\
   addr = path ++ [(visit,gas.inst_id)] /\ dft_pos_pending_saved zs saved` by
    (fs[dft_pos_pending_aligned_phase_def] >> gvs[]) >>
  `dft_pos_pending_gas_frame w C D fi bi pre gas call post
     (SOME (gas,addr)) lf (DftCaller g 0 b' call s) /\
   dft_pos_pending_gas_stack w C D fi bi pre gas call post zs ls rs /\
   r.dft_occ_saved = (path,visit)::saved /\ LENGTH saved = LENGTH zs /\
   nL = nR + SUC (LENGTH (dft_pos_pending_gas_events zs)) + LENGTH H /\
   dft_original_ready l /\ dft_original_ready r` by
    (fs[dft_pos_pending_gas_phase_def, dft_pos_pending_gas_stack_def] >> gvs[]) >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_pending_gas_stack_fill] >>
  `(ls = [] ==> saved = []) /\ (rs = [] ==> saved = [])` by
    metis_tac[dft_pos_pending_gas_stack_length, LENGTH_NIL] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (FUNPOW (dft_occ_oracle_next w D) 2 r)` by
    metis_tac[dft_original_runtime_next, dft_original_runtime_iter] >>
  qpat_x_assum `dft_pos_pending_gas_frame _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dft_pos_pending_gas_frame_def] >> strip_tac >> gvs[] >>
  qpat_assum `s.vs_inst_idx = LENGTH pre`
    (fn th => drule_all (REWRITE_RULE [th] dft_pos_gas_call_return_success)) >>
  disch_then (qspecl_then [`D`,`C`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[dft_pos_pending_aligned_phase_def, dft_pos_pending_gas_phase_def,
    dft_pos_control_def] >> metis_tac[]
QED
