(* Mixed suspended callers for the fixed GAS/INVOKE edit.
   This boundary does not assert closure across the active edited pair. *)
Theory dftOccurrenceCallStack
Ancestors
  dftOccurrenceSuspended dftOccurrenceGasEdit dftOccurrenceOpenCall
  dftOccurrenceMachine dftOccurrenceReplay dftOpenErase dftOpenMachine
  dftOccurrenceReturn dftOccurrenceResidual venomState venomExecSemantics
  venomInst arithmetic list

Definition dft_mixed_frame_def:
  dft_mixed_frame bb0 pre gas call post v w path visit
      (DftCaller fnL bL bbL instL sL) (DftCaller fnR bR bbR instR sR) <=>
    bL = 0 /\ bR = 0 /\
    fnR = dft_gas_edit_fn bb0 pre gas call post fnL /\
    bbR = dft_gas_edit_block bb0 pre gas call post bbL /\
    instR = instL /\ instL.inst_opcode = INVOKE /\
    get_instruction bbL sL.vs_inst_idx = SOME instL /\
    get_instruction bbR sR.vs_inst_idx = SOME instL /\
    (sR = sL \/
     (bbL = bb0 /\ instL = call /\
      sL.vs_inst_idx = SUC (LENGTH pre) /\ sR.vs_inst_idx = LENGTH pre /\
      ~MEM v call.inst_outputs /\
      dft_cut_pair [(v,w (path ++ [(visit,gas.inst_id)]))] [] sL sR))
End

Definition dft_mixed_stack_def:
  (dft_mixed_stack bb0 pre gas call post v w [] [] [] [] <=> T) /\
  (dft_mixed_stack bb0 pre gas call post v w (fL::tL) (fR::tR)
      (adrL::savedL) (adrR::savedR) <=>
    adrR = adrL /\
    dft_mixed_frame bb0 pre gas call post v w (FST adrL) (SND adrL) fL fR /\
    dft_mixed_stack bb0 pre gas call post v w tL tR savedL savedR) /\
  (dft_mixed_stack bb0 pre gas call post v w _ _ _ _ <=> F)
End

Theorem dft_mixed_stack_nil[simp]:
  dft_mixed_stack bb0 pre gas call post v w [] [] [] []
Proof
  simp[dft_mixed_stack_def]
QED

Theorem dft_mixed_stack_cons[simp]:
  dft_mixed_stack bb0 pre gas call post v w (fL::tL) (fR::tR)
    ((path,visit)::savedL) ((path,visit)::savedR) <=>
  dft_mixed_frame bb0 pre gas call post v w path visit fL fR /\
  dft_mixed_stack bb0 pre gas call post v w tL tR savedL savedR
Proof
  simp[dft_mixed_stack_def]
QED

Theorem dft_mixed_stack_head:
  dft_mixed_stack bb0 pre gas call post v w (fL::tL) stackR
    savedL savedR ==>
  ?fR tR path visit tailL tailR.
    stackR = fR::tR /\ savedL = (path,visit)::tailL /\
    savedR = (path,visit)::tailR /\
    dft_mixed_frame bb0 pre gas call post v w path visit fL fR /\
    dft_mixed_stack bb0 pre gas call post v w tL tR tailL tailR
Proof
  Cases_on `stackR` >> Cases_on `savedL` >> Cases_on `savedR` >>
  simp[dft_mixed_stack_def] >> Cases_on `h'` >> simp[]
QED

Theorem dft_mixed_stack_lengths:
  dft_mixed_stack bb0 pre gas call post v w tL tR savedL savedR ==>
  LENGTH tL = LENGTH tR /\ LENGTH savedL = LENGTH tL /\
  LENGTH savedR = LENGTH tR
Proof
  qid_spec_tac `tR` >> qid_spec_tac `savedL` >> qid_spec_tac `savedR` >>
  Induct_on `tL` >> Cases_on `tR` >> Cases_on `savedL` >>
  Cases_on `savedR` >> simp[dft_mixed_stack_def] >> rpt pairarg_tac >>
  simp[dft_mixed_stack_def] >> metis_tac[]
QED

Theorem dft_mixed_frame_erase:
  dft_mixed_frame bb0 pre gas call post v w path visit fL fR ==>
  dft_fill_frame 0 fL = fL /\ dft_fill_frame 0 fR = fR
Proof
  Cases_on `fL` >> Cases_on `fR` >>
  simp[dft_mixed_frame_def, dft_fill_frame_def]
QED

Theorem dft_mixed_stack_erase:
  dft_mixed_stack bb0 pre gas call post v w tL tR savedL savedR ==>
  MAP (dft_fill_frame 0) tL = tL /\ MAP (dft_fill_frame 0) tR = tR
Proof
  qid_spec_tac `tR` >> qid_spec_tac `savedL` >> qid_spec_tac `savedR` >>
  Induct_on `tL` >> Cases_on `tR` >> Cases_on `savedL` >>
  Cases_on `savedR` >> simp[dft_mixed_stack_def] >> rpt strip_tac >>
  drule dft_mixed_frame_erase >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem dft_mixed_frame_shape:
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL bL bbL instL sL) (DftCaller fnR bR bbR instR sR) ==>
  bL = 0 /\ bR = 0 /\ instR = instL /\
  fnR = dft_gas_edit_fn bb0 pre gas call post fnL /\
  bbR = dft_gas_edit_block bb0 pre gas call post bbL
Proof
  simp[dft_mixed_frame_def] >> metis_tac[]
QED

Theorem dft_mixed_pending_suspend:
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL 0 bbL call sL) (DftCaller fnR 0 bbR call sR) /\
  sL <> sR ==>
  dft_suspend_frames v (w (path ++ [(visit,gas.inst_id)]))
    (DftCaller fnL 0 bbL call sL) (DftCaller fnR 0 bbR call sR) /\
  bbL = bb0 /\ sL.vs_inst_idx = SUC (LENGTH pre) /\
  sR.vs_inst_idx = LENGTH pre
Proof
  simp[dft_mixed_frame_def, dft_suspend_frames_def] >> metis_tac[]
QED

(* No context-specific fact is needed to pop a frame. In particular the
   target callee may have been recursively edited. *)
Theorem dft_mixed_pending_pop:
  dft_suspend_frames v g (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnL 0 bbL call sL::tailL) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnR 0 bbR call sR::tailR) nR /\
  l.dft_occ_saved = (path,visit)::savedL /\
  r.dft_occ_saved = (path,visit)::savedR /\
  MAP (dft_fill_frame 0) tailL = tailL /\
  MAP (dft_fill_frame 0) tailR = tailR ==>
  dft_suspend_resumed v g (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) tailL tailR savedL savedR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C' r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C' r)
Proof
  strip_tac >>
  Cases_on `dft_restore call.inst_outputs ret cs sL`
  >- (`dft_restore call.inst_outputs ret cs sR = NONE` by
        metis_tac[dft_restore_pair_failure] >>
      disj2_tac >> simp[dft_suspend_cleared_def] >>
      metis_tac[dft_suspend_pop_failure]) >>
  `?afterR. dft_restore call.inst_outputs ret cs sR = SOME afterR` by
    (Cases_on `dft_restore call.inst_outputs ret cs sR` >>
     metis_tac[dft_restore_pair_failure]) >>
  `call.inst_opcode = INVOKE` by gvs[dft_suspend_frames_def] >>
  `dft_cut_pair [(v,g)] [] x afterR` by
    metis_tac[dft_suspend_frames_restore] >>
  disj1_tac >>
  drule_all dft_suspend_pop >> disch_tac >>
  rev_drule_all dft_suspend_pop >> disch_tac >>
  simp[dft_suspend_resumed_def] >> metis_tac[dft_suspend_pop]
QED

(* Two outstanding reads, with independent values at two saved addresses.
   Popping the inner frame leaves the entire outer descriptor untouched. *)
Theorem dft_mixed_two_pending_pop:
  dft_mixed_frame bb0 pre gas call post v w p1 j1
    (DftCaller fn1 0 bb1 call s1) (DftCaller fn1' 0 bb1' call t1) /\
  s1 <> t1 /\
  dft_mixed_frame bb0 pre gas call post v w p2 j2 f2 f2' /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    [DftCaller fn1 0 bb1 call s1; f2] nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    [DftCaller fn1' 0 bb1' call t1; f2'] nR /\
  l.dft_occ_saved = [(p1,j1);(p2,j2)] /\
  r.dft_occ_saved = [(p1,j1);(p2,j2)] ==>
  dft_mixed_stack bb0 pre gas call post v w [f2] [f2'] [(p2,j2)] [(p2,j2)] /\
  (dft_suspend_resumed v (w (p1 ++ [(j1,gas.inst_id)]))
     (DftCaller fn1 0 bb1 call s1) (DftCaller fn1' 0 bb1' call t1)
     [f2] [f2'] [(p2,j2)] [(p2,j2)] p1 j1
     (dft_occ_oracle_next w C l)
     (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
   dft_suspend_cleared (dft_occ_oracle_next w C l)
     (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r))
Proof
  strip_tac >> conj_tac >- simp[] >>
  drule_all dft_mixed_pending_suspend >> strip_tac >>
  drule dft_mixed_frame_erase >> strip_tac >>
  irule dft_mixed_pending_pop >> simp[] >> metis_tac[]
QED

Theorem dft_mixed_two_pending_discharge:
  dft_mixed_frame bb0 pre gas call post v w p2 j2 f2 f2' /\
  dft_suspend_resumed v (w (p1 ++ [(j1,gas.inst_id)]))
    (DftCaller fn1 0 bb1 call s1) (DftCaller fn1' 0 bb1' call t1)
    [f2] [f2'] [(p2,j2)] [(p2,j2)] p1 j1 l r /\
  s1.vs_inst_idx = SUC t1.vs_inst_idx /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  get_instruction bb1' (SUC t1.vs_inst_idx) = SOME gas ==>
  ?s nL nR.
    l.dft_occ_core = DftOpen (DftAt fn1 0 bb1 s) [f2] nL /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r).dft_occ_core =
      DftOpen (DftAt fn1' 0 bb1' s) [f2'] (SUC nR) /\
    l.dft_occ_saved = [(p2,j2)] /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r).dft_occ_saved = [(p2,j2)] /\
    l.dft_occ_path = (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r).dft_occ_path /\
    l.dft_occ_visit = (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r).dft_occ_visit /\
    dft_mixed_stack bb0 pre gas call post v w [f2] [f2'] [(p2,j2)] [(p2,j2)]
Proof
  strip_tac >> drule dft_mixed_frame_erase >> strip_tac >>
  drule dft_suspend_return_discharge >>
  disch_then (qspec_then `dft_gas_edit_ctx bb0 pre gas call post C` mp_tac) >>
  simp[] >> metis_tac[]
QED

Definition dft_mixed_sync_def:
  dft_mixed_sync bb0 pre gas call post v w l r <=>
    ?ctl tL tR nL nR.
      l.dft_occ_core = DftOpen ctl tL nL /\
      r.dft_occ_core = DftOpen
        (dft_edit_control (dft_gas_edit_fn bb0 pre gas call post)
          (dft_gas_edit_block bb0 pre gas call post) ctl) tR nR /\
      dft_fill_control 0 ctl = ctl /\
      dft_mixed_stack bb0 pre gas call post v w tL tR
        l.dft_occ_saved r.dft_occ_saved /\
      l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit
End

Theorem dft_mixed_init:
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] nL))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn bb0 pre gas call post fn) 0 s) [] nR))
Proof
  simp[dft_mixed_sync_def, dft_occ_init_def, dft_edit_control_def,
       dft_fill_control_def] >> metis_tac[]
QED

Theorem dft_mixed_fill_twice[local,simp]:
  dft_fill_frame 0 (dft_fill_frame 1 frame) = dft_fill_frame 0 frame
Proof
  Cases_on `frame` >> simp[dft_fill_frame_def]
QED

Theorem dft_mixed_sync_enter:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode <> PHI /\ call.inst_opcode <> PHI /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  simp[dft_mixed_sync_def] >> rpt strip_tac >> gvs[] >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule dft_mixed_stack_lengths >> strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_open_next_def, dft_erase_def, dft_gas_edit_lookup_block] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def] >>
  `!bb. eval_phis s (dft_gas_edit_block bb0 pre gas call post bb).bb_instructions =
        eval_phis s bb.bb_instructions` by metis_tac[dft_nonphi_edit_phis] >>
  `!bb. phi_prefix_length
        (dft_gas_edit_block bb0 pre gas call post bb).bb_instructions =
        phi_prefix_length bb.bb_instructions` by
    metis_tac[dft_nonphi_edit_phi_length] >>
  Cases_on `eval_phis s x.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `stack` >> Cases_on `tR` >> gvs[dft_mixed_stack_def] >>
  metis_tac[]
QED

Theorem dft_mixed_sync_at:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre /\
                   s.vs_inst_idx <> SUC (LENGTH pre)) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  simp[dft_mixed_sync_def] >> rpt strip_tac >> gvs[] >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule dft_mixed_stack_lengths >> strip_tac >>
  `get_instruction (dft_gas_edit_block bb0 pre gas call post bb) s.vs_inst_idx =
    get_instruction bb s.vs_inst_idx` by
    metis_tac[dft_gas_edit_instruction_outside] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
           dft_occ_update_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  suspend "ordinary"
QED

Resume dft_mixed_sync_at[invoke]:
  simp[dft_open_invoke_def, dft_gas_edit_lookup_function] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def] >>
  PairCases_on `x` >> Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def, dft_gas_edit_setup_callee] >>
  rename1 `setup_callee callee args s` >> Cases_on `setup_callee callee args s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def, dft_fill_frame_def, MAP_MAP_o,
       combinTheory.o_DEF, SF ETA_ss, dft_mixed_frame_def]
QED

Resume dft_mixed_sync_at[gas]:
  Cases_on `inst.inst_outputs`
  >- simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
           dft_occ_update_def] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
  simp[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def, dft_occ_address_def, MAP_MAP_o,
       combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `stack` >> Cases_on `tR` >> gvs[dft_mixed_stack_def] >> metis_tac[]
QED

Resume dft_mixed_sync_at[ordinary]:
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[dft_fill_def, dft_fill_control_def, dft_edit_control_def,
       dft_occ_update_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `stack` >> Cases_on `tR` >> gvs[dft_mixed_stack_def] >> metis_tac[]
QED

Finalise dft_mixed_sync_at

Definition dft_mixed_discharge_def:
  dft_mixed_discharge bb0 pre gas call post v w l r <=>
    ?fnL fnR bbL bbR callerL callerR tailL tailR savedL savedR path visit.
      dft_mixed_frame bb0 pre gas call post v w path visit
        (DftCaller fnL 0 bbL call callerL) (DftCaller fnR 0 bbR call callerR) /\
      callerL <> callerR /\
      dft_mixed_stack bb0 pre gas call post v w tailL tailR savedL savedR /\
      dft_suspend_resumed v (w (path ++ [(visit,gas.inst_id)]))
        (DftCaller fnL 0 bbL call callerL) (DftCaller fnR 0 bbR call callerR)
        tailL tailR savedL savedR path visit l r
End

Theorem dft_mixed_discharge_next:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_mixed_discharge bb0 pre gas call post v w l r ==>
  dft_mixed_sync bb0 pre gas call post v w l
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  simp[dft_mixed_discharge_def] >> rpt strip_tac >>
  drule_all dft_mixed_pending_suspend >> strip_tac >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule dft_mixed_stack_lengths >> strip_tac >>
  `get_instruction bbR (SUC callerR.vs_inst_idx) = SOME gas` by
    (gvs[dft_mixed_frame_def] >>
     simp[dft_gas_edit_block_def, get_instruction_def,
          EL_APPEND_EQN]) >>
  `tailR = [] ==> savedR = []` by (strip_tac >> gvs[]) >>
  drule dft_suspend_return_discharge >>
  disch_then (qspec_then `dft_gas_edit_ctx bb0 pre gas call post C` mp_tac) >>
  simp[] >> strip_tac >>
  simp[dft_mixed_sync_def] >>
  gvs[dft_mixed_frame_def, dft_edit_control_def, dft_fill_control_def]
QED

Theorem dft_mixed_ordinary_pop:
  dft_mixed_stack bb0 pre gas call post v w tailL tailR savedL savedR /\
  fnR = dft_gas_edit_fn bb0 pre gas call post fnL /\
  bbR = dft_gas_edit_block bb0 pre gas call post bbL /\
  inst.inst_opcode = INVOKE /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnL 0 bbL inst caller::tailL) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnR 0 bbR inst caller::tailR) nR /\
  l.dft_occ_saved = (path,visit)::savedL /\
  r.dft_occ_saved = (path,visit)::savedR /\
  dft_restore inst.inst_outputs ret cs caller = SOME after ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> drule dft_mixed_stack_erase >> strip_tac >>
  drule_all dft_suspend_pop >> disch_tac >>
  rev_drule_all dft_suspend_pop >> disch_tac >>
  simp[dft_mixed_sync_def, dft_edit_control_def, dft_fill_control_def] >>
  metis_tac[dft_suspend_pop]
QED

Theorem dft_mixed_done_clear:
  c.dft_occ_core = DftOpen (DftDone result) stack n /\
  (stack = [] \/ !ret cs. result <> IntRet ret cs) ==>
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftDone result) [] n /\
  (dft_occ_oracle_next w C c).dft_occ_saved = [] /\
  (dft_occ_oracle_next w C c).dft_occ_path = c.dft_occ_path /\
  (dft_occ_oracle_next w C c).dft_occ_visit = c.dft_occ_visit
Proof
  strip_tac >> Cases_on `result` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_fill_def, dft_fill_control_def, dft_open_next_def,
      dft_open_return_def, dft_erase_def, dft_occ_update_def] >>
  metis_tac[]
QED

Theorem dft_mixed_pending_return:
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL 0 bbL call callerL) (DftCaller fnR 0 bbR call callerR) /\
  callerL <> callerR /\
  dft_mixed_stack bb0 pre gas call post v w tailL tailR savedL savedR /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnL 0 bbL call callerL::tailL) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnR 0 bbR call callerR::tailR) nR /\
  l.dft_occ_saved = (path,visit)::savedL /\
  r.dft_occ_saved = (path,visit)::savedR ==>
  dft_mixed_discharge bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> drule_all dft_mixed_pending_suspend >> strip_tac >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule_all dft_mixed_pending_pop >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre gas call post C`, `C`] mp_tac) >>
  strip_tac >- (disj1_tac >> simp[dft_mixed_discharge_def] >> metis_tac[]) >>
  simp[]
QED

Theorem dft_mixed_frame_return:
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fnL 0 bbL inst callerL) (DftCaller fnR 0 bbR inst callerR) /\
  dft_mixed_stack bb0 pre gas call post v w tailL tailR savedL savedR /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnL 0 bbL inst callerL::tailL) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnR 0 bbR inst callerR::tailR) nR /\
  l.dft_occ_saved = (path,visit)::savedL /\
  r.dft_occ_saved = (path,visit)::savedR ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_mixed_discharge bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> Cases_on `callerL = callerR`
  >- (gvs[dft_mixed_frame_def] >>
      Cases_on `dft_restore inst.inst_outputs ret cs callerL`
      >- (disj2_tac >> disj2_tac >>
          simp[dft_suspend_cleared_def] >> metis_tac[dft_suspend_pop_failure]) >>
      disj1_tac >> irule dft_mixed_ordinary_pop >> simp[] >> metis_tac[]) >>
  `inst = call` by gvs[dft_mixed_frame_def] >> gvs[] >>
  disj2_tac >> irule dft_mixed_pending_return >> simp[] >> metis_tac[]
QED

Theorem dft_mixed_sync_done:
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_mixed_discharge bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  qpat_x_assum `dft_mixed_sync _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_mixed_sync_def]) >>
  gvs[dft_edit_control_def] >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule dft_mixed_stack_lengths >> strip_tac >>
  Cases_on `stack`
  >- (gvs[] >> disj1_tac >>
      drule dft_mixed_done_clear >> simp[] >> disch_tac >>
      rev_drule dft_mixed_done_clear >> simp[] >> disch_tac >>
      simp[dft_mixed_sync_def, dft_edit_control_def, dft_fill_control_def] >>
      metis_tac[dft_mixed_done_clear]) >>
  drule dft_mixed_stack_head >> strip_tac >> gvs[] >>
  Cases_on `result`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return" >>
  suspend "error"
QED

Resume dft_mixed_sync_done[ok]:
  disj1_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_occ_update_def,
       dft_mixed_sync_def, dft_edit_control_def]
QED

Resume dft_mixed_sync_done[halt]:
  disj1_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_occ_update_def,
       dft_mixed_sync_def, dft_edit_control_def]
QED

Resume dft_mixed_sync_done[abort]:
  disj1_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_occ_update_def,
       dft_mixed_sync_def, dft_edit_control_def]
QED

Resume dft_mixed_sync_done[error]:
  disj1_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_occ_update_def,
       dft_mixed_sync_def, dft_edit_control_def]
QED

Resume dft_mixed_sync_done[return]:
  Cases_on `h` >> Cases_on `fR` >>
  drule dft_mixed_frame_shape >> strip_tac >> gvs[] >>
  irule dft_mixed_frame_return >> simp[] >> metis_tac[]
QED

Finalise dft_mixed_sync_done

(* Non-vacuity: each saved residual below is an actual call slot on both
   sides; the two oracle values use their own saved dynamic addresses. *)
Theorem dft_mixed_pending_instance:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs ==>
  dft_mixed_frame bb0 pre gas call post v w path visit
    (DftCaller fn 0 bb0 call
      ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
        with vs_inst_idx := SUC (LENGTH pre)))
    (DftCaller (dft_gas_edit_fn bb0 pre gas call post fn) 0
      (dft_gas_edit_block bb0 pre gas call post bb0) call
      (s with vs_inst_idx := LENGTH pre))
Proof
  strip_tac >> simp[dft_mixed_frame_def, get_instruction_def,
    dft_gas_edit_block_def, EL_APPEND_EQN, dft_cut_pair_def,
    dft_cut_data_def, dft_pending_apply_def, update_var_def]
QED

Theorem dft_mixed_two_pending_instance:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs ==>
  dft_mixed_stack bb0 pre gas call post v w
    [DftCaller fn1 0 bb0 call
       ((update_var v (w (p1 ++ [(j1,gas.inst_id)])) s1)
         with vs_inst_idx := SUC (LENGTH pre));
     DftCaller fn2 0 bb0 call
       ((update_var v (w (p2 ++ [(j2,gas.inst_id)])) s2)
         with vs_inst_idx := SUC (LENGTH pre))]
    [DftCaller (dft_gas_edit_fn bb0 pre gas call post fn1) 0
       (dft_gas_edit_block bb0 pre gas call post bb0) call
       (s1 with vs_inst_idx := LENGTH pre);
     DftCaller (dft_gas_edit_fn bb0 pre gas call post fn2) 0
       (dft_gas_edit_block bb0 pre gas call post bb0) call
       (s2 with vs_inst_idx := LENGTH pre)]
    [(p1,j1);(p2,j2)] [(p1,j1);(p2,j2)]
Proof
  strip_tac >> simp[] >> conj_tac >> irule dft_mixed_pending_instance >> simp[]
QED

Theorem dft_mixed_two_pending_return_discharge:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_mixed_frame bb0 pre gas call post v w p1 j1
    (DftCaller fn1 0 bb1 call s1) (DftCaller fn1' 0 bb1' call t1) /\ s1 <> t1 /\
  dft_mixed_frame bb0 pre gas call post v w p2 j2
    (DftCaller fn2 0 bb2 call s2) (DftCaller fn2' 0 bb2' call t2) /\ s2 <> t2 /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    [DftCaller fn1 0 bb1 call s1; DftCaller fn2 0 bb2 call s2] nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    [DftCaller fn1' 0 bb1' call t1; DftCaller fn2' 0 bb2' call t2] nR /\
  l.dft_occ_saved = [(p1,j1);(p2,j2)] /\
  r.dft_occ_saved = [(p1,j1);(p2,j2)] ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)
      (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  `dft_mixed_stack bb0 pre gas call post v w
    [DftCaller fn2 0 bb2 call s2] [DftCaller fn2' 0 bb2' call t2]
    [(p2,j2)] [(p2,j2)]` by simp[] >>
  drule_all dft_mixed_pending_return >>
  disch_then (qspec_then `C` strip_assume_tac)
  >- (disj1_tac >> irule dft_mixed_discharge_next >> simp[]) >>
  simp[]
QED
