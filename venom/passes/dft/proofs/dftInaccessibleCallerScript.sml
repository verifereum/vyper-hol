(* Structural callee transport, independent of the hidden caller payload. *)
Theory dftInaccessibleCaller
Ancestors
  dftOccurrenceSuspended dftOccurrenceMachine dftOccurrenceReplay
  dftOpenErase dftOpenMachine dftOccurrenceReturn venomExecSemantics
  venomInst venomState arithmetic list

Definition dft_hidden_caller_def:
  dft_hidden_caller R frameL frameR tailL tailR savedL savedR path visit l r <=>
    R frameL frameR /\
    ?ctl prefix ghosts nL nR.
      l.dft_occ_core = DftOpen ctl (prefix ++ frameL::tailL) nL /\
      r.dft_occ_core = DftOpen ctl (prefix ++ frameR::tailR) nR /\
      dft_erase l.dft_occ_core = l.dft_occ_core /\
      dft_erase r.dft_occ_core = r.dft_occ_core /\
      LENGTH ghosts = LENGTH prefix /\ EVERY dft_occ_frame_ok prefix /\
      l.dft_occ_saved = ghosts ++ (path,visit)::savedL /\
      r.dft_occ_saved = ghosts ++ (path,visit)::savedR /\
      l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit
End

Definition dft_hidden_return_def:
  dft_hidden_return frameL frameR tailL tailR savedL savedR path visit l r <=>
    ?ret cs nL nR.
      l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frameL::tailL) nL /\
      r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frameR::tailR) nR /\
      l.dft_occ_saved = (path,visit)::savedL /\
      r.dft_occ_saved = (path,visit)::savedR
End

Theorem dft_hidden_caller_observe:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r ==>
  (dft_open_observe fn inst s l.dft_occ_core <=>
   dft_open_observe fn inst s r.dft_occ_core)
Proof
  simp[dft_hidden_caller_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_hidden_caller_address:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r ==>
  dft_occ_address l = dft_occ_address r
Proof
  simp[dft_hidden_caller_def] >> rpt strip_tac >>
  simp[dft_occ_address_def]
QED

Theorem dft_hidden_fill_frame[local,simp]:
  dft_fill_frame 0 (dft_fill_frame 1 frame) = dft_fill_frame 0 frame
Proof
  Cases_on `frame` >> simp[dft_fill_frame_def]
QED

Theorem dft_hidden_caller_enter:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_hidden_caller R fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_hidden_caller_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_fill_def, dft_fill_control_def,
           dft_occ_update_def, dft_suspend_cleared_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, dft_erase_def,
       dft_fill_def, dft_fill_control_def, SF ETA_ss] >>
  Cases_on `prefix` >> gvs[] >> metis_tac[]
QED

Theorem dft_hidden_caller_at:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_hidden_caller R fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_hidden_caller_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_fill_def, dft_fill_control_def,
           dft_occ_update_def, dft_suspend_cleared_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  suspend "ordinary"
QED

Resume dft_hidden_caller_at[invoke]:
  simp[dft_open_invoke_def] >> Cases_on `decode_invoke inst` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def] >>
  PairCases_on `x` >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def] >>
  rename1 `setup_callee callee args s` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def, dft_fill_frame_def, MAP_MAP_o,
       combinTheory.o_DEF, SF ETA_ss] >>
  simp[dft_occ_frame_ok_def]
QED

Resume dft_hidden_caller_at[gas]:
  Cases_on `inst.inst_outputs`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
  simp[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def, dft_occ_address_def, MAP_MAP_o,
       combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `prefix` >> gvs[] >> metis_tac[]
QED

Resume dft_hidden_caller_at[ordinary]:
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `prefix` >> gvs[] >> metis_tac[]
QED

Finalise dft_hidden_caller_at

Theorem dft_hidden_caller_done:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_hidden_return fL fR tL tR sL sR path visit l r \/
  dft_hidden_caller R fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  qpat_x_assum `dft_hidden_caller _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dft_hidden_caller_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  Cases_on `prefix`
  >- suspend "distinguished" >>
  suspend "nested"
QED

Resume dft_hidden_caller_done[distinguished]:
  gvs[] >> Cases_on `result` >>
  simp[dft_hidden_return_def, dft_occ_oracle_next_def,
       dft_occ_next_def, dft_next_inf_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def, dft_open_return_def,
       dft_erase_def, dft_occ_update_def, dft_suspend_cleared_def]
QED

Resume dft_hidden_caller_done[nested]:
  Cases_on `h` >> Cases_on `ghosts` >> gvs[dft_fill_frame_def,
    dft_occ_frame_ok_def] >> PairCases_on `h` >>
  disj2_tac >>
  Cases_on `result` >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       dft_open_next_def, dft_open_return_def, dft_erase_def,
       dft_occ_update_def, dft_suspend_cleared_def] >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_fill_def, dft_fill_control_def, dft_open_deliver_def,
       dft_open_continue_def, is_terminator_def, dft_occ_update_def,
       dft_suspend_cleared_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  disj1_tac >> simp[] >> metis_tac[]
QED

Finalise dft_hidden_caller_done

Theorem dft_hidden_caller_next:
  dft_hidden_caller R fL fR tL tR sL sR path visit l r ==>
  dft_hidden_return fL fR tL tR sL sR path visit l r \/
  dft_hidden_caller R fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n` by
    (Cases_on `l.dft_occ_core` >> simp[]) >>
  `dft_erase l.dft_occ_core = l.dft_occ_core` by
    gvs[dft_hidden_caller_def] >>
  Cases_on `ctl` >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  metis_tac[dft_hidden_caller_enter, dft_hidden_caller_at, dft_hidden_caller_done]
QED

(* A finite bound either remains suspended throughout or encounters a return
   boundary BEFORE stepping it, or a clearing step. A return at time zero
   is permitted: the hidden payload is deliberately not restored here. *)
Theorem dft_hidden_caller_prefix:
  !j l r. dft_hidden_caller R fL fR tL tR sL sR path visit l r ==>
    ((!k. k <= j ==>
       dft_hidden_caller R fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) k l)
         (FUNPOW (dft_occ_oracle_next w C) k r)) \/
     ?h. h <= j /\
       (dft_hidden_return fL fR tL tR sL sR path visit
          (FUNPOW (dft_occ_oracle_next w C) h l)
          (FUNPOW (dft_occ_oracle_next w C) h r) \/
        dft_suspend_cleared
          (FUNPOW (dft_occ_oracle_next w C) h l)
          (FUNPOW (dft_occ_oracle_next w C) h r)) /\
       !k. k < h ==>
         dft_hidden_caller R fL fR tL tR sL sR path visit
           (FUNPOW (dft_occ_oracle_next w C) k l)
           (FUNPOW (dft_occ_oracle_next w C) k r))
Proof
  Induct_on `j`
  >- simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (first_assum (qspec_then `j` mp_tac) >> rewrite_tac[LESS_EQ_REFL] >>
      disch_tac >> drule dft_hidden_caller_next >>
      disch_then (qspecl_then [`w`, `C`] strip_assume_tac)
      >- (disj2_tac >> qexists `j` >> simp[] >>
          rpt strip_tac >> first_x_assum irule >> decide_tac)
      >- (disj1_tac >> rpt strip_tac >>
          Cases_on `k = SUC j` >> gvs[FUNPOW_SUC] >>
          first_x_assum irule >> decide_tac) >>
      disj2_tac >> qexists `SUC j` >> simp[FUNPOW_SUC] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  disj2_tac >> qexists `h` >> simp[] >> decide_tac
QED
