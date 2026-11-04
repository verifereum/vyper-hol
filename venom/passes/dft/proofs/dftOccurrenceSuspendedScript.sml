(* Same-context callee transport with one inaccessible pending GAS. *)
Theory dftOccurrenceSuspended
Ancestors
  dftOccurrenceOpenCall dftOccurrenceGasEdit dftOccurrenceMachine
  dftOccurrenceReplay dftOpenErase dftOpenMachine dftOccurrenceReturn
  dftOccurrenceResidual venomState
  venomExecSemantics venomInst arithmetic list

Definition dft_suspend_frames_def:
  dft_suspend_frames v g (DftCaller fnL bL bbL callL sL)
      (DftCaller fnR bR bbR callR sR) <=>
    bL = 0 /\ bR = 0 /\ callL = callR /\
    callL.inst_opcode = INVOKE /\ ~MEM v callL.inst_outputs /\
    dft_cut_pair [(v,g)] [] sL sR
End

(* The tails and distinguished saved address remain fixed during suspension.
   Only the common nested prefix grows and shrinks. *)
Definition dft_suspended_def:
  dft_suspended v g frameL frameR tailL tailR savedL savedR path visit l r <=>
    dft_suspend_frames v g frameL frameR /\
    ?ctl prefix ghosts nL nR.
      l.dft_occ_core = DftOpen ctl (prefix ++ frameL::tailL) nL /\
      r.dft_occ_core = DftOpen ctl (prefix ++ frameR::tailR) nR /\
      dft_erase l.dft_occ_core = l.dft_occ_core /\
      dft_erase r.dft_occ_core = r.dft_occ_core /\
      LENGTH ghosts = LENGTH prefix /\ EVERY dft_occ_frame_ok prefix /\
      l.dft_occ_saved = ghosts ++ (path,visit)::savedL /\
      r.dft_occ_saved = ghosts ++ (path,visit)::savedR /\
      l.dft_occ_path = r.dft_occ_path /\
      l.dft_occ_visit = r.dft_occ_visit
End

Definition dft_suspend_cleared_def:
  dft_suspend_cleared l r <=>
    ?result nL nR.
      l.dft_occ_core = DftOpen (DftDone result) [] nL /\
      r.dft_occ_core = DftOpen (DftDone result) [] nR /\
      l.dft_occ_saved = [] /\ r.dft_occ_saved = []
End

Definition dft_suspend_resumed_def:
  dft_suspend_resumed v g frameL frameR tailL tailR savedL savedR path visit l r <=>
    ?fnL fnR bbL bbR call sL sR afterL afterR ret cs nL nR.
      frameL = DftCaller fnL 0 bbL call sL /\
      frameR = DftCaller fnR 0 bbR call sR /\
      dft_restore call.inst_outputs ret cs sL = SOME afterL /\
      dft_restore call.inst_outputs ret cs sR = SOME afterR /\
      dft_cut_pair [(v,g)] [] afterL afterR /\
      l.dft_occ_core = DftOpen (DftAt fnL 0 bbL
        (afterL with vs_inst_idx := SUC sL.vs_inst_idx)) tailL nL /\
      r.dft_occ_core = DftOpen (DftAt fnR 0 bbR
        (afterR with vs_inst_idx := SUC sR.vs_inst_idx)) tailR nR /\
      l.dft_occ_saved = savedL /\ r.dft_occ_saved = savedR /\
      l.dft_occ_path = path /\ r.dft_occ_path = path /\
      l.dft_occ_visit = visit /\ r.dft_occ_visit = visit
End

Theorem dft_suspended_observe:
  dft_suspended v g fL fR tL tR sL sR path visit l r ==>
  (dft_open_observe fn inst s l.dft_occ_core <=>
   dft_open_observe fn inst s r.dft_occ_core)
Proof
  simp[dft_suspended_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_suspended_address:
  dft_suspended v g fL fR tL tR sL sR path visit l r ==>
  dft_occ_address l = dft_occ_address r
Proof
  simp[dft_suspended_def] >> rpt strip_tac >>
  simp[dft_occ_address_def]
QED

Theorem dft_suspend_frames_restore:
  dft_suspend_frames v g (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) /\
  dft_restore call.inst_outputs ret cs sL = SOME afterL /\
  dft_restore call.inst_outputs ret cs sR = SOME afterR ==>
  dft_cut_pair [(v,g)] [] afterL afterR
Proof
  simp[dft_suspend_frames_def] >> metis_tac[dft_gas_cut_return]
QED

Theorem dft_suspend_fill_frame[local,simp]:
  dft_fill_frame 0 (dft_fill_frame 1 frame) = dft_fill_frame 0 frame
Proof
  Cases_on `frame` >> simp[dft_fill_frame_def]
QED

Theorem dft_suspend_pop:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb call caller::tail) n /\
  c.dft_occ_saved = (path,visit)::saved /\
  MAP (dft_fill_frame 0) tail = tail /\ call.inst_opcode = INVOKE /\
  dft_restore call.inst_outputs ret cs caller = SOME after ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftAt fn 0 bb
        (after with vs_inst_idx := SUC caller.vs_inst_idx)) tail n;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>
Proof
  simp[dft_restore_def] >> strip_tac >>
  rewrite_tac[dft_occ_oracle_next_def] >>
  drule_all dft_occ_pop >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
       MAP_MAP_o, combinTheory.o_DEF, dft_fill_frame_def, SF ETA_ss]
QED

Theorem dft_suspend_pop_failure:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb call caller::tail) n /\
  dft_restore call.inst_outputs ret cs caller = NONE ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Error "invoke: return arity mismatch")) [] n /\
  (dft_occ_oracle_next w C c).dft_occ_saved = []
Proof
  simp[dft_restore_def] >> strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       dft_open_next_def, dft_open_return_def, dft_erase_def,
       dft_occ_update_def]
QED

Theorem dft_suspend_distinguished_return:
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
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
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
  simp[dft_suspend_resumed_def] >>
  metis_tac[dft_suspend_pop]
QED

Theorem dft_suspended_enter:
  dft_suspended v g fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_suspended v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_suspended_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def,
      APPEND_11_LENGTH] >>
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

Theorem dft_suspended_at:
  dft_suspended v g fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n ==>
  dft_suspended v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_suspended_def] >> rpt strip_tac >> gvs[] >>
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

Resume dft_suspended_at[invoke]:
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

Resume dft_suspended_at[gas]:
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

Resume dft_suspended_at[ordinary]:
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_open_continue_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `prefix` >> gvs[] >> metis_tac[]
QED

Finalise dft_suspended_at

Theorem dft_suspended_done:
  dft_suspended v g fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftDone result) stack n ==>
  dft_suspended v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_resumed v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  qpat_x_assum `dft_suspended _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dft_suspended_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  Cases_on `prefix`
  >- suspend "distinguished" >>
  suspend "nested"
QED

Resume dft_suspended_done[distinguished]:
  Cases_on `result`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret"
  >> suspend "error"
QED

Resume dft_suspended_done[ok]:
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_return_def,
       dft_erase_def, dft_occ_update_def, dft_suspend_cleared_def]
QED
Resume dft_suspended_done[halt]:
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_return_def,
       dft_erase_def, dft_occ_update_def, dft_suspend_cleared_def]
QED
Resume dft_suspended_done[abort]:
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_return_def,
       dft_erase_def, dft_occ_update_def, dft_suspend_cleared_def]
QED
Resume dft_suspended_done[error]:
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_open_return_def,
       dft_erase_def, dft_occ_update_def, dft_suspend_cleared_def]
QED
Resume dft_suspended_done[intret]:
  Cases_on `fL` >> Cases_on `fR` >> gvs[dft_suspend_frames_def, dft_fill_frame_def] >>
  disj2_tac >> irule dft_suspend_distinguished_return >>
  simp[dft_suspend_frames_def] >> metis_tac[]
QED
Resume dft_suspended_done[nested]:
  Cases_on `h` >> Cases_on `ghosts` >> gvs[dft_fill_frame_def,
    dft_occ_frame_ok_def] >> PairCases_on `h` >>
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
Finalise dft_suspended_done

Definition dft_suspend_exit_def:
  dft_suspend_exit v g fL fR tL tR sL sR path visit l r <=>
    dft_suspend_resumed v g fL fR tL tR sL sR path visit l r \/
    dft_suspend_cleared l r
End

Theorem dft_suspended_next:
  dft_suspended v g fL fR tL tR sL sR path visit l r ==>
  dft_suspended v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_exit v g fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n` by
    (Cases_on `l.dft_occ_core` >> simp[]) >>
  `dft_erase l.dft_occ_core = l.dft_occ_core` by
    gvs[dft_suspended_def] >>
  Cases_on `ctl` >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  metis_tac[dft_suspended_enter, dft_suspended_at, dft_suspended_done,
            dft_suspend_exit_def]
QED

Theorem dft_suspended_prefix:
  !j l r. dft_suspended v g fL fR tL tR sL sR path visit l r ==>
    ((!k. k <= j ==>
       dft_suspended v g fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) k l)
         (FUNPOW (dft_occ_oracle_next w C) k r)) \/
     ?h. 0 < h /\ h <= j /\
       dft_suspend_exit v g fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) h l)
         (FUNPOW (dft_occ_oracle_next w C) h r) /\
       !k. k < h ==>
         dft_suspended v g fL fR tL tR sL sR path visit
           (FUNPOW (dft_occ_oracle_next w C) k l)
           (FUNPOW (dft_occ_oracle_next w C) k r))
Proof
  Induct_on `j`
  >- simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (first_assum (qspec_then `j` mp_tac) >> rewrite_tac[LESS_EQ_REFL] >>
      disch_tac >> drule dft_suspended_next >>
      disch_then (qspecl_then [`w`, `C`] strip_assume_tac)
      >- (disj1_tac >> rpt strip_tac >>
          Cases_on `k = SUC j` >> gvs[FUNPOW_SUC] >>
          first_x_assum irule >> decide_tac) >>
      disj2_tac >> qexists_tac `SUC j` >> simp[FUNPOW_SUC] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  disj2_tac >> qexists_tac `h` >> simp[] >> decide_tac
QED

Theorem dft_suspend_pending_cut:
  dft_cut_pair [(v,g)] []
    ((update_var v g s) with vs_inst_idx := k) s
Proof
  simp[dft_cut_pair_def, dft_cut_data_def, dft_pending_apply_def,
       update_var_def]
QED

Theorem dft_suspend_pending_data:
  dft_cut_pair [(v,g)] [] s t ==>
  dft_cut_data s = dft_cut_data (update_var v g t)
Proof
  simp[dft_cut_pair_def, dft_pending_apply_def] >>
  rpt strip_tac >> gvs[] >>
  simp[dft_cut_data_def, update_var_def]
QED

Theorem dft_suspend_gas_step:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  (stack = [] ==> c.dft_occ_saved = []) /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] ==>
  dft_occ_oracle_next w C c = c with dft_occ_core :=
    DftOpen (DftAt fn 0 bb
      ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)])) s)
        with vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC n)
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_erase_def, dft_occ_update_def, dft_occ_address_def,
       MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `stack` >> gvs[dft_occ_config_component_equality]
QED

Theorem dft_suspend_push:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  get_instruction bb s.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftEnter callee 0 cs)
        (DftCaller fn 0 bb call s::stack) n;
      dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved|>
Proof
  strip_tac >> rewrite_tac[dft_occ_oracle_next_def] >>
  drule_all dft_occ_push >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem dft_suspend_crossing_entry:
  bbL.bb_instructions = pre ++ [gas;call] ++ post /\
  bbR.bb_instructions = pre ++ [call;gas] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\ ~MEM (Var v) ops /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) tailL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) tailR nR /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  l.dft_occ_saved = savedL /\ r.dft_occ_saved = savedR /\
  MAP (dft_fill_frame 0) tailL = tailL /\
  MAP (dft_fill_frame 0) tailR = tailR /\
  (tailL = [] ==> savedL = []) ==>
  let g = w (path ++ [(visit,gas.inst_id)]);
      sGas = (update_var v g s) with vs_inst_idx := SUC s.vs_inst_idx
  in dft_suspended v g (DftCaller fnL 0 bbL call sGas)
       (DftCaller fnR 0 bbR call s) tailL tailR savedL savedR path visit
       (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
       (dft_occ_oracle_next w C r)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `DftCaller fnL 0 bbL call sGas` >>
  `dft_cut_pair [(v,w (path ++ [(visit,gas.inst_id)]))] [] sGas s` by
    simp[Abbr `sGas`, dft_suspend_pending_cut] >>
  `eval_operands ops sGas = SOME args` by
    metis_tac[dft_gas_cut_operands] >>
  `setup_callee callee args sGas = SOME cs` by
    metis_tac[dft_gas_cut_setup] >>
  `get_instruction bbL s.vs_inst_idx = SOME gas /\
   get_instruction bbL sGas.vs_inst_idx = SOME call /\
   get_instruction bbR s.vs_inst_idx = SOME call` by
    simp[get_instruction_def, Abbr `sGas`, EL_APPEND_EQN, update_var_def] >>
  `tailL = [] ==> l.dft_occ_saved = []` by simp[] >>
  drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  gvs[Abbr `sGas`] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_open_next_def, dft_open_invoke_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       dft_occ_update_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  simp[dft_suspended_def, dft_suspend_frames_def, dft_suspend_pending_cut,
       dft_erase_def, dft_fill_def, dft_fill_control_def, dft_fill_frame_def]
QED

(* Failure is synchronized even when no callee can be entered. *)
Theorem dft_suspend_call_failure:
  dft_cut_pair [(v,g)] [] sL sR /\
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL sL) tailL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR sR) tailR nR /\
  get_instruction bbL sL.vs_inst_idx = SOME call /\
  get_instruction bbR sR.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  ~(?nm ops callee args cs.
    decode_invoke call = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops sR = SOME args /\ setup_callee callee args sR = SOME cs) ==>
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_open_next_def, dft_open_invoke_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def] >>
  Cases_on `decode_invoke call`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  PairCases_on `x` >>
  `eval_operands x1 sL = eval_operands x1 sR` by
    (irule dft_gas_cut_operands >> simp[] >> metis_tac[]) >>
  Cases_on `lookup_function x0 C.ctx_functions`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  `!args. setup_callee callee args sL = setup_callee callee args sR` by
    metis_tac[dft_gas_cut_setup] >>
  Cases_on `eval_operands x1 sR`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  `setup_callee callee args sR = NONE` by
    (Cases_on `setup_callee callee args sR` >> gvs[]) >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def]
QED

(* Return restores data, not the stored instruction index. The pending read
   completes the residual at the rejoin index. *)
Theorem dft_suspend_return_discharge:
  dft_suspend_resumed v (w (path ++ [(visit,gas.inst_id)]))
    (DftCaller fnL 0 bbL call callerL) (DftCaller fnR 0 bbR call callerR)
    tailL tailR savedL savedR path visit l r /\
  callerL.vs_inst_idx = SUC callerR.vs_inst_idx /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  get_instruction bbR (SUC callerR.vs_inst_idx) = SOME gas /\
  MAP (dft_fill_frame 0) tailR = tailR /\
  (tailR = [] ==> savedR = []) ==>
  ?sL sR nL nR.
    l.dft_occ_core = DftOpen (DftAt fnL 0 bbL sL) tailL nL /\
    (dft_occ_oracle_next w C r).dft_occ_core =
      DftOpen (DftAt fnR 0 bbR sR) tailR (SUC nR) /\
    sL = sR /\ sL.vs_inst_idx = SUC (SUC callerR.vs_inst_idx) /\
    l.dft_occ_path = (dft_occ_oracle_next w C r).dft_occ_path /\
    l.dft_occ_visit = (dft_occ_oracle_next w C r).dft_occ_visit /\
    l.dft_occ_saved = savedL /\
    (dft_occ_oracle_next w C r).dft_occ_saved = savedR
Proof
  simp[dft_suspend_resumed_def] >> rpt strip_tac >> gvs[] >>
  `dft_cut_data afterL = dft_cut_data
     (update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) afterR)` by
    metis_tac[dft_suspend_pending_data] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       is_terminator_def, dft_erase_def, dft_fill_def, dft_fill_control_def,
       dft_occ_update_def, dft_occ_address_def, MAP_MAP_o,
       combinTheory.o_DEF, SF ETA_ss] >>
  gvs[dft_cut_data_def, venom_state_component_equality, update_var_def] >>
  Cases_on `tailR` >> gvs[]
QED

Theorem dft_suspended_prefix_observations:
  dft_suspended v g fL fR tL tR sL sR path visit l r ==>
    ((!k. k <= j ==>
       dft_suspended v g fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) k l)
         (FUNPOW (dft_occ_oracle_next w C) k r) /\
       !fn inst s.
         (dft_open_observe fn inst s
           (FUNPOW (dft_occ_oracle_next w C) k l).dft_occ_core <=>
          dft_open_observe fn inst s
           (FUNPOW (dft_occ_oracle_next w C) k r).dft_occ_core)) \/
     ?h. 0 < h /\ h <= j /\
       dft_suspend_exit v g fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) h l)
         (FUNPOW (dft_occ_oracle_next w C) h r) /\
       !k. k < h ==>
         dft_suspended v g fL fR tL tR sL sR path visit
           (FUNPOW (dft_occ_oracle_next w C) k l)
           (FUNPOW (dft_occ_oracle_next w C) k r) /\
         !fn inst s.
           (dft_open_observe fn inst s
             (FUNPOW (dft_occ_oracle_next w C) k l).dft_occ_core <=>
            dft_open_observe fn inst s
             (FUNPOW (dft_occ_oracle_next w C) k r).dft_occ_core))
Proof
  strip_tac >> drule dft_suspended_prefix >>
  disch_then (qspecl_then [`w`, `C`, `j`] strip_assume_tac)
  >- (disj1_tac >> metis_tac[dft_suspended_observe]) >>
  disj2_tac >> qexists_tac `h` >> simp[] >>
  metis_tac[dft_suspended_observe]
QED
