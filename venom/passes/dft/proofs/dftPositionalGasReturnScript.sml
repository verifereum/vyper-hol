Theory dftPositionalGasReturn
Ancestors
  dftPositionalGasCall dftPositionalGasSegment dftOccurrenceReturn
  dftOccurrenceOpenCall dftPositionalRuntime
  dftRecursiveReturnReplay dftOccurrenceMachine dftOccurrenceReplay dftOpenErase
  dftOpenMachine venomExecSemantics venomState venomInst list arithmetic

Theorem dft_pos_gas_return_fill[local,simp]:
  dft_fill_frame a (dft_fill_frame b fr) = dft_fill_frame a fr
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def]
QED

Theorem dft_pos_gas_return_pop[local]:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller f 0 b call s :: ls) n /\
  c.dft_occ_saved = (path,visit)::saved /\
  call.inst_opcode = INVOKE /\
  dft_restore call.inst_outputs ret cs s = SOME a /\
  MAP (dft_fill_frame 0) ls = ls ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftAt f 0 b
         (a with vs_inst_idx := SUC s.vs_inst_idx)) ls n;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>
Proof
  strip_tac >>
  fs[dft_restore_def] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
    dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
    dft_open_continue_def, dft_erase_def, dft_occ_update_def,
    is_terminator_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem dft_pos_gas_call_return_success:
  b.bb_instructions = pre ++ [gas;call] ++ post /\
  b'.bb_instructions = pre ++ [call;gas] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller f 0 b call
      ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
        with vs_inst_idx := SUC s.vs_inst_idx) :: ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 b' call s :: rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  r.dft_occ_saved = (path,visit)::saved /\
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs /\
  (ls = [] ==> saved = []) /\ (rs = [] ==> saved = []) /\
  dft_restore call.inst_outputs ret cs s = SOME a ==>
  let t = (update_var v (w (path ++ [(visit,gas.inst_id)])) a)
            with vs_inst_idx := LENGTH pre + 2
  in dft_occ_oracle_next w C l = l with
      <|dft_occ_core := DftOpen (DftAt f 0 b t) ls nL;
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|> /\
    FUNPOW (dft_occ_oracle_next w D) 2 r = r with
      <|dft_occ_core := DftOpen (DftAt g 0 b' t) rs (SUC nR);
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|> /\
    dft_occ_gas_event gas (path ++ [(visit,gas.inst_id)])
      (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  qabbrev_tac `z = w (path ++ [(visit,gas.inst_id)])` >>
  `dft_restore call.inst_outputs ret cs
    ((update_var v z s) with vs_inst_idx := SUC s.vs_inst_idx) =
    SOME ((update_var v z a) with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[dft_restore_index, dft_restore_update] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b
      (((update_var v z a) with vs_inst_idx := SUC s.vs_inst_idx) with
        vs_inst_idx := SUC (((update_var v z s) with
          vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx))) ls nL;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    (irule dft_pos_gas_return_pop >> simp[Abbr `z`] >> metis_tac[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt g 0 b'
      (a with vs_inst_idx := SUC s.vs_inst_idx)) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    (irule dft_pos_gas_return_pop >> metis_tac[]) >>
  `get_instruction b' (SUC s.vs_inst_idx) = SOME gas` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `dft_occ_oracle_next w D (dft_occ_oracle_next w D r) =
    (dft_occ_oracle_next w D r) with
    <|dft_occ_core := DftOpen (DftAt g 0 b'
      ((update_var v z a) with vs_inst_idx := LENGTH pre + 2)) rs (SUC nR);
      dft_occ_saved := saved|>` by
    (simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
      dft_open_deliver_def, dft_open_continue_def, dft_occ_address_def,
      get_instruction_def, EL_APPEND_EQN, ADD1, is_terminator_def,
      dft_occ_update_def, update_var_def, Abbr `z`, MAP_MAP_o,
      combinTheory.o_DEF, SF ETA_ss] >>
     Cases_on `rs` >> gvs[]) >>
  simp[FUNPOW_2, Abbr `z`, dft_occ_gas_event_def, dft_occ_event_def,
    get_instruction_def, EL_APPEND_EQN, ADD1] >> metis_tac[]
QED

Theorem dft_pos_gas_return_failed_pop[local]:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller f 0 b call s :: ls) n /\
  dft_restore call.inst_outputs ret cs s = NONE ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] n;
      dft_occ_saved := []|>
Proof
  strip_tac >> fs[dft_restore_def] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
    dft_open_next_def, dft_open_return_def, dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_gas_call_return_failure:
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller f 0 b call t :: ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller g 0 b' call s :: rs) nR /\
  dft_restore call.inst_outputs ret cs s = NONE ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nL;
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nR;
      dft_occ_saved := []|>
Proof
  strip_tac >>
  `dft_restore call.inst_outputs ret cs t = NONE` by
    metis_tac[dft_restore_pair_failure] >>
  conj_tac >> irule dft_pos_gas_return_failed_pop >> metis_tac[]
QED

Theorem dft_pos_gas_return_other_pop[local]:
  c.dft_occ_core = DftOpen (DftDone result) ls n /\
  (!ret cs. result <> IntRet ret cs) ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone result) [] n; dft_occ_saved := []|>
Proof
  strip_tac >> Cases_on `result` >> gvs[] >> Cases_on `ls` >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
    dft_open_next_def, dft_open_return_def, dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_gas_call_return_other:
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR /\
  (!ret cs. result <> IntRet ret cs) ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>
Proof
  strip_tac >> conj_tac >> irule dft_pos_gas_return_other_pop >> metis_tac[]
QED

Theorem dft_pos_gas_call_invoke_error[local]:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_cut_pair [(v,z)] [] t s /\ ~MEM (Var v) call.inst_operands ==>
  ((dft_open_invoke C f budget b call t ls nL =
      DftOpen (DftDone (Error msg)) [] nL) <=>
   (dft_open_invoke D g budget' b' call s rs nR =
      DftOpen (DftDone (Error msg)) [] nR))
Proof
  strip_tac >> Cases_on `decode_invoke call`
  >- simp[dft_open_invoke_def] >>
  rename1 `decode_invoke call = SOME dec` >> PairCases_on `dec` >>
  `~MEM (Var v) dec1` by
    (fs[decode_invoke_def, AllCaseEqs()] >> gvs[]) >>
  `eval_operands dec1 t = eval_operands dec1 s` by
    metis_tac[dft_gas_cut_operands] >>
  `OPTREL (dft_pos_functions C D)
    (lookup_function dec0 C.ctx_functions) (lookup_function dec0 D.ctx_functions)` by
    metis_tac[dft_pos_edit_function_lookup] >>
  `!fl fr args st. dft_pos_functions C D fl fr ==>
    setup_callee fl args st = setup_callee fr args st` by
    metis_tac[dft_pos_edit_setup] >>
  Cases_on `lookup_function dec0 C.ctx_functions` >>
  Cases_on `lookup_function dec0 D.ctx_functions` >> gvs[] >>
  simp[dft_open_invoke_def] >>
  rename1 `dft_pos_functions C D calleeL calleeR` >>
  `setup_callee calleeL args t = setup_callee calleeR args s` by
    metis_tac[dft_pos_edit_setup, dft_gas_cut_setup] >>
  Cases_on `eval_operands dec1 s` >> simp[] >>
  `setup_callee calleeL x t = setup_callee calleeR x s` by
    metis_tac[dft_pos_edit_setup, dft_gas_cut_setup] >>
  Cases_on `setup_callee calleeR x s` >> simp[]
QED

Theorem dft_pos_gas_call_failed_step[local]:
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls n /\
  get_instruction b s.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE /\
  dft_open_invoke C f 1 b call s (MAP (dft_fill_frame 1) ls) n =
    DftOpen (DftDone (Error msg)) [] n ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] n; dft_occ_saved := []|>
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_gas_call_entry_failure:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_pos_slot C D fi bi f g b b' /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_open_invoke D g 1 b' call s (MAP (dft_fill_frame 1) rs) nR =
    DftOpen (DftDone (Error msg)) [] nR ==>
  FUNPOW (dft_occ_oracle_next w C) 2 l = l with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] (SUC nL);
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] nR;
      dft_occ_saved := []|>
Proof
  strip_tac >>
  `b.bb_instructions = pre ++ [gas;call] ++ post /\
   b'.bb_instructions = pre ++ [call;gas] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  qabbrev_tac `z = w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])` >>
  qabbrev_tac `t = (update_var v z s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `dft_cut_pair [(v,z)] [] t s` by
    simp[Abbr `t`, dft_pos_gas_call_cut] >>
  `get_instruction b s.vs_inst_idx = SOME gas /\
   get_instruction b t.vs_inst_idx = SOME call /\
   get_instruction b' s.vs_inst_idx = SOME call` by
    simp[get_instruction_def, EL_APPEND_EQN, Abbr `t`, ADD1] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b t)
        (MAP (dft_fill_frame 0) ls) (SUC nL);
      dft_occ_saved := if ls = [] then [] else l.dft_occ_saved|>` by
    (simp[NoAsms, Abbr `t`, Abbr `z`] >>
     irule dft_pos_gas_one_step >> metis_tac[]) >>
  `dft_open_invoke C f 1 b call t
    (MAP (dft_fill_frame 1) (MAP (dft_fill_frame 0) ls)) (SUC nL) =
    DftOpen (DftDone (Error msg)) [] (SUC nL)` by
    metis_tac[dft_pos_gas_call_invoke_error] >>
  `dft_occ_oracle_next w C (dft_occ_oracle_next w C l) =
    (dft_occ_oracle_next w C l) with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] (SUC nL);
      dft_occ_saved := []|>` by
    (irule dft_pos_gas_call_failed_step >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[FUNPOW_2] >>
  irule dft_pos_gas_call_failed_step >> metis_tac[]
QED

Theorem dft_pos_gas_call_entry_failure_cases:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_pos_slot C D fi bi f g b b' /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
  ((decode_invoke call = NONE /\ msg = "invoke: bad operand format") \/
   (?nm ops. decode_invoke call = SOME (nm,ops) /\
     lookup_function nm D.ctx_functions = NONE /\
     msg = "invoke: function not found") \/
   (?nm ops callee. decode_invoke call = SOME (nm,ops) /\
     lookup_function nm D.ctx_functions = SOME callee /\
     eval_operands ops s = NONE /\ msg = "invoke: undefined argument") \/
   (?nm ops callee args. decode_invoke call = SOME (nm,ops) /\
     lookup_function nm D.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = NONE /\
     msg = "invoke: empty function")) ==>
  FUNPOW (dft_occ_oracle_next w C) 2 l = l with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] (SUC nL);
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error msg)) [] nR;
      dft_occ_saved := []|> /\
  dft_occ_gas_event gas
    (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) l /\
  dft_occ_event call
    (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)])
    (dft_occ_oracle_next w C l) /\
  dft_occ_event call
    (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)]) r
Proof
  strip_tac >>
  `dft_open_invoke D g 1 b' call s (MAP (dft_fill_frame 1) rs) nR =
    DftOpen (DftDone (Error msg)) [] nR` by
    (gvs[dft_open_invoke_def]) >>
  `b.bb_instructions = pre ++ [gas;call] ++ post /\
   b'.bb_instructions = pre ++ [call;gas] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  drule_all dft_pos_gas_call_entry_failure >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  drule_all dft_pos_gas_call_events >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >> simp[]
QED
