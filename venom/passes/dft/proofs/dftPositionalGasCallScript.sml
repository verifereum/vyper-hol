Theory dftPositionalGasCall
Ancestors
  dftPositionalGasSegment dftPositionalRuntime dftOccurrenceOpenCall
  dftOccurrenceResidual dftOccurrenceMachine dftOccurrenceReplay dftOpenErase
  dftOpenMachine venomExecSemantics venomState venomInst list arithmetic

Theorem dft_pos_gas_call_cut:
  dft_cut_pair [(v,z)] []
    ((update_var v z s) with vs_inst_idx := i) s
Proof
  simp[dft_cut_pair_def, dft_pending_apply_def, dft_cut_data_def,
    update_var_def] >> qexists `s with vs_inst_idx := 0` >> simp[]
QED

Theorem dft_pos_gas_call_decode[local]:
  decode_invoke call = SOME (nm,ops) /\
  ~MEM (Var v) call.inst_operands ==> ~MEM (Var v) ops
Proof
  simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem dft_pos_gas_call_fill[local,simp]:
  dft_fill_frame a (dft_fill_frame b fr) = dft_fill_frame a fr
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def]
QED

Theorem dft_pos_gas_call_push[local]:
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls n /\
  get_instruction b s.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftEnter callee 0 cs)
       (DftCaller f 0 b call s :: MAP (dft_fill_frame 0) ls) n;
      dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved|>
Proof
  strip_tac >> rewrite_tac[dft_occ_oracle_next_def] >>
  drule_all dft_occ_push >> disch_then (qspec_then `\n. w (dft_occ_address c)` mp_tac) >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def,
    dft_fill_frame_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem dft_pos_gas_call_callee[local]:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  lookup_function nm D.ctx_functions = SOME calleeR ==>
  ?calleeL. lookup_function nm C.ctx_functions = SOME calleeL /\
    dft_pos_functions C D calleeL calleeR /\
    (!args s. setup_callee calleeL args s = setup_callee calleeR args s)
Proof
  strip_tac >>
  `OPTREL (dft_pos_functions C D)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)` by
    metis_tac[dft_pos_edit_function_lookup] >>
  Cases_on `lookup_function nm C.ctx_functions` >> gvs[] >>
  metis_tac[dft_pos_edit_setup]
QED

Theorem dft_pos_gas_call_enter:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_pos_slot C D fi bi f g b b' /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\
  ~MEM v call.inst_outputs /\ s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  eval_operands ops s = SOME args /\ setup_callee calleeR args s = SOME cs ==>
  let addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)];
      t = (update_var v (w addr) s) with vs_inst_idx := SUC s.vs_inst_idx
  in ?calleeL. dft_pos_functions C D calleeL calleeR /\
    FUNPOW (dft_occ_oracle_next w C) 2 l = l with
      <|dft_occ_core := DftOpen (DftEnter calleeL 0 cs)
          (DftCaller f 0 b call t :: MAP (dft_fill_frame 0) ls) (nL+1);
        dft_occ_path := l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)];
        dft_occ_visit := 0;
        dft_occ_saved := (l.dft_occ_path,l.dft_occ_visit)::
          (if ls = [] then [] else l.dft_occ_saved)|> /\
    dft_occ_oracle_next w D r = r with
      <|dft_occ_core := DftOpen (DftEnter calleeR 0 cs)
          (DftCaller g 0 b' call s :: MAP (dft_fill_frame 0) rs) nR;
        dft_occ_path := r.dft_occ_path ++ [(r.dft_occ_visit,call.inst_id)];
        dft_occ_visit := 0;
        dft_occ_saved := (r.dft_occ_path,r.dft_occ_visit)::r.dft_occ_saved|> /\
    dft_cut_pair [(v,w addr)] [] t s
Proof
  strip_tac >>
  `b.bb_instructions = pre ++ [gas;call] ++ post /\
   b'.bb_instructions = pre ++ [call;gas] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  `?calleeL. lookup_function nm C.ctx_functions = SOME calleeL /\
    dft_pos_functions C D calleeL calleeR /\
    (!args s. setup_callee calleeL args s = setup_callee calleeR args s)` by
    metis_tac[dft_pos_gas_call_callee] >>
  qabbrev_tac `addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]` >>
  qabbrev_tac `t = (update_var v (w addr) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `dft_cut_pair [(v,w addr)] [] t s` by
    simp[Abbr `t`, dft_pos_gas_call_cut] >>
  `~MEM (Var v) ops` by metis_tac[dft_pos_gas_call_decode] >>
  `eval_operands ops t = SOME args /\ setup_callee calleeL args t = SOME cs` by
    metis_tac[dft_gas_cut_operands, dft_gas_cut_setup] >>
  `get_instruction b s.vs_inst_idx = SOME gas /\
   get_instruction b t.vs_inst_idx = SOME call /\
   get_instruction b' s.vs_inst_idx = SOME call` by
    simp[get_instruction_def, EL_APPEND_EQN, Abbr `t`, ADD1] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b t)
        (MAP (dft_fill_frame 0) ls) (SUC nL);
      dft_occ_saved := if ls = [] then [] else l.dft_occ_saved|>` by
    (simp[NoAsms, Abbr `t`, Abbr `addr`] >>
     irule dft_pos_gas_one_step >> metis_tac[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftEnter calleeR 0 cs)
        (DftCaller g 0 b' call s :: MAP (dft_fill_frame 0) rs) nR;
      dft_occ_path := r.dft_occ_path ++ [(r.dft_occ_visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (r.dft_occ_path,r.dft_occ_visit)::r.dft_occ_saved|>` by
    (irule dft_pos_gas_call_push >> metis_tac[]) >>
  `dft_occ_oracle_next w C (dft_occ_oracle_next w C l) =
    (dft_occ_oracle_next w C l) with
    <|dft_occ_core := DftOpen (DftEnter calleeL 0 cs)
        (DftCaller f 0 b call t :: MAP (dft_fill_frame 0) (MAP (dft_fill_frame 0) ls))
        (SUC nL);
      dft_occ_path := (dft_occ_oracle_next w C l).dft_occ_path ++
        [((dft_occ_oracle_next w C l).dft_occ_visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := ((dft_occ_oracle_next w C l).dft_occ_path,
        (dft_occ_oracle_next w C l).dft_occ_visit)::
        (dft_occ_oracle_next w C l).dft_occ_saved|>` by
    (irule dft_pos_gas_call_push >> simp[] >> metis_tac[]) >>
  simp[] >> qexists `calleeL` >>
  gvs[FUNPOW_2, Abbr `addr`, Abbr `t`, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, ADD1]
QED

Theorem dft_pos_gas_call_events:
  b.bb_instructions = pre ++ [gas;call] ++ post /\
  b'.bb_instructions = pre ++ [call;gas] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit ==>
  dft_occ_gas_event gas
    (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) l /\
  dft_occ_event call
    (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)])
    (dft_occ_oracle_next w C l) /\
  dft_occ_event call
    (l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)]) r
Proof
  strip_tac >>
  `get_instruction b s.vs_inst_idx = SOME gas` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all dft_pos_gas_one_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[dft_occ_gas_event_def, dft_occ_event_def,
    get_instruction_def, EL_APPEND_EQN, update_var_def, ADD1] >>
  metis_tac[]
QED
