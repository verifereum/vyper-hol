(* Actual entry boundary across one GAS/INVOKE edit. *)
Theory dftOccurrenceCallCrossing
Ancestors
  dftOccurrenceCallStack dftOccurrenceSuspended dftOccurrenceGasEdit
  dftOccurrenceOpenCall dftOccurrenceMachine dftOccurrenceReplay
  dftOpenErase dftOpenMachine dftOccurrenceResidual venomState
  venomExecSemantics venomInst arithmetic list
  unitMemInv contextCodegenRel dftOccurrenceGasEditTrace

Theorem dft_mixed_before_shape:
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n ==>
  ?tailR nR.
    r.dft_occ_core = DftOpen
      (DftAt (dft_gas_edit_fn bb0 pre gas call post fn) 0
        (dft_gas_edit_block bb0 pre gas call post bb0) s) tailR nR /\
    dft_mixed_stack bb0 pre gas call post v w stack tailR
      l.dft_occ_saved r.dft_occ_saved /\
    MAP (dft_fill_frame 0) stack = stack /\
    MAP (dft_fill_frame 0) tailR = tailR /\
    (stack = [] ==> l.dft_occ_saved = []) /\
    l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit
Proof
  simp[dft_mixed_sync_def] >> rpt strip_tac >> gvs[] >>
  drule dft_mixed_stack_erase >> strip_tac >>
  drule dft_mixed_stack_lengths >> strip_tac >>
  simp[dft_edit_control_def] >> metis_tac[LENGTH_NIL]
QED

Theorem dft_mixed_crossing_gas:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_occ_oracle_next w C l = l with dft_occ_core :=
    DftOpen (DftAt fn 0 bb0
      ((update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) s)
        with vs_inst_idx := SUC (LENGTH pre))) stack (SUC n)
Proof
  strip_tac >> drule_all dft_mixed_before_shape >> strip_tac >>
  `get_instruction bb0 s.vs_inst_idx = SOME gas` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all dft_suspend_gas_step >> simp[]
QED

Theorem dft_crossing_fill_twice[local,simp]:
  dft_fill_frame 0 (dft_fill_frame 1 frame) = dft_fill_frame 0 frame
Proof
  Cases_on `frame` >> simp[dft_fill_frame_def]
QED

(* Entry equations, with no future-return premise. *)
Theorem dft_mixed_crossing_entry:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\ ~MEM (Var v) ops /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  let sGas = (update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) s)
                with vs_inst_idx := SUC (LENGTH pre)
  in ?tailR nR.
    dft_occ_oracle_next w C (dft_occ_oracle_next w C l) = l with
      <|dft_occ_core := DftOpen (DftEnter callee 0 cs)
          (DftCaller fn 0 bb0 call sGas::stack) (SUC n);
        dft_occ_path := l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)];
        dft_occ_visit := 0;
        dft_occ_saved := (l.dft_occ_path,l.dft_occ_visit)::l.dft_occ_saved|> /\
    dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r = r with
      <|dft_occ_core := DftOpen
          (DftEnter (dft_gas_edit_fn bb0 pre gas call post callee) 0 cs)
          (DftCaller (dft_gas_edit_fn bb0 pre gas call post fn) 0
            (dft_gas_edit_block bb0 pre gas call post bb0) call s::tailR) nR;
        dft_occ_path := l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)];
        dft_occ_visit := 0;
        dft_occ_saved := (l.dft_occ_path,l.dft_occ_visit)::r.dft_occ_saved|> /\
    dft_mixed_stack bb0 pre gas call post v w stack tailR
      l.dft_occ_saved r.dft_occ_saved
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `DftCaller fn 0 bb0 call sGas` >>
  drule_all dft_mixed_before_shape >> strip_tac >>
  `dft_cut_pair [(v,w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]))] [] sGas s` by
    simp[Abbr `sGas`, dft_suspend_pending_cut] >>
  `eval_operands ops sGas = SOME args` by metis_tac[dft_gas_cut_operands] >>
  `setup_callee callee args sGas = SOME cs` by metis_tac[dft_gas_cut_setup] >>
  `get_instruction bb0 sGas.vs_inst_idx = SOME call /\
   get_instruction (dft_gas_edit_block bb0 pre gas call post bb0) s.vs_inst_idx = SOME call` by
    simp[Abbr `sGas`, get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN] >>
  drule_all dft_mixed_crossing_gas >>
  disch_then (qspec_then `C` assume_tac) >>
  gvs[Abbr `sGas`] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_open_next_def, dft_open_invoke_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       dft_occ_update_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss,
       dft_gas_edit_lookup_function, dft_gas_edit_setup_callee]
QED

Theorem dft_mixed_crossing_success:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\ ~MEM (Var v) ops /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> drule_all dft_mixed_crossing_entry >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `s with vs_inst_idx := LENGTH pre = s` by simp[venom_state_component_equality] >>
  `dft_mixed_frame bb0 pre gas call post v w l.dft_occ_path l.dft_occ_visit
    (DftCaller fn 0 bb0 call
      ((update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) s)
        with vs_inst_idx := SUC (LENGTH pre)))
    (DftCaller (dft_gas_edit_fn bb0 pre gas call post fn) 0
      (dft_gas_edit_block bb0 pre gas call post bb0) call
      (s with vs_inst_idx := LENGTH pre))` by
    (irule dft_mixed_pending_instance >> simp[]) >>
  simp[dft_mixed_sync_def, dft_edit_control_def, dft_fill_control_def] >>
  metis_tac[]
QED

Theorem dft_mixed_crossing_failure:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  ~(?nm ops callee args cs.
    decode_invoke call = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_suspend_cleared
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> drule_all dft_mixed_before_shape >> strip_tac >>
  drule_all dft_mixed_crossing_gas >>
  disch_then (qspec_then `C` assume_tac) >>
  qabbrev_tac `sGas = (update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) s)
    with vs_inst_idx := SUC (LENGTH pre)` >>
  `dft_cut_pair [(v,w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]))] [] sGas s` by
    simp[Abbr `sGas`, dft_suspend_pending_cut] >>
  `get_instruction bb0 sGas.vs_inst_idx = SOME call /\
   get_instruction (dft_gas_edit_block bb0 pre gas call post bb0) s.vs_inst_idx = SOME call` by
    simp[Abbr `sGas`, get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN] >>
  Cases_on `decode_invoke call`
  >- (gvs[Abbr `sGas`] >>
      simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_open_next_def, dft_open_invoke_def, dft_erase_def,
        dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_suspend_cleared_def]) >>
  PairCases_on `x` >>
  `eval_operands x1 sGas = eval_operands x1 s` by
    (irule dft_gas_cut_operands >> simp[] >> metis_tac[]) >>
  `!callee args. setup_callee callee args sGas = setup_callee callee args s` by
    metis_tac[dft_gas_cut_setup] >>
  gvs[Abbr `sGas`] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_open_next_def, dft_open_invoke_def, dft_erase_def,
    dft_fill_def, dft_fill_control_def, dft_occ_update_def,
    dft_gas_edit_lookup_function, dft_gas_edit_setup_callee] >>
  Cases_on `lookup_function x0 C.ctx_functions`
  >- simp[dft_suspend_cleared_def, dft_occ_update_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands x1 s`
  >- simp[dft_suspend_cleared_def, dft_occ_update_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  `setup_callee callee args s = NONE` by
    (Cases_on `setup_callee callee args s` >> gvs[]) >>
  simp[dft_gas_edit_setup_callee, dft_suspend_cleared_def,
       dft_occ_update_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_mixed_crossing:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r) \/
  dft_suspend_cleared
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  Cases_on `?nm ops callee args cs.
    decode_invoke call = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs`
  >- (pop_assum strip_assume_tac >> disj1_tac >>
      irule dft_mixed_crossing_success >> metis_tac[]) >>
  disj2_tac >> irule dft_mixed_crossing_failure >> simp[] >> metis_tac[]
QED

Theorem dft_mixed_crossing_gas_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ dft_open_observe fn' inst st l.dft_occ_core ==>
  inst_mem_ranges inst st = []
Proof
  simp[dft_open_observe_def] >> rpt strip_tac >> gvs[] >>
  `inst = gas` by gvs[get_instruction_def, EL_APPEND_EQN] >>
  irule dft_edit_gas_ranges >> simp[]
QED

Theorem dft_mixed_crossing_call_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ dft_open_observe fnR inst st r.dft_occ_core ==>
  ?sL. dft_open_observe fn call sL (dft_occ_oracle_next w C l).dft_occ_core /\
    sL.vs_memory = st.vs_memory /\ sL.vs_alloca_next = st.vs_alloca_next /\
    inst_mem_ranges call sL = inst_mem_ranges inst st
Proof
  strip_tac >> drule_all dft_mixed_before_shape >> strip_tac >>
  drule_all dft_mixed_crossing_gas >>
  disch_then (qspec_then `C` assume_tac) >>
  gvs[dft_open_observe_def] >>
  `inst = call` by
    gvs[get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN] >>
  simp[dft_open_observe_def, get_instruction_def, EL_APPEND_EQN,
       update_var_def, inst_mem_ranges_def, source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem dft_mixed_crossing_nested_entry:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\ ~MEM (Var v) ops /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  dft_mixed_frame bb0 pre gas call post v w p j
    (DftCaller outerL 0 blockL call oldL)
    (DftCaller outerR 0 blockR call oldR) /\ oldL <> oldR /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s)
    [DftCaller outerL 0 blockL call oldL] nL /\
  r.dft_occ_core = DftOpen
    (DftAt (dft_gas_edit_fn bb0 pre gas call post fn) 0
      (dft_gas_edit_block bb0 pre gas call post bb0) s)
    [DftCaller outerR 0 blockR call oldR] nR /\
  l.dft_occ_saved = [(p,j)] /\ r.dft_occ_saved = [(p,j)] /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_mixed_sync bb0 pre gas call post v w
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >> irule dft_mixed_crossing_success >>
  simp[] >>
  `dft_mixed_sync bb0 pre gas call post v w l r` by
    (simp[dft_mixed_sync_def, dft_edit_control_def, dft_fill_control_def] >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem dft_mixed_crossing_enter_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\ ~MEM (Var v) ops /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  ~dft_open_observe fnL inst st
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l)).dft_occ_core /\
  ~dft_open_observe fnR inst st
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r).dft_occ_core
Proof
  strip_tac >> drule_all dft_mixed_crossing_entry >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> simp[dft_open_observe_def]
QED
