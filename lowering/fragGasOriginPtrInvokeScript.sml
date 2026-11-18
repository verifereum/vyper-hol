(* Shared completed INVOKE transport for joint origin/pointer paths. *)
Theory fragGasOriginPtrInvoke
Ancestors
  fragGasOriginPtrExec fragGasOriginPtr fragGasOrigin fragGasFocus
  fragGasPathPtr fragExecPtr fragExecMem fragExec gasEvents gasEventsFuel
  ptrSafeRun memSafeRun contextCodegenRel codegenRel unitTransformDefs intCallStep
  venomExecSemantics venomExecProofs
  venomInst venomState finite_map list arithmetic

Theorem terminal_path_certificate[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) marks (r,G',tn') /\ exit_result r ==>
  ?fuel bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_from fuel ctx fn s = r /\
    ghost_run fuel ctx fn PG G tn s = (G',tn') /\
    mem_safe_run fuel ctx fn s /\
    ptr_safe_run D lo fuel ctx fn PG G tn s /\
    marks = MAP (\key. key IN explicit)
      (gas_events_block fuel ctx fn.fn_name bb s ++
       case exec_block fuel ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks fuel ctx fn u
       | _ => [])
Proof
  strip_tac >>
  drule gas_origin_ptr_path_exec >>
  disch_then strip_assume_tac
  >- gvs[exit_result_def] >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule_all gas_origin_path_events >> strip_tac >>
  `!e. run_from fuel ctx fn s <> Error e` by
    metis_tac[exit_result_not_error] >>
  `!e. run_from fuel' ctx fn s <> Error e` by
    metis_tac[exit_result_not_error] >>
  `!k. run_from k ctx fn s = block_run k ctx fn bb s` by
    simp[run_from_def, block_run_def] >>
  `!e. block_run fuel ctx fn bb s <> Error e` by metis_tac[] >>
  `!e. block_run fuel' ctx fn bb s <> Error e` by metis_tac[] >>
  `ghost_block fuel' ctx fn PG G tn bb s = ghost_block fuel ctx fn PG G tn bb s` by
    (Cases_on `fuel <= fuel'`
     >- (irule (cj 2 ghost_fuel_mono_up) >> simp[]) >>
     sym_tac >> irule (cj 2 ghost_fuel_mono_up) >> simp[]) >>
  `ghost_run fuel' ctx fn PG G tn s = (G',tn')` by
    (qpat_x_assum `ghost_run fuel _ _ _ _ _ _ = _` mp_tac >>
     simp[ghost_run_def]) >>
  qexistsl_tac [`fuel'`,`bb`] >> simp[] >>
  metis_tac[mem_safe_run_all_fuel, ptr_safe_run_all_fuel]
QED

Theorem setup_terminal_certificate:
  enters_block fn setup entered /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (entered,G,tn) marks (r,G',tn') /\ exit_result r ==>
  ?fuel.
    run_blocks fuel ctx fn setup = r /\
    ghost_blocks fuel ctx fn PG G tn setup = (G',tn') /\
    mem_safe_blocks fuel ctx fn setup /\
    ptr_safe_blocks D lo fuel ctx fn PG G tn setup /\
    marks = MAP (\key. key IN explicit) (gas_events_blocks fuel ctx fn setup)
Proof
  strip_tac >> drule_all terminal_path_certificate >> strip_tac >>
  `frame_run fuel ctx fn entered = r` by
    gvs[frame_run_def, run_from_def, block_run_def] >>
  drule_then (qspecl_then [`ctx`,`PG`,`G`,`tn`,`fuel`] strip_assume_tac)
    frame_run_enters_block >>
  qexists_tac `SUC fuel` >> simp[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `lookup_block entered.vs_current_bb fn.fn_blocks = SOME bb'` by
    (drule eval_phis_preserves_current_bb >> simp[] >> strip_tac >> gvs[]) >>
  gvs[] >>
  simp[Once mem_safe_blocks_def, Once ptr_safe_blocks_def,
       mem_safe_run_def, ptr_safe_run_def] >>
  gvs[mem_safe_run_def, ptr_safe_run_def] >>
  simp[SimpRHS, Once gas_events_blocks_def]
QED

Theorem gas_origin_ptr_invoke_intret:
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  gas_invoke_entry (ctx,caller) s callee entered /\
  ptr_inst_ok D lo 0 ctx caller G tn inst s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ret se,Gc,tc) /\
  LENGTH inst.inst_outputs = LENGTH ret.iret_values ==>
  ?out.
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s se)) = SOME out /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,caller,PG) (s,G,tn) marks
      (OK (out with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL (set inst.inst_outputs)),
       tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
Proof
  strip_tac >>
  qpat_x_assum `gas_invoke_entry _ _ _ _` mp_tac >>
  simp[gas_invoke_entry_def] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac
    `gas_origin_ptr_path _ (entered,FEMPTY,_) _ _` >>
  `enters_block callee setup entered` by
    (simp[enters_block_def, Abbr `entered`] >> metis_tac[]) >>
  `exit_result (IntRet ret se)` by simp[exit_result_def] >>
  drule_all setup_terminal_certificate >> strip_tac >>
  `?out. bind_outputs inst.inst_outputs ret.iret_values
     (adopt_return_fmp ret (merge_callee_state s se)) = SOME out` by
    simp[bind_outputs_def] >>
  `step_inst fuel ctx inst s = OK out` by simp[Once step_inst_def] >>
  `~out.vs_halted` by
    (drule_all step_inst_invoke_OK_control >> simp[]) >>
  `mem_safe_step fuel ctx inst s` by
    (drule_all mem_safe_step_invoke >>
     simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `ptr_safe_step D lo fuel ctx caller PG G tn inst s` by
    (simp[Once ptr_safe_step_def] >>
     gvs[ptr_inst_ok_def]) >>
  `ghost_step fuel ctx PG G tn inst s =
    (DRESTRICT G (COMPL (set inst.inst_outputs)),
     tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))` by
    (drule_all ghost_step_invoke >> simp[]) >>
  `marks = MAP (\key. key IN explicit)
      (gas_events_step fuel ctx caller.fn_name inst s)` by
    simp[Once gas_events_step_def] >>
  qexists_tac `out` >> simp[] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac
  >- (qexists_tac `fuel` >> simp[is_terminator_def]) >>
  qexists_tac `fuel` >>
  simp[is_terminator_def] >>
  metis_tac[gas_events_length, LENGTH_MAP]
QED

Theorem gas_origin_ptr_invoke_exit:
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  gas_invoke_entry (ctx,caller) s callee entered /\
  ptr_inst_ok D lo 0 ctx caller G tn inst s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (r,Gc,tc) /\
  exit_result r /\ (!ret se. r <> IntRet ret se) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,caller,PG) (s,G,tn) marks (r,G,tn)
Proof
  strip_tac >>
  qpat_x_assum `gas_invoke_entry _ _ _ _` mp_tac >>
  simp[gas_invoke_entry_def] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac
    `gas_origin_ptr_path _ (entered,FEMPTY,_) _ _` >>
  `enters_block callee setup entered` by
    (simp[enters_block_def, Abbr `entered`] >> metis_tac[]) >>
  drule_all setup_terminal_certificate >> strip_tac >>
  `step_inst fuel ctx inst s = r` by
    (Cases_on `r` >> gvs[exit_result_def] >> simp[Once step_inst_def]) >>
  `mem_safe_step fuel ctx inst s` by
    (drule_all mem_safe_step_invoke >>
     simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `ptr_safe_step D lo fuel ctx caller PG G tn inst s` by
    (simp[Once ptr_safe_step_def] >> gvs[ptr_inst_ok_def]) >>
  `marks = MAP (\key. key IN explicit)
      (gas_events_step fuel ctx caller.fn_name inst s)` by
    simp[Once gas_events_step_def] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac
  >- (qexists_tac `fuel` >> simp[]) >>
  qexists_tac `fuel` >> simp[] >>
  metis_tac[gas_events_length, LENGTH_MAP]
QED
