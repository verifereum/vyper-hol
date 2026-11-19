(* Stopped no-call rows: fixed inventories, including early failure. *)
Theory gasFocusTerminalInventory
Ancestors
  gasFocusInitialRowReplay gasFocusTerminalRow dftIndexedExec dftRunRel
  gasEvents gasOracleReplay frameGasEvents venomExecSemantics venomExecProofs
  venomInst venomState stateEquiv list rich_list arithmetic

Theorem focus_terminal_silent_extension[local]:
  !zs s bb bb' last.
    DROP s.vs_inst_idx bb.bb_instructions = zs ++ [last] /\
    DROP s.vs_inst_idx bb'.bb_instructions = zs /\
    is_terminator last.inst_opcode ==>
    gas_events_block fuel C owner bb s = gas_events_block fuel C owner bb' s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`s.vs_inst_idx < LENGTH bb.bb_instructions /\
       LENGTH bb'.bb_instructions <= s.vs_inst_idx` by
        (qpat_x_assum `DROP _ bb.bb_instructions = _`
           (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
         gvs[DROP_EQ_NIL, LENGTH_DROP]) >>
      `EL s.vs_inst_idx bb.bb_instructions = last` by
        (qpat_x_assum `DROP _ bb.bb_instructions = _`
           (mp_tac o AP_TERM ``EL 0:instruction list -> instruction``) >>
         simp[EL_DROP]) >>
      `last.inst_opcode <> GAS /\ last.inst_opcode <> INVOKE` by
        (Cases_on `last.inst_opcode` >> gvs[is_terminator_def]) >>
      once_rewrite_tac[gas_events_block_def] >>
      simp[get_instruction_def, gas_events_step_def] >>
      Cases_on `step_inst fuel C last s` >> simp[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH bb'.bb_instructions` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ bb'.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx bb'.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = zs ++ [last] /\
   DROP (SUC s.vs_inst_idx) bb'.bb_instructions = zs` by
    gvs[DROP_CONS_EL] >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  Cases_on `is_terminator h.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem focus_terminal_row_inventory:
  !fuel C fn entry bb ps zs last sp.
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = ps ++ zs ++ [last] /\
    phi_prefix_length bb.bb_instructions = LENGTH ps /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    eval_phis entry bb.bb_instructions = OK sp /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_pseudo i.inst_opcode) zs /\
    is_terminator last.inst_opcode ==>
    !sites. sites = MAP (\i. (fn.fn_name,i.inst_id))
                      (FILTER (\i. i.inst_opcode = GAS) zs) ==>
    !slots. slots = REPLICATE (LENGTH sites) NONE ==>
    !keys. keys = MAP (\i. (a,e,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) zs) ==>
    LENGTH slots = LENGTH sites /\ LENGTH keys = LENGTH sites /\
       FILTER IS_SOME slots = [] /\
       !gs tail.
         LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots gs ==>
         !R. R = entry with vs_gas_readings := gs ++ tail ==>
         !B. B = sp with <|vs_inst_idx := LENGTH ps; vs_gas_readings := gs ++ tail|> ==>
         ((!q. FOLDR (dft_exec_cons fuel C) OK zs B = q /\
               (!u. q <> OK u) ==>
               run_blocks (SUC fuel) C fn R = q /\
               (?extra. sites = gas_events_blocks (SUC fuel) C fn R ++ extra)) /\
          (!t r. FOLDR (dft_exec_cons fuel C) OK zs B = OK t /\
                 step_inst fuel C last t = r /\
                 ((!u. r <> OK u) \/ (?u. r = OK u /\ u.vs_halted)) ==>
                 run_blocks (SUC fuel) C fn R =
                   (case r of OK u => Halt u | other => other) /\
                 gas_events_blocks (SUC fuel) C fn R = sites))
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  rpt gen_tac >> strip_tac >> simp[] >>
  `FILTER IS_SOME (REPLICATE
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) zs)) (NONE:256 word option)) = []` by
    (qsuff_tac `!n. FILTER IS_SOME (REPLICATE n (NONE:256 word option)) = []`
     >- simp[] >> Induct >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `LENGTH gs = LENGTH (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `eval_phis (entry with vs_gas_readings := gs ++ tail) bb.bb_instructions =
   OK (sp with vs_gas_readings := gs ++ tail)` by
    (mp_tac (Q.SPECL [`bb.bb_instructions`, `entry`] gas_eval_phis) >>
     simp[gas_replay_at_def] >>
     disch_then (qspec_then `gs ++ tail` mp_tac) >>
     Cases_on `eval_phis (entry with vs_gas_readings := gs ++ tail) bb.bb_instructions` >>
     gvs[lift_result_def]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) C fn R` >>
  qmatch_goalsub_abbrev_tac `FOLDR (dft_exec_cons fuel C) OK zs B` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) zs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `DROP B.vs_inst_idx bb.bb_instructions = zs ++ [last]` by
    (`LENGTH ps - (LENGTH ps + LENGTH zs) = 0` by decide_tac >>
     simp[Abbr `B`, DROP_APPEND]) >>
  `exec_block fuel C bb B = dft_exec_suffix fuel C (zs ++ [last]) B` by
    (irule dft_exec_suffix_boundary >> simp[]) >>
  `B with vs_gas_readings := gs ++ tail = B` by simp[Abbr `B`] >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
    focus_initial_unvisited_row_replay) >>
  disch_then (qspecl_then [`fuel`, `C`, `fn.fn_name`, `B`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_events_block fuel C fn.fn_name short B` >>
  `gas_events_block fuel C fn.fn_name bb B =
   gas_events_block fuel C fn.fn_name short B` by
    (irule focus_terminal_silent_extension >>
     qexistsl_tac [`last`, `zs`] >> simp[Abbr `short`, DROP_APPEND]) >>
  `lookup_block R.vs_current_bb fn.fn_blocks = SOME bb` by simp[Abbr `R`] >>
  `run_block fuel C bb R = exec_block fuel C bb B` by
    simp[run_block_def, Abbr `B`] >>
  `gas_events_blocks (SUC fuel) C fn R =
   gas_events_block fuel C fn.fn_name bb B ++
   (case exec_block fuel C bb B of
      OK t => if t.vs_halted then [] else gas_events_blocks fuel C fn t
    | other => [])` by
    simp[Once gas_events_blocks_def, Abbr `B`] >>
  conj_tac >- suspend "early" >> suspend "terminal"
QED

Resume focus_terminal_row_inventory[early]:
  strip_tac >>
  `exec_block fuel C bb B = FOLDR (dft_exec_cons fuel C) OK zs B` by
    (simp[dft_exec_suffix_append, Once dft_exec_prefix_continue] >>
     Cases_on `FOLDR (dft_exec_cons fuel C) OK zs B` >> gvs[]) >>
  Cases_on `dft_exec_suffix fuel C (zs ++ [last]) B` >>
  gvs[run_blocks_unfold]
QED

Resume focus_terminal_row_inventory[terminal]:
  gen_tac >> strip_tac >>
  `exec_block fuel C bb B =
   (case step_inst fuel C last t of OK u => Halt u | other => other)` by
    (simp[dft_exec_suffix_append, Once dft_exec_prefix_continue] >>
     simp[dft_exec_suffix_def] >>
     Cases_on `step_inst fuel C last t` >> gvs[]) >>
  `gas_events_block fuel C fn.fn_name short B =
   MAP (\i. (fn.fn_name,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) zs)` by
    metis_tac[] >>
  Cases_on `step_inst fuel C last t` >>
  Cases_on `dft_exec_suffix fuel C (zs ++ [last]) B` >>
  gvs[run_blocks_unfold]
QED

Finalise focus_terminal_row_inventory
