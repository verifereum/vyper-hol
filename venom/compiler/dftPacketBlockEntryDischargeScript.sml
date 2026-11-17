Theory dftPacketBlockEntryDischarge
Ancestors
  dftPacketBlockFreshEntry dftPacketCalleeInitialization dftPacketCallRowStructure dftCorrectness
  dftPacketClosedRowNative dftGasFromListRestore dftGasFromListLookup
  dftAvailability dftRunRel dftIndexedExec o1PassContract unitShapeDefs
  venomWf venomWfProps venomExecProofs venomExecSemantics venomInst
  venomState list rich_list sorting

(* The successful source full-row endpoint may have arbitrary readings.
   Availability and labels depend only on the other state components. *)
Theorem dft_packet_block_entry_discharge:
  dft_fn_rel sf tf /\ tf = dft_fn sf /\
  o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\
  lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb0 /\
  strict_dom_vars_defined sf in_state /\
  fn_reachable sf in_state.vs_current_bb /\
  ctx_labels_bound C7 in_state.vs_labels /\
  ctx_labels_bound C8 in_state.vs_labels /\
  bb0.bb_instructions = ps0 ++ xs0 /\
  EVERY (\i. is_pseudo i.inst_opcode) ps0 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs0 /\
  xs0 <> [] /\ is_terminator (LAST xs0).inst_opcode /\
  eval_phis in_state bb0.bb_instructions = OK sp0 /\
  FOLDR (dft_exec_cons fuel C7) OK
    (DROP (phi_prefix_length bb0.bb_instructions) bb0.bb_instructions)
    ((sp0 with vs_gas_readings := gs) with
      vs_inst_idx := phi_prefix_length bb0.bb_instructions) =
    OK (post with vs_gas_readings := tail) /\
  step_inst f C8 inst s = OK post /\ ~post.vs_halted /\
  enters_block tf post s1 /\
  lookup_block post.vs_current_bb tf.fn_blocks = SOME bt1 /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
  get_instruction bt1 s1.vs_inst_idx = SOME next ==>
  ?bb1 ps1 xs1 ys1 rho1.
    lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
    lookup_block post.vs_current_bb tf.fn_blocks = SOME bt1 /\
    bt1.bb_label = bb1.bb_label /\ bb1.bb_label = post.vs_current_bb /\
    bb1.bb_instructions = ps1 ++ xs1 /\ bt1.bb_instructions = ps1 ++ ys1 /\
    EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\
    EVERY inst_shape_ok bb1.bb_instructions /\
    EVERY inst_wf bb1.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs1) /\
    LENGTH xs1 = LENGTH ys1 /\ PERM rho1 (COUNT_LIST (LENGTH xs1)) /\
    LIST_REL (\q y. q < LENGTH xs1 /\
      y.inst_id = (EL q xs1).inst_id /\ from_block [EL q xs1] y) rho1 ys1 /\
    strict_dom_vars_defined sf post /\ fn_reachable sf post.vs_current_bb /\
    ctx_labels_bound C7 post.vs_labels /\ ctx_labels_bound C8 post.vs_labels /\
    (s1.vs_inst_idx = LENGTH ps1 ==> dft_remaining_inv sf bb1 xs1 s1) /\
    !a d j N'.
    ?body_entry ms ess ks count front closed brest.
      count = 0 /\ front = OK s1 /\ closed = F /\ brest = NONE /\
      phi_prefix_length bt1.bb_instructions <= s1.vs_inst_idx /\
      s1.vs_inst_idx <= LENGTH ps1 /\
      (if s1.vs_inst_idx < LENGTH ps1 then
         body_entry = NONE /\ ms = [] /\ ess = [] /\ ks = [] /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length bt1.bb_instructions) (TAKE s1.vs_inst_idx ps1))
           (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
         (!F gs z R.
           N' <= F /\
           z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) /\
           R = (\entry. case eval_phis entry bb1.bb_instructions of
             OK sp =>
               (gas_events_block (F-SUC d) C7 sf.fn_name
                 (bb1 with bb_instructions :=
                   TAKE (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions ++ z)
                 (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions),
                FOLDR (dft_exec_cons (F-SUC d) C7) OK z
                 (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
             | other => ([],other)) ==>
           R (post with vs_gas_readings := gs) =
             ([],OK (s1 with vs_gas_readings := gs)))
       else
         s1.vs_inst_idx = LENGTH ps1 /\ body_entry = SOME (s1,SUC j) /\
         dft_remaining_inv sf bb1 xs1 s1 /\
         ms = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
         ess = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
         ks = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(a,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length bt1.bb_instructions) ps1)
           (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
         LENGTH ms = LENGTH xs1 /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
         LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
         LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
         ALL_DISTINCT (FLAT ks) /\
         (!q. q < LENGTH xs1 ==>
           ((EL q xs1).inst_opcode = GAS ==>
             EL q ms = [NONE] /\ EL q ess = [(sf.fn_name,(EL q xs1).inst_id)] /\
             EL q ks = [(a,SUC d,(EL q xs1).inst_id)]) /\
           ((EL q xs1).inst_opcode <> GAS ==>
             EL q ms = [] /\ EL q ess = [] /\ EL q ks = [])) /\
         (!F k kgss tail.
           N' <= F /\ k <= LENGTH xs1 /\
           EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs1) /\
           (!q. q < k /\ (EL q xs1).inst_opcode = INVOKE ==> MEM q (TAKE 0 rho1)) /\
           LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
             (TAKE k ms) kgss ==>
           (?extra. FLAT (TAKE k ess) =
             gas_events_block (F-SUC d) C7 sf.fn_name
               <|bb_label := s1.vs_current_bb; bb_instructions :=
                 REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
               (s1 with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
           (!u. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
               (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
             gas_events_block (F-SUC d) C7 sf.fn_name
               <|bb_label := s1.vs_current_bb; bb_instructions :=
                 REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
               (s1 with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
             u.vs_gas_readings = tail /\
             trace_gas (trace_block a (SUC d) (F-SUC d) C7 sf
               (bb1 with bb_instructions := TAKE (LENGTH ps1 + k) bb1.bb_instructions)
               (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
                 ZIP (FLAT (TAKE k ks),FLAT kgss) /\
             (!tail'.
               FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
                 (s1 with vs_gas_readings := FLAT kgss ++ tail') =
                   OK (u with vs_gas_readings := tail') /\
               gas_events_block (F-SUC d) C7 sf.fn_name
                 <|bb_label := s1.vs_current_bb; bb_instructions :=
                   REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
                 (s1 with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
         (!F q kgss tail z R.
           N' <= F /\ q < LENGTH xs1 /\
           EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
           (!r. r < q /\ (EL r xs1).inst_opcode = INVOKE ==> MEM r (TAKE 0 rho1)) /\
           z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
           R = (\entry. case eval_phis entry bb1.bb_instructions of
             OK sp =>
               (gas_events_block (F-SUC d) C7 sf.fn_name
                 (bb1 with bb_instructions :=
                   TAKE (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions ++ z)
                 (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions),
                FOLDR (dft_exec_cons (F-SUC d) C7) OK z
                 (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
             | other => ([],other)) /\
           LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss ==>
           SND (R (post with vs_gas_readings := FLAT kgss ++ tail)) =
             FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q xs1)
               (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
           (?extra. FLAT (TAKE q ess) =
             FST (R (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
           (!events u. R (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
             events = FLAT (TAKE q ess) /\ u.vs_gas_readings = tail /\
             trace_gas (trace_block a (SUC d) (F-SUC d) C7 sf
               (bb1 with bb_instructions := TAKE (LENGTH ps1 + q) bb1.bb_instructions)
               (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
                 ZIP (FLAT (TAKE q ks),FLAT kgss) /\
             !tail'. R (post with vs_gas_readings := FLAT kgss ++ tail') =
               (events,OK (u with vs_gas_readings := tail')))))
Proof
  strip_tac >>
  `wf_function sf /\ ssa_form sf /\ fn_inst_wf sf` by
    gvs[dft_fn_rel_def,wf_ssa_def] >>
  `MEM bb0 sf.fn_blocks /\ bb0.bb_label = in_state.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  `EVERY inst_wf bb0.bb_instructions` by
    (gvs[fn_inst_wf_def,EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `run_block fuel C7 bb0 (in_state with vs_gas_readings := gs) =
    OK (post with vs_gas_readings := tail)` by suspend "source_run" >>
  `fn_reachable sf post.vs_current_bb /\ strict_dom_vars_defined sf post` by
    (`strict_dom_vars_defined sf (in_state with vs_gas_readings := gs)` by
       (qpat_x_assum `strict_dom_vars_defined sf in_state` mp_tac >>
        simp[strict_dom_vars_defined_def]) >>
     drule_all dft_successor_available >> simp[strict_dom_vars_defined_def]) >>
  `ctx_labels_bound C7 post.vs_labels /\ ctx_labels_bound C8 post.vs_labels` by
    (drule ctx_labels_bound_run_block >> simp[] >>
     drule ctx_labels_bound_run_block >> simp[]) >>
  `?bb1. lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1` by
    (Cases_on `lookup_block post.vs_current_bb sf.fn_blocks` >>
     metis_tac[dft_fn_lookup_block_none,optionTheory.NOT_NONE_SOME]) >>
  drule_all dft_packet_paired_row_structure >> strip_tac >>
  rename1 `PERM rho1 (COUNT_LIST (LENGTH xs1))` >>
  `MEM bb1 sf.fn_blocks /\ bb1.bb_label = post.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  `EVERY inst_shape_ok bb1.bb_instructions` by suspend "shape" >>
  `s1.vs_inst_idx = LENGTH ps ==> dft_remaining_inv sf bb1 xs1 s1` by
    (drule_all dft_packet_callee_body_initialized >> simp[]) >>
  qexistsl [`bb1`,`ps`,`xs1`,`ys`,`rho1`] >> simp[] >>
  rpt gen_tac >> irule dft_packet_block_fresh_entry >> simp[] >>
  qexistsl [`C8`,`post`,`sp1`] >> simp[]
QED

Resume dft_packet_block_entry_discharge[source_run]:
  FAIL_TAC "source_run"
QED

Resume dft_packet_block_entry_discharge[shape]:
  `EVERY inst_shape_ok (fn_insts sf)` by
    (qpat_x_assum `o1_ctx_shape C7` mp_tac >>
     simp[o1_ctx_shape_def,EVERY_MEM] >> strip_tac >>
     qpat_x_assum `!e. MEM e C7.ctx_functions ==> _`
       (qspec_then `sf` mp_tac) >>
     simp[o1_fn_shape_def,fn_shape_ok_def,EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `EVERY inst_shape_ok (fn_insts sf)` mp_tac >>
  simp[EVERY_MEM,fn_insts_def] >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  irule fmp_fn_insts_blocks_intro >> qexists_tac `bb1` >> simp[]
QED

Finalise dft_packet_block_entry_discharge
