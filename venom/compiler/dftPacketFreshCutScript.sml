Theory dftPacketFreshCut
Ancestors
  dftPacketEntryReplay dftPacketFreshRow dftPacketNativeSlice dftRunRel dftIndexedExec
  dftGasToListReplay gasEvents frameGasEvents venomExecSemantics
  venomInst venomState venomExecProofs stateEquiv list rich_list arithmetic

Theorem fresh_cut_pseudo_events[local]:
  !pre bb s t.
    EVERY (\i. is_pseudo i.inst_opcode) pre /\
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ rest /\
    FOLDR (dft_exec_cons f C) OK pre s = OK t ==>
    gas_events_block f C owner bb s = gas_events_block f C owner bb t
Proof
  Induct_on `pre` >- simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> GAS /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[LIST_EQ_REWRITE,LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ rest` by
    gvs[DROP_CONS_EL] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  gvs[dft_exec_cons_def,AllCaseEqs()] >>
  rename1 `step_inst f C h s = OK u` >>
  simp[Once gas_events_defs,get_instruction_def,gas_events_step_plain] >>
  first_x_assum irule >> simp[]
QED

Theorem fresh_cut_body_eval[local]:
  R = (\entry. case eval_phis entry bb.bb_instructions of
    OK sp =>
      (gas_events_block f C7 sf.fn_name
        (bb with bb_instructions :=
          TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
       FOLDR (dft_exec_cons f C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  FOLDR (dft_exec_cons g C8) OK
    (DROP (phi_prefix_length (ps ++ ys)) ps)
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
  be.vs_inst_idx = LENGTH ps /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs ==>
  !gs. R (entry with vs_gas_readings := gs) =
    (gas_events_block f C7 sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>
      (be with vs_gas_readings := gs),
     FOLDR (dft_exec_cons f C7) OK (TAKE q xs)
      (be with vs_gas_readings := gs))
Proof
  strip_tac >> gen_tac >>
  drule_all dft_packet_body_entry_replay >>
  disch_then (qspecl_then [`gs`,`f`,`C7`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     res_tac >> Cases_on `i.inst_opcode` >>
     gvs[is_pseudo_def,is_terminator_def]) >>
  gvs[dft_phi_prefix_append,dft_eval_phis_append] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (DROP (phi_prefix_length ps) ps)` by simp[EVERY_DROP] >>
  simp[Once FOLDR_APPEND] >>
  reverse conj_tac
  >- simp[Once dft_exec_prefix_continue] >>
  `TAKE (phi_prefix_length ps) (ps ++ xs) = TAKE (phi_prefix_length ps) ps` by
    simp[TAKE_APPEND1,phi_prefix_length_le] >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC,TAKE_DROP] >>
  qmatch_goalsub_abbrev_tac `gas_events_block f C7 sf.fn_name eb _` >>
  `gas_events_block f C7 sf.fn_name eb
      (sp' with vs_inst_idx := phi_prefix_length ps) =
    gas_events_block f C7 sf.fn_name eb (be with vs_gas_readings := gs)` by
    (irule fresh_cut_pseudo_events >>
     qexistsl [`DROP (phi_prefix_length ps) ps`,`TAKE q xs`] >>
     simp[EVERY_DROP,Abbr `eb`,DROP_APPEND1,phi_prefix_length_le]) >>
  asm_rewrite_tac[] >>
  irule gas_events_block_suffix_cong >>
  qexists `TAKE q xs` >>
  simp[Abbr `eb`,DROP_APPEND]
QED

Theorem dft_packet_fresh_body_cut:
  R = (\entry. case eval_phis entry bb.bb_instructions of
    OK sp =>
      (gas_events_block f C7 sf.fn_name
        (bb with bb_instructions :=
          TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
       FOLDR (dft_exec_cons f C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  FOLDR (dft_exec_cons g C8) OK
    (DROP (phi_prefix_length (ps ++ ys)) ps)
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
  be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(a,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss ==>
  SND (R (entry with vs_gas_readings := FLAT kgss ++ tail)) =
    FOLDR (dft_exec_cons f C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) /\
  (?extra. FLAT (TAKE q ess) =
    FST (R (entry with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
  (!events u. R (entry with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
    events = FLAT (TAKE q ess) /\ u.vs_gas_readings = tail /\
    trace_gas (trace_block a e f C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
      (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE q ks),FLAT kgss) /\
    !tail'. R (entry with vs_gas_readings := FLAT kgss ++ tail') =
      (events,OK (u with vs_gas_readings := tail')))
Proof
  strip_tac >>
  drule_all fresh_cut_body_eval >> disch_then assume_tac >>
  `q <= LENGTH xs` by decide_tac >>
  drule_all dft_packet_fresh_row_replay >>
  disch_then (qspecl_then [`tail`,`f`,`C7`] strip_assume_tac) >>
  qpat_x_assum `R = _` kall_tac >>
  qpat_assum `!gs. R _ = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[pairTheory.FST,pairTheory.SND,pairTheory.PAIR_EQ] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `_ = _ ++ extra` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >>
  strip_tac >> metis_tac[]
QED

Theorem dft_packet_fresh_pseudo_cut:
  R = (\entry. case eval_phis entry bb.bb_instructions of
    OK sp =>
      (gas_events_block f C7 sf.fn_name
        (bb with bb_instructions :=
          TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
       FOLDR (dft_exec_cons f C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  phi_prefix_length (ps ++ ys) <= k /\ k < LENGTH ps /\
  z = DROP (phi_prefix_length bb.bb_instructions) (TAKE k ps) /\
  FOLDR (dft_exec_cons g C8) OK
    (DROP (phi_prefix_length (ps ++ ys)) (TAKE k ps))
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK t ==>
  !gs. R (entry with vs_gas_readings := gs) =
    ([],OK (t with vs_gas_readings := gs))
Proof
  strip_tac >> gen_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     res_tac >> Cases_on `i.inst_opcode` >>
     gvs[is_pseudo_def,is_terminator_def]) >>
  gvs[dft_phi_prefix_append,dft_eval_phis_append] >>
  qspecl_then [`ps`,`entry`,`gs`] mp_tac replay_phis >>
  simp[residual_result_def] >>
  Cases_on `eval_phis (entry with vs_gas_readings := gs) ps` >>
  simp[lift_result_def] >> strip_tac >> gvs[] >>
  `EVERY (\i. is_pseudo i.inst_opcode)
     (DROP (phi_prefix_length ps) (TAKE k ps))` by
    simp[EVERY_DROP,EVERY_TAKE] >>
  qpat_x_assum `FOLDR _ _ _ _ = OK t`
    (mp_then Any mp_tac dft_packet_pseudo_fold_gas) >>
  simp[] >>
  disch_then (qspecl_then [`gs`,`f`,`C7`] assume_tac) >>
  `TAKE (phi_prefix_length ps) (ps ++ xs) =
   TAKE (phi_prefix_length ps) (TAKE k ps)` by
    simp[TAKE_APPEND1,phi_prefix_length_le,TAKE_TAKE_T] >>
  pure_asm_rewrite_tac[TAKE_DROP] >>
  simp[] >>
  `t.vs_inst_idx = k` by
    (qspecl_then [`k - phi_prefix_length ps`,
       `sp with <|vs_inst_idx := phi_prefix_length ps; vs_gas_readings := gs|>`,
       `t with vs_gas_readings := gs`] mp_tac
       (Q.INST [`bb` |-> `bb with bb_instructions := TAKE k ps`,
                `fuel` |-> `f`, `C` |-> `C7`]
         (cj 1 native_trace_block_prefix_split)) >>
     simp[TAKE_LENGTH_TOO_LONG,EVERY_DROP,EVERY_TAKE]) >>
  `gas_events_block f C7 sf.fn_name (bb with bb_instructions := TAKE k ps)
     (sp with <|vs_inst_idx := phi_prefix_length ps; vs_gas_readings := gs|>) =
   gas_events_block f C7 sf.fn_name (bb with bb_instructions := TAKE k ps)
     (t with vs_gas_readings := gs)` by
    (irule fresh_cut_pseudo_events >>
     qexistsl [`DROP (phi_prefix_length ps) (TAKE k ps)`,`[]`] >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[Once gas_events_defs,get_instruction_def,LENGTH_TAKE]
QED
