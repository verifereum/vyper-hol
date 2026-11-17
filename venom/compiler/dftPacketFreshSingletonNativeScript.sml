Theory dftPacketFreshSingletonNative
Ancestors dftRunRel[qualified,ignore_grammar]
  dftPacketFreshSingletonNormalize dftPacketFreshChildOccurrence
  dftPacketEntryReplay dftPacketFreshRow dftPacketFillingBoundary
  dftIndexedExec dftGasFromListTraceDefs gasEvents venomExecSemantics
  venomInst venomState venomExecProofs list rich_list arithmetic

Theorem dft_packet_fresh_singleton_native:
  !F.
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis entry (ps ++ ys) = OK sp /\
  m = phi_prefix_length bb.bb_instructions /\
  e = SUC d /\ e <= F /\
  ((?be q ms ks.
      FOLDR (dft_exec_cons g C8) OK
        (DROP (phi_prefix_length (ps ++ ys)) ps)
        (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
      be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
      z = DROP m ps ++ TAKE q xs /\ k = LENGTH ps - m + q /\
      ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
      ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(b,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
      Mc = FLAT (TAKE q ms) /\ Kc = FLAT (TAKE q ks)) \/
   (?l t.
      m <= l /\ l < LENGTH ps /\ k = l-m /\
      z = DROP m (TAKE l ps) /\ Mc = [] /\ Kc = [] /\
      FOLDR (dft_exec_cons g C8) OK
        (DROP (phi_prefix_length (ps ++ ys)) (TAKE l ps))
        (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK t)) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc gs /\
  plan_eval F C7 sf.fn_name [(bb,e,z)]
    (entry with vs_gas_readings := gs ++ tail) = (events,OK u) ==>
  u.vs_inst_idx = m+k /\
  ?before after.
    trace_blocks b d (F-d) C7 sf (entry with vs_gas_readings := gs ++ tail) =
      before ++ [((b,e,(EL k (DROP m bb.bb_instructions)).inst_id),sf,
        EL k (DROP m bb.bb_instructions),u)] ++ after /\
    trace_gas before = ZIP (Kc,gs)
Proof
  qx_gen_tac `fuel` >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `m <= LENGTH ps` by gvs[dft_phi_prefix_append,phi_prefix_length_le] >>
  `k < LENGTH (DROP m bb.bb_instructions) /\
   z = TAKE k (DROP m bb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) z` by
    (gvs[dft_phi_prefix_append,DROP_APPEND1,TAKE_APPEND2,
         DROP_TAKE,EVERY_DROP,EVERY_TAKE,EVERY_CONJ] >>
     simp[TAKE_APPEND1]) >>
  `k <= LENGTH (DROP m bb.bb_instructions)` by decide_tac >>
  drule_all dft_packet_fresh_singleton_source_prefix >>
  disch_then (qspecl_then [`fuel`,`C7`,`sf.fn_name`,`e`,`gs ++ tail`] strip_assume_tac) >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK
     (TAKE k (DROP m bb.bb_instructions)) (sp' with vs_inst_idx := m) = OK u` by
    metis_tac[pairTheory.PAIR_EQ] >>
  `u.vs_inst_idx = m+k /\
   ?after. trace_blocks b d (fuel-d) C7 sf (entry with vs_gas_readings := gs ++ tail) =
     trace_block b e (fuel-e) C7 sf
       (bb with bb_instructions := TAKE (m+k) bb.bb_instructions)
       (sp' with vs_inst_idx := m) ++
     [((b,e,(EL k (DROP m bb.bb_instructions)).inst_id),sf,
       EL k (DROP m bb.bb_instructions),u)] ++ after` by
    ((irule dft_packet_fresh_child_prefix_occurrence >> simp[] >> (gvs[dft_packet_fresh_child_prefix_occurrence]))) >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  qexistsl [`trace_block b e (fuel-e) C7 sf
    (bb with bb_instructions := TAKE (m+k) bb.bb_instructions)
    (sp' with vs_inst_idx := m)`,`after`] >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >> suspend "zip"
QED

Resume dft_packet_fresh_singleton_native[zip]:
  markerLib.RESUME_TAC
  >- suspend "pseudo_zip"
  >> suspend "body_zip"
QED

Resume dft_packet_fresh_singleton_native[body_zip]:
  drule_all dft_packet_body_entry_replay >>
  disch_then (qspecl_then [`gs ++ tail`,`fuel-e`,`C7`] strip_assume_tac) >>
  `sp'' = sp'` by gvs[dft_eval_phis_append] >>
  `trace_gas (trace_block b e (fuel-e) C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions)
      (sp' with vs_inst_idx := m)) =
   trace_gas (trace_block b e (fuel-e) C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions)
      (be with vs_gas_readings := gs ++ tail))` by
    (irule dft_packet_fresh_body_trace_prefix >>
     gvs[dft_phi_prefix_append]) >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK (DROP m ps ++ TAKE q xs)
      (sp' with vs_inst_idx := m) = OK u` by metis_tac[] >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := gs ++ tail) = OK u` by
    ((qpat_x_assum `FOLDR _ _ (_ ++ _) _ = OK u` mp_tac >>
     simp[Once FOLDR_APPEND,Once dftRunRelTheory.dft_exec_prefix_continue,
          EVERY_DROP,dft_phi_prefix_append] >> (gvs[Once FOLDR_APPEND, Once dftRunRelTheory.dft_exec_prefix_continue, EVERY_DROP, dft_phi_prefix_append]))) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) gs` by metis_tac[] >>
  drule dft_packet_flat_filling_split >> strip_tac >>
  `q <= LENGTH xs` by decide_tac >>
  qabbrev_tac `ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs)` >>
  `ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs)` by simp[Abbr `ess`] >>
  drule_all dft_packet_fresh_row_replay >>
  disch_then (qspecl_then [`tail`,`fuel-e`,`C7`] strip_assume_tac) >>
  qpat_assum `gs = FLAT gss` (fn eqth =>
    qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _`
      (mp_tac o PURE_REWRITE_RULE [GSYM eqth] o Q.SPEC `u`)) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `m+k = LENGTH ps+q` by decide_tac >>
  qpat_assum `m+k = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `trace_gas _ = trace_gas _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `trace_gas _ = ZIP _` mp_tac >>
  qpat_assum `bb.bb_instructions = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `Kc = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[NoAsms,ADD_COMM]
QED

Resume dft_packet_fresh_singleton_native[pseudo_zip]:
  `m+k = l` by decide_tac >>
  `trace_gas (trace_block b e (fuel-e) C7 sf
      (bb with bb_instructions := TAKE l bb.bb_instructions)
      (sp' with vs_inst_idx := m)) = []` by
    (irule dft_packet_fresh_pseudo_trace_prefix >>
     qexistsl [`m`,`ps`,`u`,`xs`] >>
     simp[] >> metis_tac[]) >>
  qpat_assum `m+k = l` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `trace_gas _ = []` (fn th => pure_rewrite_tac[th]) >>
  gvs[]
QED

Finalise dft_packet_fresh_singleton_native
