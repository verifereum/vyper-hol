Theory dftPacketRowAlignment
Ancestors
  dftPacketEntryReplay dftPacketFillingBoundary dftGasFromListReplayBoundary
  dftGasToListReplay dftIndexedExec dftRunRel venomInst venomExecSemantics
  venomExecProofs list rich_list

Theorem dft_packet_row_body_success:
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  FOLDR (dft_exec_cons f C8) OK
    (DROP (phi_prefix_length (ps ++ ys)) ps)
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
  (case eval_phis (entry with vs_gas_readings := gs) (ps ++ xs) of
    OK sp' => FOLDR (dft_exec_cons g C7) OK
      (DROP (phi_prefix_length (ps ++ xs)) ps ++ TAKE q xs)
      (sp' with vs_inst_idx := phi_prefix_length (ps ++ xs))
  | other => other) = OK u ==>
  FOLDR (dft_exec_cons g C7) OK (TAKE q xs)
    (be with vs_gas_readings := gs) = OK u
Proof
  strip_tac >> drule_all dft_packet_body_entry_replay >>
  disch_then (qspecl_then [`gs`,`g`,`C7`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `i.inst_opcode` >>
     gvs[is_pseudo_def, is_terminator_def]) >>
  gvs[dft_phi_prefix_append, dft_eval_phis_append] >>
  qpat_x_assum `FOLDR _ _ (_ ++ _) _ = _` mp_tac >>
  simp[FOLDR_APPEND, dft_exec_prefix_continue, EVERY_DROP]
QED

Theorem dft_packet_plan_stopped[local]:
  !rows es r. (!s. r <> OK s) ==>
  FOLDL (\(es,r) row.
    case r of
      OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
    | other => (es,other)) (es,r) rows = (es,r)
Proof
  Induct >> rpt gen_tac >> strip_tac >> Cases_on `r` >> gvs[]
QED

Theorem dft_packet_plan_success_prefix:
  FOLDL (\(es,r) row.
    case r of
      OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
    | other => (es,other)) (initial,OK entry) (pre ++ post) =
      (events,OK u) ==>
  ?prior s.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
      | other => (es,other)) (initial,OK entry) pre = (prior,OK s)
Proof
  simp[FOLDL_APPEND] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ pref post` >>
  PairCases_on `pref` >> Cases_on `pref1` >>
  gvs[dft_packet_plan_stopped]
QED

Theorem dft_packet_plan_last_success:
  FOLDL (\(es,r) row.
    case r of
      OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
    | other => (es,other)) (initial,OK entry) (prefix ++ [row]) =
      (events,OK u) ==>
  ?prior s es.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
      | other => (es,other)) (initial,OK entry) prefix = (prior,OK s) /\
    row_eval row s = (es,OK u) /\ events = prior ++ es
Proof
  simp[FOLDL_APPEND] >> pairarg_tac >>
  rename1 `_ = (prior,r0)` >> Cases_on `r0` >> gvs[] >>
  strip_tac >> Cases_on `row_eval row v` >> gvs[]
QED

Theorem dft_packet_closed_plan_alignment:
  !(F:num) C7 C8 owner row_eval plan_eval entries rows slotss gss tail.
  row_eval = (\(bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (F-e) C7 owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F-e) C7) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
      | other => (es,other)) ([],OK entry) plan) /\
  LENGTH entries = SUC (LENGTH rows) /\
  LENGTH slotss = LENGTH rows /\
  (!i. i < LENGTH rows ==>
    ?bb e ps xs ys sp be.
      EL i rows = (bb,e,DROP (phi_prefix_length bb.bb_instructions)
                              bb.bb_instructions) /\
      bb.bb_instructions = ps ++ xs /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
      eval_phis (EL i entries) (ps ++ ys) = OK sp /\
      FOLDR (dft_exec_cons (F-e) C8) OK
        (DROP (phi_prefix_length (ps ++ ys)) ps)
        (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
      (!gs rest.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL i slotss) gs ==>
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
           (be with vs_gas_readings := gs ++ rest))) ==>
         residual_result rest (OK (EL (SUC i) entries))
           (FOLDR (dft_exec_cons (F-e) C7) OK xs
             (be with vs_gas_readings := gs ++ rest))))) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) slotss gss ==>
  (!k events u.
    k <= LENGTH rows /\
    plan_eval (TAKE k rows)
      (HD entries with vs_gas_readings := FLAT gss ++ tail) = (events,OK u) ==>
    u = EL k entries with vs_gas_readings := FLAT (DROP k gss) ++ tail) /\
  (!events u.
    plan_eval rows (HD entries with vs_gas_readings := FLAT gss ++ tail) =
      (events,OK u) ==>
    u = LAST entries with vs_gas_readings := tail)
Proof
  rpt gen_tac >> strip_tac >> conj_asm1_tac
  >- (Induct_on `k`
      >- (rpt strip_tac >> gvs[] >>
          Cases_on `entries` >> gvs[]) >>
      rpt gen_tac >> strip_tac >>
      `k < LENGTH rows` by decide_tac >>
      `TAKE (SUC k) rows = TAKE k rows ++ [EL k rows]` by
        simp[arithmeticTheory.ADD1, TAKE_EL_SNOC, SNOC_APPEND] >>
      qpat_x_assum `plan_eval _ _ = _` mp_tac >>
      qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >>
      BETA_TAC >>
      qpat_assum `TAKE (SUC k) rows = _` (fn th => pure_rewrite_tac[th]) >>
      disch_then (mp_then Any mp_tac dft_packet_plan_last_success) >>
      strip_tac >>
      `s = EL k entries with vs_gas_readings := FLAT (DROP k gss) ++ tail` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!i. i < LENGTH rows ==> _`
        (drule_then strip_assume_tac) >>
      `LENGTH gss = LENGTH rows` by metis_tac[LIST_REL_LENGTH] >>
      `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
         (EL k slotss) (EL k gss)` by metis_tac[LIST_REL_EL_EQN] >>
      `FLAT (DROP k gss) ++ tail =
         EL k gss ++ (FLAT (DROP (SUC k) gss) ++ tail)` by
        simp[Once DROP_EL_CONS, GSYM arithmeticTheory.ADD1, APPEND_ASSOC] >>
      qpat_x_assum `plan_eval = _` kall_tac >>
      qpat_x_assum `!events u. k <= LENGTH rows /\ _ ==> _` kall_tac >>
      qpat_x_assum `FOLDL _ _ _ = _` kall_tac >>
      `EVERY (\i. i.inst_opcode <> PHI) xs` by
        (qpat_assum `EVERY (\x. ~is_pseudo x.inst_opcode) xs` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
      `DROP (phi_prefix_length (ps ++ xs)) (ps ++ xs) =
         DROP (phi_prefix_length (ps ++ xs)) ps ++ TAKE (LENGTH xs) xs` by
        simp[dft_phi_prefix_append, DROP_APPEND1, phi_prefix_length_le] >>
      qpat_x_assum `row_eval _ _ = _` mp_tac >>
      qpat_x_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `EL k rows = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `s = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
      simp[NoAsms, pairTheory.pair_case_thm] >>
      qpat_assum `bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
      strip_tac >>
      `((case eval_phis (EL k entries with vs_gas_readings :=
             FLAT (DROP k gss) ++ tail) (ps ++ xs) of
           OK sp' => FOLDR (dft_exec_cons (F'-e) C7) OK
             (DROP (phi_prefix_length (ps ++ xs)) ps ++ TAKE (LENGTH xs) xs)
             (sp' with vs_inst_idx := phi_prefix_length (ps ++ xs))
         | other => other) = OK u)` by
        (qpat_x_assum `_ = (es,OK u)` mp_tac >>
         qpat_assum `DROP _ (ps ++ xs) = _`
           (fn th => pure_rewrite_tac[th]) >>
         Cases_on `eval_phis (EL k entries with vs_gas_readings :=
           FLAT (DROP k gss) ++ tail) (ps ++ xs)` >> simp[]) >>
      `FOLDR (dft_exec_cons (F'-e) C7) OK xs
         (be with vs_gas_readings := FLAT (DROP k gss) ++ tail) = OK u` by
        metis_tac[dft_packet_row_body_success, TAKE_LENGTH_ID] >>
      qpat_x_assum `FOLDR _ OK xs _ = OK u` mp_tac >>
      qpat_assum `FLAT (DROP k gss) ++ tail = _`
        (fn th => pure_rewrite_tac[th]) >> strip_tac >>
      drule_all dft_packet_closed_ok_entry >> simp[])
  >> rpt gen_tac >> strip_tac >>
  `LENGTH gss = LENGTH rows` by metis_tac[LIST_REL_LENGTH] >>
  qpat_x_assum `row_eval = _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH rows ==> _` kall_tac >>
  first_x_assum (qspec_then `LENGTH rows` mp_tac) >>
  `DROP (LENGTH rows) gss = []` by metis_tac[DROP_LENGTH_NIL] >>
  `entries <> []` by (Cases_on `entries` >> gvs[]) >>
  `EL (LENGTH rows) entries = LAST entries` by simp[LAST_EL] >>
  simp[]
QED
