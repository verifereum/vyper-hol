Theory dftPacketBlockFreshEntry
Ancestors
  dftPacketFreshCut dftPacketFreshRow dftRunRel dftIndexedExec
  dftGasFromListTraceDefs gasEvents venomExecSemantics venomInst venomState
  list rich_list arithmetic venomExecProofs

Theorem dft_packet_block_fresh_entry:
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  bt.bb_label = bb.bb_label /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ EVERY inst_shape_ok bb.bb_instructions /\
  PERM row_order (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\
    y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) row_order ys /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  eval_phis post bt.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
  get_instruction bt s1.vs_inst_idx = SOME next /\
  (s1.vs_inst_idx = LENGTH ps ==> dft_remaining_inv sf bb xs s1) /\
  e = SUC d /\ h1 = SUC j ==>
  ?body_entry ms ess ks count front closed brest.
    count = 0 /\ front = OK s1 /\ closed = F /\ brest = NONE /\
    phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\
    s1.vs_inst_idx <= LENGTH ps /\
    (if s1.vs_inst_idx < LENGTH ps then
       body_entry = NONE /\ ms = [] /\ ess = [] /\ ks = [] /\
       (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
         (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1) /\
       (!F gs z R.
         N' <= F /\
         z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s1.vs_inst_idx ps) /\
         R = (\entry. case eval_phis entry bb.bb_instructions of
           OK sp =>
             (gas_events_block (F-e) C7 sf.fn_name
               (bb with bb_instructions :=
                 TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
               (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
              FOLDR (dft_exec_cons (F-e) C7) OK z
               (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
           | other => ([],other)) ==>
         R (post with vs_gas_readings := gs) =
           ([],OK (s1 with vs_gas_readings := gs)))
     else
       s1.vs_inst_idx = LENGTH ps /\ body_entry = SOME (s1,h1) /\
       dft_remaining_inv sf bb xs s1 /\
       ms = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
       ess = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs) /\
       ks = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(a,e,(EL q xs).inst_id)] else []) (LENGTH xs) /\
       (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt.bb_instructions) ps)
         (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1) /\
       LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
       LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
       LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
       ALL_DISTINCT (FLAT ks) /\
       (!q. q < LENGTH xs ==>
         ((EL q xs).inst_opcode = GAS ==>
           EL q ms = [NONE] /\ EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
           EL q ks = [(a,e,(EL q xs).inst_id)]) /\
         ((EL q xs).inst_opcode <> GAS ==>
           EL q ms = [] /\ EL q ess = [] /\ EL q ks = [])) /\
       (!F k kgss tail.
         N' <= F /\ k <= LENGTH xs /\
         EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
         (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE 0 row_order)) /\
         LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
           (TAKE k ms) kgss ==>
         (?extra. FLAT (TAKE k ess) =
           gas_events_block (F-e) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
         (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
             (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
           gas_events_block (F-e) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
           u.vs_gas_readings = tail /\
           trace_gas (trace_block a e (F-e) C7 sf
             (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
             (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
               ZIP (FLAT (TAKE k ks),FLAT kgss) /\
           (!tail'.
             FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
               (s1 with vs_gas_readings := FLAT kgss ++ tail') =
                 OK (u with vs_gas_readings := tail') /\
             gas_events_block (F-e) C7 sf.fn_name
               <|bb_label := s1.vs_current_bb; bb_instructions :=
                 REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
               (s1 with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
       (!F q kgss tail z R.
         N' <= F /\ q < LENGTH xs /\
         EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
         (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE 0 row_order)) /\
         z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
         R = (\entry. case eval_phis entry bb.bb_instructions of
           OK sp =>
             (gas_events_block (F-e) C7 sf.fn_name
               (bb with bb_instructions :=
                 TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
               (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
              FOLDR (dft_exec_cons (F-e) C7) OK z
               (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
           | other => ([],other)) /\
         LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss ==>
         SND (R (post with vs_gas_readings := FLAT kgss ++ tail)) =
           FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
             (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
         (?extra. FLAT (TAKE q ess) =
           FST (R (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
         (!events u. R (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
           events = FLAT (TAKE q ess) /\ u.vs_gas_readings = tail /\
           trace_gas (trace_block a e (F-e) C7 sf
             (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
             (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
               ZIP (FLAT (TAKE q ks),FLAT kgss) /\
           !tail'. R (post with vs_gas_readings := FLAT kgss ++ tail') =
             (events,OK (u with vs_gas_readings := tail')))))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bt.bb_instructions <= LENGTH ps` by
    simp[dft_phi_prefix_append,phi_prefix_length_le] >>
  Cases_on `s1.vs_inst_idx < LENGTH ps`
  >- suspend "pseudo"
  >> suspend "body"
QED

Resume dft_packet_block_fresh_entry[pseudo]:
  qexistsl [`NONE`,`[]`,`[]`,`[]`,`0`,`OK s1`,`F`,`NONE`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- gvs[] >> conj_tac >- gvs[] >>
  qpat_assum `s1.vs_inst_idx < LENGTH ps`
    (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (gvs[] >> simp[DROP_TAKE]) >>
  suspend "pseudo_cut"
QED

Resume dft_packet_block_fresh_entry[body]:
  `s1.vs_inst_idx = LENGTH ps` by gvs[] >>
  qexistsl [`SOME (s1,h1)`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs)`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs)`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(a,e,(EL q xs).inst_id)] else []) (LENGTH xs)`,
    `0`,`OK s1`,`F`,`NONE`] >>
  suspend "body_clauses"
QED

Resume dft_packet_block_fresh_entry[pseudo_cut]:
  rpt gen_tac >> strip_tac >>
  irule dft_packet_fresh_pseudo_cut >>
  goal_assum (drule_at (Pat `R = _`)) >>
  goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >>
  qexistsl [`C8`,`0`,`s1.vs_inst_idx`,`sp`,`ys`] >>
  gvs[DROP_TAKE]
QED

Resume dft_packet_block_fresh_entry[body_clauses]:
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- gvs[] >> conj_tac >- simp[] >>
  qpat_assum `~(s1.vs_inst_idx < LENGTH ps)`
    (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (gvs[] >> simp[DROP_LENGTH_TOO_LONG]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "shape_ms_ess" >>
  conj_tac >- suspend "shape_ms_ks" >>
  conj_tac >- suspend "keys_distinct" >>
  conj_tac >- (simp[EL_GENLIST] >> rpt strip_tac >> simp[]) >>
  conj_tac >- suspend "body_U" >>
  suspend "body_cut"
QED

Resume dft_packet_block_fresh_entry[shape_ms_ess]:
  simp[LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
  Cases_on `(EL n xs).inst_opcode = GAS` >> simp[]
QED

Resume dft_packet_block_fresh_entry[shape_ms_ks]:
  simp[LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
  Cases_on `(EL n xs).inst_opcode = GAS` >> simp[]
QED

Resume dft_packet_block_fresh_entry[keys_distinct]:
  `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(a,e,(EL q xs).inst_id)] else []) (LENGTH xs) =
   MAP (\i. if i.inst_opcode = GAS then [(a,e,i.inst_id)] else []) xs` by
    simp[LIST_EQ_REWRITE,EL_MAP,EL_GENLIST] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Induct_on `xs` >> simp[MEM_FLAT,MEM_MAP] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = GAS` >> gvs[] >>
  strip_tac >> gvs[MEM_FLAT,MEM_MAP,AllCaseEqs()] >>
  metis_tac[]
QED

Resume dft_packet_block_fresh_entry[body_U]:
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE k xs)` by
    (simp[EVERY_EL,EL_TAKE,LENGTH_TAKE] >> rpt strip_tac >>
     gvs[EVERY_EL,EL_TAKE,LENGTH_TAKE] >> metis_tac[]) >>
  irule dft_packet_fresh_row_replay >>
  goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >>
  simp[]
QED

Resume dft_packet_block_fresh_entry[body_cut]:
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs)` by
    (simp[EVERY_EL,EL_TAKE,LENGTH_TAKE] >> rpt strip_tac >>
     gvs[EVERY_EL,EL_TAKE,LENGTH_TAKE] >> metis_tac[]) >>
  irule dft_packet_fresh_body_cut >>
  simp[] >>
  qexistsl [`C8`,`0`,`sp`,`ys`] >>
  gvs[DROP_LENGTH_TOO_LONG]
QED

Finalise dft_packet_block_fresh_entry
