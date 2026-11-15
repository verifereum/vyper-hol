Theory readonlyInvokeCopyFwdHistoryOperandOrigins
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdReadonlyPositions list rich_list option

Theorem ricf_operand_fold_none[local]:
  !events. FOLDL (ricf_edit_operand i iid j) NONE events = NONE
Proof
  Induct >> simp[ricf_edit_operand_def, pairTheory.FORALL_PROD]
QED


Theorem ricf_operand_fold_origin[local]:
  !events old new.
    FOLDL (ricf_edit_operand i iid j) (SOME old) events = SOME new ==>
    new = old \/
    ?e src. MEM (e,src) events /\ new = src /\ i <> e.rfe_index /\
      MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `FOLDL _ (SOME old) (ev::events) = SOME new` >>
  PairCases_on `ev` >> simp[ricf_edit_operand_def] >>
  Cases_on `i = ev0.rfe_index` >> simp[ricf_operand_fold_none] >>
  Cases_on `MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) ev0.rfe_sites)` >>
  simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[MEM]
QED

Theorem ricf_event_log_origin[local]:
  !bb es last. ricf_block_trace bb es last ==>
    !e src. MEM (e,src) (ricf_event_log bb es) ==>
      ?prefix suffix current.
        es = prefix ++ e::suffix /\ ricf_block_trace bb prefix current /\
        ricf_event_ok e current /\ src = ricf_event_source e current
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[ricf_event_log_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`[]`,`es`,`bb`] >> simp[ricf_block_trace_nil]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`e::prefix`,`suffix`,`current`] >> simp[] >>
  irule ricf_block_trace_cons >> metis_tac[]
QED

Theorem ricf_block_trace_operand_origin:
  ricf_block_trace bb es last /\ i < LENGTH bb.bb_instructions /\
  j < LENGTH (EL i bb.bb_instructions).inst_operands /\
  j < LENGTH (EL i last.bb_instructions).inst_operands ==>
  EL j (EL i last.bb_instructions).inst_operands =
    EL j (EL i bb.bb_instructions).inst_operands \/
  ?prefix e suffix current.
    es = prefix ++ e::suffix /\ ricf_block_trace bb prefix current /\
    ricf_event_ok e current /\ i <> e.rfe_index /\
    MEM ((EL i bb.bb_instructions).inst_id,j)
      (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites) /\
    EL j (EL i last.bb_instructions).inst_operands = ricf_event_source e current
Proof
  strip_tac >> drule ricf_block_trace_operand_history >>
  disch_then (qspecl_then [`i`,`j`] mp_tac) >> simp[ricf_operand_at_def] >>
  strip_tac >> qpat_x_assum `SOME _ = FOLDL _ _ _` (assume_tac o SYM) >>
  drule ricf_operand_fold_origin >> strip_tac >> simp[] >>
  drule_all ricf_event_log_origin >> strip_tac >>
  disj2_tac >> qexistsl_tac [`prefix`,`e`,`suffix`,`current`] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]
QED

Theorem ricf_logged_function_operand_origin:
  !ctx0 fn log last. ricf_logged_function_trace ctx0 fn log last ==>
  !b i j.
    ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
    b < LENGTH fn.fn_blocks /\
    i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    j < LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_operands ==>
    EL j (EL i (EL b last.fn_blocks).bb_instructions).inst_operands =
      EL j (EL i (EL b fn.fn_blocks).bb_instructions).inst_operands \/
    ?round es prefix e current.
      ricf_located_event ctx0 fn log round b es prefix e current /\
      i <> e.rfe_index /\
      MEM ((EL i (EL b fn.fn_blocks).bb_instructions).inst_id,j)
        (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites) /\
      EL j (EL i (EL b last.fn_blocks).bb_instructions).inst_operands =
        ricf_event_source e current
Proof
  ho_match_mp_tac ricf_logged_function_trace_strongind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `ricf_logged_round ctx0 round logs mid` >>
  rename1 `ricf_logged_function_trace ctx0 mid tail last` >>
  `ricf_function_trace ctx0 round mid` by
    metis_tac[ricf_logged_round_erases, ricf_function_trace_cons,
      ricf_function_trace_nil] >>
  `ricf_function_edit round mid /\
   ricf_readonly_function_edit ctx0.icf_rma round mid` by
    metis_tac[ricf_function_trace_edit, ricf_function_trace_readonly_edit] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts mid))` by
    metis_tac[ricf_function_edit_ids] >>
  `b < LENGTH mid.fn_blocks /\
   i < LENGTH (EL b mid.fn_blocks).bb_instructions /\
   (EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
   (EL i (EL b mid.fn_blocks).bb_instructions).inst_id =
     (EL i (EL b round.fn_blocks).bb_instructions).inst_id /\
   LENGTH (EL i (EL b mid.fn_blocks).bb_instructions).inst_operands =
     LENGTH (EL i (EL b round.fn_blocks).bb_instructions).inst_operands` by
    (fs[ricf_readonly_function_edit_def, ricf_readonly_block_edit_def,
       LIST_REL_EL_EQN, ricf_readonly_inst_edit_def, ricf_inst_edit_def] >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then `b` mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `j < LENGTH (EL i (EL b mid.fn_blocks).bb_instructions).inst_operands` by
    metis_tac[] >>
  qpat_x_assum `!b i j. _` (qspecl_then [`b`,`i`,`j`] mp_tac) >>
  simp[] >> strip_tac
  >- (drule_all ricf_logged_round_block >> strip_tac >>
      drule_all ricf_block_trace_operand_origin >> strip_tac >> simp[] >>
      disj2_tac >>
      qexistsl_tac [`round`,`EL b logs`,`prefix`,`e`,`current`] >>
      simp[] >> pure_rewrite_tac[ricf_located_event_def] >>
      qexistsl_tac [`last`,`logs`,`mid`,`suffix`] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[] >>
      metis_tac[ricf_logged_function_trace_cons]) >>
  rename1 `ricf_located_event ctx0 mid tail next_round b es prefix e current` >>
  disj2_tac >> qexistsl_tac [`next_round`,`es`,`prefix`,`e`,`current`] >>
  simp[] >> fs[ricf_located_event_def] >>
  metis_tac[ricf_logged_function_trace_cons, MEM]
QED

Theorem ricf_operand_fold_selected_origin[local]:
  !events old new.
    FOLDL (ricf_edit_operand i iid j) (SOME old) events = SOME new /\
    (?e src. MEM (e,src) events /\ i <> e.rfe_index /\
      MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)) ==>
    ?e src. MEM (e,src) events /\ new = src /\ i <> e.rfe_index /\
      MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `FOLDL _ (SOME old) (ev::events) = SOME new` >>
  PairCases_on `ev` >> simp[ricf_edit_operand_def] >>
  Cases_on `i = ev0.rfe_index` >> simp[ricf_operand_fold_none] >>
  Cases_on `MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) ev0.rfe_sites)`
  >- (simp[] >> strip_tac >> drule ricf_operand_fold_origin >>
      strip_tac >> metis_tac[MEM]) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!old new. _` (qspecl_then [`old`,`new`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> metis_tac[MEM]
QED

Theorem ricf_event_log_append[local]:
  !bb prefix current. ricf_block_trace bb prefix current ==>
  !suffix. ricf_event_log bb (prefix ++ suffix) =
    ricf_event_log bb prefix ++ ricf_event_log current suffix
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[ricf_event_log_def] >>
  rpt strip_tac >> simp[ricf_event_log_def]
QED

Theorem ricf_block_trace_selected_operand_origin[local]:
  ricf_block_trace bb es last /\ ricf_block_trace bb prefix current /\
  es = prefix ++ e::suffix /\
  i < LENGTH bb.bb_instructions /\
  j < LENGTH (EL i bb.bb_instructions).inst_operands /\
  j < LENGTH (EL i last.bb_instructions).inst_operands /\
  i <> e.rfe_index /\
  MEM ((EL i bb.bb_instructions).inst_id,j)
    (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites) ==>
  ?prefix' e' suffix' current'.
    es = prefix' ++ e'::suffix' /\ ricf_block_trace bb prefix' current' /\
    ricf_event_ok e' current' /\ i <> e'.rfe_index /\
    MEM ((EL i bb.bb_instructions).inst_id,j)
      (MAP (\(ri,p). (ri.inst_id,p)) e'.rfe_sites) /\
    EL j (EL i last.bb_instructions).inst_operands = ricf_event_source e' current'
Proof
  strip_tac >>
  `MEM (e,ricf_event_source e current) (ricf_event_log bb es)` by
    (drule ricf_event_log_append >>
     disch_then (qspec_then `e::suffix` assume_tac) >>
     simp[ricf_event_log_def, MEM_APPEND] >> metis_tac[]) >>
  qpat_assum `ricf_block_trace bb es last`
    (mp_tac o MATCH_MP ricf_block_trace_operand_history) >>
  disch_then (qspecl_then [`i`,`j`] mp_tac) >> simp[ricf_operand_at_def] >>
  strip_tac >> qpat_x_assum `SOME _ = FOLDL _ _ _` (assume_tac o SYM) >>
  drule ricf_operand_fold_selected_origin >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choosel_then [`chosen`,`src`] strip_assume_tac) >>
  qpat_assum `ricf_block_trace bb es last`
    (mp_tac o MATCH_MP ricf_event_log_origin) >>
  disch_then (qspecl_then [`chosen`,`src`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`selected_prefix`,`selected_suffix`,`selected_current`]
    strip_assume_tac) >>
  qexistsl_tac [`selected_prefix`,`chosen`,`selected_suffix`,`selected_current`] >>
  metis_tac[]
QED

Theorem ricf_operand_origin_log_suffix[local]:
  !ctx0 fn log last. ricf_logged_function_trace ctx0 fn log last ==>
  !round logs mid. MEM (round,logs,mid) log ==>
    ?before after. log = before ++ (round,logs,mid)::after /\
      ricf_logged_function_trace ctx0 mid after last
Proof
  ho_match_mp_tac ricf_logged_function_trace_strongind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `ricf_logged_round ctx0 first_fn first_logs first_mid` >>
  rename1 `ricf_logged_function_trace ctx0 first_mid tail last` >>
  rpt gen_tac >> simp[] >> strip_tac
  >- (gvs[] >> qexistsl_tac [`[]`,`tail`] >> simp[]) >>
  first_x_assum drule >>
  disch_then (qx_choosel_then [`prelog`,`postlog`] strip_assume_tac) >>
  qexistsl_tac [`(first_fn,first_logs,first_mid)::prelog`,`postlog`] >> simp[]
QED

Theorem ricf_logged_function_selected_operand_origin:
  ricf_logged_function_trace ctx0 fn log last /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  j < LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_operands /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  i <> e.rfe_index /\
  MEM ((EL i (EL b fn.fn_blocks).bb_instructions).inst_id,j)
    (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites) ==>
  ?selected_round selected_es selected_prefix selected_event selected_current.
    ricf_located_event ctx0 fn log selected_round b selected_es
      selected_prefix selected_event selected_current /\
    i <> selected_event.rfe_index /\
    MEM ((EL i (EL b fn.fn_blocks).bb_instructions).inst_id,j)
      (MAP (\(ri,p). (ri.inst_id,p)) selected_event.rfe_sites) /\
    EL j (EL i (EL b last.fn_blocks).bb_instructions).inst_operands =
      ricf_event_source selected_event selected_current
Proof
  strip_tac >>
  qpat_x_assum `ricf_located_event _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_located_event_def]) >>
  `ricf_function_trace ctx0 fn round /\ ricf_logged_round ctx0 round logs mid` by
    (qpat_assum `ricf_logged_function_trace ctx0 fn log last`
       (mp_tac o MATCH_MP ricf_logged_function_trace_member) >>
     disch_then (qspecl_then [`round`,`logs`,`mid`] mp_tac) >> simp[]) >>
  `ricf_function_edit fn round /\
   ricf_readonly_function_edit ctx0.icf_rma fn round` by
    metis_tac[ricf_function_trace_edit, ricf_function_trace_readonly_edit] >>
  drule_all ricf_call_readonly_position >> strip_tac >>
  `ricf_inst_edit (EL i (EL b fn.fn_blocks).bb_instructions)
     (EL i (EL b round.fn_blocks).bb_instructions)` by
    metis_tac[ricf_call_function_position] >>
  `(EL i (EL b round.fn_blocks).bb_instructions).inst_id =
     (EL i (EL b fn.fn_blocks).bb_instructions).inst_id` by
    fs[ricf_inst_edit_def] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts round))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_function_trace ctx0 round mid` by
    metis_tac[ricf_logged_round_erases, ricf_function_trace_cons,
      ricf_function_trace_nil] >>
  `ricf_function_edit round mid /\
   ricf_readonly_function_edit ctx0.icf_rma round mid` by
    metis_tac[ricf_function_trace_edit, ricf_function_trace_readonly_edit] >>
  `b < LENGTH mid.fn_blocks /\
   i < LENGTH (EL b mid.fn_blocks).bb_instructions /\
   (EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
   LENGTH (EL i (EL b mid.fn_blocks).bb_instructions).inst_operands =
     LENGTH (EL i (EL b round.fn_blocks).bb_instructions).inst_operands` by
    metis_tac[ricf_call_readonly_position] >>
  `ricf_inst_edit (EL i (EL b round.fn_blocks).bb_instructions)
     (EL i (EL b mid.fn_blocks).bb_instructions)` by
    metis_tac[ricf_call_function_position] >>
  `(EL i (EL b mid.fn_blocks).bb_instructions).inst_id =
     (EL i (EL b fn.fn_blocks).bb_instructions).inst_id` by
    fs[ricf_inst_edit_def] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts mid))` by
    metis_tac[ricf_function_edit_ids] >>
  `j < LENGTH (EL i (EL b round.fn_blocks).bb_instructions).inst_operands /\
   j < LENGTH (EL i (EL b mid.fn_blocks).bb_instructions).inst_operands` by metis_tac[] >>
  drule_all ricf_logged_round_block >> strip_tac >>
  `?bp be bs bc.
    es = bp ++ be::bs /\ ricf_block_trace (EL b round.fn_blocks) bp bc /\
    ricf_event_ok be bc /\ i <> be.rfe_index /\
    MEM ((EL i (EL b round.fn_blocks).bb_instructions).inst_id,j)
      (MAP (\(ri,p). (ri.inst_id,p)) be.rfe_sites) /\
    EL j (EL i (EL b mid.fn_blocks).bb_instructions).inst_operands =
      ricf_event_source be bc` by
    (irule ricf_block_trace_selected_operand_origin >> simp[] >> metis_tac[]) >>
  `ricf_located_event ctx0 fn log round b es bp be bc` by
    (pure_rewrite_tac[ricf_located_event_def] >>
     qexistsl_tac [`last`,`logs`,`mid`,`bs`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     fs[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  `?before after. log = before ++ (round,logs,mid)::after /\
      ricf_logged_function_trace ctx0 mid after last` by
    (qpat_assum `ricf_logged_function_trace ctx0 fn log last`
       (mp_tac o MATCH_MP ricf_operand_origin_log_suffix) >>
     disch_then (qspecl_then [`round`,`logs`,`mid`] mp_tac) >> simp[]) >>
  qpat_assum `ricf_logged_function_trace ctx0 mid after last`
    (mp_tac o MATCH_MP ricf_logged_function_operand_origin) >>
  disch_then (qspecl_then [`b`,`i`,`j`] mp_tac) >> simp[] >> strip_tac
  >- (qexistsl_tac [`round`,`es`,`bp`,`be`,`bc`] >> simp[] >> metis_tac[]) >>
  rename1 `ricf_located_event ctx0 mid after next_round b next_es next_prefix next_event next_current` >>
  qexistsl_tac [`next_round`,`next_es`,`next_prefix`,`next_event`,`next_current`] >>
  simp[] >> fs[ricf_located_event_def, APPEND_ASSOC] >>
  metis_tac[MEM_APPEND, APPEND_ASSOC, APPEND]
QED
