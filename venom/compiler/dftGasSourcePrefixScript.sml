Theory dftGasSourcePrefix
Ancestors
  dftGasFromListTraceDefs dftGasFromListReadings
  gasEvents gasCount gasOracleReplay dftIndexedExec dftRunRel dftBlockSim
  removeUnusedGasProofs venomExecProofs venomExecSemantics venomState venomInst
  list rich_list option arithmetic

Theorem noninvoke_block_events_prefix:
  !fuel C owner bb s.
    EVERY (\i. i.inst_opcode <> INVOKE)
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?extra.
      MAP (\i. (owner,i.inst_id))
        (FILTER (\i. i.inst_opcode = GAS)
          (DROP s.vs_inst_idx bb.bb_instructions)) =
      gas_events_block fuel C owner bb s ++ extra
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (drule rich_listTheory.DROP_CONS_EL >>
      disch_then (fn th => fs[th]) >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
           gas_events_step_def] >>
      Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
      simp[] >>
      Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS` >>
      simp[] >>
      Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
      simp[] >>
      first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `v' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[] >> gvs[]) >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def, DROP_EQ_NIL]
QED

Theorem prefix_ok_cursor:
  !pre s u.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH pre
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem noninvoke_prefix_events_exact_at:
  !pre s bb xs u.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ xs /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    gas_events_block fuel C owner bb s =
    MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
    gas_events_block fuel C owner bb u
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       gas_events_step_def] >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `xs`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS` >> gvs[]
QED

Theorem noninvoke_prefix_events_exact:
  !pre s u xs.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    gas_events_block fuel C owner
      <|bb_label := label; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ xs)|> s =
    MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
    gas_events_block fuel C owner
      <|bb_label := label; bb_instructions :=
        REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u
Proof
  rpt strip_tac >>
  `u.vs_inst_idx = s.vs_inst_idx + LENGTH pre` by
    (irule prefix_ok_cursor >> simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_events_block fuel C owner bb s` >>
  `gas_events_block fuel C owner bb s =
   MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
   gas_events_block fuel C owner bb u` by
    (irule noninvoke_prefix_events_exact_at >>
     simp[Abbr `bb`, DROP_APPEND]) >>
  `gas_events_block fuel C owner bb u =
   gas_events_block fuel C owner
     <|bb_label := label; bb_instructions :=
       REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u` by
    (irule gas_events_block_suffix_cong >> qexists_tac `xs` >>
     simp[Abbr `bb`, DROP_APPEND, DROP_DROP_T]) >>
  gvs[]
QED

Theorem noninvoke_prefix_readings_exact:
  !pre s pg rest u.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ rest) = OK u ==>
    u.vs_gas_readings = rest
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := pg ++ rest)` >> gvs[] >>
  `?pg'. LENGTH pg' = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
    v.vs_gas_readings = pg' ++ rest` by
    (Cases_on `h.inst_opcode = GAS`
     >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
         Cases_on `pg` >> gvs[update_var_def]) >>
     drule_all dft_nonconsuming_ok_readings >> strip_tac >>
     qexists_tac `pg` >> gvs[]) >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `pg'`, `rest`, `u`] mp_tac) >>
  simp[NoAsms] >> disch_then irule >>
  `v with vs_gas_readings := pg' ++ rest = v` by
    simp[venom_state_component_equality] >> gvs[]
QED

Theorem prefix_ok_readings_replay:
  !xs s t bb.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    FOLDR (dft_exec_cons fuel C) OK xs s = OK t ==>
    t.vs_gas_readings =
      DROP (LENGTH (gas_events_block fuel C owner bb s)) s.vs_gas_readings /\
    !tail. FOLDR (dft_exec_cons fuel C) OK xs
      (s with vs_gas_readings :=
        gasOracleReplay$gas_prefix (LENGTH (gas_events_block fuel C owner bb s))
          s.vs_gas_readings ++ tail) = OK (t with vs_gas_readings := tail)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      `gas_events_block fuel C owner bb s = []` by
        simp[Once gas_events_block_def, venomInstTheory.get_instruction_def] >>
      simp[gasOracleReplayTheory.gas_prefix_def]) >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  first_x_assum (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (drule_then assume_tac) >>
  mp_tac (cj 1 gas_count_suffix) >>
  disch_then (qspecl_then [`fuel`, `C`, `h`, `s`] mp_tac) >>
  simp[gas_count_suffix_def] >> strip_tac >>
  conj_tac
  >- (simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
           gas_events_length, rich_listTheory.DROP_DROP_T] >>
      simp[SimpRHS, Once gas_count_block_def, venomInstTheory.get_instruction_def] >>
      simp[arithmeticTheory.ADD_COMM]) >>
  gen_tac >>
  `gasOracleReplay$gas_replay_at (gas_count_step fuel C h s)
    (step_inst fuel C h) s` by
    (irule removeUnusedGasProofsTheory.remove_unused_step_successful_replay_count >> simp[]) >>
  qpat_x_assum `gasOracleReplay$gas_replay_at _ _ _` mp_tac >>
  simp[gasOracleReplayTheory.gas_replay_at_def] >> strip_tac >>
  qpat_x_assum `!tail. lift_result _ _ _ _ _`
    (qspec_then `gasOracleReplay$gas_prefix
       (LENGTH (gas_events_block fuel C owner bb
         (v with vs_inst_idx := SUC s.vs_inst_idx))) v.vs_gas_readings ++ tail` mp_tac) >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       gas_events_length, gasOracleReplayTheory.gas_prefix_add,
       dftIndexedExecTheory.dft_exec_cons_def, GSYM APPEND_ASSOC] >>
  `gas_count_block fuel C bb s = gas_count_step fuel C h s +
     gas_count_block fuel C bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once gas_count_block_def, venomInstTheory.get_instruction_def] >>
  `gas_count_block fuel C bb s = gas_count_step fuel C h s +
     LENGTH (gas_events_block fuel C owner bb
       (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[gas_events_length] >>
  qpat_x_assum `gas_count_block fuel C bb s = _ + LENGTH _`
    (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[gasOracleReplayTheory.gas_prefix_add, GSYM APPEND_ASSOC] >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  Cases_on `step_inst fuel C h
    (s with vs_gas_readings :=
      gasOracleReplay$gas_prefix (gas_count_step fuel C h s) s.vs_gas_readings ++
      gasOracleReplay$gas_prefix
        (LENGTH (gas_events_block fuel C owner bb
          (v with vs_inst_idx := SUC s.vs_inst_idx)))
        (DROP (gas_count_step fuel C h s) s.vs_gas_readings) ++ tail)` >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >> gvs[]
QED

Theorem gas_padding_filling_length:
  !xs gss.
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (MAP (\x. if x.inst_opcode = GAS then [NONE : bytes32 option] else []) xs) gss ==>
    LENGTH (FLAT gss) = LENGTH (FILTER (\x. x.inst_opcode = GAS) xs)
Proof
  Induct >> Cases_on `gss` >> simp[] >> gen_tac >> strip_tac >>
  rename1 `LIST_REL _ (if inst.inst_opcode = GAS then _ else _) readings` >>
  Cases_on `inst.inst_opcode = GAS` >> gvs[] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[]
QED

Theorem gas_padding_events:
  !xs. FLAT (MAP (\x. if x.inst_opcode = GAS then [(owner,x.inst_id)] else []) xs) =
    MAP (\x. (owner,x.inst_id)) (FILTER (\x. x.inst_opcode = GAS) xs)
Proof
  Induct >> simp[] >> gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem prescribed_prefix_ok_replay:
  !fuel C owner pre s gs tail u.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := gs ++ tail) = OK u /\
    LENGTH (gas_events_block fuel C owner
      <|bb_label := s.vs_current_bb; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>
      (s with vs_gas_readings := gs ++ tail)) = LENGTH gs ==>
    u.vs_gas_readings = tail /\
    !tail'. FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := gs ++ tail') =
      OK (u with vs_gas_readings := tail')
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`pre`, `s with vs_gas_readings := gs ++ tail`, `u`,
    `<|bb_label := s.vs_current_bb; bb_instructions :=
      REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>`]
    prefix_ok_readings_replay) >>
  (impl_tac >- simp[DROP_APPEND, DROP_REPLICATE]) >>
  qpat_assum `LENGTH (gas_events_block _ _ _ _ _) = LENGTH gs`
    (fn len => pure_rewrite_tac[len]) >>
  simp_tac (srw_ss()) [gasOracleReplayTheory.gas_prefix_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, TAKE_LENGTH_APPEND] >>
  simp[DROP_LENGTH_APPEND]
QED

(* Successful native prefixes identify dynamic occurrence keys, including
   a nonzero starting cursor. This is separate from original-site events. *)
Theorem noninvoke_prefix_trace_keys:
  !pre s bb u gs tail fuel C func p d.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    LENGTH gs = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := gs ++ tail) = OK u ==>
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_block p d fuel C func bb
        (s with vs_gas_readings := gs ++ tail)) =
    ZIP (MAP (\i. (p,d,i.inst_id))
      (FILTER (\i. i.inst_opcode = GAS) pre), gs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      simp[Once trace_defs, get_instruction_def, trace_gas_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := gs ++ tail)` >> gvs[] >>
  simp[Once trace_defs, get_instruction_def, trace_step_noninvoke] >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS`
  >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
      Cases_on `gs` >> fs[update_var_def] >>
      first_x_assum (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `u`, `t`, `tail`,
         `fuel`, `C`, `func`, `p`, `d`] mp_tac) >>
      simp[visit_gas_def]) >>
  drule_all dft_nonconsuming_ok_readings >> strip_tac >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `u`, `gs`, `tail`,
     `fuel`, `C`, `func`, `p`, `d`] mp_tac) >>
  `v with vs_gas_readings := gs ++ tail = v` by
    simp[venom_state_component_equality] >>
  simp[visit_gas_def]
QED

Theorem initial_occurrence_prefix_keys:
  !xs be C func p d ms ks.
    ms = MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs /\
    ks = MAP (\i. if i.inst_opcode = GAS then [(p,d,i.inst_id)] else []) xs ==>
    !fuel k kgss tail bb u.
      k <= LENGTH xs /\
      DROP be.vs_inst_idx bb.bb_instructions = TAKE k xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k ==> (EL q xs).inst_opcode <> INVOKE) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE k ms) kgss /\
      FOLDR (dft_exec_cons fuel C) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      dftGasFromListTraceDefs$trace_gas
        (dftGasFromListTraceDefs$trace_block p d fuel C func bb
          (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE k ks), FLAT kgss)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (TAKE k xs)` by
    (simp[EVERY_EL] >> qx_gen_tac `qi` >> strip_tac >>
     `qi < k` by (gvs[LENGTH_TAKE] >> decide_tac) >>
     `EL qi (TAKE k xs) = EL qi xs` by
       (irule listTheory.EL_TAKE >> simp[]) >>
     conj_tac
     >- (qpat_x_assum `!q. q < k ==> _` (qspec_then `qi` mp_tac) >> simp[]) >>
     qpat_x_assum `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs)`
       (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `qi` mp_tac) >> simp[LENGTH_TAKE]) >>
  `LENGTH (FLAT kgss) = LENGTH (FILTER (\i. i.inst_opcode = GAS) (TAKE k xs))` by
    (irule gas_padding_filling_length >> gvs[GSYM MAP_TAKE]) >>
  `!ys. FLAT (MAP (\i. if i.inst_opcode = GAS then [(p,d,i.inst_id)] else []) ys) =
    MAP (\i. (p,d,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) ys)` by
    (Induct >> simp[] >> gen_tac >> IF_CASES_TAC >> simp[]) >>
  `FLAT (TAKE k ks) =
    MAP (\i. (p,d,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) (TAKE k xs))` by
    simp[GSYM MAP_TAKE] >>
  simp[] >> irule noninvoke_prefix_trace_keys >> simp[]
QED

Theorem initial_occurrence_prefix_replay:
  !xs be C owner ms ess.
    ms = MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs /\
    ess = MAP (\i. if i.inst_opcode = GAS then [(owner,i.inst_id)] else []) xs ==>
    !F k kgss tail.
      k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k ==> (EL q xs).inst_opcode <> INVOKE) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE k ms) kgss ==>
      (?extra.
        FLAT (TAKE k ess) =
          gas_events_block F C owner
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u.
        FOLDR (dft_exec_cons F C) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block F C owner
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        !tail'.
          FOLDR (dft_exec_cons F C) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') =
            OK (u with vs_gas_readings := tail') /\
          gas_events_block F C owner
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `gas_events_block step_fuel C owner _ _` >>
  qabbrev_tac `pre = TAKE k xs` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
    (simp[EVERY_EL, Abbr `pre`] >> qx_gen_tac `qi` >> strip_tac >>
     `qi < k` by (gvs[LENGTH_TAKE] >> decide_tac) >>
     `EL qi (TAKE k xs) = EL qi xs` by
       (irule listTheory.EL_TAKE >> simp[]) >>
     conj_tac
     >- (qpat_x_assum `!q. q < k ==> _` (qspec_then `qi` mp_tac) >> simp[]) >>
     qpat_x_assum `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs)`
       (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `qi` mp_tac) >> simp[LENGTH_TAKE]) >>
  `LENGTH (FLAT kgss) = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre)` by
    (irule gas_padding_filling_length >> gvs[Abbr `pre`, GSYM MAP_TAKE]) >>
  `FLAT (TAKE k ess) =
     MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre)` by
    simp[Abbr `pre`, GSYM MAP_TAKE, gas_padding_events] >>
  `!st label. gas_events_block step_fuel C owner
     <|bb_label := label; bb_instructions :=
       REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] [])|> st = []` by
    simp[Once gas_events_block_def, get_instruction_def] >>
  conj_tac
  >- (qspecl_then [`step_fuel`, `C`, `owner`,
        `<|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>`,
        `be with vs_gas_readings := FLAT kgss ++ tail`] mp_tac
        noninvoke_block_events_prefix >>
      simp[DROP_APPEND, DROP_REPLICATE] >> fs[EVERY_MEM]) >>
  gen_tac >> strip_tac >>
  `gas_events_block step_fuel C owner
     <|bb_label := be.vs_current_bb; bb_instructions :=
       REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>
     (be with vs_gas_readings := FLAT kgss ++ tail) =
     FLAT (TAKE k ess)` by
    (drule_all noninvoke_prefix_events_exact >>
     disch_then (qspecl_then [`owner`, `be.vs_current_bb`, `[]`] mp_tac) >>
     simp[]) >>
  `u.vs_gas_readings = tail /\
   !tail'. FOLDR (dft_exec_cons step_fuel C) OK pre
     (be with vs_gas_readings := FLAT kgss ++ tail') =
     OK (u with vs_gas_readings := tail')` by
    (irule prescribed_prefix_ok_replay >>
     simp[] >> qexists_tac `owner` >> simp[]) >>
  simp[] >> qx_gen_tac `fresh_tail` >>
  `FOLDR (dft_exec_cons step_fuel C) OK pre
     (be with vs_gas_readings := FLAT kgss ++ fresh_tail) =
     OK (u with vs_gas_readings := fresh_tail)` by simp[] >>
  qpat_x_assum `FOLDR _ OK pre
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u` kall_tac >>
  drule_all noninvoke_prefix_events_exact >>
  disch_then (qspecl_then [`owner`, `be.vs_current_bb`, `[]`] mp_tac) >>
  simp[]
QED
