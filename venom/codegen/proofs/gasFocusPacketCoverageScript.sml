Theory gasFocusPacketCoverage
Ancestors
  dftGasFromListLookup[qualified,ignore_grammar]
  gasFocusUniformStop gasFocusJointProgress codegenEntrySim[qualified]
  gasFocusVisitSiteProjection dftPacketNativeSlice dftPacketClosedRowNative
  gasFocusGasPreEdge gasFocusPlainGasPreEdge gasFocusFalseCodegenContext
  gasFocusOptLabelFlow gasFocusOptStaticAssembly codegenAsmProgOk
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  o1ContractCfgNormCursors cfgNormSupplySim stateFrame
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel fnPlanPlaceRevertPostamble
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic

Libs stepInstBaseLib

Triviality cover_marked_prefix:
  n = MIN (LENGTH marks) (SUC (LENGTH sites)) /\
  n <= LENGTH events /\ TAKE n events <<= sites /\
  TAKE n events = TAKE n source /\ MAP project source = marks ++ extra ==>
  ?rest. MAP project sites = marks ++ rest
Proof
  strip_tac >>
  drule IS_PREFIX_LENGTH >> simp[] >> strip_tac >>
  `n = LENGTH marks` by (fs[MIN_DEF] >> decide_tac) >>
  fs[IS_PREFIX_APPEND] >>
  qexists `MAP project l` >> simp[MAP_TAKE, TAKE_APPEND1]
QED

Triviality cover_events_at_larger_fuel:
  (!F. N <= F ==> gas_events_blocks F C fn s <<= sites) ==>
  gas_events_blocks f C fn s <<= sites
Proof
  strip_tac >>
  qspecl_then [`f`, `C`, `fn`, `s`, `MAX f N`] mp_tac
    (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `MAX f N` mp_tac) >>
  simp[] >> metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND]
QED

Triviality cover_stopped_events:
  ((!err. stopped <> Error err) \/ f <= fu) /\
  n <= LENGTH (gas_events_blocks f C fn s) /\
  run_blocks fu C fn s = stopped /\
  gas_events_blocks fu C fn s = events /\
  events <<= Ecut /\ Ecut <<= sites ==>
  TAKE n (gas_events_blocks f C fn s) <<= sites
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_events_blocks f C fn s <<= events` by
    (qsuff_tac `gas_events_blocks (MAX f fu) C fn s = events`
     >- (qspecl_then [`f`, `C`, `fn`, `s`, `MAX f fu`] mp_tac
          (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
         simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
     Cases_on `f <= fu`
     >- (`MAX f fu = fu` by (simp[MAX_DEF] >> decide_tac) >> simp[]) >>
     `!err. run_blocks fu C fn s <> Error err` by metis_tac[] >>
     qspecl_then [`fu`, `C`, `fn`, `s`, `MAX f fu`] mp_tac
       (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
     simp[]) >>
  irule IS_PREFIX_TRANS >>
  qexists `gas_events_blocks f C fn s` >>
  conj_tac >- metis_tac[IS_PREFIX_TRANS] >>
  PURE_REWRITE_TAC [IS_PREFIX_EQ_TAKE] >>
  qexists `n` >> simp[]
QED

Triviality cover_taken_at_fuel:
  f <= fu /\ gas_events_blocks fu C fn s <<= sites ==>
  TAKE n (gas_events_blocks f C fn s) <<= sites
Proof
  strip_tac >>
  irule IS_PREFIX_TRANS >> qexists `gas_events_blocks f C fn s` >>
  conj_tac
  >- (qspecl_then [`f`,`C`,`fn`,`s`,`fu`] mp_tac
        (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
      simp[IS_PREFIX_APPEND] >> metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND]) >>
  PURE_REWRITE_TAC [IS_PREFIX_EQ_TAKE'] >> qexists `n` >> REFL_TAC
QED

Triviality cover_take_slots:
  LIST_REL rel (slots ++ later) raw ==>
  LIST_REL rel slots (TAKE (LENGTH slots) raw)
Proof
  rw[LIST_REL_EL_EQN, LENGTH_TAKE, EL_TAKE, EL_APPEND1] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[EL_APPEND1]
QED

Triviality cover_events_at_fuel:
  n <= LENGTH (gas_events_blocks f C fn s) /\ f <= fu /\
  gas_events_blocks fu C fn s = events /\ Ecut = events ++ extra /\
  sites = Ecut ++ later ==>
  TAKE n (gas_events_blocks f C fn s) <<= sites
Proof
  strip_tac >>
  irule cover_stopped_events >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Ecut`, `events`, `fu`, `run_blocks fu C fn s`] >>
  simp[IS_PREFIX_APPEND]
QED

Theorem cover_cfg_active:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ==>
  s8.vs_gas_readings = s9.vs_gas_readings /\
  s8.vs_labels = s9.vs_labels /\
  active_inst fn9 inst9 s9
Proof
  Cases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  drule cover_cfg_cursors_frame >> simp[] >> strip_tac >>
  qpat_assum `EVERY _ schedules`
    (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  drule cfg_norm_cursors_last >> simp[] >> metis_tac[]
QED

Triviality cover_block_events_split:
  s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
  FOLDR (dft_exec_cons f C) OK
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u ==>
  gas_events_block f C fn.fn_name bb s =
    gas_events_block f C fn.fn_name
      (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s ++
    gas_events_block f C fn.fn_name bb u
Proof
  strip_tac >> drule_all native_trace_block_prefix_split >>
  disch_then (qspecl_then [`[]`, `fn`, `0`] (mp_tac o cj 2)) >>
  ONCE_REWRITE_TAC [GSYM (Q.SPECL [`[]`, `0`, `f`, `C`, `fn`]
    (cj 2 focus_visit_site_projection))] >>
  disch_then SUBST1_TAC >> simp[FILTER_APPEND_DISTRIB, MAP_APPEND]
QED

Triviality cover_invoke_events_prefix:
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME ent ==>
  gas_events_blocks f C callee ent <<= gas_events_block f C owner bb s
Proof
  strip_tac >> drule gas_events_block_at >>
  disch_then (qspecl_then [`f`, `C`, `owner`] SUBST1_TAC) >>
  simp[gas_events_step_def, IS_PREFIX_APPEND] >>
  Cases_on `step_inst f C i s` >> simp[] >> metis_tac[]
QED

Triviality cover_closed_row_events:
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis entry bb.bb_instructions = OK sp /\
  z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  z <> [] /\ is_terminator (LAST z).inst_opcode /\
  s = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  FOLDR (dft_exec_cons f C) OK z s = OK u /\ ~u.vs_halted ==>
  gas_events_blocks (SUC f) C sf entry =
    gas_events_block f C sf.fn_name
      (bb with bb_instructions :=
        TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z) s ++
    gas_events_blocks f C sf u
Proof
  strip_tac >>
  `exec_block f C bb s = OK u` by
    (qspecl_then [`f`, `C`, `bb`, `s`, `z`] mp_tac
       native_exec_block_terminated_fold >>
     simp[]) >>
  qpat_x_assum `s = sp with vs_inst_idx := _` SUBST_ALL_TAC >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_events_blocks_def)) >>
  simp[TAKE_DROP]
QED

Triviality cover_open_row_events:
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis entry bb.bb_instructions = OK sp /\
  s = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  LENGTH z < LENGTH (DROP s.vs_inst_idx bb.bb_instructions) /\
  z = TAKE (LENGTH z) (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z /\
  FOLDR (dft_exec_cons f C) OK z s = OK u ==>
  ?after. gas_events_blocks (SUC f) C sf entry =
    gas_events_block f C sf.fn_name
      (bb with bb_instructions := TAKE s.vs_inst_idx bb.bb_instructions ++ z) s ++
    (gas_events_block f C sf.fn_name bb u ++ after)
Proof
  strip_tac >>
  `s.vs_inst_idx + LENGTH z <= LENGTH bb.bb_instructions` by
    (qpat_assum `LENGTH z < LENGTH (DROP _ bb.bb_instructions)` mp_tac >>
     simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
  `TAKE s.vs_inst_idx bb.bb_instructions ++ z =
     TAKE (s.vs_inst_idx + LENGTH z) bb.bb_instructions` by
    (REWRITE_TAC [TAKE_SUM] >>
     qpat_assum `z = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >> REFL_TAC) >>
  `gas_events_block f C sf.fn_name bb s =
   gas_events_block f C sf.fn_name
     (bb with bb_instructions := TAKE (s.vs_inst_idx + LENGTH z) bb.bb_instructions) s ++
   gas_events_block f C sf.fn_name bb u` by
    (irule cover_block_events_split >>
     qpat_assum `z = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >> simp[]) >>
  qexists `case exec_block f C bb s of
            OK v => if v.vs_halted then [] else gas_events_blocks f C sf v
          | _ => []` >>
  qpat_x_assum `s = sp with vs_inst_idx := _` SUBST_ALL_TAC >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_events_blocks_def)) >>
  simp[APPEND_ASSOC]
QED

Triviality cover_fold_event_prefix:
  !rows step.
    (!es r row.
      step (es,r) row =
        (es ++ FST (step ([],r) row), SND (step ([],r) row))) ==>
    !es r.
      FOLDL step (es,r) rows =
        (es ++ FST (FOLDL step ([],r) rows),
         SND (FOLDL step ([],r) rows))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  rename1 `FOLDL next (es,r) (h::rows)` >>
  first_x_assum (qspec_then `next` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> pure_rewrite_tac [FOLDL] >>
  first_assum (qspecl_then [`es`, `r`, `h`] SUBST1_TAC) >>
  Cases_on `next ([],r) h` >>
  rename1 `next ([],r) h = (local_events,local_result)` >>
  simp[NoAsms] >>
  qpat_assum `!es r. FOLDL next (es,r) rows = _`
    (qspecl_then [`es ++ local_events`, `local_result`] SUBST1_TAC) >>
  qpat_assum `!es r. FOLDL next (es,r) rows = _`
    (qspecl_then [`local_events`, `local_result`] SUBST1_TAC) >>
  simp[NoAsms, APPEND_ASSOC]
QED

Triviality cover_cfg_block_opcodes:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
  !ss fn m tt gn i a pending j v.
    HD rounds = (ss,fn,m) /\ LAST rounds = (tt,gn,NONE) /\
    HD cells = ((i,a),pending) /\ LAST cells = ((j,v),NONE) /\
    ~MEM j.inst_opcode [ASSIGN; JMP; JNZ] ==>
    a.vs_inst_idx = v.vs_inst_idx /\
    ?bb gb. lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
         lookup_block v.vs_current_bb gn.fn_blocks = SOME gb /\
         MAP (\k. k.inst_opcode) bb.bb_instructions =
         MAP (\k. k.inst_opcode) gb.bb_instructions
Proof
  ho_match_mp_tac cfg_norm_cursors_strongind >> simp[LAST_CONS] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[supply_norm_inv_def] >> drule_all dftGasFromListLookupTheory.wf_active_lookup >> metis_tac[])
  >- (qpat_assum `!tt gn j v. _` (qspecl_then [`tt`, `gn`, `j`, `v'`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then strip_assume_tac >>
      `wf_function fn /\ wf_function next_fn` by
        (drule_all_then assume_tac cfg_norm_round_supply_norm_inv >>
         gvs[supply_norm_inv_def]) >>
      `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
        (irule venomExecProofsTheory.wf_lookup_block >> simp[]) >>
      `lookup_block bb.bb_label next_fn.fn_blocks =
       SOME (supply_block_image pred target split repls bb)` by
        (qspecl_then [`next_fn`, `supply_block_image pred target split repls bb`] mp_tac
           venomExecProofsTheory.wf_lookup_block >> simp[]) >>
      qexistsl [`bb`, `gb`] >>
      qpat_x_assum `lookup_block _ next_fn.fn_blocks = SOME _` mp_tac >>
      qpat_x_assum `lookup_block _ next_fn.fn_blocks = SOME _` mp_tac >>
      strip_tac >> strip_tac >> gvs[supply_block_image_opcodes]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by gvs[supply_norm_inv_def] >>
  `MEM (EL v.vs_inst_idx split.bb_instructions).inst_opcode [ASSIGN; JMP; JNZ]` by
    (drule_all supply_split_index_shape >> simp[] >> metis_tac[]) >>
  drule cfg_norm_cursors_admin_opcode >>
  qpat_assum `LAST _ = ((j,v'),NONE)`
    (fn th => PURE_REWRITE_TAC [HD, pairTheory.FST, th]) >>
  qpat_assum `MEM _ [ASSIGN; JMP; JNZ]`
    (fn th => PURE_REWRITE_TAC [th]) >>
  simp[]
QED

Triviality cover_revert_step:
  i.inst_opcode = REVERT ==>
  step_inst f C i s <> OK u /\ step_inst f C i s <> IntRet ir u
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[]
QED

Triviality cover_revert_fold:
  !pre s.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\ i.inst_opcode = REVERT ==>
    FOLDR (dft_exec_cons f C) OK (pre ++ [i]) s <> OK u /\
    FOLDR (dft_exec_cons f C) OK (pre ++ [i]) s <> IntRet ir u
Proof
  Induct >> simp[dftIndexedExecTheory.dft_exec_cons_def] >> rpt strip_tac
  >- (Cases_on `step_inst f C i s` >> gvs[cover_revert_step, is_terminator_def])
  >- (Cases_on `step_inst f C i s` >> gvs[cover_revert_step, is_terminator_def])
  >- (Cases_on `step_inst f C h s` >> gvs[] >>
      metis_tac[dftRunRelTheory.dft_swap_nonterminator_no_intret])
  >- (Cases_on `step_inst f C h s` >> gvs[] >>
      metis_tac[dftRunRelTheory.dft_swap_nonterminator_no_intret])
QED

Triviality cover_fold_rows:
  !rows row_eval (collector : num -> venom_state -> 'a list) finish valid
    depth initial entry events u.
    rows <> [] /\
    (!pre row post prior s ev next.
       rows = pre ++ row::post /\
       FOLDL (\(es,result) row.
         case result of
           OK st => (es ++ FST (row_eval row st),SND (row_eval row st))
         | other => (es,other)) (initial,OK entry) pre = (prior,OK s) /\
       row_eval row s = (ev,OK next) ==>
       if post = [] then
         valid row next /\ (?after. collector (depth + LENGTH pre) s =
           ev ++ (finish row next ++ after))
       else collector (depth + LENGTH pre) s =
           ev ++ collector (depth + SUC (LENGTH pre)) next) /\
    FOLDL (\(es,result) row.
      case result of
        OK s => (es ++ FST (row_eval row s),SND (row_eval row s))
      | other => (es,other)) (initial,OK entry) rows = (events,OK u) ==>
    valid (LAST rows) u /\
    ?after. initial ++ collector depth entry =
      events ++ (finish (LAST rows) u ++ after)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `row_eval h entry` >>
  rename1 `row_eval h entry = (local_events,result)` >>
  `?next. result = OK next` by
    (`h::rows = [h] ++ rows` by simp[] >>
     qpat_x_assum `h::rows = [h] ++ rows` (fn split =>
       qpat_assum `FOLDL _ (initial,OK entry) (h::rows) = _`
         (mp_tac o MATCH_MP dftPacketRowAlignmentTheory.dft_packet_plan_success_prefix o
          CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV split))))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `result = OK next` SUBST_ALL_TAC >>
  qpat_assum `row_eval h entry = _` (fn row =>
    qpat_assum `FOLDL _ (initial,OK entry) (h::rows) = _`
      (assume_tac o SIMP_RULE (srw_ss()) [row])) >>
  qpat_assum `!pre row post prior s ev next. _`
    (qspecl_then [`[]`, `h`, `rows`, `initial`, `entry`, `local_events`, `next`]
      mp_tac) >>
  impl_tac >- simp[] >>
  Cases_on `rows` >> simp[NoAsms, LAST_CONS] >> strip_tac
  >- (qpat_assum `row_eval h entry = _` (fn row =>
        qpat_x_assum `FOLDL _ (initial,OK entry) [h] = _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [row])) >>
      conj_tac >- gvs[] >> qexists `after` >> gvs[APPEND_ASSOC]) >>
  first_x_assum (qspecl_then [`row_eval`, `collector`, `finish'`, `valid`, `SUC depth`,
    `initial ++ local_events`, `next`, `events`, `u`] mp_tac) >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!pre row post prior s ev next. _`
        (qspecl_then [`h::pre`, `row`, `post`, `prior`, `s`, `ev`, `next'`]
          mp_tac) >>
      impl_tac >- simp[] >> simp[NoAsms, ADD_CLAUSES]) >>
      first_assum ACCEPT_TAC) >>
  simp[APPEND_ASSOC, LAST_CONS, ADD1]
QED

Triviality cover_common_event_prefix:
  low <<= full /\ captured <<= full /\
  n <= LENGTH low /\ n <= LENGTH captured /\ captured <<= sites ==>
  TAKE n low <<= sites
Proof
  strip_tac >>
  `TAKE n low = TAKE n captured` by
    (`TAKE n low = TAKE n full /\ TAKE n captured = TAKE n full` suffices_by simp[] >>
     conj_tac
     >- (qpat_x_assum `low <<= full` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
         simp[TAKE_APPEND1]) >>
     qpat_x_assum `captured <<= full`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[TAKE_APPEND1]) >>
  irule IS_PREFIX_TRANS >> qexists `captured` >> simp[] >>
  PURE_REWRITE_TAC [IS_PREFIX_EQ_TAKE] >> qexists `n` >> simp[]
QED

Triviality cover_fold_index:
  !xs s.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    FOLDR (dft_exec_cons f C) OK xs s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH xs
Proof
  Induct >> simp[dftIndexedExecTheory.dft_exec_cons_def] >> rpt strip_tac >>
  Cases_on `step_inst f C h s` >> gvs[] >>
  first_x_assum drule >> simp[ADD_CLAUSES]
QED

Triviality cover_native_plan:
  replay_row = (\(bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (fuel-e) C sf.fn_name
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (fuel-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  replay_plan = (\plan entry. FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (replay_row row s), SND (replay_row row s))
      | other => (es,other)) ([],OK entry) plan) /\
  wf_function sf /\ plan <> [] /\
  MAP (\(bb,e,z). e) plan = GENLIST (\r. incoming + SUC r) (LENGTH plan) /\
  (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
    e <= fuel /\ MEM bb sf.fn_blocks /\
    (if SUC r < LENGTH plan then
      bb.bb_instructions <> [] /\
      EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
      is_terminator (LAST bb.bb_instructions).inst_opcode /\
      ~MEM (LAST bb.bb_instructions).inst_opcode [RET; RETFMP; DRET] /\
      z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
     else
      LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
  (!r bb e z es st.
    r < LENGTH plan /\ EL r plan = (bb,e,z) /\
    replay_plan (TAKE r plan) entry = (es,OK st) ==>
    lookup_block st.vs_current_bb sf.fn_blocks = SOME bb /\
    (0 < r ==> ~st.vs_halted)) /\
  replay_plan plan entry = (events,OK u) ==>
  (\(bb,e,z). \st:venom_state. get_instruction bb st.vs_inst_idx =
    SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
      bb.bb_instructions))) (LAST plan) u /\
  ?after. gas_events_blocks (fuel-incoming) C sf entry =
    events ++ (((\(bb,e,z). gas_events_block (fuel-e) C sf.fn_name bb) (LAST plan)) u ++ after)
Proof
  strip_tac >>
  mp_tac (Q.ISPECL [`plan:(basic_block # num # instruction list) list`,
    `replay_row:(basic_block # num # instruction list) -> venom_state ->
      (string # num) list # exec_result`,
    `\d st. gas_events_blocks (fuel-d) C sf st`,
    `\(bb,e,z):basic_block # num # instruction list.
      gas_events_block (fuel-e) C sf.fn_name bb`,
    `\(bb,e,z):basic_block # num # instruction list. \st:venom_state.
      get_instruction bb st.vs_inst_idx = SOME (EL (LENGTH z)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions))`,
    `incoming:num`, `[]:(string # num) list`, `entry:venom_state`,
    `events:(string # num) list`, `u:venom_state`] cover_fold_rows) >>
  simp[NoAsms] >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          PairCases_on `row` >>
          rename1 `plan = pre ++ [(bb,e,z)] ++ post` >>
          qabbrev_tac `k = LENGTH pre` >>
          `k < LENGTH plan /\ EL k plan = (bb,e,z) /\ TAKE k plan = pre` by
            (qpat_assum `plan = _` SUBST1_TAC >>
             simp[NoAsms, Abbr `k`, EL_APPEND] >>
             PURE_REWRITE_TAC [GSYM APPEND_ASSOC, TAKE_LENGTH_APPEND] >> REFL_TAC) >>
          `e = incoming + SUC k` by
            (qpat_assum `MAP _ plan = _`
               (mp_tac o AP_TERM ``EL k : num list -> num``) >>
             simp[EL_MAP, EL_GENLIST]) >>
          qpat_assum `!r bb e z. r < LENGTH plan /\ _ ==> _`
            (qspecl_then [`k`, `bb`, `e`, `z`] mp_tac) >>
          impl_tac >- simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
          `replay_plan (TAKE k plan) entry = (prior,OK s)` by
            (qpat_assum `replay_plan = _` (fn eval =>
               qpat_assum `TAKE k plan = pre`
                 (fn take => PURE_REWRITE_TAC [eval, take])) >>
             BETA_TAC >> first_assum ACCEPT_TAC) >>
          qpat_assum `!r bb e z es st. r < LENGTH plan /\ _ ==> _`
            (qspecl_then [`k`, `bb`, `e`, `z`, `prior`, `s`] mp_tac) >>
          impl_tac >- simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
          `fuel - (incoming + k) = SUC (fuel-e)` by
            (qpat_assum `e = incoming + SUC k` mp_tac >>
             qpat_assum `e <= fuel` mp_tac >>
             simp[NoAsms, Abbr `k`] >> decide_tac) >>
          Cases_on `eval_phis s bb.bb_instructions` >>
          qpat_assum `replay_row = _` (fn row =>
            qpat_assum `replay_row (bb,e,z) s = _`
              (mp_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [row])) >>
          qpat_assum `eval_phis s bb.bb_instructions = _`
            (fn phis => simp_tac (srw_ss()) [phis]) >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          `SUC k < LENGTH plan <=> post <> []` by
            (qpat_assum `plan = _` SUBST1_TAC >> Cases_on `post` >>
             simp[NoAsms, Abbr `k`] >> decide_tac) >>
          `fuel - (incoming + SUC k) = fuel-e` by simp[Abbr `k`] >>
          qpat_assum `fuel - (incoming + k) = SUC (fuel-e)`
            (fn th => PURE_REWRITE_TAC [th]) >>
          qpat_assum `fuel - (incoming + SUC k) = fuel-e`
            (fn th => PURE_REWRITE_TAC [th]) >>
          Cases_on `post = []` >>
          qpat_x_assum `if SUC k < LENGTH plan then _ else _` mp_tac >>
          qpat_assum `SUC k < LENGTH plan <=> post <> []`
            (fn th => PURE_REWRITE_TAC [th]) >>
          (qpat_assum `post = []` (fn th => simp_tac bool_ss [th]) ORELSE
           qpat_assum `post <> []` (fn th => simp_tac bool_ss [th])) >>
          disch_then (map_every assume_tac o CONJUNCTS)
          >- (conj_tac
              >- (`next.vs_inst_idx = phi_prefix_length bb.bb_instructions + LENGTH z` by
                    (drule_all cover_fold_index >> simp[]) >>
                  qpat_assum `LENGTH z < LENGTH (DROP _ _)` mp_tac >>
                  simp_tac (srw_ss()) [NoAsms, get_instruction_def, LENGTH_DROP] >> rpt strip_tac >>
                  `phi_prefix_length bb.bb_instructions + LENGTH z <
                    LENGTH bb.bb_instructions` by decide_tac >> simp[EL_DROP]) >>
              mp_tac (Q.INST [`entry` |-> `s`, `sp` |-> `v`, `f` |-> `fuel-e`,
                `u` |-> `next`, `s` |-> `v with vs_inst_idx :=
                   phi_prefix_length bb.bb_instructions`] cover_open_row_events) >>
              impl_tac >- (simp[] >>
                qpat_assum `LENGTH z < LENGTH (DROP _ _)`
                  (ACCEPT_TAC o REWRITE_RULE [LENGTH_DROP])) >>
              qpat_assum `gas_events_block _ _ _ _ _ = ev`
                (fn th => simp[NoAsms, th])) >>
          `TAKE (SUC k) plan = pre ++ [(bb,e,z)]` by
            simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
          `replay_plan (TAKE (SUC k) plan) entry = (prior ++ ev,OK next)` by
            (qpat_assum `replay_plan = _` (fn ev => PURE_REWRITE_TAC [ev]) >>
             qpat_assum `TAKE (SUC k) plan = _` SUBST1_TAC >>
             BETA_TAC >> PURE_REWRITE_TAC [FOLDL_APPEND, FOLDL] >>
             qpat_assum `FOLDL _ ([],OK entry) pre = _` SUBST1_TAC >>
             qpat_assum `replay_row (bb,e,z) s = _` (fn row => simp[NoAsms, row])) >>
          `SUC k < LENGTH plan` by simp[] >>
          `?b2 e2 z2. EL (SUC k) plan = (b2,e2,z2)` by
            metis_tac[pairTheory.PAIR] >>
          rename1 `EL (SUC k) plan = (b2,e2,z2)` >>
          `~next.vs_halted` by
            (qpat_assum `!r bb e z es st. r < LENGTH plan /\ _ ==> _`
              (qspecl_then [`SUC k`, `b2`, `e2`, `z2`, `prior ++ ev`, `next`] mp_tac) >>
             simp[]) >>
          `bb_well_formed bb` by fs[wf_function_def, EVERY_MEM] >>
          `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
            metis_tac[venomExecProofsTheory.phi_prefix_length_lt_wf] >>
          `z <> [] /\ is_terminator (LAST z).inst_opcode` by
            (qpat_assum `z = DROP _ _` SUBST1_TAC >> simp[DROP_EQ_NIL, last_drop]) >>
          mp_tac (Q.INST [`entry` |-> `s`, `sp` |-> `v`, `f` |-> `fuel-e`,
            `u` |-> `next`, `s` |-> `v with vs_inst_idx :=
               phi_prefix_length bb.bb_instructions`] cover_closed_row_events) >>
          impl_tac >- simp[] >>
          qpat_assum `gas_events_block _ _ _ _ _ = ev`
            (fn th => simp[NoAsms, th])) >>
      qpat_assum `replay_plan = _` (fn eval =>
        qpat_assum `replay_plan plan entry = (events,OK u)`
          (ACCEPT_TAC o CONV_RULE (DEPTH_CONV BETA_CONV) o PURE_REWRITE_RULE [eval]))) >>
  simp[]
QED

Triviality cover_fold_levels:
  !rows row_eval (collector : num -> venom_state -> 'a list)
      depth initial entry events u.
    (!pre row post prior s ev next.
       rows = pre ++ row::post /\
       FOLDL (\(es,result) row.
         case result of
           OK st => (es ++ FST (row_eval row st),SND (row_eval row st))
         | other => (es,other)) (initial,OK entry) pre = (prior,OK s) /\
       row_eval row s = (ev,OK next) ==>
       ev ++ (if post = [] then [] else collector (depth + SUC (LENGTH pre)) next)
           <<= collector (depth + LENGTH pre) s) /\
    FOLDL (\(es,result) row.
      case result of
        OK st => (es ++ FST (row_eval row st),SND (row_eval row st))
      | other => (es,other)) (initial,OK entry) rows = (events,OK u) ==>
    events <<= initial ++ collector depth entry
Proof
  Induct >- simp[IS_PREFIX_APPEND] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `row_eval h entry` >>
  rename1 `row_eval h entry = (local_events,result)` >>
  `?next. result = OK next` by
    (`h::rows = [h] ++ rows` by simp[] >>
     qpat_x_assum `h::rows = [h] ++ rows` (fn split =>
       qpat_assum `FOLDL _ (initial,OK entry) (h::rows) = _`
         (mp_tac o MATCH_MP dftPacketRowAlignmentTheory.dft_packet_plan_success_prefix o
          CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV split))))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `result = OK next` SUBST_ALL_TAC >>
  qpat_assum `row_eval h entry = _` (fn row =>
    qpat_x_assum `FOLDL _ (initial,OK entry) (h::rows) = _`
      (assume_tac o SIMP_RULE (srw_ss()) [row])) >>
  qpat_assum `!pre row post prior s ev next. _`
    (qspecl_then [`[]`, `h`, `rows`, `initial`, `entry`, `local_events`, `next`]
      mp_tac) >>
  impl_tac >- simp[] >>
  Cases_on `rows = []`
  >- (qpat_x_assum `rows = []` SUBST_ALL_TAC >>
      simp[NoAsms] >> strip_tac >>
      qpat_x_assum `FOLDL _ (initial ++ local_events,OK next) [] = _`
        (strip_assume_tac o REWRITE_RULE [FOLDL, pairTheory.PAIR_EQ]) >>
      gvs[]) >>
  simp[NoAsms, ADD_CLAUSES] >>
  qpat_assum `rows <> []` (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  first_x_assum (qspecl_then [`row_eval`, `collector`, `SUC depth`,
    `initial ++ local_events`, `next`, `events`, `u`] mp_tac) >>
  impl_tac
  >- (conj_tac >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!pre row post prior s ev next. _`
        (qspecl_then [`h::pre`, `row`, `post`, `prior`, `s`, `ev`, `next'`]
          mp_tac) >>
      impl_tac >- simp[] >> simp[NoAsms, ADD_CLAUSES]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  irule IS_PREFIX_TRANS >> qexists `initial ++ (local_events ++ collector (SUC depth) next)` >>
  conj_tac >- simp[GSYM APPEND_ASSOC] >>
  PURE_REWRITE_TAC [APPEND_ASSOC] >> first_assum ACCEPT_TAC
QED

Triviality cover_native_levels:
  level_eval = (\(sf,plan,call) entry.
    (FST (plan_eval fuel C sf.fn_name plan entry),
      case SND (plan_eval fuel C sf.fn_name plan entry) of
        OK u => (case call of NONE => OK u | SOME c => call_setup C c u)
      | other => other)) /\
  rooted_eval fuel C = (\levels entry.
    FOLDL (\(es,r) level.
      case r of
        OK s => (es ++ FST (level_eval level s),SND (level_eval level s))
      | other => (es,other)) ([],OK entry) levels) /\
  levels <> [] /\ HD depths = 0 /\ FST (HD levels) = root /\
  (!k sf plan call prior s ev u.
    k < LENGTH levels /\ EL k levels = (sf,plan,call) /\
    rooted_eval fuel C (TAKE k levels) entry = (prior,OK s) /\
    plan_eval fuel C sf.fn_name plan s = (ev,OK u) ==>
    (\(bb,e,z). \st:venom_state. get_instruction bb st.vs_inst_idx =
      SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions))) (LAST plan) u /\
    ?after. gas_events_blocks (fuel-EL k depths) C sf s =
      ev ++ ((\(bb,e,z). gas_events_block (fuel-e) C sf.fn_name bb) (LAST plan) u ++ after)) /\
  (!k sf plan call.
    k < LENGTH levels /\ EL k levels = (sf,plan,call) ==>
    if SUC k < LENGTH levels then
      ?c nm ops bb e z.
        call = SOME c /\ LAST plan = (bb,e,z:instruction list) /\
        c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
        lookup_function nm C.ctx_functions = SOME (FST (EL (SUC k) levels)) /\
        EL (SUC k) depths = e
    else call = NONE) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval fuel C levels entry = (events,OK result) ==>
  events <<= gas_events_blocks fuel C root entry
Proof
  strip_tac >>
  mp_tac (Q.ISPECL [`levels:(ir_function # (basic_block # num # instruction list) list #
    instruction option) list`,
    `level_eval:(ir_function # (basic_block # num # instruction list) list #
    instruction option) -> venom_state -> (string # num) list # exec_result`,
    `\k s. gas_events_blocks (fuel-EL k depths) C (FST (EL k (levels : (ir_function #
      (basic_block # num # instruction list) list # instruction option) list))) s`,
    `0:num`, `[]:(string # num) list`, `entry:venom_state`, `events:(string # num) list`,
    `result:venom_state`] cover_fold_levels) >>
  simp[NoAsms] >>
  impl_tac
  >- (conj_tac
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          PairCases_on `row` >>
          rename1 `levels = pre ++ [(sf,plan,call)] ++ post` >>
          qabbrev_tac `k = LENGTH pre` >>
          `k < LENGTH levels /\ EL k levels = (sf,plan,call) /\ TAKE k levels = pre` by
            (qpat_assum `levels = _` SUBST1_TAC >>
             simp[NoAsms, Abbr `k`, EL_APPEND] >>
             PURE_REWRITE_TAC [GSYM APPEND_ASSOC, TAKE_LENGTH_APPEND] >> REFL_TAC) >>
          `rooted_eval fuel C (TAKE k levels) entry = (prior,OK s)` by
            (qpat_assum `rooted_eval fuel C = _` (fn eval =>
              qpat_assum `TAKE k levels = _`
                (fn take => PURE_REWRITE_TAC [eval, take])) >>
             BETA_TAC >> first_assum ACCEPT_TAC) >>
          Cases_on `plan_eval fuel C sf.fn_name plan s` >>
          rename1 `plan_eval fuel C sf.fn_name plan s = (local_events,local_result)` >>
          qpat_assum `level_eval = _` (fn level =>
            qpat_x_assum `level_eval (sf,plan,call) s = _`
              (mp_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [level])) >>
          Cases_on `local_result` >> simp[] >> strip_tac >>
          rename1 `plan_eval fuel C sf.fn_name plan s = (local_events,OK caller)` >>
          qpat_assum `!k sf plan call prior s ev u. _`
            (qspecl_then [`k`, `sf`, `plan`, `call`, `prior`, `s`,
              `local_events`, `caller`] mp_tac) >>
          impl_tac >- simp[] >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
          Cases_on `post = []`
          >- (simp[Abbr `k`] >> PURE_REWRITE_TAC [IS_PREFIX_APPEND] >>
              qexists `((\(bb,e,z). gas_events_block (fuel-e) C sf.fn_name bb)
                (LAST plan)) caller ++ after` >> simp[EL_APPEND]) >>
          `SUC k < LENGTH levels` by
            (qpat_assum `levels = _` SUBST1_TAC >> Cases_on `post` >>
             simp[NoAsms, Abbr `k`] >> gvs[] >> decide_tac) >>
          qpat_assum `!k sf plan call. k < LENGTH levels /\ _ ==> _`
            (qspecl_then [`k`, `sf`, `plan`, `call`] mp_tac) >>
          impl_tac >- simp[] >>
          qpat_assum `SUC k < LENGTH levels` (fn th => simp_tac bool_ss [th]) >>
          strip_tac >>
          qpat_x_assum `_ = OK next` mp_tac >>
          qpat_assum `call = SOME _` (fn call_eq =>
            qpat_assum `decode_invoke _ = SOME (nm,ops)` (fn decode =>
              qpat_assum `lookup_function nm C.ctx_functions = _`
                (fn lookup => simp_tac (srw_ss()) [call_eq,decode,lookup]))) >>
          Cases_on `eval_operands ops caller` >> simp_tac (srw_ss()) [] >> strip_tac >>
          rename1 `eval_operands ops caller = SOME args` >>
          `get_instruction bb caller.vs_inst_idx = SOME (EL (LENGTH (z:instruction list))
             (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions))` by
            (qpat_assum `(\(bb,e,z). \st. get_instruction _ _ = _) (LAST plan) caller`
              mp_tac >> qpat_assum `LAST plan = _` (fn th => simp_tac (srw_ss()) [th])) >>
          `setup_callee (FST (EL (SUC k) (levels :
             (ir_function # (basic_block # num # instruction list) list # instruction option) list)))
             args caller = SOME next` by
            (qpat_x_assum `_ = OK next` mp_tac >>
             Cases_on `setup_callee (FST (EL (SUC k) (levels :
               (ir_function # (basic_block # num # instruction list) list #
               instruction option) list))) args caller` >> simp_tac (srw_ss()) []) >>
          mp_tac (Q.INST [`f` |-> `fuel-EL (SUC k) depths`,
            `owner` |-> `sf.fn_name`, `s` |-> `caller`, `ent` |-> `next`,
            `i` |-> `EL (LENGTH (z:instruction list)) (DROP (phi_prefix_length bb.bb_instructions)
              bb.bb_instructions)`, `callee` |-> `FST (EL (SUC k)
              (levels : (ir_function # (basic_block # num # instruction list) list #
                instruction option) list))`] cover_invoke_events_prefix) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          qpat_assum `call = SOME _` (fn call_eq =>
            qpat_assum `levels = _` (fn split =>
              PURE_REWRITE_TAC [GSYM (REWRITE_RULE [call_eq] split)])) >>
          map_every (fn pat => qpat_assum pat (fn th => simp_tac (srw_ss()) [th]))
            [`post <> []`, `EL k levels = _`, `gas_events_blocks (fuel - EL k depths) C sf s = _`,
             `LAST plan = _`, `local_events = ev`] >>
          PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
          simp_tac (srw_ss()) [] >> metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3]) >>
      qpat_assum `rooted_eval fuel C = _` (fn eval =>
        qpat_assum `rooted_eval fuel C levels entry = _`
          (ACCEPT_TAC o CONV_RULE (DEPTH_CONV BETA_CONV) o PURE_REWRITE_RULE [eval]))) >>
  simp[GSYM EL]
QED

Triviality cover_rooted_events:
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
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan =
      GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok fuel C levels paths depths root entry [] 0 /\
  MEM root C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  rooted_eval fuel C levels entry = (events,OK result) ==>
  events <<= gas_events_blocks fuel C root entry
Proof
  strip_tac >>
  qpat_assum `levels_ok = _` (fn th =>
    qpat_x_assum `levels_ok fuel C levels paths depths root entry [] 0`
      (map_every assume_tac o CONJUNCTS o
        CONV_RULE (DEPTH_CONV BETA_CONV) o PURE_REWRITE_RULE [th])) >>
  qabbrev_tac `L = (\(sf,plan,call) entry.
    (FST (plan_eval fuel C sf.fn_name plan entry),
      case SND (plan_eval fuel C sf.fn_name plan entry) of
        OK u => (case call of NONE => OK u | SOME c => call_setup C c u)
      | other => other))` >>
  mp_tac (Q.INST [`level_eval` |-> `L`] cover_native_levels) >>
  impl_tac
  >- (conj_tac
      >- (qpat_assum `Abbrev (L = _)`
           (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) >>
      conj_tac
      >- (qpat_assum `rooted_eval = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
          BETA_TAC >> rpt ABS_TAC >>
          AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
          PURE_REWRITE_TAC [FUN_EQ_THM] >>
          qx_gen_tac `acc` >> qx_gen_tac `level` >>
          PairCases_on `acc` >> PairCases_on `level` >>
          Cases_on `acc1` >> simp[Abbr `L`]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `plan_ok fuel C sf (EL k depths) plan s` by
            (qpat_assum `!i sf plan call. _`
              (qspecl_then [`k`, `sf`, `plan`, `call`] mp_tac) >>
             impl_tac >- simp[] >> metis_tac[]) >>
          `wf_function sf` by
            (Cases_on `k`
             >- (`sf = root` by (Cases_on `levels` >> fs[]) >>
                 fs[EVERY_MEM]) >>
             rename1 `EL (SUC n) levels = (sf,plan,call)` >>
             `?pf pp pc. EL n levels = (pf,pp,pc)` by metis_tac[pairTheory.PAIR] >>
             qpat_assum `!i sf plan call. _`
               (qspecl_then [`n`, `pf`, `pp`, `pc`] mp_tac) >>
             `n < LENGTH levels` by decide_tac >>
             impl_tac >- simp[] >> disch_then (mp_tac o cj 3) >>
             qpat_assum `SUC n < LENGTH levels` (fn th => simp_tac bool_ss [th]) >>
             disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
             `MEM sf C.ctx_functions` by
               (qpat_assum `lookup_function _ _ = SOME (FST (EL (SUC n) levels))`
                 (mp_tac o MATCH_MP lookup_function_MEM) >> simp[]) >>
             fs[EVERY_MEM]) >>
          mp_tac (Q.INST [`replay_row` |-> `row_eval fuel C sf.fn_name`,
            `replay_plan` |-> `plan_eval fuel C sf.fn_name`, `entry` |-> `s`,
            `incoming` |-> `EL k depths`, `events` |-> `ev`] cover_native_plan) >>
          qpat_assum `plan_ok = _` (fn ok =>
            qpat_x_assum `plan_ok fuel C sf (EL k depths) plan s`
              (strip_assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o
               PURE_REWRITE_RULE [ok])) >>
          impl_tac
          >- (conj_tac
              >- (qpat_assum `row_eval = _` (fn eq => CONV_TAC (LHS_CONV
                    (PURE_REWRITE_CONV [eq]))) >> BETA_TAC >> REFL_TAC) >>
              conj_tac
              >- (qpat_assum `plan_eval = _` (fn eq => CONV_TAC (LHS_CONV
                    (PURE_REWRITE_CONV [eq]))) >> BETA_TAC >> REFL_TAC) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
          simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!i sf plan call. _`
            (qspecl_then [`k`, `sf`, `plan`, `call`] mp_tac) >>
          impl_tac >- simp[] >> disch_then (assume_tac o cj 3) >>
          Cases_on `SUC k < LENGTH levels` >>
          qpat_x_assum `if SUC k < LENGTH levels then _ else _` mp_tac
          >- (qpat_assum `SUC k < LENGTH levels`
                (fn th => PURE_REWRITE_TAC [th, COND_CLAUSES]) >>
              disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
              qexistsl [`c`, `nm`, `ops`, `bb`, `e`, `z`] >> simp[]) >>
          qpat_assum `~(SUC k < LENGTH levels)`
            (fn th => PURE_REWRITE_TAC [th, COND_CLAUSES]) >> simp[]) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Triviality cover_terminal_visit:
  (!i t. terminal i t ==>
    i.inst_opcode <> INVOKE /\
    (!fuel C u. step_inst fuel C i t <> OK u) /\
    (!fuel C ir u. step_inst fuel C i t <> IntRet ir u)) ==>
  (!P D fuel C f inst s. !h p d id fn i t.
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) /\
    terminal i t ==>
    LENGTH (trace_step P D fuel C f inst s) = SUC h /\
    (!u. step_inst fuel C inst s <> OK u) /\
    (!ir u. step_inst fuel C inst s <> IntRet ir u)) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) /\
    terminal i t ==>
    LENGTH (trace_block P D fuel C f bb s) = SUC h /\
    (!u. exec_block fuel C bb s <> OK u) /\
    (!ir u. exec_block fuel C bb s <> IntRet ir u)) /\
  (!P D fuel C f s. !h p d id fn i t.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) /\
    terminal i t ==>
    LENGTH (trace_blocks P D fuel C f s) = SUC h /\
    (!u. run_blocks fuel C f s <> OK u) /\
    (!ir u. run_blocks fuel C f s <> IntRet ir u))
Proof
  strip_tac >> ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume cover_terminal_visit[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  first_x_assum drule_all >> strip_tac >>
  CONV_TAC (DEPTH_CONV (REWR_CONV venomExecSemanticsTheory.step_inst_def) THENC
    REDEPTH_CONV BETA_CONV) >>
  Cases_on `run_blocks fuel C callee cs` >> gvs[]
QED

Resume cover_terminal_visit[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >>
      qpat_assum `!i t. terminal i t ==> _` drule >> strip_tac >>
      `trace_step P D fuel C f head s = []` by simp[Once (cj 1 trace_defs)] >>
      Cases_on `step_inst fuel C head s` >> gvs[] >>
      once_rewrite_tac [venomExecSemanticsTheory.exec_block_def] >> simp[]) >>
  gvs[] >>
  Cases_on `n < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      Cases_on `step_inst fuel C head s` >> gvs[] >>
      once_rewrite_tac [venomExecSemanticsTheory.exec_block_def] >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  gvs[EL_APPEND] >>
  qpat_assum `!h p d id fn i t. h < LENGTH (trace_block P D fuel C f bb _) /\ _ ==> _`
    (qspecl_then [`n - LENGTH (trace_step P D fuel C f head s)`,
       `p`, `d`, `id`, `fn`, `i`, `t`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  strip_tac >>
  once_rewrite_tac [venomExecSemanticsTheory.exec_block_def] >> simp[] >> decide_tac
QED

Resume cover_terminal_visit[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      Cases_on `exec_block n C bb start` >> gvs[] >>
      once_rewrite_tac [venomExecSemanticsTheory.run_blocks_def] >> simp[Abbr `start`]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND] >>
  qpat_assum `!h p d id fn i t. h < LENGTH (trace_blocks P (SUC D) n C f post) /\ _ ==> _`
    (qspecl_then [`h - LENGTH (trace_block P (SUC D) n C f bb start)`,
       `p`, `d`, `id`, `fn`, `i`, `t`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  strip_tac >>
  once_rewrite_tac [venomExecSemanticsTheory.run_blocks_def] >> simp[Abbr `start`] >> decide_tac
QED

Finalise cover_terminal_visit

Triviality cover_codecopy_error:
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst; Label l; sz] /\
  FLOOKUP s.vs_labels l = NONE ==>
  ?err. step_inst fuel C i s = Error err
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def] >>
  Cases_on `eval_operand dst s` >> simp[]
QED

Theorem cover_forward_suffix:
  wf_function fn /\ active_inst fn inst s /\ in_revert_forward fn s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       MEM inst.inst_opcode [RETURNDATACOPY; REVERT] /\
       (LAST bb.bb_instructions).inst_opcode = REVERT /\
       !k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
         (EL k bb.bb_instructions).inst_opcode <> INVOKE
Proof
  strip_tac >>
  drule_all dftGasFromListLookupTheory.wf_active_lookup >> strip_tac >>
  `bb_well_formed bb` by
    (drule venomExecProofsTheory.lookup_block_MEM >> fs[wf_function_def, EVERY_MEM]) >>
  `revert_forward_at bb s.vs_inst_idx` by fs[in_revert_forward_def] >>
  qexists `bb` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (drule_all revert_forward_at_opcode >> simp[]) >>
  qpat_x_assum `revert_forward_at bb _`
    (strip_assume_tac o REWRITE_RULE [revert_forward_at_def]) >>
  gvs[revert_forward_pair_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  `?r. r < LENGTH bb.bb_instructions /\
    (EL r bb.bb_instructions).inst_opcode = REVERT /\
    (!k. s.vs_inst_idx <= k /\ k < r ==>
      (EL k bb.bb_instructions).inst_opcode <> INVOKE)` by
    (qexists `if s.vs_inst_idx < j then j else s.vs_inst_idx` >>
     Cases_on `s.vs_inst_idx < j` >> gvs[] >>
     rpt strip_tac >>
     `k < LENGTH bb.bb_instructions` by decide_tac >>
     Cases_on `k = s.vs_inst_idx` >> gvs[] >>
     `s.vs_inst_idx < k /\ k < j` by decide_tac >>
     res_tac >> fs[]) >>
  `r = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >> first_x_assum irule >> simp[is_terminator_def]) >>
  (conj_tac
   >- (`bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
       simp_tac (srw_ss()) [LAST_EL, ASSUME ``bb.bb_instructions <> []``] >>
       qpat_assum `r = PRE _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
       first_assum ACCEPT_TAC) >>
   qx_gen_tac `k` >> strip_tac >>
   Cases_on `k = r` >- fs[] >>
   `k < r` by decide_tac >> metis_tac[])
QED

Triviality cover_current_var_defined:
  wf_function fn /\ wf_ssa fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ inst.inst_opcode <> PHI /\
  MEM (Var v) inst.inst_operands ==>
  v IN FDOM s.vs_vars
Proof
  simp[supply_prefix_defined_def, supply_entry_defined_def, active_inst_def,
       wf_ssa_def] >>
  disch_then (REPEAT_TCL STRIP_THM_THEN assume_tac) >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `def_available_at fn bb (SOME inst) v` by
    (qpat_x_assum `def_dominates_uses fn` mp_tac >>
     simp_tac bool_ss [def_dominates_uses_def] >>
     disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [def_available_at_def, optionTheory.option_case_def]) >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
      `j = s.vs_inst_idx` by metis_tac[ALL_DISTINCT_EL_IMP, EL_MAP, LENGTH_MAP] >>
      metis_tac[LESS_TRANS]) >>
  `def_bb.bb_label <> s.vs_current_bb` by
    (fs[wf_function_def, fn_labels_def] >>
     metis_tac[dftCorrectnessTheory.all_distinct_map_mem_inj]) >>
  qpat_x_assum `strict_dom_vars_defined _ _` mp_tac >>
  simp[venomWfPropsTheory.strict_dom_vars_defined_def] >> metis_tac[]
QED

Theorem cover_cfg_cursor_shape:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ==>
  MEM fn9 C9.ctx_functions /\ wf_function fn9 /\ wf_ssa fn9 /\
  active_inst fn9 inst9 s9 /\ supply_prefix_defined fn9 s9
Proof
  Cases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  conj_tac
  >- (qpat_assum `MAP (FST o SND) schedules = C9.ctx_functions` (SUBST1_TAC o SYM) >>
      simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  drule cfg_norm_cursors_last >> simp[supply_norm_inv_def] >> metis_tac[]
QED

Triviality cover_invoke_setup:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ wf_ssa fn /\
  supply_prefix_defined fn s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE ==>
  ?nm ops callee args ent.
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME ent
Proof
  strip_tac >>
  `o1_fn_shape C fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by
    (qpat_x_assum `active_inst fn inst s` mp_tac >>
     simp[active_inst_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     strip_tac >> qexists `bb` >> simp[] >> metis_tac[EL_MEM]) >>
  `?nm ops. inst.inst_operands = Label nm :: ops /\ MEM nm (ctx_fn_names C)` by
    (fs[o1_fn_shape_def, fn_invoke_ok_def] >> metis_tac[]) >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee` by
    (Cases_on `lookup_function nm C.ctx_functions` >> fs[ctx_fn_names_def] >>
     metis_tac[lookup_function_not_mem]) >>
  `wf_function fn /\ fn_shape_ok fn` by fs[o1_fn_shape_def] >>
  `inst_shape_ok inst` by fs[fn_shape_ok_def, EVERY_MEM] >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (qpat_assum `inst_shape_ok inst`
       (mp_tac o cj 4 o REWRITE_RULE [inst_shape_ok_def]) >>
     simp_tac (srw_ss()) [label_positions_ok_def,
       ASSUME ``inst.inst_opcode = INVOKE``, ASSUME ``inst.inst_operands = Label nm :: ops``]) >>
  `IS_SOME (eval_operands ops s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     qx_gen_tac `op` >> strip_tac >> Cases_on `op` >>
     gvs[eval_operand_def, stackPlanTypesTheory.is_label_operand_def,
         lookup_var_def, FLOOKUP_DEF, EVERY_MEM] >>
     `inst.inst_opcode <> PHI` by simp[]
     >- (`MEM (Var s') inst.inst_operands` by
           (qpat_assum `inst.inst_operands = Label nm :: ops` SUBST1_TAC >> simp[]) >>
         irule cover_current_var_defined >>
         qexistsl [`fn`, `inst`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     res_tac >> gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C callee` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `callee.fn_blocks <> []` by fs[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
  simp[decode_invoke_def, setup_callee_def, NULL_EQ]
QED

Theorem cover_cfg_joint_blocks:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] ==>
  s8.vs_inst_idx = s9.vs_inst_idx /\
  ?bt gb. lookup_block s8.vs_current_bb fn8.fn_blocks = SOME bt /\
      lookup_block s9.vs_current_bb fn9.fn_blocks = SOME gb /\
      MAP (\i. i.inst_opcode) bt.bb_instructions =
      MAP (\i. i.inst_opcode) gb.bb_instructions
Proof
  Cases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `cfg_norm_cursors C8 q r`
    (fn th => mp_tac (MATCH_MP (Q.SPECL [`C8`,`q`,`r`] cover_cfg_block_opcodes) th)) >>
  disch_then (qspecl_then [`s`,`fn8`,`meta`,`t`,`fn9`,`inst8`,`s8`,
     `pending`,`inst9`,`s9`] mp_tac) >>
  simp[]
QED

Triviality cover_cfg_cursor_inst:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
  !j v. LAST cells = ((j,v),NONE) /\
     ~MEM j.inst_opcode [ASSIGN; JMP; JNZ; PHI] ==>
     FST (FST (HD cells)) = j
Proof
  ho_match_mp_tac cfg_norm_cursors_strongind >> simp[LAST_CONS] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (qpat_assum `!j v. _ ==> _` (qspecl_then [`j`,`v'`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      `(EL a.vs_inst_idx bb.bb_instructions).inst_opcode = j.inst_opcode` by
        (mp_tac (Q.INST [`i` |-> `a.vs_inst_idx`, `bb` |-> `bb`,
          `pred` |-> `pred`, `target` |-> `target`, `split` |-> `split`,
          `repls` |-> `repls`] supply_block_image_index) >> simp[]) >>
      `label_positions_ok (EL a.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `EVERY label_positions_ok (fn_insts fn)` mp_tac >>
         simp_tac (srw_ss()) [EVERY_MEM] >>
         disch_then irule >>
         simp[fn_insts_def] >> metis_tac[MEM_fn_insts_blocks, EL_MEM]) >>
      `~MEM (EL a.vs_inst_idx bb.bb_instructions).inst_opcode [PHI; JMP; JNZ]` by fs[] >>
      mp_tac (Q.INST [`i` |-> `a.vs_inst_idx`, `bb` |-> `bb`,
        `pred` |-> `pred`, `target` |-> `target`, `split` |-> `split`,
        `repls` |-> `repls`] o1ContractCfgNormTheory.supply_block_image_index_unchanged) >>
      simp[]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by gvs[supply_norm_inv_def] >>
  `MEM (EL v.vs_inst_idx split.bb_instructions).inst_opcode [ASSIGN; JMP; JNZ]` by
    (drule_all supply_split_index_shape >> simp[] >> metis_tac[]) >>
  drule cfg_norm_cursors_admin_opcode >>
  qpat_assum `LAST _ = ((j,v'),NONE)`
    (fn th => PURE_REWRITE_TAC [HD, pairTheory.FST, th]) >>
  qpat_assum `MEM _ [ASSIGN; JMP; JNZ]`
    (fn th => PURE_REWRITE_TAC [th]) >>
  simp[]
QED

Theorem cover_cfg_joint_inst:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ; PHI] ==>
  inst8 = inst9
Proof
  Cases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  qpat_assum `cfg_norm_cursors C8 q r`
    (fn th => mp_tac (MATCH_MP (Q.SPECL [`C8`,`q`,`r`] cover_cfg_cursor_inst) th)) >>
  disch_then (qspecl_then [`inst9`,`s9`] mp_tac) >>
  simp[]
QED

Triviality cover_memory_observation:
  (~source_memory_reads_disjoint cpl inst s \/
   ~context_source_memory_writes_disjoint cpl inst s) ==>
  inv_memory_observation inst.inst_opcode
Proof
  Cases_on `inst.inst_opcode` >>
  simp[dftGasInvCrossingProbeTheory.inv_memory_observation_def,
    source_memory_reads_disjoint_def, context_source_memory_writes_disjoint_def,
    source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def]
QED

Triviality cover_trace_gas_length:
  !visits. LENGTH (trace_gas visits) =
    LENGTH (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) visits)
Proof
  Induct >> simp[trace_gas_def] >>
  gen_tac >> PairCases_on `h` >> fs[trace_gas_def, visit_gas_def] >>
  Cases_on `h4.inst_opcode = GAS` >> simp[]
QED

Triviality cover_terminal_rooted_sites:
  trace_blocks [] 0 fuel C sf entry = before ++ [((p,d,id),sf',inst,u)] ++ after /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  (!f ctx v. step_inst f ctx inst u <> OK v) /\
  (!f ctx ir v. step_inst f ctx inst u <> IntRet ir v) /\
  LENGTH (trace_gas before) = LENGTH Ecut /\
  Ecut <<= gas_events_blocks fuel C sf entry /\ Ecut <<= sites ==>
  gas_events_blocks fuel C sf entry <<= sites
Proof
  strip_tac >>
  `LENGTH (trace_blocks [] 0 fuel C sf entry) = SUC (LENGTH before)` by
    ((fn goal =>
        let
          val terminal = BETA_RULE (Q.INST
            [`terminal` |-> `\i t. i = inst /\ t = u`] cover_terminal_visit)
        in
          SUBGOAL_THEN (lhand (concl terminal))
            (fn guard => mp_tac (Q.SPECL [`[]`,`0`,`fuel`,`C`,`sf`,`entry`,
                `LENGTH (before:list_visit list)`,`p`,`d`,`id`,`sf'`,`inst`,`u`]
              (cj 3 (MP terminal guard)))) goal
        end)
     >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     rw[EL_APPEND] >> decide_tac) >>
  `after = []` by
    (qpat_assum `LENGTH (trace_blocks [] 0 fuel C sf entry) = _` mp_tac >>
     qpat_assum `trace_blocks [] 0 fuel C sf entry = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [] >> Cases_on `after` >> simp_tac (srw_ss()) [] >> decide_tac) >>
  `LENGTH (gas_events_blocks fuel C sf entry) = LENGTH (trace_gas before)` by
    (ONCE_REWRITE_TAC [GSYM (Q.SPECL [`[]`,`0`,`fuel`,`C`,`sf`,`entry`]
       (cj 3 focus_visit_site_projection))] >>
     qpat_assum `trace_blocks [] 0 fuel C sf entry = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [cover_trace_gas_length, FILTER_APPEND_DISTRIB,
       ASSUME ``after = ([]:list_visit list)``, ASSUME ``inst.inst_opcode <> GAS``]) >>
  qpat_x_assum `Ecut <<= gas_events_blocks _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  gvs[] >>
  `LENGTH (l:(string # num) list) = 0` by decide_tac >>
  fs[LENGTH_NIL]
QED

Theorem cover_remaining_no_invoke:
  PERM row_order (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) row_order ys /\
  (!k. row_count <= k /\ k < LENGTH ys ==> (EL k ys).inst_opcode <> INVOKE) ==>
  !r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE row_count row_order)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `MEM r row_order` by metis_tac[sortingTheory.PERM_MEM_EQ, MEM_COUNT_LIST] >>
  qpat_x_assum `MEM r row_order`
    (qx_choose_then `k` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `LENGTH ys = LENGTH row_order /\ from_block [EL r xs] (EL k ys)` by
    (qpat_assum `LIST_REL _ row_order ys` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> conj_tac >- simp[] >>
     first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `(EL k ys).inst_opcode = INVOKE` by
    (gvs[dftStructuralTheory.from_block_def, dftDefsTheory.is_flippable_def,
         venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def]) >>
  `k < row_count` by (CCONTR_TAC >> fs[NOT_LESS] >> res_tac >> fs[]) >>
  ONCE_REWRITE_TAC [MEM_EL] >>
  qexists `k` >> simp[EL_TAKE, LENGTH_TAKE_EQ, MIN_DEF]
QED
Triviality cover_phi_before_body:
  !ps xs. EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
    phi_prefix_length (ps ++ xs) <= LENGTH ps
Proof
  Induct >> simp[phi_prefix_length_def]
  >- (Cases_on `xs` >> simp[phi_prefix_length_def] >>
      rpt strip_tac >> `h.inst_opcode <> PHI` by metis_tac[is_pseudo_def] >> simp[]) >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def]
QED

Theorem cover_last_row_source:
  bb_well_formed bb /\ bb.bb_instructions = ps ++ xs /\
  xs <> [] /\ (LAST bb.bb_instructions).inst_opcode = REVERT /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
  0 < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (PRE (LENGTH xs)) xs) /\
  (EL (LENGTH (DROP (phi_prefix_length bb.bb_instructions) ps ++
                TAKE (PRE (LENGTH xs)) xs))
       (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_opcode = REVERT
Proof
  strip_tac >>
  `0 < LENGTH xs` by (Cases_on `xs` >> gvs[]) >>
  `!j. j < LENGTH xs /\ is_terminator (EL j xs).inst_opcode ==> j = PRE (LENGTH xs)` by
    (qpat_assum `bb_well_formed bb`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [bb_well_formed_def]) >>
     rpt strip_tac >>
     qpat_assum `bb.bb_instructions = ps ++ xs`
       (fn eq => qpat_assum `!i. i < LENGTH bb.bb_instructions /\ _ ==> _`
         (mp_tac o PURE_REWRITE_RULE [eq] o Q.SPEC `LENGTH (ps:instruction list) + j`)) >>
     `(EL (LENGTH ps + j) (ps ++ xs):instruction) = EL j xs` by
       (simp_tac (srw_ss()) [EL_APPEND2]) >>
     simp_tac (srw_ss()) [ASSUME ``j < LENGTH (xs:instruction list)``,
       ASSUME ``is_terminator (EL j xs).inst_opcode``,
       ASSUME ``(EL (LENGTH ps + j) (ps ++ xs):instruction) = EL j xs``] >>
     decide_tac) >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    metis_tac[cover_phi_before_body] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (simp[EVERY_EL, LENGTH_TAKE, EL_TAKE] >>
      rpt strip_tac >> res_tac >> decide_tac) >>
  `(EL (PRE (LENGTH xs)) xs).inst_opcode = REVERT` by
    (qpat_assum `bb.bb_instructions = ps ++ xs`
       (fn eq => qpat_assum `(LAST bb.bb_instructions).inst_opcode = REVERT`
          (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp_tac (srw_ss()) [LAST_APPEND_NOT_NIL, LAST_EL,
       ASSUME ``xs <> ([]:instruction list)``]) >>
  qabbrev_tac `ph = phi_prefix_length bb.bb_instructions` >>
  `DROP ph bb.bb_instructions = DROP ph ps ++ xs` by
    (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
     simp_tac (srw_ss()) [DROP_APPEND1, ASSUME ``ph <= LENGTH (ps:instruction list)``]) >>
  qpat_assum `DROP ph bb.bb_instructions = _` SUBST1_TAC >>
  `LENGTH (TAKE (PRE (LENGTH xs)) xs) = PRE (LENGTH xs)` by
    (irule LENGTH_TAKE >> decide_tac) >>
  PURE_REWRITE_TAC [LENGTH_APPEND] >>
  qpat_assum `LENGTH (TAKE _ xs) = _` SUBST1_TAC >>
  qpat_assum `(EL (PRE (LENGTH xs)) xs).inst_opcode = REVERT` (fn th =>
    PURE_REWRITE_TAC [GSYM th]) >>
  AP_TERM_TAC >>
  simp_tac (srw_ss()) [EL_APPEND2]
QED

Triviality cover_order_prefix_unique:
  ALL_DISTINCT order /\ order = ds ++ e::tail /\ order = ds' ++ e::tail' ==>
  ds = ds'
Proof
  strip_tac >>
  `LENGTH ds < LENGTH order /\ EL (LENGTH ds) order = e` by
    (qpat_assum `order = ds ++ e::tail` SUBST1_TAC >> simp[EL_APPEND]) >>
  `LENGTH ds' < LENGTH order /\ EL (LENGTH ds') order = e` by
    (qpat_assum `order = ds' ++ e::tail'` SUBST1_TAC >> simp[EL_APPEND]) >>
  `LENGTH ds = LENGTH ds'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `TAKE (LENGTH ds) order = ds /\ TAKE (LENGTH ds') order = ds'` by
    (conj_tac
     >- (qpat_assum `order = ds ++ e::tail` SUBST1_TAC >>
         MATCH_ACCEPT_TAC TAKE_LENGTH_APPEND) >>
     qpat_assum `order = ds' ++ e::tail'` SUBST1_TAC >>
     MATCH_ACCEPT_TAC TAKE_LENGTH_APPEND) >>
  metis_tac[]
QED

Triviality cover_cut_paths_unique:
  MAP (\(a,ds,e,q,z). a) cuts = paths /\
  MAP (\(a,ds,e,q,z). a) cuts' = paths /\
  (!i a ds e q z. i < LENGTH cuts /\ EL i cuts = (a,ds,e,q,z) ==>
    (?order later. orders a = SOME order /\ ALL_DISTINCT order /\ order = ds ++ e::later) /\
    (if SUC i = LENGTH cuts then e = d0 /\ q = q0 /\ z = z0
     else ?cid. EL (SUC i) paths = (e,cid)::a /\
          call_idx a e cid = SOME q /\ cut_prefix a e q = z)) /\
  (!i a ds e q z. i < LENGTH cuts' /\ EL i cuts' = (a,ds,e,q,z) ==>
    (?order later. orders a = SOME order /\ ALL_DISTINCT order /\ order = ds ++ e::later) /\
    (if SUC i = LENGTH cuts' then e = d0 /\ q = q0 /\ z = z0
     else ?cid. EL (SUC i) paths = (e,cid)::a /\
          call_idx a e cid = SOME q /\ cut_prefix a e q = z)) ==>
  cuts = cuts'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH cuts = LENGTH cuts'` by metis_tac[LENGTH_MAP] >>
  irule LIST_EQ >> simp[] >> qx_gen_tac `i` >> strip_tac >>
  `?a ds e q z. EL i cuts = (a,ds,e,q,z)` by metis_tac[pairTheory.PAIR] >>
  `?a' ds' e' q' z'. EL i cuts' = (a',ds',e',q',z')` by metis_tac[pairTheory.PAIR] >>
  `a = a'` by
    (`EL i paths = a /\ EL i paths = a'` suffices_by (strip_tac >> metis_tac[]) >>
     conj_tac
     >- (qpat_assum `MAP _ cuts = paths` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
     qpat_assum `MAP _ cuts' = paths` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
  qpat_x_assum `!i a ds e q z. i < LENGTH cuts /\ EL i cuts = _ ==> _`
    (qspecl_then [`i`, `a`, `ds`, `e`, `q`, `z`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `ord` (qx_choose_then `later` (map_every assume_tac o CONJUNCTS)))
    assume_tac) >>
  qpat_x_assum `!i a ds e q z. i < LENGTH cuts' /\ EL i cuts' = _ ==> _`
    (qspecl_then [`i`, `a'`, `ds'`, `e'`, `q'`, `z'`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `ord'` (qx_choose_then `later'` (map_every assume_tac o CONJUNCTS)))
    assume_tac) >>
  `e = e' /\ q = q' /\ z = z'` by
    (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
     qpat_x_assum `if SUC i = LENGTH cuts' then _ else _` mp_tac >>
     qpat_assum `LENGTH cuts = LENGTH cuts'` (fn th => PURE_REWRITE_TAC [th]) >>
     Cases_on `SUC i = LENGTH cuts'` >> simp[] >> rpt strip_tac >>
     metis_tac[CONS_11, pairTheory.PAIR_EQ, optionTheory.SOME_11]) >>
  `ds = ds'` by
    (qpat_assum `ALL_DISTINCT ord` mp_tac >>
     qpat_assum `ord = _` mp_tac >>
     qpat_assum `ord' = _` mp_tac >>
     qpat_assum `orders a = SOME ord` mp_tac >>
     qpat_assum `orders a' = SOME ord'` mp_tac >>
     qpat_assum `e = e'` mp_tac >> qpat_assum `a = a'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[cover_order_prefix_unique, optionTheory.SOME_11]) >>
  simp[]
QED


Triviality cover_packet_nonpseudo_body:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs hist) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,row_count,front,closed,brest) /\
  ~is_pseudo inst.inst_opcode ==> IS_SOME body_entry
Proof
  strip_tac >>
  drule_all_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))
    dftFinitePacketTheory.dft_packet_return_data >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,OK s,F,NONE)` mp_tac >>
  qpat_assum `FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,row_count,front,closed,brest)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]
QED


Theorem cover_error_active_frame_reloc:
  (active_frame_plan_reloc asm_lo rpolicy unit cpl prog fn s ast ra rest mem0 \/
   ?entry pc_ret. entry_frame_plan_reloc asm_lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0) /\
  code_labels_agree prog asm_lo /\
  active_inst fn inst s /\ step_inst 0 unit.cu_context inst s = Error err ==>
  ?ast'. active_frame_plan_reloc asm_lo rpolicy unit cpl prog fn s ast' ra rest mem0
Proof
  strip_tac >- metis_tac[] >>
  `s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (qpat_assum `entry_frame_plan_reloc _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [fnFramePrefixEntryTheory.entry_frame_plan_reloc_def]) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  Cases_on `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
  >- (drule_all fnFramePrefixEntryTheory.entry_frame_plan_ready_reloc >> metis_tac[]) >>
  `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by decide_tac >>
  drule_all_then strip_assume_tac fnFramePrefixEntryTheory.entry_frame_active_param_reloc >>
  drule_all fnFramePrefixEntryTheory.entry_frame_plan_next_reloc >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  gvs[]
QED

Theorem cover_error_active_frame:
  (active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 \/
   ?entry pc_ret. entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0) /\
  active_inst fn inst s /\ step_inst 0 unit.cu_context inst s = Error err ==>
  ?ast'. active_frame_plan rpolicy unit cpl prog fn s ast' ra rest mem0
Proof
  rewrite_tac[GSYM fnFramePrefixTheory.active_frame_plan_reloc_specialize,
    GSYM fnFramePrefixEntryTheory.entry_frame_plan_reloc_specialize] >>
  metis_tac[cover_error_active_frame_reloc, code_labels_agree_refl]
QED

Theorem cover_error_active_shape_reloc:
  active_frame_plan_reloc asm_lo rpolicy unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ code_layout_valid vs0 /\
  (!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w (FLOOKUP asm_lo l)) ==>
  inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode /\
  (inst.inst_opcode = RET ==> inst.inst_operands <> []) /\
  FLOOKUP s.vs_labels "code_end" <> NONE
Proof
  strip_tac >>
  qpat_assum `active_frame_plan_reloc asm_lo rpolicy unit cpl prog fn s ast ra rest mem0`
    (REPEAT_TCL CHOOSE_THEN assume_tac o PURE_REWRITE_RULE
      [fnFramePrefixTheory.active_frame_plan_reloc_def]) >>
  drule_then strip_assume_tac fnBlockBodyStepsTheory.body_plan_inv_facts_reloc >>
  `wf_function fn` by
    (qpat_assum `codegen_ready_fn fn` mp_tac >> simp_tac (srw_ss()) [stackPlanGenTheory.codegen_ready_fn_def]) >>
  drule_all_then (qx_choose_then `ab` strip_assume_tac) dftGasFromListLookupTheory.wf_active_lookup >>
  qhdtm_assum `body_plan_inv_reloc`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [fnBlockBodyStepsTheory.body_plan_inv_reloc_def]) >>
  `ab = bb` by
    (qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME ab` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.SOME_11]) >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    (qpat_assum `get_instruction ab s.vs_inst_idx = SOME inst` mp_tac >>
     qpat_assum `ab = bb` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `s.vs_inst_idx = k` (fn th => PURE_REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all_then strip_assume_tac fnBlockBodyStepsTheory.body_plan_inv_inst_reloc >>
  `MEM inst (non_param_insts bb)` by
    (qpat_assum `non_param_insts bb = DROP _ _` SUBST1_TAC >>
     ONCE_REWRITE_TAC [MEM_EL] >>
     qexists `k - LENGTH (get_params bb.bb_instructions)` >>
     simp_tac (srw_ss()) [EL_DROP, LENGTH_DROP] >>
     qpat_assum `k < LENGTH bb.bb_instructions` mp_tac >>
     qpat_assum `LENGTH (get_params bb.bb_instructions) <= k` mp_tac >>
     qpat_assum `EL k bb.bb_instructions = inst` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     `k - LENGTH (get_params bb.bb_instructions) +
          LENGTH (get_params bb.bb_instructions) = k` by decide_tac >>
     conj_tac >- decide_tac >>
     `k - LENGTH (get_params bb.bb_instructions) + LENGTH (get_params bb.bb_instructions) <
        LENGTH bb.bb_instructions` by decide_tac >>
     simp[EL_DROP]) >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (MATCH_MP_TAC (Q.SPECL [`fn`,`bb`,`inst`]
       fnBlockBodyHelpersTheory.reachable_fn_mem_inst) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `MEM inst (non_param_insts bb)` mp_tac >>
      simp_tac (srw_ss()) [stackPlanGenTheory.non_param_insts_def, MEM_FILTER]) >>
  conj_tac
  >- (strip_tac >> qpat_assum `retpc_shape_ok fn`
       (fn th => qspec_then `inst` mp_tac (cj 1 (REWRITE_RULE [retpc_shape_ok_def] th))) >>
      qpat_assum `MEM inst (fn_insts (reachable_fn fn))`
        (fn th => simp_tac (srw_ss()) [th, ASSUME ``inst.inst_opcode = RET``]) >>
      disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `inst.inst_operands = _ ++ [Var _]`
        (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_assum `code_layout_valid vs0`
    (mp_tac o cj 2 o PURE_REWRITE_RULE [code_layout_valid_def]) >>
  qpat_assum `!l. FLOOKUP vs0.vs_labels l = _`
    (qspec_then `"code_end"` mp_tac) >>
  qpat_assum `!l. FLOOKUP s.vs_labels l = _`
    (qspec_then `"code_end"` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `FLOOKUP asm_lo "code_end"` >> simp[]

QED

Theorem cover_error_active_shape:
  active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ code_layout_valid vs0 /\
  codegen_asm_entry_rel cpl prog vs0 entry_asm ==>
  inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode /\
  (inst.inst_opcode = RET ==> inst.inst_operands <> []) /\
  FLOOKUP s.vs_labels "code_end" <> NONE
Proof
  rewrite_tac[GSYM fnFramePrefixTheory.active_frame_plan_reloc_specialize] >>
  strip_tac >>
  qpat_assum `codegen_asm_entry_rel cpl prog vs0 entry_asm`
    (assume_tac o cj 7 o PURE_REWRITE_RULE [codegenEntrySimTheory.codegen_asm_entry_rel_def]) >>
  drule_all (Q.INST [`asm_lo` |-> `SND (compute_label_offsets prog)`]
    cover_error_active_shape_reloc) >> simp[]
QED


Triviality cover_eval_operands_nil:
  eval_operands ops s = SOME [] <=> ops = []
Proof
  Cases_on `ops` >> simp[eval_operands_def] >>
  rpt CASE_TAC >> gvs[]
QED

fun cover_expand_opcode eq =
  let
    val lemma = stepInstBaseLib.opcode_clause (rhs (concl eq))
    val wellformed =
      REWRITE_CONV [inst_wf_def, eq, opcode_case_def] ``inst_wf inst``
  in
    PURE_ONCE_REWRITE_TAC [MATCH_MP lemma eq] >>
    qpat_x_assum `inst_wf inst` (strip_assume_tac o REWRITE_RULE [wellformed])
  end;

val cover_noerror_finish =
  gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM,
    exec_pure1_def, exec_pure2_def, exec_pure3_def, exec_read0_def, exec_read1_def,
    exec_write2_def, exec_gas_def, exec_alloca_def, exec_ext_call_def,
    exec_delegatecall_def, exec_create_def, LET_THM,
    eval_operands_def, stackPlanTypesTheory.is_label_operand_def] >>
  rpt (CASE_TAC >> gvs[cover_eval_operands_nil, eval_operands_def, eval_operand_def]);

Triviality cover_noninvoke_noerror:
  inst_wf inst /\ label_positions_ok inst /\
  ~MEM inst.inst_opcode [INVOKE; PHI; DRET; DJMP] /\
  (inst.inst_opcode = RET ==> inst.inst_operands <> []) /\
  (!idx. MEM inst.inst_opcode [PARAM; FMP_PARAM] /\ inst.inst_operands = [Lit idx] ==>
     w2n idx < LENGTH s.vs_params) /\
  (!op. MEM op inst.inst_operands /\
     (~MEM inst.inst_opcode [JMP; JNZ] \/ ~is_label_operand op) ==>
     IS_SOME (eval_operand op s)) ==>
  step_inst fuel C inst s <> Error err
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [JMP; JNZ] ==> IS_SOME (eval_operands inst.inst_operands s)` by
    (strip_tac >> simp[eval_operands_IS_SOME_EVERY, EVERY_MEM]) >>
  `!c l1 l2. inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label l1; Label l2] ==>
      IS_SOME (eval_operand c s)` by
    (rpt strip_tac >>
     qpat_assum `label_positions_ok inst` mp_tac >>
     qpat_assum `inst.inst_opcode = JNZ` (fn op_eq =>
       qpat_assum `inst.inst_operands = [c; Label l1; Label l2]` (fn args =>
         simp_tac (srw_ss()) [label_positions_ok_def,op_eq,args])) >>
     strip_tac >>
     qpat_assum `!op. MEM op inst.inst_operands /\ _ ==> _`
       (qspec_then `c` mp_tac) >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  simp_tac (srw_ss()) [step_inst_non_invoke, ASSUME ``inst.inst_opcode <> INVOKE``] >>
  (* Keep the evaluator cases separate for the kernel's tactic budget. *)
  Cases_on `inst.inst_opcode` >>
  qpat_assum `inst.inst_opcode = _` cover_expand_opcode
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- (`!op. MEM op rest ==> IS_SOME (eval_operand op s)` by simp[] >>
      `0 < LENGTH (REVERSE (rest:operand list)) /\ 1 < LENGTH (REVERSE rest)` by
        (qpat_assum `LENGTH rest = w2n tc + 2` mp_tac >>
         simp_tac (srw_ss()) [] >> decide_tac) >>
      `IS_SOME (eval_operand (EL 0 (REVERSE rest)) s) /\
       IS_SOME (eval_operand (EL 1 (REVERSE rest)) s)` by
        (qpat_assum `!op. MEM op rest ==> _` mp_tac >>
         qpat_assum `0 < LENGTH (REVERSE (rest:operand list))` mp_tac >>
         qpat_assum `1 < LENGTH (REVERSE (rest:operand list))` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[EL_MEM, MEM_REVERSE]) >>
      `IS_SOME (eval_operands (DROP 2 (REVERSE rest)) s)` by
        (qpat_assum `!op. MEM op rest ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[eval_operands_IS_SOME_EVERY, EVERY_MEM, MEM_DROP] >>
         rpt strip_tac >>
         `MEM (EL (m + 2) (REVERSE rest)) (REVERSE (rest:operand list))` by
           (MATCH_MP_TAC EL_MEM >> simp[]) >>
         qpat_assum `!op. MEM op rest ==> _`
           (qspec_then `EL (m + 2) (REVERSE (rest:operand list))` mp_tac) >>
         fs[]) >>
      gvs[LET_THM] >>
      rpt (CASE_TAC >> gvs[]))
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
  >- cover_noerror_finish
QED


Triviality cover_value_label_shape:
  label_positions_ok inst /\ MEM (Label l) inst.inst_operands /\
  ~MEM inst.inst_opcode [PHI; INVOKE; JMP; JNZ] ==>
  (inst.inst_opcode = ADD /\ l = "code_end") \/
  (inst.inst_opcode = CODECOPY /\ l = "runtime_begin" /\
   ?dst sz. inst.inst_operands = [dst; Label l; sz])
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ADD`
  >- (qpat_x_assum `MEM (Label l) inst.inst_operands` mp_tac >>
      qpat_x_assum `label_positions_ok inst` mp_tac >>
      simp[label_positions_ok_def] >>
      rpt CASE_TAC >> rw[] >>
      gvs[EVERY_MEM, stackPlanTypesTheory.is_label_operand_def] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `inst.inst_opcode = CODECOPY`
  >- (qpat_x_assum `MEM (Label l) inst.inst_operands` mp_tac >>
      qpat_x_assum `label_positions_ok inst` mp_tac >>
      simp[label_positions_ok_def] >>
      rpt CASE_TAC >> rw[] >>
      gvs[EVERY_MEM, stackPlanTypesTheory.is_label_operand_def] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `~MEM inst.inst_opcode [JMP; JNZ; PHI; INVOKE; ADD; CODECOPY]` by fs[] >>
  drule_all_then assume_tac fnBlockBodyHelpersTheory.label_positions_ok_other >>
  fs[EVERY_MEM] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem cover_noninvoke_runtime_error:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ wf_ssa fn /\
  supply_prefix_defined fn s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  ~is_param_opcode inst.inst_opcode /\
  (inst.inst_opcode = RET ==> inst.inst_operands <> []) /\
  FLOOKUP s.vs_labels "code_end" <> NONE /\
  step_inst 0 C inst s = Error err ==>
  inst.inst_opcode = CODECOPY /\
  (?dst sz. inst.inst_operands = [dst; Label "runtime_begin"; sz]) /\
  FLOOKUP s.vs_labels "runtime_begin" = NONE
Proof
  strip_tac >>
  `o1_fn_shape C fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def] >> metis_tac[MEM_fn_insts_blocks, EL_MEM]) >>
  `inst_wf inst` by
    (qpat_assum `o1_fn_shape C fn`
       (mp_tac o cj 2 o PURE_REWRITE_RULE [o1_fn_shape_def]) >>
     qpat_assum `active_inst fn inst s` (mp_tac o PURE_REWRITE_RULE [active_inst_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[EL_MEM]) >>
  `wf_function fn /\ inst_shape_ok inst /\ inst.inst_opcode <> DRET` by
    fs[o1_fn_shape_def, fn_shape_ok_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >>
  `~MEM inst.inst_opcode [INVOKE; PHI; DRET; DJMP]` by fs[inst_shape_ok_def] >>
  `label_positions_ok inst` by fs[inst_shape_ok_def] >>
  CCONTR_TAC >>
  `!op. MEM op inst.inst_operands /\
     (~MEM inst.inst_opcode [JMP; JNZ] \/ ~is_label_operand op) ==>
     IS_SOME (eval_operand op s)` by
    (qx_gen_tac `op` >>
     disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `op`
     >- simp[eval_operand_def]
     >- (drule_all_then assume_tac cover_current_var_defined >>
        fs[eval_operand_def, lookup_var_def, FLOOKUP_DEF]) >>
     fs[stackPlanTypesTheory.is_label_operand_def] >>
     `~MEM inst.inst_opcode [PHI; INVOKE; JMP; JNZ]` by fs[] >>
     drule_all cover_value_label_shape >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
     >- (Cases_on `FLOOKUP s.vs_labels "code_end"` >> gvs[eval_operand_def]) >>
     Cases_on `FLOOKUP s.vs_labels "runtime_begin"` >> gvs[eval_operand_def]) >>
  `step_inst 0 C inst s <> Error err` by
    (MATCH_MP_TAC cover_noninvoke_noerror >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       rpt strip_tac >>
       qpat_assum `MEM inst.inst_opcode [PARAM; FMP_PARAM]`
         (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
       qpat_assum `~is_param_opcode inst.inst_opcode` mp_tac >>
       qpat_assum `inst.inst_opcode = _`
         (fn th => simp_tac (srw_ss()) [th,is_param_opcode_def])]) >>
  qpat_assum `step_inst 0 C inst s <> Error err` mp_tac >>
  qpat_assum `step_inst 0 C inst s = Error err`
    (fn th => simp_tac (srw_ss()) [th])
QED

(* Scratch statement for elaboration and independent review.
   Use the concrete stopped frontier on the same walk and run.
   The bounded source family is the one in H1. Coverage is over every
   compatible filling and does not take a late per-filling antecedent. *)
val coverage_gas_callback =
  List.nth (strip_conj (lhand (concl focus_joint_progress_for)),1);

val coverage_frame_callback = ``
  !stk PG G tn fn inst s oms om hs h ast (ss:sym_state).
    (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog
      (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                  vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast) /\
    (fin = asm_opt_finalizer ==> frame
      (JointConfig stk PG G tn fn inst s oms om hs h) ast ss) ==>
    ?ra rest mem0.
      active_frame_plan_reloc asm_lo rpolicy out.po_unit cpl prog fn s ast ra rest mem0 \/
      ?entry pc_ret. entry_frame_plan_reloc asm_lo rpolicy out.po_unit cpl prog
        fn entry s ast ra pc_ret rest mem0``;

Theorem focus_packet_coverage_for:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    n2w cpl.cp_initial_fmp = vs0.vs_initial_fmp /\
    ^coverage_gas_callback /\
    ^coverage_frame_callback /\
    code_labels_agree prog asm_lo /\
    (!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w (FLOOKUP asm_lo l)) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    (0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps asm_lo (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    symbolic asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    frame
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (?align old_cursors old_asm old_sym costs.
    LENGTH costs = LENGTH evs9 /\ LENGTH old_asm = LENGTH evs9 /\
    (fin = asm_opt_finalizer ==> LENGTH old_sym = LENGTH evs9) /\
    align 0 = 0 /\ align (LENGTH evs9) = j /\
    asm_fuel = SUM costs /\ ast = EL (LENGTH evs9) ((entry_asm_state vs0 es0)::old_asm) /\
    (fin = asm_opt_finalizer ==> ss = EL (LENGTH evs9) (sym_init (entry_asm_state vs0 es0)::old_sym)) /\
    LIST_REL (\cost edge. 0 < cost \/
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (SND edge) <
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (FST edge))
      costs (ZIP (TAKE (LENGTH evs9) (q90::qs9),qs9)) /\
    (!k. k < LENGTH evs9 ==>
      align k <= j /\
      (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
      align (SUC k) <= j /\
      cfg_norm_joint_cursors (stage 8) (stage 9) (old_cursors k) (EL (align k) (q80::qs8)) (EL k
        (q90::qs9)) /\
      asm_steps asm_lo (build_offset_to_pc prog)
        prog (EL k costs) (EL k ((entry_asm_state vs0 es0)::old_asm)) =
          AsmOK (EL (SUC k) ((entry_asm_state vs0 es0)::old_asm)) /\
      (fin = asm_opt_finalizer ==>
        symbolic (EL k costs) (EL k (sym_init (entry_asm_state vs0
          es0)::old_sym)) =
          SymOK (EL (SUC k) (sym_init (entry_asm_state vs0 es0)::old_sym))) /\
      (case ((EL (align k) (q80::qs8)),(EL k (q90::qs9))) of
        (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
         JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
          (~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
    source_memory_reads_disjoint cpl inst9 s9 /\
    context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
    !dst x sz src off.
      inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
      code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
      FLOOKUP asm_lo "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2)) /\ (active_inst fn9 inst9 s9 /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm' ops callee args ent.
      decode_invoke inst9 = SOME (nm',ops) /\
      lookup_function nm' (stage 9).ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
          (align (SUC k) = SUC (align k) /\ i8.inst_opcode = GAS ==>
            u8.vs_gas_readings <> [])))) /\
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          (p <> p \/ d <> d \/ s8 <> s8 \/
            (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
             (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
          (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
             inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  ((?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\
      r8 = (case r of OK u => Halt u | other => other) /\
      ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/
       (?ex u. r = Abort ex u)) /\
      run_blocks N (stage 8) root_tf root_entry = r8 /\
      (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
          raw_slots gs ==>
        ?extra. sites = gas_events_blocks F (stage 7) root_sf
          (root_entry with vs_gas_readings := gs ++ tail) ++ extra)) \/
    in_revert_forward fn9 s9 \/
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     (~source_memory_reads_disjoint cpl inst9 s9 \/
      ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
    (fin = asm_opt_finalizer /\
      ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
        inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
        eval_operand (Var x) s9 = SOME src /\
        FLOOKUP asm_lo "code_end" = SOME off /\
        ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
    (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
    (inst9.inst_opcode = INVOKE /\
     ~(?callee_name ops callee args ent.
        decode_invoke inst9 = SOME (callee_name,ops) /\
        lookup_function callee_name (stage 9).ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
    (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err))) ==>
    (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?rest. MAP project sites = markf (raw ++ [0w]) ++ rest)
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >>
  (fn (asl, goal) =>
    let
      val provider = CONV_RULE (DEPTH_CONV BETA_CONV)
        (PURE_REWRITE_RULE [LET_THM]
          gasFocusSourceProviderTheory.focus_source_cut_provider_for)
      fun premise tm =
        if is_conj tm then
          let val (l, r) = dest_conj tm in CONJ (premise l) (premise r) end
        else if List.exists (aconv tm) asl then ASSUME tm
        else raise mk_HOL_ERR "focus_packet_coverage" "provider premise"
          (term_to_string tm)
      val source = List.last (CONJUNCTS (MP provider (premise (lhand (concl provider)))))
    in
      (qspec_then `raw` mp_tac source >> impl_tac >- first_assum ACCEPT_TAC >>
       rpt (disch_then (REPEAT_TCL CHOOSE_THEN
         (map_every assume_tac o CONJUNCTS)))) (asl, goal)
    end) >>
  `LENGTH (raw:bytes32 list) = LENGTH sites` by
    (qpat_assum `LIST_REL _ raw_slots raw` (assume_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_events_blocks f7 (stage 7) root_sf R` >>
  qmatch_asmsub_abbrev_tac `gas_events_blocks f unit.cu_context entryfn A` >>
  qabbrev_tac `n = MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))` >>
  `n = MIN (LENGTH (markf (raw ++ [0w]))) (SUC (LENGTH sites))` by
    simp[Abbr `n`, ADD1] >>
  irule cover_marked_prefix >>
  qexistsl [`gas_events_blocks f7 (stage 7) root_sf R`, `extra`,
            `n`, `gas_events_blocks f unit.cu_context entryfn A`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\ _) \/ _`
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN
      (map_every assume_tac o CONJUNCTS)) assume_tac)
  >- (irule IS_PREFIX_TRANS >>
      qexists `gas_events_blocks f7 (stage 7) root_sf R` >>
      conj_tac
      >- (irule cover_events_at_larger_fuel >> qexists `N` >>
          rpt strip_tac >> simp[Abbr `R`, IS_PREFIX_APPEND] >>
          qpat_assum `!F gs tail. N <= F /\ _ ==> ?extra. sites = _`
            (qspecl_then [`F`, `raw`, `[0w]`] mp_tac) >> simp[]) >>
      PURE_REWRITE_TAC [IS_PREFIX_EQ_TAKE] >> qexists `n` >> simp[]) >>
  `~(inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = [])` by
    (strip_tac >> drule_then strip_assume_tac cover_cfg_active >>
     `s9.vs_gas_readings = []` by
       (qpat_assum `s8.vs_gas_readings = s9.vs_gas_readings` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!stk PG G tn fn inst s oms om hs h n ast ss. _`
       (drule_all_then (mp_tac o CONJUNCT1)) >> simp[]) >>
  qpat_x_assum `?sf inc entry order res nrest bb bt ps xs ys rho
                   in_state h0 body_entry count front closed brest. _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?q z src_inst cuts levels Mcut Ecut Kcut mr er kr. _`
    (qx_choose_then `q` (qx_choose_then `z` (qx_choose_then `src_inst`
      (REPEAT_TCL CHOOSE_THEN (fn th => assume_tac (cj 2 th)))))) >>
  qpat_assum `dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry
                (j,obs) acts blocks calls ms_tab es_tab ks_tab rooted_eval p d _ raw_slots sites unused`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
                body_entry count front closed brest q z.
                _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`p`,`d`,`sf`,`fn8`,`inc`,`entry`,`order`,`res`,`nrest`,`bb`,`bt`,
      `ps`,`xs`,`ys`,`rho'`,`in_state`,`h0`,`body_entry`,`count'`,`front`,`closed`,
      `brest`,`q`,`z`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      `st = s8` by
        (qpat_assum `JointConfig stk8 _ _ _ _ _ s8 _ _ _ _ = _` mp_tac >> simp[]) >>
      qpat_assum `st = s8` SUBST1_TAC >>
      qpat_assum `(IS_SOME body_entry /\ _) \/ _`
        mp_tac >>
      simp_tac (srw_ss()) [] >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  rename1 `AM [] = Mcut ++ mr` >>
  rename1 `AE [] = Ecut ++ er` >>
  `raw_slots = Mcut ++ mr /\ sites = Ecut ++ er` by
    (conj_tac
     >- (qpat_assum `raw_slots = AM []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `sites = AE []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut
     (TAKE (LENGTH Mcut) raw)` by
    (qpat_assum `LIST_REL _ raw_slots raw` mp_tac >>
     qpat_assum `raw_slots = Mcut ++ mr` SUBST1_TAC >>
     MATCH_ACCEPT_TAC cover_take_slots) >>
  qabbrev_tac `fuel = MAX N f7` >>
  Cases_on `rooted_eval fuel (stage 7) levels R` >>
  rename1 `rooted_eval fuel (stage 7) levels R = (events,stop)` >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==>
    levels_ok F (stage 7) levels _ _ root_sf _ [] 0 /\ _`
    (qspecl_then [`fuel`, `TAKE (LENGTH Mcut) raw`,
                   `DROP (LENGTH Mcut) raw ++ [0w]`] mp_tac) >>
  `N <= fuel /\ f7 <= fuel` by simp[Abbr `fuel`] >>
  qpat_assum `Abbrev (R = root_entry with vs_gas_readings := raw ++ [0w])`
    (fn th => simp_tac (srw_ss()) [TAKE_DROP, APPEND_ASSOC,
      GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `rooted_eval fuel (stage 7) levels R = (events,stop)`
    (fn th => PURE_REWRITE_TAC [th]) >>
  Cases_on `stop` >> simp_tac (srw_ss()) [] >>
  TRY (disch_then (CONJUNCTS_THEN2 assume_tac
         (CONJUNCTS_THEN2 (qx_choose_then `spare` assume_tac)
           (map_every assume_tac o CONJUNCTS))) >>
       irule cover_events_at_fuel >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`Ecut`,`events`,`spare`,`fuel`,`er`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `spare` assume_tac)
      (map_every assume_tac o CONJUNCTS))) >>
  `Ecut <<= gas_events_blocks fuel (stage 7) root_sf R` by
    (qpat_assum `levels_ok fuel (stage 7) levels _ _ root_sf R [] 0`
       (fn th =>
         let
           val lemma = PART_MATCH (fn tm => List.nth (strip_conj (lhand tm), 6))
             cover_rooted_events (concl th)
         in
           mp_tac (Q.INST [`result` |-> `v`, `events` |-> `Ecut`] lemma)
         end) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (qpat_assum `o1_ctx_shape (stage 7)` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >>
              simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
              metis_tac[] >> NO_TAC) >>
         qpat_assum `rooted_eval fuel (stage 7) levels R = (events,OK v)`
           (fn th => qpat_assum `events = Ecut` (ACCEPT_TAC o (fn eq => REWRITE_RULE [eq] th)))) >>
     DISCH_THEN ACCEPT_TAC) >>
  Cases_on `n <= LENGTH Mcut`
  >- (irule cover_common_event_prefix >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`Ecut`, `gas_events_blocks fuel (stage 7) root_sf R`] >>
      conj_tac
      >- (qpat_assum `LENGTH Mcut = LENGTH Ecut`
            (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `sites = Ecut ++ er` SUBST1_TAC >> simp[IS_PREFIX_APPEND]) >>
      qspecl_then [`f7`, `stage 7`, `root_sf`, `R`, `fuel`] mp_tac
        (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
      simp_tac (srw_ss()) [IS_PREFIX_APPEND, ASSUME ``f7 <= fuel``]) >>
  drule_then strip_assume_tac cover_cfg_cursor_shape >>
  `o1_ctx_shape (stage 9)` by
    (qpat_assum `!k. k <= 9 ==> _` (qspec_then `9` mp_tac) >> simp[]) >>
  `~(inst9.inst_opcode = INVOKE /\
       ~(?nm ops callee args ent.
          decode_invoke inst9 = SOME (nm,ops) /\
          lookup_function nm (stage 9).ctx_functions = SOME callee /\
          eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent))` by
    (strip_tac >> drule_all cover_invoke_setup >>
     qpat_x_assum `~(?nm ops callee args ent. decode_invoke inst9 = _ /\ _)` mp_tac >>
     simp_tac (srw_ss()) []) >>
  Cases_on `in_revert_forward fn9 s9`
  >- suspend "forward" >>
  Cases_on `(inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
      (~source_memory_reads_disjoint cpl inst9 s9 \/
       ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
      (fin = asm_opt_finalizer /\
       ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
         inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
         eval_operand (Var x) s9 = SOME src /\
         FLOOKUP asm_lo "code_end" = SOME off /\
         ~(w2n (src - n2w off) < dimword (:256) DIV 2))`
  >- suspend "guard" >>
  suspend "error"
QED

Resume focus_packet_coverage_for[guard]:
  `inv_memory_observation inst9.inst_opcode` by
    (qpat_assum `(inst9.inst_opcode <> INVOKE /\ _) \/ (fin = asm_opt_finalizer /\ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     FIRST [qpat_assum `inst9.inst_opcode = CODECOPY`
              (fn th => simp_tac (srw_ss())
                [dftGasInvCrossingProbeTheory.inv_memory_observation_def, th]),
            irule cover_memory_observation >> metis_tac[]]) >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ; PHI]` by
    (qpat_assum `inv_memory_observation inst9.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `inst9.inst_opcode` >> simp[dftGasInvCrossingProbeTheory.inv_memory_observation_def]) >>
  drule_all_then assume_tac cover_cfg_joint_inst >>
  `inv_memory_observation inst8.inst_opcode` by
    (qpat_assum `inst8 = inst9` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  (fn (asl,goal) =>
    let
      val supplier = CONV_RULE (DEPTH_CONV BETA_CONV)
         (PURE_REWRITE_RULE [LET_THM] gasFocusCutGuardsTheory.focus_cut_guard_or_stop_for)
      fun premise tm =
        if is_conj tm then
          let val (l,r) = dest_conj tm in CONJ (premise l) (premise r) end
        else if List.exists (aconv tm) asl then ASSUME tm
        else raise mk_HOL_ERR "focus_packet_coverage" "guard premise" (term_to_string tm)
    in
      mp_tac (MP supplier (premise (lhand (concl supplier)))) (asl,goal)
    end) >>
  disch_then (CONJUNCTS_THEN2
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) (K ALL_TAC)) >>
  qpat_x_assum `inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/ _ ==> _` mp_tac >>
  impl_tac >- (DISJ1_TAC >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `gq` (qx_choose_then `gz` (qx_choose_then `gi`
    (qx_choose_then `gcuts` (qx_choose_then `glevels` (qx_choose_then `gM`
      (qx_choose_then `gE` (qx_choose_then `gK` (qx_choose_then `gmr`
        (qx_choose_then `ger` (qx_choose_then `gkr`
          (map_every assume_tac o CONJUNCTS)))))))))))) >>
  qpat_x_assum `(~in_revert_forward fn9 s9 /\ _) \/
    _ <= LENGTH gM \/ _` mp_tac >>
  qpat_assum `Abbrev (n = MIN _ _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac assume_tac)))
  >- (qpat_assum `(inst9.inst_opcode <> INVOKE /\ _) \/ (fin = asm_opt_finalizer /\ _)` mp_tac >>
      qpat_assum `~in_revert_forward fn9 s9 /\ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[])
  >- (`gq = q /\ gz = z` by
        (qpat_assum `(IS_SOME body_entry' /\ _) \/ _` mp_tac >>
         qpat_assum `(IS_SOME body_entry /\ _) \/ _` mp_tac >>
         qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho',in_state,h0,body_entry,count',front,closed,brest)` mp_tac >>
         qpat_assum `FLOOKUP blocks (p,d) = SOME (bb',bt',ps',xs',ys',rho'',in_state',h0',body_entry',count'',front',closed',brest')` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         fs[optionTheory.IS_SOME_EXISTS]) >>
      qabbrev_tac `orders = \a. OPTION_MAP (\(_,_,_,_,o1,_,_). o1)
        (FLOOKUP acts a)` >>
      qabbrev_tac `call_idx = \a e cid. OPTION_MAP FST (FLOOKUP calls (a,e,cid))` >>
      qabbrev_tac `cut_prefix = \a e q.
        (\(bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest).
           DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs)
        (THE (FLOOKUP blocks (a,e)))` >>
      `cuts = gcuts` by
        ((fn (asl,goal) =>
            mp_tac (Q.INST [`orders` |-> `orders`, `call_idx` |-> `call_idx`,
                   `cut_prefix` |-> `cut_prefix`, `d0` |-> `d`,
                   `q0` |-> `q`, `z0` |-> `z`,
                   `paths` |-> `REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p)))`]
              (PART_MATCH rand cover_cut_paths_unique goal)) (asl,goal)) >>
         impl_tac >-
           (conj_tac >- first_assum ACCEPT_TAC >>
            conj_tac >- first_assum ACCEPT_TAC >>
            conj_tac >>
            (rpt gen_tac >> strip_tac >>
             qmatch_asmsub_abbrev_tac `EL i cs = (a,ds,e,q',z')` >>
             qpat_assum `!i a ds e q z. i < LENGTH cs /\ EL i cs = _ ==> _`
               (qspecl_then [`i`,`a`,`ds`,`e`,`q'`,`z'`] mp_tac) >>
             impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
             disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
             conj_tac
             >- (qexistsl [`orderi`,`later`] >>
                 qpat_assum `FLOOKUP acts a = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`
                   (fn th => simp_tac (srw_ss()) [Abbr `orders`, th]) >>
                 conj_tac
                 >- (qpat_assum `!a sf tf inc entry order res nrest.
                       FLOOKUP acts a = _ ==> _`
                       (qspecl_then [`a`,`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`] mp_tac) >>
                     impl_tac >- first_assum ACCEPT_TAC >>
                     disch_then (fn th => PURE_ONCE_REWRITE_TAC [List.nth (CONJUNCTS th, 5)]) >>
                     simp_tac (srw_ss()) [ALL_DISTINCT_GENLIST]) >>
                 qpat_assum `orderi = ds ++ e::later`
                   (fn th => simp_tac (srw_ss()) [th])) >>
             qpat_assum `MAP _ cs = REVERSE _` (fn paths =>
               qpat_assum `if SUC i = LENGTH cs then _ else _`
                 (mp_tac o PURE_REWRITE_RULE [paths])) >>
             Cases_on `SUC i = LENGTH cs`
             >- (qpat_assum `SUC i = LENGTH cs` (fn th =>
                   PURE_REWRITE_TAC [th, COND_CLAUSES]) >>
                 qpat_assum `gq = q` (fn qeq =>
                   qpat_assum `gz = z` (fn zeq =>
                     simp_tac (srw_ss()) [qeq,zeq]))) >>
             qpat_assum `~(SUC i = LENGTH cs)` (fn th =>
               PURE_REWRITE_TAC [th, COND_CLAUSES]) >>
             disch_then (qx_choose_then `cid`
               (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
             qexists `cid` >>
             qpat_assum `FLOOKUP calls (a,e,cid) = SOME _` (fn call =>
               qpat_assum `FLOOKUP blocks (a,e) = SOME _` (fn row =>
                 simp_tac (srw_ss()) [Abbr `call_idx`, Abbr `cut_prefix`, call,row])) >>
             conj_tac
             >- (qpat_assum `EL (SUC i) (REVERSE _) = (e,cid)::a`
                   (fn th => simp_tac (srw_ss()) [th])) >>
             qpat_assum `z' = DROP _ _ ++ TAKE q' _`
               (fn th => simp_tac (srw_ss()) [th]))) >>
         DISCH_THEN ACCEPT_TAC) >>
      `gM = Mcut` by
        (qpat_assum `gM = FLAT (MAP _ gcuts)` SUBST1_TAC >>
         qpat_assum `Mcut = FLAT (MAP _ cuts)` SUBST1_TAC >>
         qpat_assum `cuts = gcuts` SUBST1_TAC >> REFL_TAC) >>
      qpat_assum `n <= LENGTH gM` mp_tac >>
      qpat_assum `~(n <= LENGTH Mcut)` mp_tac >>
      qpat_assum `gM = Mcut` (fn th => simp_tac (srw_ss()) [th]))
  >- (qpat_assum `LENGTH gM < n /\ in_revert_forward fn9 s9` mp_tac >>
      qpat_assum `~in_revert_forward fn9 s9` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `LENGTH gM < n /\ ?F events stopped. _`
    (CONJUNCTS_THEN2 (K ALL_TAC)
      (qx_choose_then `gf` (qx_choose_then `gevents` (qx_choose_then `gstop`
        (map_every assume_tac o CONJUNCTS))))) >>
  qpat_assum `Abbrev (R = root_entry with vs_gas_readings := raw ++ [0w])`
    (fn ab =>
       let
         val rw = GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)
         val normalize = SIMP_RULE (srw_ss()) [TAKE_DROP, APPEND_ASSOC, rw]
       in
         qpat_assum `run_blocks gf (stage 7) root_sf _ = gstop`
           (assume_tac o normalize) >>
         qpat_assum `gas_events_blocks gf (stage 7) root_sf _ = gevents`
           (assume_tac o normalize)
       end) >>
  irule cover_stopped_events >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`gE`, `gevents`, `gf`, `gstop`] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    DISJ1_TAC >> first_assum ACCEPT_TAC,
    PURE_REWRITE_TAC [IS_PREFIX_APPEND] >>
      FIRST [first_assum ACCEPT_TAC, qexists `ger` >> first_assum ACCEPT_TAC]]

QED

Resume focus_packet_coverage_for[forward]:
  drule_all_then strip_assume_tac cover_forward_suffix >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ]` by
    (qpat_assum `MEM inst9.inst_opcode [RETURNDATACOPY; REVERT]` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[] >> fs[]) >>
  `fn = fn8 /\ inst = inst8 /\ st = s8` by
    (qpat_assum `JointConfig stk8 _ _ _ _ _ s8 _ _ _ _ = _` mp_tac >> simp[]) >>
  qpat_assum `?sf inc entry order bb bt ps xs ys rr in_state h0 body_entry count.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\ _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `lookup_block s8.vs_current_bb fn8.fn_blocks = SOME bt` by
    (qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho',in_state,h0,body_entry,count',front,closed,brest)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,OK st,F,NONE)` mp_tac >>
     qpat_assum `lookup_block st.vs_current_bb fn.fn_blocks = SOME _` mp_tac >>
     qpat_assum `fn = fn8` (fn feq =>
       qpat_assum `st = s8` (fn seq =>
         PURE_REWRITE_TAC [feq,seq])) >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >> fs[]) >>
  drule_all cover_cfg_joint_blocks >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `cb` (qx_choose_then `cg` (map_every assume_tac o CONJUNCTS)))) >>
  `?gb. lookup_block s9.vs_current_bb fn9.fn_blocks = SOME gb /\
     (LAST gb.bb_instructions).inst_opcode = REVERT /\
     (!k. s9.vs_inst_idx <= k /\ k < LENGTH gb.bb_instructions ==>
        (EL k gb.bb_instructions).inst_opcode <> INVOKE) /\
     MAP (\i. i.inst_opcode) bt.bb_instructions =
     MAP (\i. i.inst_opcode) gb.bb_instructions` by
    (qexists `cg` >>
     qpat_assum `MAP _ cb.bb_instructions = MAP _ cg.bb_instructions` mp_tac >>
     qpat_assum `lookup_block s8.vs_current_bb fn8.fn_blocks = SOME bt` mp_tac >>
     qpat_assum `lookup_block s8.vs_current_bb fn8.fn_blocks = SOME cb` mp_tac >>
     qpat_assum `lookup_block s9.vs_current_bb fn9.fn_blocks = SOME cg` mp_tac >>
     qpat_assum `lookup_block s9.vs_current_bb fn9.fn_blocks = SOME bb'` mp_tac >>
     qpat_assum `(LAST bb'.bb_instructions).inst_opcode = REVERT` mp_tac >>
     qpat_assum `!k. s9.vs_inst_idx <= k /\ k < LENGTH bb'.bb_instructions ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[optionTheory.SOME_11]) >>
  `LENGTH bt.bb_instructions = LENGTH gb.bb_instructions` by
    (qpat_assum `MAP _ bt.bb_instructions = MAP _ gb.bb_instructions`
       (mp_tac o AP_TERM ``LENGTH:opcode list -> num``) >>
     simp_tac (srw_ss()) [LENGTH_MAP]) >>
  `bt.bb_instructions <> [] /\ gb.bb_instructions <> []` by
    (qpat_assum `get_instruction bt s8.vs_inst_idx = SOME inst8` mp_tac >>
     qpat_assum `LENGTH bt.bb_instructions = LENGTH gb.bb_instructions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [get_instruction_def, AllCaseEqs()] >>
     rpt strip_tac >>
     `LENGTH bt.bb_instructions <> 0 /\ LENGTH gb.bb_instructions <> 0` by decide_tac >>
     fs[LENGTH_NIL]) >>
  `(LAST bt.bb_instructions).inst_opcode = REVERT` by
    (qpat_assum `MAP _ bt.bb_instructions = MAP _ gb.bb_instructions`
       (mp_tac o AP_TERM ``LAST:opcode list -> opcode``) >>
     simp_tac (srw_ss()) [LAST_MAP, ASSUME ``bt.bb_instructions <> []``,
       ASSUME ``gb.bb_instructions <> []``,
       ASSUME ``(LAST gb.bb_instructions).inst_opcode = REVERT``]) >>
  `!k. s8.vs_inst_idx <= k /\ k < LENGTH bt.bb_instructions ==>
    (EL k bt.bb_instructions).inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     `k < LENGTH gb.bb_instructions /\ s9.vs_inst_idx <= k` by
       (qpat_assum `LENGTH bt.bb_instructions = LENGTH gb.bb_instructions`
          (SUBST1_TAC o SYM) >>
        qpat_assum `s8.vs_inst_idx = s9.vs_inst_idx` (SUBST1_TAC o SYM) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `(EL k bt.bb_instructions).inst_opcode = (EL k gb.bb_instructions).inst_opcode` by
       (qpat_assum `MAP _ bt.bb_instructions = MAP _ gb.bb_instructions`
          (mp_tac o AP_TERM ``EL k : opcode list -> opcode``) >>
        simp_tac (srw_ss()) [EL_MAP, ASSUME ``k < LENGTH bt.bb_instructions``,
          ASSUME ``k < LENGTH gb.bb_instructions``]) >>
     qpat_assum `!k. s9.vs_inst_idx <= k /\ k < LENGTH gb.bb_instructions ==> _`
       (qspec_then `k` mp_tac) >>
     simp_tac (srw_ss()) [ASSUME ``s9.vs_inst_idx <= k``,
       ASSUME ``k < LENGTH gb.bb_instructions``,
       GSYM (ASSUME ``(EL k bt.bb_instructions).inst_opcode = (EL k gb.bb_instructions).inst_opcode``),
       ASSUME ``(EL k bt.bb_instructions).inst_opcode = INVOKE``]) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
    (qspecl_then [`p`,`d`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho'`,`in_state`,
      `h0`,`body_entry`,`count'`,`front`,`closed`,`brest`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ; PHI]` by
    (qpat_assum `MEM inst9.inst_opcode [RETURNDATACOPY; REVERT]` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[] >> fs[]) >>
  drule_all_then assume_tac cover_cfg_joint_inst >>
  `LENGTH ps <= s8.vs_inst_idx` by
    (CCONTR_TAC >>
     `s8.vs_inst_idx < LENGTH ps` by
       (qpat_assum `~(LENGTH ps <= s8.vs_inst_idx)` mp_tac >> decide_tac) >>
     qpat_assum `get_instruction bt s8.vs_inst_idx = SOME inst8` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `EVERY (\x. is_pseudo x.inst_opcode) ps` mp_tac >>
     qpat_assum `MEM inst9.inst_opcode [RETURNDATACOPY; REVERT]` mp_tac >>
     qpat_assum `inst8 = inst9` mp_tac >>
     qpat_assum `s8.vs_inst_idx < LENGTH ps` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[get_instruction_def, AllCaseEqs(), EL_APPEND1, EVERY_EL] >>
     first_x_assum (qspec_then `s8.vs_inst_idx` mp_tac) >>
     simp_tac (srw_ss()) [is_pseudo_def] >> gvs[is_pseudo_def]) >>
  `IS_SOME body_entry /\ s8.vs_inst_idx = LENGTH ps + count' /\ count' < LENGTH ys` by
    (qpat_assum `case body_entry' of NONE => _ | SOME pair => _` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho',in_state,h0,body_entry,count',front,closed,brest)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,body_entry',_,OK st,F,NONE)` mp_tac >>
     qpat_assum `st = s8` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `LENGTH ps <= s8.vs_inst_idx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[] >> Cases_on `body_entry` >> gvs[] >>
     PairCases_on `x` >> gvs[]) >>
  `!k. count' <= k /\ k < LENGTH ys ==> (EL k ys).inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     qpat_assum `!k. s8.vs_inst_idx <= k /\ k < LENGTH bt.bb_instructions ==> _`
       (qspec_then `LENGTH (ps:instruction list) + k` mp_tac) >>
     qpat_assum `bt.bb_instructions = ps ++ ys` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `s8.vs_inst_idx = LENGTH ps + count'` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `count' <= k` (fn le =>
       qpat_assum `k < LENGTH ys` (fn lt =>
         qpat_assum `(EL k ys).inst_opcode = INVOKE` (fn inv =>
           simp_tac (srw_ss()) [EL_APPEND2,le,lt,inv])))) >>
  `!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count' rho')` by
    (mp_tac (Q.INST [`row_order` |-> `rho'`, `row_count` |-> `count'`,
       `xs` |-> `xs`, `ys` |-> `ys`] cover_remaining_no_invoke) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     DISCH_THEN ACCEPT_TAC) >>
  `dft_fn_rel sf fn8` by
    (qpat_assum `!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (qspecl_then [`p`,`sf`,`fn8`,`inc`,`entry`,`order`,`res`,`nrest`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => ACCEPT_TAC (List.nth (CONJUNCTS th, 2)))) >>
  `sf'' = sf /\ tf = fn8` by
    (qpat_assum `FLOOKUP acts p = SOME (sf'',tf,_,_,_,_,_)` mp_tac >>
     qpat_assum `FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label fn8.fn_blocks = SOME bt` by
    (qpat_assum `sf'' = sf` (SUBST1_TAC o SYM) >>
     qpat_assum `tf = fn8` (SUBST1_TAC o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `wf_function sf /\ MEM bb sf.fn_blocks /\ bb_well_formed bb` by
    (qpat_assum `dft_fn_rel sf fn8` mp_tac >>
     qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [dftRunRelTheory.dft_fn_rel_def] >>
     rpt strip_tac >> metis_tac[venomExecProofsTheory.lookup_block_MEM, wf_function_def]) >>
  drule_all_then strip_assume_tac dftRunRelTheory.dft_fn_rel_lookup_order >>
  `LAST bt.bb_instructions = LAST bb.bb_instructions` by
    (MATCH_MP_TAC dftRunRelTheory.dft_block_rel_last >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
        MATCH_MP_TAC (Q.SPECL [`sf`,`bb`] dftWfTheory.wf_fn_block_inst_ids_distinct) >>
        conj_tac >> first_assum ACCEPT_TAC]) >>
  `(LAST bb.bb_instructions).inst_opcode = REVERT` by
    (qpat_assum `LAST bt.bb_instructions = LAST bb.bb_instructions` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `xs <> []` by
    (qpat_assum `LENGTH xs = LENGTH ys` mp_tac >>
     qpat_assum `count' < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `xs` >> Cases_on `ys` >> simp[]) >>
  drule_all_then strip_assume_tac cover_last_row_source >>
  qabbrev_tac `endq = PRE (LENGTH xs)` >>
  qabbrev_tac `endz = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE endq xs` >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
                body_entry count front closed brest q z.
                _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`p`,`d`,`sf`,`fn8`,`inc`,`entry`,`order`,`res`,`nrest`,`bb`,`bt`,
      `ps`,`xs`,`ys`,`rho'`,`in_state`,`h0`,`body_entry`,`count'`,`front`,`closed`,
      `brest`,`endq`,`endz`] mp_tac) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      DISJ1_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `0 < LENGTH (xs:instruction list)` mp_tac >>
          simp_tac (srw_ss()) [Abbr `endq`] >> decide_tac) >>
      conj_tac >- simp_tac (srw_ss()) [Abbr `endz`, Abbr `endq`] >>
      conj_tac >- (simp_tac (srw_ss()) [Abbr `endq`] >> first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      qpat_assum `!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==> _`
        (qspec_then `r` mp_tac) >>
      impl_tac >- (conj_tac
                   >- (qpat_assum `r < endq` mp_tac >>
                       simp_tac (srw_ss()) [Abbr `endq`] >> decide_tac) >>
                   first_assum ACCEPT_TAC) >>
      DISCH_THEN ACCEPT_TAC) >>
  disch_then (qx_choose_then `endcuts` (qx_choose_then `endlevels`
    (qx_choose_then `endM` (qx_choose_then `endE` (qx_choose_then `endK`
      (qx_choose_then `endmr` (qx_choose_then `ender` (qx_choose_then `endkr`
        (map_every assume_tac o CONJUNCTS))))))))) >>
  `raw_slots = endM ++ endmr /\ sites = endE ++ ender` by
    (conj_tac
     >- (qpat_assum `raw_slots = AM []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `sites = AE []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) endM
     (TAKE (LENGTH endM) raw)` by
    (qpat_assum `LIST_REL _ raw_slots raw` mp_tac >>
     qpat_assum `raw_slots = endM ++ endmr` SUBST1_TAC >>
     MATCH_ACCEPT_TAC cover_take_slots) >>
  Cases_on `rooted_eval fuel (stage 7) endlevels R` >>
  rename1 `rooted_eval fuel (stage 7) endlevels R = (endevents,endstop)` >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ endM gs ==>
      levels_ok F (stage 7) endlevels _ _ root_sf _ [] 0 /\ _`
    (qspecl_then [`fuel`, `TAKE (LENGTH endM) raw`,
                   `DROP (LENGTH endM) raw ++ [0w]`] mp_tac) >>
  qpat_assum `Abbrev (R = root_entry with vs_gas_readings := raw ++ [0w])`
    (fn th => simp_tac (srw_ss()) [TAKE_DROP, APPEND_ASSOC,
      GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `rooted_eval fuel (stage 7) endlevels R = (endevents,endstop)`
    (fn th => PURE_REWRITE_TAC [th]) >>
  Cases_on `endstop` >> simp_tac (srw_ss()) [] >>
  TRY (disch_then (CONJUNCTS_THEN2 assume_tac
         (CONJUNCTS_THEN2 (qx_choose_then `endspare` assume_tac)
           (map_every assume_tac o CONJUNCTS))) >>
       irule cover_events_at_fuel >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`endE`,`endevents`,`endspare`,`fuel`,`ender`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `endspare` assume_tac)
      (map_every assume_tac o CONJUNCTS))) >>
  `endE <<= gas_events_blocks fuel (stage 7) root_sf R` by
    (qpat_assum `levels_ok fuel (stage 7) endlevels _ _ root_sf R [] 0`
       (fn th =>
         let
           val lemma = PART_MATCH (fn tm => List.nth (strip_conj (lhand tm), 6))
             cover_rooted_events (concl th)
         in
           mp_tac (Q.INST [`result` |-> `v'`, `events` |-> `endE`] lemma)
         end) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (qpat_assum `o1_ctx_shape (stage 7)` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >>
              simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
              metis_tac[] >> NO_TAC) >>
         qpat_assum `rooted_eval fuel (stage 7) endlevels R = (endevents,OK v')`
           (fn th => qpat_assum `endevents = endE`
              (ACCEPT_TAC o (fn eq => REWRITE_RULE [eq] th)))) >>
     DISCH_THEN ACCEPT_TAC) >>
  qpat_x_assum `?before after. trace_blocks [] 0 fuel (stage 7) root_sf R = _ /\
      trace_gas before = ZIP (endK,TAKE (LENGTH endM) raw)`
    (qx_choose_then `endbefore` (qx_choose_then `endafter` (map_every assume_tac o CONJUNCTS))) >>
  `LENGTH (trace_gas endbefore) = LENGTH endE` by
    (qpat_assum `trace_gas endbefore = _` SUBST1_TAC >>
     qpat_assum `LIST_REL _ endM (TAKE (LENGTH endM) raw)`
       (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH endM = LENGTH endE` mp_tac >>
     qpat_assum `LENGTH endM = LENGTH endK` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     `LENGTH endK = LENGTH (TAKE (LENGTH endM) raw)` by metis_tac[] >>
     qpat_assum `LENGTH endK = LENGTH (TAKE (LENGTH endM) raw)`
       (fn th => PURE_REWRITE_TAC [cj 1 (MATCH_MP LENGTH_ZIP th)]) >>
     metis_tac[]) >>
  `gas_events_blocks fuel (stage 7) root_sf R <<= sites` by
    (qabbrev_tac `endinst = EL (LENGTH endz)
       (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` >>
     MATCH_MP_TAC (Q.INST [`after` |-> `endafter`, `before` |-> `endbefore`,
       `Ecut` |-> `endE`, `p` |-> `p`, `d` |-> `d`, `id` |-> `endinst.inst_id`,
       `sf` |-> `root_sf`, `sf'` |-> `sf`, `inst` |-> `endinst`, `u` |-> `v'`]
       cover_terminal_rooted_sites) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `sites = endE ++ ender` (fn th =>
         (simp_tac (srw_ss()) [th,IS_PREFIX_APPEND] >> NO_TAC)),
       qpat_assum `endinst.inst_opcode = REVERT` (fn th =>
         let val failure = MATCH_MP cover_revert_step th in
           simp_tac (srw_ss()) [th,cj 1 failure,cj 2 failure]
         end)]) >>
  irule cover_taken_at_fuel >> qexists `fuel` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume focus_packet_coverage_for[error]:
  `inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err` by
    (qpat_assum `in_revert_forward fn9 s9 \/ _` mp_tac >>
     qpat_assum `~in_revert_forward fn9 s9` mp_tac >>
     qpat_assum `~(inst8.inst_opcode = GAS /\ _)` mp_tac >>
     qpat_assum `~(inst9.inst_opcode = INVOKE /\ _)` mp_tac >>
     qpat_assum `~((inst9.inst_opcode <> INVOKE /\ _) \/ (fin = asm_opt_finalizer /\ _))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `?aa ra rst mem0. active_frame_plan_reloc asm_lo rpolicy out.po_unit cpl prog
      fn9 s9 aa ra rst mem0` by
    (qpat_assum `!stk PG G tn fn inst s oms om hs h ast ss. _`
       (qspecl_then [`stk9`,`PG9`,`G9`,`tn9`,`fn9`,`inst9`,`s9`,`oms9`,`om9`,
         `hs9`,`hist9`,`ast`,`ss`] mp_tac) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> symbolic _ _ = _ /\ _`
         (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
     disch_then (REPEAT_TCL CHOOSE_THEN assume_tac) >>
     qpat_assum `stage 9 = out.po_unit.cu_context`
       (fn th => qpat_assum `step_inst 0 (stage 9) inst9 s9 = Error err`
         (assume_tac o REWRITE_RULE [th])) >>
     drule_all cover_error_active_frame_reloc >>
     disch_then (qx_choose_then `aa` assume_tac) >>
     qexistsl [`aa`,`ra`,`rest`,`mem0`] >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac cover_error_active_shape_reloc >>
  drule_all cover_noninvoke_runtime_error >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `dst` (qx_choose_then `sz` assume_tac)) assume_tac)) >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ; PHI]` by
    (qpat_assum `inst9.inst_opcode = CODECOPY`
       (fn th => simp_tac (srw_ss()) [th])) >>
  drule_all_then assume_tac cover_cfg_joint_inst >>
  drule_then strip_assume_tac cover_cfg_active >>
  `inst8.inst_opcode = CODECOPY /\
    inst8.inst_operands = [dst; Label "runtime_begin"; sz] /\
    FLOOKUP s8.vs_labels "runtime_begin" = NONE` by
    (qpat_assum `inst8 = inst9` SUBST1_TAC >>
     qpat_assum `s8.vs_labels = s9.vs_labels` SUBST1_TAC >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `inv_memory_observation inst8.inst_opcode /\ ~is_pseudo inst8.inst_opcode` by
    (qpat_assum `inst8.inst_opcode = CODECOPY` (fn th =>
       simp_tac (srw_ss()) [th,dftGasInvCrossingProbeTheory.inv_memory_observation_def,is_pseudo_def])) >>
  drule_all_then assume_tac cover_packet_nonpseudo_body >>
  `EL q xs = inst8 /\ q < LENGTH xs /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by
    (qpat_assum `(IS_SOME body_entry /\ _) \/ _` mp_tac >>
     qpat_assum `IS_SOME body_entry` mp_tac >>
     qpat_assum `inv_memory_observation inst8.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `fn = fn8 /\ inst = inst8 /\ st = s8` by
    (qpat_assum `JointConfig stk8 _ _ _ _ _ s8 _ _ _ _ = _` mp_tac >> simp[]) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
    (qspecl_then [`p`,`d`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho'`,`in_state`,
      `h0`,`body_entry`,`count'`,`front`,`closed`,`brest`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `(EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) = inst8` by
    (qpat_assum `EL q xs = inst8` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     MATCH_MP_TAC (Q.INST [`ps` |-> `ps`] dftFinitePacketTheory.dft_packet_cut_instruction) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP v.vs_labels "runtime_begin" = NONE` by
    (qpat_assum `_ ==> (!op. MEM op inst.inst_operands ==> eval_operand op v = eval_operand op st) /\ _` mp_tac >>
     qpat_assum `inst = inst8` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `st = s8` (fn th => PURE_REWRITE_TAC [th]) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (fn th => qspec_then `Label "runtime_begin"` mp_tac (cj 1 th)) >>
     qpat_assum `inst8.inst_operands = [dst; Label "runtime_begin"; sz]` (fn ops =>
       qpat_assum `FLOOKUP s8.vs_labels "runtime_begin" = NONE` (fn missing =>
         simp_tac (srw_ss()) [ops,missing,eval_operand_def]))) >>
  `!f C. ?err. step_inst f C inst8 v = Error err` by
    (rpt gen_tac >> MATCH_MP_TAC (Q.INST [`dst` |-> `dst`, `sz` |-> `sz`,
       `l` |-> `"runtime_begin"`] cover_codecopy_error) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?before after. trace_blocks [] 0 fuel (stage 7) root_sf R = _ /\
      trace_gas before = ZIP (Kcut,TAKE (LENGTH Mcut) raw)`
    (qx_choose_then `before` (qx_choose_then `after` (map_every assume_tac o CONJUNCTS))) >>
  `LENGTH (trace_gas before) = LENGTH Ecut` by
    (qpat_assum `trace_gas before = _` SUBST1_TAC >>
     qpat_assum `LIST_REL _ Mcut (TAKE (LENGTH Mcut) raw)`
       (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH Mcut = LENGTH Ecut` mp_tac >>
     qpat_assum `LENGTH Mcut = LENGTH Kcut` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     `LENGTH Kcut = LENGTH (TAKE (LENGTH Mcut) raw)` by metis_tac[] >>
     qpat_assum `LENGTH Kcut = LENGTH (TAKE (LENGTH Mcut) raw)`
       (fn th => PURE_REWRITE_TAC [cj 1 (MATCH_MP LENGTH_ZIP th)]) >>
     metis_tac[]) >>
  `gas_events_blocks fuel (stage 7) root_sf R <<= sites` by
    (MATCH_MP_TAC (Q.INST [`after` |-> `after`, `before` |-> `before`,
       `Ecut` |-> `Ecut`, `p` |-> `p`, `d` |-> `d`, `id` |-> `inst8.inst_id`,
       `sf` |-> `root_sf`, `sf'` |-> `sf`, `inst` |-> `inst8`, `u` |-> `v`]
       cover_terminal_rooted_sites) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `sites = Ecut ++ er` (fn th =>
         simp_tac (srw_ss()) [th, IS_PREFIX_APPEND] >> NO_TAC),
       qpat_assum `inst8.inst_opcode = CODECOPY` (fn th =>
         simp_tac (srw_ss()) [th] >> NO_TAC),
       qpat_assum `(EL (LENGTH z) (DROP _ bb.bb_instructions)) = inst8`
         (fn th => qpat_assum `trace_blocks [] 0 fuel (stage 7) root_sf R = _`
           (ACCEPT_TAC o PURE_REWRITE_RULE [th])),
       qx_gen_tac `cfuel` >> qx_gen_tac `cctx` >> rpt gen_tac >>
       qpat_assum `!f C. ?err. step_inst f C inst8 v = Error err`
         (qspecl_then [`cfuel`,`cctx`] strip_assume_tac) >>
       qpat_assum `step_inst cfuel cctx inst8 v = Error _`
         (fn th => simp_tac (srw_ss()) [th])]) >>
  irule cover_taken_at_fuel >> qexists `fuel` >> conj_tac >> first_assum ACCEPT_TAC
QED

Finalise focus_packet_coverage_for

Theorem focus_packet_coverage:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    (0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (?align old_cursors old_asm old_sym costs.
    LENGTH costs = LENGTH evs9 /\ LENGTH old_asm = LENGTH evs9 /\
    (fin = asm_opt_finalizer ==> LENGTH old_sym = LENGTH evs9) /\
    align 0 = 0 /\ align (LENGTH evs9) = j /\
    asm_fuel = SUM costs /\ ast = EL (LENGTH evs9) ((entry_asm_state vs0 es0)::old_asm) /\
    (fin = asm_opt_finalizer ==> ss = EL (LENGTH evs9) (sym_init (entry_asm_state vs0 es0)::old_sym)) /\
    LIST_REL (\cost edge. 0 < cost \/
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (SND edge) <
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (FST edge))
      costs (ZIP (TAKE (LENGTH evs9) (q90::qs9),qs9)) /\
    (!k. k < LENGTH evs9 ==>
      align k <= j /\
      (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
      align (SUC k) <= j /\
      cfg_norm_joint_cursors (stage 8) (stage 9) (old_cursors k) (EL (align k) (q80::qs8)) (EL k
        (q90::qs9)) /\
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog (EL k costs) (EL k ((entry_asm_state vs0 es0)::old_asm)) =
          AsmOK (EL (SUC k) ((entry_asm_state vs0 es0)::old_asm)) /\
      (fin = asm_opt_finalizer ==>
        sym_steps prog (asm_data_env prog vs0.vs_code) (EL k costs) (EL k (sym_init (entry_asm_state vs0
          es0)::old_sym)) =
          SymOK (EL (SUC k) (sym_init (entry_asm_state vs0 es0)::old_sym))) /\
      (case ((EL (align k) (q80::qs8)),(EL k (q90::qs9))) of
        (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
         JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
          (~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
    source_memory_reads_disjoint cpl inst9 s9 /\
    context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
    !dst x sz src off.
      inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
      code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2)) /\ (active_inst fn9 inst9 s9 /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm' ops callee args ent.
      decode_invoke inst9 = SOME (nm',ops) /\
      lookup_function nm' (stage 9).ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
          (align (SUC k) = SUC (align k) /\ i8.inst_opcode = GAS ==>
            u8.vs_gas_readings <> [])))) /\
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          (p <> p \/ d <> d \/ s8 <> s8 \/
            (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
             (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
          (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
             inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  ((?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\
      r8 = (case r of OK u => Halt u | other => other) /\
      ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/
       (?ex u. r = Abort ex u)) /\
      run_blocks N (stage 8) root_tf root_entry = r8 /\
      (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
          raw_slots gs ==>
        ?extra. sites = gas_events_blocks F (stage 7) root_sf
          (root_entry with vs_gas_readings := gs ++ tail) ++ extra)) \/
    in_revert_forward fn9 s9 \/
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     (~source_memory_reads_disjoint cpl inst9 s9 \/
      ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
    (fin = asm_opt_finalizer /\
      ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
        inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
        eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
        ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
    (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
    (inst9.inst_opcode = INVOKE /\
     ~(?callee_name ops callee args ent.
        decode_invoke inst9 = SOME (callee_name,ops) /\
        lookup_function callee_name (stage 9).ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
    (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err))) ==>
    (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?rest. MAP project sites = markf (raw ++ [0w]) ++ rest)
Proof
  BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fin = asm_opt_finalizer ==> focus_s7_symbolic_context out.po_unit prog` by
    (disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> label_flow_ok _ /\ _`
       (fn th => drule_then (map_every assume_tac o CONJUNCTS) th) >>
     drule_all_then assume_tac focus_opt_label_flow >>
     drule_all_then strip_assume_tac focus_opt_static_assembly >>
     asm_rewrite_tac[focus_s7_symbolic_context_def]) >>
  drule_all_then (strip_assume_tac o REWRITE_RULE [codegen_context_obligations_def])
    focus_false_codegen_context >>
  `!l. FLOOKUP vs0.vs_labels l =
      OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    fs[codegenEntrySimTheory.codegen_asm_entry_rel_def] >>
  `n2w cpl.cp_initial_fmp = vs0.vs_initial_fmp` by
    fs[codegenEntrySimTheory.codegen_asm_entry_rel_def] >>
  `fin = asm_opt_finalizer ==>
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> label_flow_ok _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  mp_tac (BETA_RULE (Q.INST
    [`asm_lo` |-> `SND (compute_label_offsets prog)`,
     `symbolic` |-> `sym_steps prog (asm_data_env prog vs0.vs_code)`,
     `frame` |-> `normal_frame_symbolic_plan
       (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0`]
    focus_packet_coverage_for)) >>
  (impl_tac >- suspend "premises") >>
  disch_then (fn th => BETA_TAC >> ACCEPT_TAC th)
QED

Resume focus_packet_coverage[premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (MATCH_MP_TAC focus_plain_gas_callback >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC focus_plain_frame_projection) >>
  simp[code_labels_agree_refl]
QED

Finalise focus_packet_coverage
