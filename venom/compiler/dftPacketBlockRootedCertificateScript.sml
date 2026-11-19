Theory dftPacketBlockRootedCertificate
Ancestors
  dftPacketSameLevelCompose dftPacketBlockRootedAppend dftPacketBlockAppendShape
  dftPacketBlockAppendSemantics dftPacketBlockAppendNative
  dftPacketLiteralFullRowExtend dftPacketClosedBodyBoundary
  dftPacketBlockCutAggregate dftPacketBlockFreshEntry
  dftPacketFreshSingletonNormalize dftPacketBlockRootedOperational
  dftPacketRootedPlainStop dftPacketOperationalPrefix
  dftPacketBlockAppendValidity dftPacketBlockAppendTransport
  dftPacketBlockAppendTraceBoundary dftPacketBlockAppendStopBoundary
  dftPacketFillingBoundary dftPacketRootedOperational
  finite_map list rich_list arithmetic dftIndexedExec venomExecProofs venomInst

Theorem dft_packet_block_full_row_shape[local]:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
  DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions =
    DROP (phi_prefix_length bb.bb_instructions) ps ++ xs /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (DROP (phi_prefix_length bb.bb_instructions) ps)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    simp[dft_phi_prefix_append,phi_prefix_length_le] >>
  `phi_prefix_length (ps ++ xs) - LENGTH ps = 0` by gvs[] >>
  conj_tac >- simp[DROP_APPEND] >>
  irule EVERY_DROP >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]
QED

Theorem dft_packet_block_rooted_append:
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
    MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
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
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  Z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  z0 = DROP (phi_prefix_length bb.bb_instructions) ps /\
  oldlevels = pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)] /\
  newlevels = pre ++ [(sf,rows ++ [(bb,d,Z);(bb1,SUC d,z1)],NONE)] /\
  oldcuts = priorcuts ++ [(p,ds,d,0,z0)] /\
  newcuts = priorcuts ++ [(p,ds ++ [d],SUC d,q1,z1)] /\
  paths = MAP (\(ai,ds,ei,qi,zi). ai) oldcuts /\
  paths = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs ==>
    levels_ok F C7 oldlevels paths incoming root_sf
      (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 = FST (rooted_eval F C7 oldlevels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 oldlevels
      (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 oldlevels
          (root_entry with vs_gas_readings := gs ++ tail)) = E0 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,d,(EL (LENGTH z0) Z).inst_id),sf,EL (LENGTH z0) Z,u)] ++ after /\
          trace_gas before = ZIP (K0,gs)) /\
        (!tail'. rooted_eval F C7 oldlevels
          (root_entry with vs_gas_readings := gs ++ tail') =
          (E0,OK (u with vs_gas_readings := tail')))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 oldlevels
            (root_entry with vs_gas_readings := gs ++ tail)))) /\
  (!F gs tail ev u.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
    rooted_eval F C7 oldlevels
      (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
    u = (be with vs_gas_readings := tail)) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\ ~post.vs_halted /\
  bb.bb_instructions <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  LENGTH Mb = LENGTH Eb /\ LENGTH Mb = LENGTH Kb /\
  (!F gs tail. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs ==>
    (?extra. Eb = gas_events_block (F-d) C7 sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := gs ++ tail) ++ extra) /\
    ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
        (be with vs_gas_readings := gs ++ tail))) ==>
      gas_events_block (F-d) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail) = Eb /\
      residual_result tail (OK post)
        (FOLDR (dft_exec_cons (F-d) C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) /\
    (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
      trace_gas (trace_block p d (F-d) C7 sf
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail)) = ZIP (Kb,gs))) /\
  N <= Nnew /\ SUC d <= Nnew /\
  lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\ MEM bb1 sf.fn_blocks /\
  bb1.bb_instructions = ps1 ++ xs1 /\ bt1.bb_instructions = ps1 ++ ys1 /\
  bt1.bb_label = bb1.bb_label /\
  EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\
  LENGTH xs1 = LENGTH ys1 /\ EVERY inst_shape_ok bb1.bb_instructions /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
  get_instruction bt1 s1.vs_inst_idx = SOME next1 /\
  ((q1 = 0 /\ s1.vs_inst_idx < LENGTH ps1 /\
    z1 = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) /\
    M1 = [] /\ E1 = [] /\ K1 = [] /\
    (!F t. Nnew <= F ==>
      row_eval F C7 sf.fn_name (bb1,SUC d,z1)
        (post with vs_gas_readings := t) = ([],OK (s1 with vs_gas_readings := t)))) \/
   (s1.vs_inst_idx = LENGTH ps1 /\ q1 < LENGTH xs1 /\
    z1 = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q1 xs1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q1 xs1) /\
    (!r. r < q1 ==> (EL r xs1).inst_opcode <> INVOKE) /\
    LENGTH ms1 = LENGTH xs1 /\ LENGTH ess1 = LENGTH ms1 /\ LENGTH ks1 = LENGTH ms1 /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms1 ess1 /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms1 ks1 /\
    M1 = FLAT (TAKE q1 ms1) /\ E1 = FLAT (TAKE q1 ess1) /\ K1 = FLAT (TAKE q1 ks1) /\
    (!F kgss tail. Nnew <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q1 ms1) kgss ==>
      SND (row_eval F C7 sf.fn_name (bb1,SUC d,z1)
        (post with vs_gas_readings := FLAT kgss ++ tail)) =
        FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q1 xs1)
          (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
      (?extra. E1 = FST (row_eval F C7 sf.fn_name (bb1,SUC d,z1)
        (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
      (!events u. row_eval F C7 sf.fn_name (bb1,SUC d,z1)
          (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
        events = E1 /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
          (bb1 with bb_instructions := TAKE (LENGTH ps1 + q1) bb1.bb_instructions)
          (s1 with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (K1,FLAT kgss) /\
        (!tail'. row_eval F C7 sf.fn_name (bb1,SUC d,z1)
          (post with vs_gas_readings := FLAT kgss ++ tail') =
          (events,OK (u with vs_gas_readings := tail'))))))) /\
  (!F gs tail events u.
    Nnew <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gs /\
    row_eval F C7 sf.fn_name (bb1,SUC d,z1)
      (post with vs_gas_readings := gs ++ tail) = (events,OK u) /\
    inv_memory_observation focus.inst_opcode /\ EL q1 xs1 = focus ==>
    (!op. MEM op focus.inst_operands ==> eval_operand op u = eval_operand op obs_state) /\
    u.vs_initial_fmp = obs_state.vs_initial_fmp) /\
  M0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) oldcuts) /\
  E0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) oldcuts) /\
  K0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) oldcuts) /\
  (!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) priorcuts ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) /\
  (!f. MEM f ds ==>
    FLOOKUP ms_tab' (p,f) = FLOOKUP ms_tab (p,f) /\
    FLOOKUP es_tab' (p,f) = FLOOKUP es_tab (p,f) /\
    FLOOKUP ks_tab' (p,f) = FLOOKUP ks_tab (p,f)) /\
  Mb = FLAT (THE (FLOOKUP ms_tab' (p,d))) /\
  Eb = FLAT (THE (FLOOKUP es_tab' (p,d))) /\
  Kb = FLAT (THE (FLOOKUP ks_tab' (p,d))) /\
  M1 = FLAT (TAKE q1 (THE (FLOOKUP ms_tab' (p,SUC d)))) /\
  E1 = FLAT (TAKE q1 (THE (FLOOKUP es_tab' (p,SUC d)))) /\
  K1 = FLAT (TAKE q1 (THE (FLOOKUP ks_tab' (p,SUC d)))) ==>
  MAP (\(ai,ds,ei,qi,zi). ai) newcuts = paths /\
  FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) newcuts) = M0 ++ Mb ++ M1 /\
  FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) newcuts) = E0 ++ Eb ++ E1 /\
  FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) newcuts) = K0 ++ Kb ++ K1 /\
  LENGTH (M0 ++ Mb ++ M1) = LENGTH (E0 ++ Eb ++ E1) /\
  LENGTH (M0 ++ Mb ++ M1) = LENGTH (K0 ++ Kb ++ K1) /\
  (!F gs tail.
    Nnew <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (M0 ++ Mb ++ M1) gs ==>
    levels_ok F C7 newlevels paths incoming root_sf
      (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 ++ Eb ++ E1 = FST (rooted_eval F C7 newlevels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 newlevels
      (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 newlevels
          (root_entry with vs_gas_readings := gs ++ tail)) = E0 ++ Eb ++ E1 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,SUC d,(EL (LENGTH z1)
              (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions)).inst_id),sf,
              EL (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions),u)] ++ after /\
          trace_gas before = ZIP (K0 ++ Kb ++ K1,gs)) /\
        (!tail'. rooted_eval F C7 newlevels
          (root_entry with vs_gas_readings := gs ++ tail') =
          (E0 ++ Eb ++ E1,OK (u with vs_gas_readings := tail'))) /\
        (s1.vs_inst_idx < LENGTH ps1 ==> u with vs_gas_readings := s1.vs_gas_readings = s1) /\
        (inv_memory_observation focus.inst_opcode /\ EL q1 xs1 = focus ==>
          (!op. MEM op focus.inst_operands ==> eval_operand op u = eval_operand op obs_state) /\
          u.vs_initial_fmp = obs_state.vs_initial_fmp)
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 newlevels
            (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (qpat_x_assum `paths = MAP _ oldcuts` (fn th => rewrite_tac[th]) >>
      simp[Once EQ_SYM_EQ] >>
      qpat_x_assum `oldcuts = _` (fn th => rewrite_tac[th]) >>
      qpat_x_assum `newcuts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (qspecl_then
        [`\k. THE (FLOOKUP ms_tab k)`, `\k. THE (FLOOKUP ms_tab' k)`,
         `\U cuts. FLAT (MAP (\(ai,ds,ei,qi,zi).
           FLAT (MAP (\f. FLAT (U (ai,f))) ds) ++
           FLAT (TAKE qi (U (ai,ei)))) cuts)`,
         `priorcuts`,`p`,`ds`,`d`,`q1`,`z0`,`z1`,`oldcuts`,`newcuts`]
        mp_tac dft_packet_block_cut_aggregate >>
      impl_tac >- (simp[] >> rpt conj_tac >> metis_tac[]) >>
      disch_then (CONJUNCTS_THEN2 mp_tac kall_tac) >> simp[]) >>
  conj_tac
  >- (qspecl_then
        [`\k. THE (FLOOKUP es_tab k)`, `\k. THE (FLOOKUP es_tab' k)`,
         `\U cuts. FLAT (MAP (\(ai,ds,ei,qi,zi).
           FLAT (MAP (\f. FLAT (U (ai,f))) ds) ++
           FLAT (TAKE qi (U (ai,ei)))) cuts)`,
         `priorcuts`,`p`,`ds`,`d`,`q1`,`z0`,`z1`,`oldcuts`,`newcuts`]
        mp_tac dft_packet_block_cut_aggregate >>
      impl_tac >- (simp[] >> rpt conj_tac >> metis_tac[]) >>
      disch_then (CONJUNCTS_THEN2 mp_tac kall_tac) >> simp[]) >>
  conj_tac
  >- (qspecl_then
        [`\k. THE (FLOOKUP ks_tab k)`, `\k. THE (FLOOKUP ks_tab' k)`,
         `\U cuts. FLAT (MAP (\(ai,ds,ei,qi,zi).
           FLAT (MAP (\f. FLAT (U (ai,f))) ds) ++
           FLAT (TAKE qi (U (ai,ei)))) cuts)`,
         `priorcuts`,`p`,`ds`,`d`,`q1`,`z0`,`z1`,`oldcuts`,`newcuts`]
        mp_tac dft_packet_block_cut_aggregate >>
      impl_tac >- (simp[] >> rpt conj_tac >> metis_tac[]) >>
      disch_then (CONJUNCTS_THEN2 mp_tac kall_tac) >> simp[]) >>
  `LENGTH M1 = LENGTH E1 /\ LENGTH M1 = LENGTH K1` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- simp[] >>
     qpat_x_assum `M1 = FLAT (TAKE q1 ms1)` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `E1 = FLAT (TAKE q1 ess1)` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `K1 = FLAT (TAKE q1 ks1)` (fn th => rewrite_tac[th]) >>
     `MAP LENGTH ms1 = MAP LENGTH ess1` by
       (rewrite_tac[MAP_EQ_EVERY2] >> asm_rewrite_tac[]) >>
     `MAP LENGTH ms1 = MAP LENGTH ks1` by
       (rewrite_tac[MAP_EQ_EVERY2] >> asm_rewrite_tac[]) >>
     pure_rewrite_tac[LENGTH_FLAT,MAP_TAKE] >>
     qpat_x_assum `MAP LENGTH ms1 = MAP LENGTH ess1`
       (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `MAP LENGTH ms1 = MAP LENGTH ks1`
       (fn th => rewrite_tac[GSYM th])) >>
  conj_tac
  >- (pure_rewrite_tac[LENGTH_APPEND] >>
      qpat_assum `LENGTH M0 = LENGTH E0` (fn th => rewrite_tac[th]) >>
      qpat_assum `LENGTH Mb = LENGTH Eb` (fn th => rewrite_tac[th]) >>
      qpat_assum `LENGTH M1 = LENGTH E1` (fn th => rewrite_tac[th])) >>
  conj_tac
  >- (pure_rewrite_tac[LENGTH_APPEND] >>
      qpat_assum `LENGTH M0 = LENGTH K0` (fn th => rewrite_tac[th]) >>
      qpat_assum `LENGTH Mb = LENGTH Kb` (fn th => rewrite_tac[th]) >>
      qpat_assum `LENGTH M1 = LENGTH K1` (fn th => rewrite_tac[th])) >>
  `Z = z0 ++ xs /\ EVERY (\i. ~is_terminator i.inst_opcode) z0` by
    (mp_tac (Q.INST [`bb` |-> `bb`, `ps` |-> `ps`, `xs` |-> `xs`]
       dft_packet_block_full_row_shape) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `Z = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `z0 = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  `!F ent. row_eval F C7 sf.fn_name (bb,d,Z) ent =
    (case SND (row_eval F C7 sf.fn_name (bb,d,z0) ent) of
       OK u => (FST (row_eval F C7 sf.fn_name (bb,d,z0) ent) ++
           gas_events_block (F-d) C7 sf.fn_name bb u,
         FOLDR (dft_exec_cons (F-d) C7) OK xs u)
     | r => (FST (row_eval F C7 sf.fn_name (bb,d,z0) ent),r))` by
    (qx_gen_tac `fuel` >> qx_gen_tac `ent` >>
     irule (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND] (BETA_RULE (Q.INST
       [`R` |-> `\z ent. row_eval (fuel:num) (C7:venom_context) sf.fn_name (bb,(d:num),z) ent`,
        `B` |-> `\u. (gas_events_block (fuel-d) C7 sf.fn_name bb u,
           FOLDR (dft_exec_cons (fuel-d) C7) OK xs u)`]
       (SPEC_ALL dft_packet_literal_full_row_extend)))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qexistsl [`C7`,`fuel-d`,`phi_prefix_length bb.bb_instructions`,`sf.fn_name`] >>
         qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `!F H. H = (\u. case FOLDR (dft_exec_cons (F-d) C7) OK xs u of
      OK v => (gas_events_block (F-d) C7 sf.fn_name bb u ++
        FST (row_eval F C7 sf.fn_name (bb1,SUC d,z1) v),
        SND (row_eval F C7 sf.fn_name (bb1,SUC d,z1) v))
    | r => (gas_events_block (F-d) C7 sf.fn_name bb u,r)) ==>
    !ent. rooted_eval F C7 newlevels ent =
    (case SND (rooted_eval F C7 oldlevels ent) of
       OK u => (FST (rooted_eval F C7 oldlevels ent) ++ FST (H u),SND (H u))
     | r => (FST (rooted_eval F C7 oldlevels ent),r))` by
    (qx_gen_tac `fuel` >> qx_gen_tac `H` >> disch_tac >> qx_gen_tac `ent` >>
     qpat_assum `oldlevels = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `newlevels = _` (fn th => pure_rewrite_tac[th]) >>
     irule (Q.SPECL
       [`rooted_eval (fuel:num) (C7:venom_context)`,
        `plan_eval (fuel:num) (C7:venom_context)`,
        `call_setup (C7:venom_context)`,
        `row_eval (fuel:num) (C7:venom_context)`]
       dft_packet_block_rooted_eval_append) >>
     qexistsl [`\u. (gas_events_block (fuel-d) C7 sf.fn_name bb u,
         FOLDR (dft_exec_cons (fuel-d) C7) OK xs u)`,
       `call_setup`,`plan_eval`,`row_eval`] >>
     conj_tac >- (simp[NoAsms] >> first_assum MATCH_ACCEPT_TAC) >>
     conj_tac
     >- (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms]) >>
     qpat_assum `H = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms,FUN_EQ_THM] >> gen_tac >>
     Cases_on `FOLDR (dft_exec_cons (fuel-d) C7) OK xs u` >> simp[NoAsms]) >>
  `EVERY (\i. i.inst_opcode <> PHI) xs1 /\
   EVERY (\i. i.inst_opcode <> PHI) ys1` by
    (qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs1` mp_tac >>
     qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) ys1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >>
     metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bb1.bb_instructions = phi_prefix_length bt1.bb_instructions /\
   eval_phis post bb1.bb_instructions = OK sp1` by
    (qpat_assum `bb1.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `eval_phis post bt1.bb_instructions = _` mp_tac >>
     qpat_assum `bt1.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms,dft_phi_prefix_append,dft_eval_phis_append] >>
     metis_tac[dft_phi_prefix_append,dft_eval_phis_append]) >>
  `?first1. get_instruction bb1 s1.vs_inst_idx = SOME first1` by
    (qpat_assum `get_instruction bt1 s1.vs_inst_idx = _` mp_tac >>
     qpat_assum `bb1.bb_instructions = _` mp_tac >>
     qpat_assum `bt1.bb_instructions = _` mp_tac >>
     qpat_assum `LENGTH xs1 = LENGTH ys1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[get_instruction_def] >>
     metis_tac[]) >>
  `LENGTH z1 < LENGTH (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
   z1 = TAKE (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) z1` by
    (qpat_assum `_ \/ _` mp_tac >>
     qpat_assum `s1 = _` mp_tac >>
     qpat_assum `phi_prefix_length bb1.bb_instructions = _` mp_tac >>
     qpat_assum `bb1.bb_instructions = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[DROP_TAKE,DROP_APPEND,TAKE_TAKE,LENGTH_TAKE] >>
     simp[TAKE_APPEND,TAKE_TAKE]) >>
  `!F gs. Nnew <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gs ==>
    (!t. ?extra. E1 = FST (row_eval F C7 sf.fn_name (bb1,SUC d,z1)
      (post with vs_gas_readings := gs ++ t)) ++ extra) /\
    (!t events u. row_eval F C7 sf.fn_name (bb1,SUC d,z1)
      (post with vs_gas_readings := gs ++ t) = (events,OK u) ==>
      events = E1 /\ u.vs_gas_readings = t /\
      (!t'. row_eval F C7 sf.fn_name (bb1,SUC d,z1)
        (post with vs_gas_readings := gs ++ t') =
        (E1,OK (u with vs_gas_readings := t'))))` by
    (qpat_assum `_ \/ _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac
     >- (rpt gen_tac >> strip_tac >> gvs[] >> simp[]) >>
     map_every qx_gen_tac [`f`,`gs`] >> strip_tac >>
     `?gss. gs = FLAT gss /\
       LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q1 ms1) gss` by
       (irule dft_packet_flat_filling_split >> metis_tac[]) >>
     qpat_x_assum `!F kgss tail. _` (qspec_then `f` mp_tac) >>
     disch_then (qspec_then `gss` mp_tac) >>
     simp[] >> metis_tac[]) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  `N <= fuel /\ SUC d <= fuel` by decide_tac >>
  `?g0 gb g1. gs = g0 ++ gb ++ g1 /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 g0 /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gb /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 g1` by
    (qexistsl [`TAKE (LENGTH M0) gs`,
       `TAKE (LENGTH Mb) (DROP (LENGTH M0) gs)`,
       `DROP (LENGTH Mb) (DROP (LENGTH M0) gs)`] >>
     conj_tac >- metis_tac[TAKE_DROP,APPEND_ASSOC] >>
     qpat_x_assum `LIST_REL _ (M0 ++ Mb ++ M1) gs` mp_tac >>
     disch_then (fn th =>
       assume_tac (Q.SPEC `LENGTH (M0 : bytes32 option list)` (MATCH_MP LIST_REL_TAKE th)) >>
       assume_tac (Q.SPEC `LENGTH (M0 : bytes32 option list)` (MATCH_MP LIST_REL_DROP th))) >>
     qpat_x_assum `LIST_REL _ (DROP _ _) _` (fn th =>
       assume_tac (Q.SPEC `LENGTH (Mb : bytes32 option list)` (MATCH_MP LIST_REL_TAKE th)) >>
       assume_tac (Q.SPEC `LENGTH (Mb : bytes32 option list)` (MATCH_MP LIST_REL_DROP th))) >>
     ntac 3 (pop_assum mp_tac) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND] >>
     disch_tac >> disch_tac >> disch_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`N` |-> `N`, `d` |-> `d`, `C7` |-> `C7`,
    `sf` |-> `sf`, `bb` |-> `bb`, `ps` |-> `ps`, `xs` |-> `xs`,
    `be` |-> `be`, `post` |-> `post`, `a` |-> `p`,
    `Mb` |-> `Mb`, `Eb` |-> `Eb`, `Kb` |-> `Kb`]
    (SPEC_ALL dft_packet_closed_body_boundary)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => assume_tac th >> mp_tac th) >>
  disch_then (qspecl_then [`fuel`,`gb`,`g1 ++ tail`,
    `be with vs_gas_readings := gb ++ g1 ++ tail`,
    `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
      (be with vs_gas_readings := gb ++ g1 ++ tail)`] mp_tac) >>
  (impl_tac >- (simp[NoAsms,APPEND_ASSOC] >>
    conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`fuel`,`g0`,`gb ++ g1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (qpat_assum `newlevels = _` (fn th => pure_rewrite_tac[th]) >>
      irule (INST_TYPE [alpha |-> ``:string # num``] dft_packet_block_append_validity) >>
      ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`\u. (gas_events_block (fuel-d) C7 sf.fn_name bb u,
        FOLDR (dft_exec_cons (fuel-d) C7) OK xs u)`,
        `call_setup`,`plan_eval`,`plan_ok`,`rooted_eval`,`row_eval`,
        `be with vs_gas_readings := gb ++ g1 ++ tail`,`z0`] >>
      conj_tac
      >- (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
          qpat_assum `!v. FOLDR _ _ _ _ = OK v ==> _` drule >>
          strip_tac >> qpat_x_assum `v = _` SUBST_ALL_TAC >>
          simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qpat_assum `oldlevels = _` (fn th => pure_rewrite_tac[GSYM th]) >>
          qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
          qpat_assum `!F gs tail ev u. N <= F /\ LIST_REL _ M0 gs /\ rooted_eval _ _ _ _ = _ ==> _`
            (qspecl_then [`fuel`,`g0`,`gb ++ g1 ++ tail`] mp_tac) >>
          qpat_assum `N <= fuel` mp_tac >>
          qpat_assum `LIST_REL _ M0 g0` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> simp[APPEND_ASSOC] >> metis_tac[]) >>
      conj_tac >- (simp[NoAsms] >> first_assum MATCH_ACCEPT_TAC) >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `oldlevels = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
      qpat_assum `levels_ok fuel C7 oldlevels _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[APPEND_ASSOC]) >>
  qabbrev_tac `A = \t. rooted_eval fuel C7 oldlevels
    (root_entry with vs_gas_readings := g0 ++ t)` >>
  qabbrev_tac `B = \t. (gas_events_block (fuel-d) C7 sf.fn_name bb
      (be with vs_gas_readings := gb ++ t),
    FOLDR (dft_exec_cons (fuel-d) C7) OK xs
      (be with vs_gas_readings := gb ++ t))` >>
  qabbrev_tac `H = \t. row_eval fuel C7 sf.fn_name (bb1,SUC d,z1)
    (post with vs_gas_readings := g1 ++ t)` >>
  qabbrev_tac `D = \t. rooted_eval fuel C7 newlevels
    (root_entry with vs_gas_readings := gs ++ t)` >>
  `!t. ?extra. E0 = FST (A t) ++ extra` by
    (gen_tac >> simp[Abbr `A`,NoAsms] >>
     qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`g0`,`t`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  `!t e u. A t = (e,OK u) ==>
    e = E0 /\ u = be with vs_gas_readings := t /\
    (!t'. A t' = (E0,OK (be with vs_gas_readings := t')))` by
    (simp[Abbr `A`,NoAsms] >> rpt gen_tac >> strip_tac >>
     `u = be with vs_gas_readings := t` by
       (qpat_assum `!F gs tail ev u. N <= F /\ LIST_REL _ M0 gs /\ rooted_eval _ _ _ _ = _ ==> _`
          (qspecl_then [`fuel`,`g0`,`t`] mp_tac) >>
        disch_then (qspecl_then [`e`,`u`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`g0`,`t`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `rooted_eval fuel C7 oldlevels _ = (e,OK u)`
       (fn th => simp[NoAsms,th]) >>
     strip_tac >> simp[NoAsms] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_x_assum `u = _` SUBST_ALL_TAC >> simp[NoAsms]) >>
  `!t. ?extra. Eb = FST (B t) ++ extra` by
    (gen_tac >> simp[Abbr `B`,NoAsms] >>
     qpat_assum `!F gs tail s r. _` (qspecl_then
       [`fuel`,`gb`,`t`,`be with vs_gas_readings := gb ++ t`,
        `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
          (be with vs_gas_readings := gb ++ t)`] mp_tac) >>
     (impl_tac >- (simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC)) >>
     metis_tac[]) >>
  `!t e u. B t = (e,OK u) ==>
    e = Eb /\ u = post with vs_gas_readings := t /\
    (!t'. B t' = (Eb,OK (post with vs_gas_readings := t')))` by
    (simp[Abbr `B`,NoAsms] >> rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`N` |-> `N`, `d` |-> `d`, `C7` |-> `C7`,
       `sf` |-> `sf`, `bb` |-> `bb`, `ps` |-> `ps`, `xs` |-> `xs`,
       `be` |-> `be`, `post` |-> `post`, `a` |-> `p`,
       `Mb` |-> `Mb`, `Eb` |-> `Eb`, `Kb` |-> `Kb`]
       (SPEC_ALL dft_packet_closed_body_tail)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspecl_then [`fuel`,`gb`,`t`,
       `be with vs_gas_readings := gb ++ t`,
       `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
          (be with vs_gas_readings := gb ++ t)`,`u`] mp_tac) >>
     (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `!F gs tail s r. _` (qspecl_then
       [`fuel`,`gb`,`t`,`be with vs_gas_readings := gb ++ t`,
        `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
          (be with vs_gas_readings := gb ++ t)`] mp_tac) >>
     (impl_tac >- (simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[NoAsms] >> rpt strip_tac >> metis_tac[]) >>
  `(!t. ?extra. E1 = FST (H t) ++ extra) /\
   (!t e u. H t = (e,OK u) ==> e = E1 /\ u.vs_gas_readings = t /\
    (!t'. H t' = (E1,OK (u with vs_gas_readings := t'))))` by
    (simp[Abbr `H`,NoAsms] >>
     qpat_assum `!F gs. Nnew <= F /\ LIST_REL _ M1 gs ==> _`
       (qspecl_then [`fuel`,`g1`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!t. D t =
    (case A (gb ++ g1 ++ t) of
       (ea,OK ua) =>
         (case B (g1 ++ t) of
            (eb,OK ub) => (ea ++ eb ++ FST (H t),SND (H t))
          | (eb,rb) => (ea ++ eb,rb))
     | (ea,ra) => (ea,ra))` by
    (gen_tac >>
     qpat_assum `!F H. H = _ ==> _`
       (qspecl_then [`fuel`,`\u. case FOLDR (dft_exec_cons (fuel-d) C7) OK xs u of
          OK v => (gas_events_block (fuel-d) C7 sf.fn_name bb u ++
            FST (row_eval fuel C7 sf.fn_name (bb1,SUC d,z1) v),
            SND (row_eval fuel C7 sf.fn_name (bb1,SUC d,z1) v))
        | r => (gas_events_block (fuel-d) C7 sf.fn_name bb u,r)`] mp_tac) >>
     rewrite_tac[] >>
     disch_then (qspec_then `root_entry with vs_gas_readings := gs ++ t` mp_tac) >>
     qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
     disch_then (mk_asm "append") >>
     Cases_on `A (gb ++ g1 ++ t)` >> rename1 `A _ = (ea,ra)` >>
     Cases_on `ra`
     >- (qpat_assum `!t e u. A t = _ ==> _` drule >> strip_tac >>
         Cases_on `B (g1 ++ t)` >> rename1 `B _ = (eb,rb)` >>
         Cases_on `rb`
         >- (qpat_assum `!t e u. B t = _ ==> _` drule >> strip_tac >>
             asm "append" mp_tac >>
             qpat_assum `A _ = _` mp_tac >> qpat_assum `B _ = _` mp_tac >>
             qpat_assum `v = _` mp_tac >> qpat_assum `v' = _` mp_tac >>
             simp[Abbr `A`,Abbr `B`,Abbr `H`,Abbr `D`,NoAsms,APPEND_ASSOC] >>
             qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             rpt strip_tac >> gvs[APPEND_ASSOC]) >>
         asm "append" mp_tac >>
         qpat_assum `A _ = _` mp_tac >> qpat_assum `B _ = _` mp_tac >>
         qpat_assum `v = _` mp_tac >>
         simp[Abbr `A`,Abbr `B`,Abbr `H`,Abbr `D`,NoAsms,APPEND_ASSOC] >>
         qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[APPEND_ASSOC]) >>
     asm "append" mp_tac >> qpat_assum `A _ = _` mp_tac >>
     simp[Abbr `A`,Abbr `D`,NoAsms,APPEND_ASSOC] >>
     qpat_assum `gs = _` (fn th => pure_rewrite_tac[th,APPEND_ASSOC]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`A`,`B`,`H`,`D`,`gb`,`g1`,`E0`,`Eb`,`E1`,`be`,`post`]
    dft_packet_block_append_transport) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => assume_tac th >> mp_tac (Q.SPEC `tail` th)) >>
  strip_tac >>
  conj_tac >- metis_tac[] >>
  `!events r. D tail = (events,r) /\ ~(?u. r = OK u) ==>
    run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = r /\
    gas_events_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = events` by
    suspend "stopped" >>
  Cases_on `D tail` >> rename1 `D tail = (events,result)` >>
  qpat_assum `D tail = _` mp_tac >>
  qpat_assum `Abbrev (D = _)`
    (fn th => simp[NoAsms,REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  disch_then (mk_asm "current") >>
  Cases_on `result` >> simp[NoAsms,markerLib.L "current"]
  >- suspend "success" >>
  first_x_assum irule >> simp[NoAsms]
QED

Resume dft_packet_block_rooted_append[success]:
  rename1 `D tail = (events,OK u)` >>
  qpat_x_assum `!e v. (events,OK u) = _ ==> _`
    (qspecl_then [`events`,`u`] mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  conj_tac >- suspend "success_trace" >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `!t'. D t' = _` (qspec_then `tail'` mp_tac) >>
      simp[Abbr `D`,NoAsms]) >>
  `row_eval fuel C7 sf.fn_name (bb1,SUC d,z1)
    (post with vs_gas_readings := g1 ++ tail) = (E1,OK u)` by
    (qpat_assum `H tail = _` mp_tac >> simp[Abbr `H`,NoAsms]) >>
  conj_tac
  >- (strip_tac >> qpat_assum `_ \/ _` mp_tac >>
      qpat_assum `Nnew <= fuel` mp_tac >>
      qpat_assum `LIST_REL _ M1 g1` mp_tac >>
      qpat_assum `row_eval fuel C7 _ _ _ = _` mp_tac >>
      qpat_assum `s1.vs_inst_idx < LENGTH ps1` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      qpat_x_assum `_ \/ _` strip_assume_tac
      >- (gvs[] >> metis_tac[]) >> gvs[]) >>
  strip_tac >>
  qpat_assum `!F gs tail events u. _ ==> (!op. _) /\ _`
    (qspecl_then [`fuel`,`g1`,`tail`,`E1`,`u`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_block_rooted_append[success_trace]:
  `rooted_eval fuel C7 oldlevels
    (root_entry with vs_gas_readings := g0 ++ gb ++ g1 ++ tail) =
    (E0,OK (be with vs_gas_readings := gb ++ g1 ++ tail))` by
    (qpat_assum `A (gb ++ g1 ++ tail) = _` mp_tac >>
     simp[Abbr `A`,NoAsms]) >>
  `FOLDR (dft_exec_cons (fuel-d) C7) OK xs
    (be with vs_gas_readings := gb ++ g1 ++ tail) =
    OK (post with vs_gas_readings := g1 ++ tail)` by
    (qpat_assum `B (g1 ++ tail) = _` mp_tac >>
     simp[Abbr `B`,NoAsms]) >>
  `!f owner b s k t.
    s.vs_inst_idx + k <= LENGTH b.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) /\
    FOLDR (dft_exec_cons f C7) OK
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + k /\
    exec_block f C7 b s = exec_block f C7 b t /\
    gas_events_block f C7 owner b s =
      gas_events_block f C7 owner
        (b with bb_instructions := TAKE (s.vs_inst_idx + k) b.bb_instructions) s ++
      gas_events_block f C7 owner b t` by
    (rpt gen_tac >> strip_tac >>
     mp_tac dft_packet_block_prefix_operational >>
     disch_then (qspecl_then [`f`,`C7`,`owner`,`b`,`s`,`k`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[NoAsms,LET_THM] >> metis_tac[]) >>
  drule_at (Pat `levels_ok _ _ _ _ _ _ _ _ _`)
    dft_packet_rooted_success_operational >>
  disch_then (drule_at (Pat `oldlevels = _`)) >>
  disch_then (drule_at (Pat `row_eval = _`)) >>
  disch_then (drule_at (Pat `plan_eval = _`)) >>
  disch_then (drule_at (Pat `call_setup = _`)) >>
  disch_then (drule_at (Pat `rooted_eval = _`)) >>
  disch_then (drule_at (Pat `plan_ok = _`)) >>
  disch_then (drule_at (Pat `levels_ok = _`)) >>
  disch_then (qspecl_then [`E0`,`be with vs_gas_readings := gb ++ g1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!f owner b s k t. _` drule_all >> simp[NoAsms]) >>
    qpat_assum `rooted_eval fuel C7 oldlevels _ = _` mp_tac >>
    simp[NoAsms,APPEND_ASSOC])) >>
  strip_tac >>
  `lookup_block be.vs_current_bb sf.fn_blocks = SOME bb` by
    (qpat_assum `lookup_block (_ with vs_gas_readings := _).vs_current_bb _ = _`
       mp_tac >> simp[NoAsms]) >>
  `get_instruction bb be.vs_inst_idx = SOME (EL (LENGTH z0) Z)` by
    (qpat_assum `(be with vs_gas_readings := _).vs_inst_idx = _` mp_tac >>
     qpat_assum `be.vs_inst_idx = LENGTH ps` mp_tac >>
     qpat_assum `bb.bb_instructions = ps ++ xs` mp_tac >>
     qpat_assum `xs <> []` mp_tac >>
     qpat_assum `Z = DROP _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `0 < LENGTH xs` by metis_tac[LENGTH_NIL,NOT_ZERO_LT_ZERO] >>
     `LENGTH z0 + phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
       (gvs[] >> decide_tac) >>
     gvs[] >> simp[get_instruction_def,listTheory.EL_DROP,ADD_COMM]) >>
  qpat_assum `exec_result_CASE (SND (rooted_eval fuel C7 oldlevels _)) _ _ _ _ _` mp_tac >>
  qpat_assum `rooted_eval fuel C7 oldlevels _ = (E0,OK _)`
    (fn th => simp[NoAsms,REWRITE_RULE[APPEND_ASSOC] th,APPEND_ASSOC]) >> strip_tac >>
  qpat_assum `!v. FOLDR _ _ _ _ = OK v ==> _`
    (qspec_then `post with vs_gas_readings := g1 ++ tail` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `row_eval fuel C7 sf.fn_name (bb1,SUC d,z1)
    (post with vs_gas_readings := g1 ++ tail) = (E1,OK u)` by
    (qpat_assum `H tail = _` mp_tac >> simp[Abbr `H`,NoAsms]) >>
  qpat_assum `gs = _` (fn th => pure_rewrite_tac[th]) >>
  irule dft_packet_block_append_trace >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `LENGTH M0 = LENGTH K0` mp_tac >>
    qpat_assum `LIST_REL _ M0 g0` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  conj_tac >- (qpat_assum `LENGTH M1 = LENGTH K1` mp_tac >>
    qpat_assum `LIST_REL _ M1 g1` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  conj_tac >- (qpat_assum `LENGTH Mb = LENGTH Kb` mp_tac >>
    qpat_assum `LIST_REL _ Mb gb` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  goal_assum (drule_at (Pat `trace_blocks [] 0 _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `get_instruction bb1 _ = _`)) >>
  goal_assum (drule_at (Pat `eval_phis post _ = _`)) >>
  goal_assum (drule_at (Pat `bb1.bb_instructions = _`)) >>
  qexistsl [`\entry. row_eval fuel C7 sf.fn_name (bb1,SUC d,z1) entry`,
    `E1`,`first1`,`q1`,`s1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `exec_block (fuel-d) C7 bb _ = _` mp_tac >>
    qpat_assum `FOLDR (dft_exec_cons (fuel-d) C7) OK xs _ = OK _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `s1 = _` mp_tac >>
    qpat_assum `phi_prefix_length bb1.bb_instructions = _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `_ \/ _` strip_assume_tac
  >- (disj1_tac >>
      `g1 = []` by
        (qpat_assum `M1 = []` mp_tac >> qpat_assum `LIST_REL _ M1 g1` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
      `u = s1 with vs_gas_readings := tail` by
        (qpat_assum `!F t. Nnew <= F ==> _` (qspecl_then [`fuel`,`tail`] mp_tac) >>
         qpat_assum `row_eval fuel C7 _ _ _ = _` mp_tac >>
         qpat_assum `Nnew <= fuel` mp_tac >>
         qpat_assum `g1 = []` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  `?gss. g1 = FLAT gss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q1 ms1) gss` by
    (irule dft_packet_flat_filling_split >>
     qpat_assum `M1 = FLAT _` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!F kgss tail. _` (qspecl_then [`fuel`,`gss`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `row_eval fuel C7 _ _ _ = _` mp_tac >>
  qpat_assum `g1 = FLAT gss` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  qpat_x_assum `!events u. _` (qspecl_then [`E1`,`u`] mp_tac) >>
  (impl_tac >- (gvs[])) >> strip_tac >>
  qpat_assum `g1 = FLAT gss` (fn th => pure_rewrite_tac[th])
  >- (qpat_assum `SND _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_assum `row_eval fuel C7 _ _ _ = _` mp_tac >>
      qpat_assum `g1 = FLAT gss` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  first_assum ACCEPT_TAC
QED

Resume dft_packet_block_rooted_append[stopped]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "stopcur") assume_tac) >>
  Cases_on `A (gb ++ g1 ++ tail)` >> rename1 `A _ = (ea,ra)` >>
  reverse (Cases_on `?u. ra = OK u`)
  >- (`D tail = (ea,ra)` by
        (qpat_assum `!t. D t = _` (qspec_then `tail` mp_tac) >>
         qpat_assum `A _ = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `~(?u. ra = OK u)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
         Cases_on `ra` >> gvs[]) >>
      qpat_assum `exec_result_CASE (SND (rooted_eval fuel C7 oldlevels _)) _ _ _ _ _` mp_tac >>
      qpat_assum `A _ = _` mp_tac >>
      qpat_assum `D tail = (ea,ra)` mp_tac >>
      asm "stopcur" mp_tac >>
      qpat_assum `~(?u. ra = OK u)` mp_tac >>
      qpat_assum `gs = _` mp_tac >>
      simp[Abbr `A`,NoAsms,APPEND_ASSOC] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      Cases_on `ra` >> gvs[APPEND_ASSOC]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `ra = OK _` SUBST_ALL_TAC >>
  qpat_assum `!t e u. A t = _ ==> _` drule >> strip_tac >>
  `rooted_eval fuel C7 oldlevels
    (root_entry with vs_gas_readings := g0 ++ gb ++ g1 ++ tail) =
    (E0,OK (be with vs_gas_readings := gb ++ g1 ++ tail))` by
    (qpat_assum `A _ = _` mp_tac >>
     qpat_assum `ea = E0` mp_tac >> qpat_assum `u = _` mp_tac >>
     simp[Abbr `A`,NoAsms]) >>
  `!f owner b s k t.
    s.vs_inst_idx + k <= LENGTH b.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) /\
    FOLDR (dft_exec_cons f C7) OK
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + k /\
    exec_block f C7 b s = exec_block f C7 b t /\
    gas_events_block f C7 owner b s =
      gas_events_block f C7 owner
        (b with bb_instructions := TAKE (s.vs_inst_idx + k) b.bb_instructions) s ++
      gas_events_block f C7 owner b t` by
    (rpt gen_tac >> strip_tac >>
     mp_tac dft_packet_block_prefix_operational >>
     disch_then (qspecl_then [`f`,`C7`,`owner`,`b`,`s`,`k`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[NoAsms,LET_THM] >> metis_tac[]) >>
  drule_at (Pat `levels_ok _ _ _ _ _ _ _ _ _`)
    dft_packet_rooted_success_operational >>
  disch_then (drule_at (Pat `oldlevels = _`)) >>
  disch_then (drule_at (Pat `row_eval = _`)) >>
  disch_then (drule_at (Pat `plan_eval = _`)) >>
  disch_then (drule_at (Pat `call_setup = _`)) >>
  disch_then (drule_at (Pat `rooted_eval = _`)) >>
  disch_then (drule_at (Pat `plan_ok = _`)) >>
  disch_then (drule_at (Pat `levels_ok = _`)) >>
  disch_then (qspecl_then [`E0`,`be with vs_gas_readings := gb ++ g1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!f owner b s k t. _` drule_all >> simp[NoAsms]) >>
    qpat_assum `rooted_eval fuel C7 oldlevels _ = _` mp_tac >>
    simp[NoAsms,APPEND_ASSOC])) >>
  strip_tac >>
  Cases_on `B (g1 ++ tail)` >> rename1 `B _ = (eb,rb)` >>
  reverse (Cases_on `?v. rb = OK v`)
  >- (`?msg. rb = Error msg` by
        (qpat_assum `~(?v. _ = OK v) ==> ?msg. _ = Error msg` mp_tac >>
         qpat_assum `B _ = _` mp_tac >>
         qpat_assum `~(?v. rb = OK v)` mp_tac >>
         simp[Abbr `B`,NoAsms] >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pairTheory.PAIR_EQ]) >>
      qpat_x_assum `rb = Error _` SUBST_ALL_TAC >>
      `D tail = (E0 ++ eb,Error msg)` by
        (qpat_assum `!t. D t = _` (qspec_then `tail` mp_tac) >>
         qpat_assum `A _ = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `B _ = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms] >> metis_tac[]) >>
      `exec_block (fuel-d) C7 bb (be with vs_gas_readings := gb ++ g1 ++ tail) = Error msg` by
        (qpat_assum `exec_block (fuel-d) C7 bb _ = _` mp_tac >>
         qpat_assum `B _ = _` mp_tac >> simp[Abbr `B`,NoAsms]) >>
      `gas_events_block (fuel-d) C7 sf.fn_name bb
        (be with vs_gas_readings := gb ++ g1 ++ tail) = eb` by
        (qpat_assum `B _ = _` mp_tac >> simp[Abbr `B`,NoAsms]) >>
      qpat_assum `run_blocks (fuel-0) _ _ _ = _` mp_tac >>
      qpat_assum `gas_events_blocks (fuel-0) _ _ _ = _` mp_tac >>
      qpat_assum `!msg. K' (Error msg) = _` (qspec_then `msg` mp_tac) >>
      qpat_assum `exec_block (fuel-d) C7 bb _ = Error msg` mp_tac >>
      qpat_assum `gas_events_block (fuel-d) C7 _ _ _ = eb` mp_tac >>
      qpat_assum `D tail = (E0 ++ eb,Error msg)` mp_tac >>
      asm "stopcur" mp_tac >> qpat_assum `gs = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[APPEND_ASSOC]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `rb = OK _` SUBST_ALL_TAC >>
  qpat_assum `!t e u. B t = _ ==> _` drule >> strip_tac >>
  `rooted_eval fuel C7 (pre ++ [(sf,rows ++ [(bb,d,Z)],NONE)])
    (root_entry with vs_gas_readings := gs ++ tail) =
      (E0 ++ Eb,OK (post with vs_gas_readings := g1 ++ tail))` by
    (`rooted_eval fuel C7 (pre ++ [(sf,rows ++ [(bb,d,Z)],NONE)])
      (root_entry with vs_gas_readings := gs ++ tail) =
      (case SND (rooted_eval fuel C7 oldlevels
         (root_entry with vs_gas_readings := gs ++ tail)) of
         OK v => (FST (rooted_eval fuel C7 oldlevels
           (root_entry with vs_gas_readings := gs ++ tail)) ++
           gas_events_block (fuel-d) C7 sf.fn_name bb v,
           FOLDR (dft_exec_cons (fuel-d) C7) OK xs v)
       | r => (FST (rooted_eval fuel C7 oldlevels
           (root_entry with vs_gas_readings := gs ++ tail)),r))` by
       (qpat_assum `oldlevels = _` (fn th => pure_rewrite_tac[th]) >>
        irule (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND] (BETA_RULE (Q.SPECL [`rooted_eval (fuel:num) (C7:venom_context)`,
          `plan_eval (fuel:num) (C7:venom_context)`,
          `call_setup (C7:venom_context)`,`row_eval (fuel:num) (C7:venom_context)`,
          `\v. (gas_events_block (fuel-d) C7 sf.fn_name bb v,
            FOLDR (dft_exec_cons (fuel-d) C7) OK xs v)`]
          dft_packet_rooted_row_extend))) >>
        qexistsl [`call_setup`,`plan_eval`,`row_eval`] >>
        conj_tac >- first_assum MATCH_ACCEPT_TAC >>
        conj_tac
        >- (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
        qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
     pop_assum mp_tac >>
     qpat_assum `rooted_eval fuel C7 oldlevels _ = (E0,OK _)` mp_tac >>
     qpat_assum `B _ = _` mp_tac >>
     qpat_assum `eb = Eb` mp_tac >> qpat_assum `v = _` mp_tac >>
     qpat_assum `gs = _` mp_tac >>
     simp[Abbr `B`,NoAsms,APPEND_ASSOC] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  drule_at (Pat `levels_ok _ _ _ _ _ _ _ _ _`)
    dft_packet_block_rooted_operational >>
  disch_then (drule_at (Pat `oldlevels = _`)) >>
  disch_then (drule_at (Pat `row_eval = _`)) >>
  disch_then (drule_at (Pat `plan_eval = _`)) >>
  disch_then (drule_at (Pat `call_setup = _`)) >>
  disch_then (drule_at (Pat `rooted_eval = _`)) >>
  disch_then (drule_at (Pat `plan_ok = _`)) >>
  disch_then (drule_at (Pat `levels_ok = _`)) >>
  disch_then (qspecl_then [`Z`,`E0 ++ Eb`,
    `post with vs_gas_readings := g1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!f owner b s k t. _` drule_all >> simp[NoAsms]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- decide_tac >>
    conj_tac
    >- (qpat_assum `rooted_eval fuel C7 (pre ++ _) _ = _` mp_tac >>
        qpat_assum `gs = _` mp_tac >> simp[NoAsms,APPEND_ASSOC]) >>
    simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `D tail = (E0 ++ Eb ++ FST (H tail),SND (H tail))` by
    (qpat_assum `!t. D t = _` (qspec_then `tail` mp_tac) >>
     qpat_assum `A _ = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `B _ = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ea = E0` mp_tac >> qpat_assum `eb = Eb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `~(?w. SND (H tail) = OK w)` by
    (asm "stopcur" mp_tac >>
     qpat_assum `D tail = (E0 ++ Eb ++ _,_)` mp_tac >>
     qpat_assum `~(?u. r = OK u)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  qpat_assum `_ \/ _` strip_assume_tac
  >- (qpat_assum `!F t. Nnew <= F ==> _` (qspecl_then [`fuel`,`g1 ++ tail`] mp_tac) >>
      qpat_assum `Nnew <= fuel` mp_tac >>
      qpat_assum `~(?w. SND (H tail) = OK w)` mp_tac >>
      simp[Abbr `H`,NoAsms] >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `phi_prefix_length bb1.bb_instructions = LENGTH ps1 /\
   z1 = TAKE q1 xs1` by
    (qpat_assum `s1 = _` mp_tac >>
     qpat_assum `s1.vs_inst_idx = LENGTH ps1` mp_tac >>
     qpat_assum `phi_prefix_length bb1.bb_instructions = _` mp_tac >>
     qpat_assum `z1 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `eval_phis (post with vs_gas_readings := g1 ++ tail) bb1.bb_instructions =
    OK (sp1 with vs_gas_readings := g1 ++ tail)` by
    (mp_tac (Q.INST [`gs` |-> `g1 ++ tail`,`s` |-> `post`,
       `insts` |-> `bb1.bb_instructions`] dftGasFromListRestoreTheory.eval_phis_restore) >>
     qpat_assum `eval_phis post bb1.bb_instructions = OK sp1` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `eval_phis (post with vs_gas_readings := g1 ++ tail) bb1.bb_instructions` >>
     simp[dftGasFromListRestoreTheory.restore_rel_def]) >>
  `H tail =
    (gas_events_block (fuel-SUC d) C7 sf.fn_name
      (bb1 with bb_instructions := TAKE (LENGTH ps1 + q1) bb1.bb_instructions)
      (s1 with vs_gas_readings := g1 ++ tail),
     FOLDR (dft_exec_cons (fuel-SUC d) C7) OK (TAKE q1 xs1)
      (s1 with vs_gas_readings := g1 ++ tail))` by
    (simp[Abbr `H`,NoAsms] >>
     qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `eval_phis (post with vs_gas_readings := g1 ++ tail) bb1.bb_instructions = _`
       (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `s1 = _` mp_tac >>
     qpat_assum `phi_prefix_length bb1.bb_instructions = phi_prefix_length _` mp_tac >>
     qpat_assum `phi_prefix_length bb1.bb_instructions = LENGTH ps1` mp_tac >>
     qpat_assum `z1 = TAKE q1 xs1` mp_tac >>
     qpat_assum `bb1.bb_instructions = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[TAKE_APPEND,TAKE_TAKE,TAKE_LENGTH_TOO_LONG]) >>
  qpat_assum `run_blocks (fuel-0) _ _ _ = SND (K'' _)`
    (assume_tac o REWRITE_RULE [SUB_0]) >>
  drule_at (Pat `run_blocks _ _ _ _ = _`) dft_packet_block_fresh_prefix_stop >>
  disch_then (qspec_then `E0 ++ Eb` mp_tac) >>
  disch_then (qspecl_then [`bb1`,`sp1 with vs_gas_readings := g1 ++ tail`,
    `s1 with vs_gas_readings := g1 ++ tail`,`q1`,`SND (H tail)`] mp_tac) >>
  (impl_tac >- (conj_tac >- decide_tac >>
    conj_tac >- (qpat_assum `gas_events_blocks (fuel-0) _ _ _ = _` mp_tac >> simp[NoAsms]) >>
    ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (qpat_assum `s1 = _` mp_tac >>
      qpat_assum `phi_prefix_length bb1.bb_instructions = phi_prefix_length _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
    conj_tac >- (qpat_assum `s1.vs_inst_idx = LENGTH ps1` mp_tac >>
      qpat_assum `q1 < LENGTH xs1` mp_tac >>
      qpat_assum `bb1.bb_instructions = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
    conj_tac >- (qpat_assum `s1.vs_inst_idx = LENGTH ps1` (fn th => simp[NoAsms,th]) >>
      qpat_assum `bb1.bb_instructions = _` (fn th => simp[NoAsms,th]) >>
      simp[NoAsms,DROP_LENGTH_APPEND,EVERY_CONJ] >> conj_tac >- first_assum ACCEPT_TAC >>
      simp[EVERY_EL,LENGTH_TAKE] >> rpt strip_tac >>
      qpat_assum `!r. r < q1 ==> (EL r xs1).inst_opcode <> INVOKE`
        (qspec_then `n` mp_tac) >>
      qpat_assum `(EL n (TAKE q1 xs1)).inst_opcode = INVOKE` mp_tac >>
      qpat_assum `n < q1` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[EL_TAKE]) >>
    conj_tac >- (qpat_assum `s1.vs_inst_idx = LENGTH ps1` (fn th => simp[NoAsms,th]) >>
      qpat_assum `bb1.bb_instructions = _` (fn th => simp[NoAsms,th]) >>
      qpat_assum `H tail = _` (fn th => simp[NoAsms,th,DROP_LENGTH_APPEND])) >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_assum `run_blocks fuel C7 root_sf _ = SND (H tail)` mp_tac >>
  qpat_assum `gas_events_blocks fuel C7 root_sf _ = E0 ++ Eb ++ _` mp_tac >>
  qpat_assum `H tail = _` mp_tac >>
  qpat_assum `D tail = (E0 ++ Eb ++ _,_)` mp_tac >>
  asm "stopcur" mp_tac >>
  qpat_assum `gs = _` mp_tac >>
  qpat_assum `s1.vs_inst_idx = LENGTH ps1` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[APPEND_ASSOC] >>
  rpt strip_tac >> gvs[]
QED

Finalise dft_packet_block_rooted_append
