Theory dftPacketBlockRootedCertificate
Ancestors
  dftPacketBlockRootedAppend dftPacketBlockAppendShape
  dftPacketBlockAppendSemantics dftPacketBlockAppendNative
  dftPacketLiteralFullRowExtend dftPacketClosedBodyBoundary
  dftPacketBlockCutAggregate dftPacketBlockFreshEntry
  dftPacketFreshSingletonNormalize dftPacketBlockRootedOperational
  dftPacketRootedPlainStop dftPacketOperationalPrefix
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
  FAIL_TAC "old"
QED
