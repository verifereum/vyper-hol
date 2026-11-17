Theory dftPacketPseudoFreshCut
Ancestors
  dftPacketLiteralRowExtend dftPacketPseudoSegment
  dftPacketRootedSegmentStop dftPacketSameLevelCompose dftPacketLastRowValidity
  dftPacketPseudoCursor dftGasFromListReadings dftRunRel
  dftIndexedExec gasEvents frameGasEvents venomExecSemantics
  venomInst venomState list rich_list arithmetic

Theorem dft_packet_pseudo_fresh_cut:
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
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  l = phi_prefix_length bb.bb_instructions /\
  l <= k /\ k < LENGTH ps /\ s.vs_inst_idx = k /\
  lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
  step_inst g C8 (EL k ps) s = OK t /\
  s1 = t with vs_inst_idx := SUC k /\
  z0 = DROP l (TAKE k ps) /\
  ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(p,d,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  ((SUC k < LENGTH ps /\ q = 0 /\ z1 = DROP l (TAKE (SUC k) ps) /\
    M1 = [] /\ E1 = [] /\ K1 = []) \/
   (SUC k = LENGTH ps /\ q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q ==> (EL r xs).inst_opcode <> INVOKE) /\
    z1 = DROP l ps ++ TAKE q xs /\
    M1 = FLAT (TAKE q ms) /\ E1 = FLAT (TAKE q ess) /\ K1 = FLAT (TAKE q ks))) /\
  cuts0 = cut_pre ++ [(p,ds,d,0,z0)] /\
  cuts1 = cut_pre ++ [(p,ds,d,q,z1)] /\
  paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts0 /\
  levels0 = level_pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)] /\
  levels1 = level_pre ++ [(sf,rows ++ [(bb,d,z1)],NONE)] /\
  LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs ==>
    levels_ok F C7 levels0 paths incoming root_sf
      (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 = FST (rooted_eval F C7 levels0
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels0
      (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels0
          (root_entry with vs_gas_readings := gs ++ tail)) = E0 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,d,(EL (LENGTH z0)
              (DROP l bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z0) (DROP l bb.bb_instructions),u)] ++ after /\
          trace_gas before = ZIP (K0,gs)) /\
        (!tail'. rooted_eval F C7 levels0
          (root_entry with vs_gas_readings := gs ++ tail') =
            (E0,OK (u with vs_gas_readings := tail'))) /\
        u with vs_gas_readings := s.vs_gas_readings = s
    | stopped =>
        run_blocks F C7 root_sf
          (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf
          (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels0
            (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  LENGTH (M0 ++ M1) = LENGTH (E0 ++ E1) /\
  LENGTH (M0 ++ M1) = LENGTH (K0 ++ K1) /\
  !F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (M0 ++ M1) gs ==>
    levels_ok F C7 levels1 (MAP (\(ai,ds,ei,qi,zi). ai) cuts1) incoming root_sf
      (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 ++ E1 = FST (rooted_eval F C7 levels1
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels1
      (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels1
          (root_entry with vs_gas_readings := gs ++ tail)) = E0 ++ E1 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,d,(EL (LENGTH z1)
              (DROP l bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z1) (DROP l bb.bb_instructions),u)] ++ after /\
          trace_gas before = ZIP (K0 ++ K1,gs)) /\
        (!tail'. rooted_eval F C7 levels1
          (root_entry with vs_gas_readings := gs ++ tail') =
            (E0 ++ E1,OK (u with vs_gas_readings := tail'))) /\
        (SUC k < LENGTH ps ==> u with vs_gas_readings := s1.vs_gas_readings = s1)
    | stopped =>
        run_blocks F C7 root_sf
          (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf
          (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels1
            (root_entry with vs_gas_readings := gs ++ tail)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `segment = [EL k ps] ++ TAKE q xs` >>
  `z1 = z0 ++ segment /\
   LENGTH z1 < LENGTH (DROP l bb.bb_instructions) /\
   z1 = TAKE (LENGTH z1) (DROP l bb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
   l + LENGTH z0 = k /\ l + LENGTH z1 = k + LENGTH segment` by
    suspend "geometry" >>
  suspend "join"
QED

Resume dft_packet_pseudo_fresh_cut[geometry]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`,`!F gs tail. _`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_tac >> qx_gen_tac `i` >> strip_tac >>
     first_x_assum drule >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def,is_terminator_def]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (gvs[Abbr `segment`,TAKE_SUC_BY_TAKE,SNOC_APPEND,DROP_APPEND1,
          LENGTH_TAKE,TAKE_DROP_SWAP,TAKE_TAKE,EVERY_DROP,EVERY_TAKE] >>
      simp[TAKE_APPEND1,GSYM ADD1,TAKE_SUC_BY_TAKE,SNOC_APPEND,DROP_APPEND1] >>
      `s.vs_inst_idx < LENGTH ps` by decide_tac >>
      fs[EVERY_EL]) >>
  gvs[Abbr `segment`] >>
  `ps = TAKE s.vs_inst_idx ps ++ [EL s.vs_inst_idx ps]` by
    (sym_tac >> irule vyperMiscTheory.TAKE_SNOC_EL >> simp[]) >>
  `DROP (phi_prefix_length (ps ++ xs)) ps =
   DROP (phi_prefix_length (ps ++ xs)) (TAKE s.vs_inst_idx ps) ++ [EL s.vs_inst_idx ps]` by
    (pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[DROP_APPEND1,LENGTH_TAKE]) >>
  simp[DROP_APPEND1,TAKE_APPEND,LENGTH_TAKE,EVERY_DROP] >>
  simp[TAKE_LENGTH_TOO_LONG,LENGTH_TAKE,GSYM ADD1]
QED

Resume dft_packet_pseudo_fresh_cut[join]:
  `((SUC k < LENGTH ps /\ segment = [EL k ps] /\ M1 = [] /\ E1 = [] /\ K1 = []) \/
    (SUC k = LENGTH ps /\ q < LENGTH xs /\
     EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
     segment = [EL k ps] ++ TAKE q xs /\
     ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
     ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs) /\
     ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(p,d,(EL r xs).inst_id)] else []) (LENGTH xs) /\
     M1 = FLAT (TAKE q ms) /\ E1 = FLAT (TAKE q ess) /\ K1 = FLAT (TAKE q ks)))` by
    suspend "segment_cases" >>
  qabbrev_tac `H = (\f v. (gas_events_block f C7 sf.fn_name
    (bb with bb_instructions := TAKE (k + LENGTH segment) bb.bb_instructions) v,
    FOLDR (dft_exec_cons f C7) OK segment v))` >>
  `!f. LENGTH M1 = LENGTH E1 /\ LENGTH M1 = LENGTH K1 /\
    segment = TAKE (LENGTH segment) (DROP k bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) segment /\
    (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gs ==>
      (?extra. E1 = FST (H f (s with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (!ev u. H f (s with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
        ev = E1 /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block p d f C7 sf
          (bb with bb_instructions := TAKE (k + LENGTH segment) bb.bb_instructions)
          (s with vs_gas_readings := gs ++ tail)) = ZIP (K1,gs) /\
        (!tail'. H f (s with vs_gas_readings := gs ++ tail') =
          (E1,OK (u with vs_gas_readings := tail')))) /\
      (!ir u. SND (H f (s with vs_gas_readings := gs ++ tail)) <> IntRet ir u)) /\
    (SUC k < LENGTH ps ==> !gs. H f (s with vs_gas_readings := gs) =
      ([],OK (s1 with vs_gas_readings := gs)))` by
    (gen_tac >> irule dft_packet_pseudo_segment >>
     rpt (goal_assum (drule_at Any)) >> simp[NoAsms,Abbr `H`] >>
     conj_tac
     >- (qexistsl_tac [`C8`,`g`,`t`] >> simp[]) >>
     qexistsl_tac [`ess`,`ks`,`ms`,`q`,`xs`] >> asm_rewrite_tac[] >> simp[NoAsms]) >>
  suspend "semantics"
QED

Resume dft_packet_pseudo_fresh_cut[segment_cases]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`,`!F gs tail. _`] >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- simp[Abbr `segment`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (TAKE q xs)` by
    (simp[EVERY_EL,LENGTH_TAKE,EL_TAKE]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs)` by
    metis_tac[EVERY_CONJ] >>
  simp[Abbr `segment`]
QED

Resume dft_packet_pseudo_fresh_cut[semantics]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  `TAKE l bb.bb_instructions ++ z1 =
   TAKE (k + LENGTH segment) bb.bb_instructions` by
    (qpat_x_assum `!F gs tail. _` kall_tac >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
        `plan_ok = _`,`levels_ok = _`] >>
     `l <= LENGTH bb.bb_instructions` by
       (qpat_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th,LENGTH_APPEND]) >> decide_tac) >>
     qpat_assum `z1 = TAKE _ _` (fn th => pure_once_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM TAKE_SUM] >>
     qpat_assum `l + LENGTH z1 = _` (fn th => pure_rewrite_tac[th]) >> REFL_TAC) >>
  `!F u. row_eval F C7 sf.fn_name (bb,d,z1) u =
    (case SND (row_eval F C7 sf.fn_name (bb,d,z0) u) of
      OK v => (FST (row_eval F C7 sf.fn_name (bb,d,z0) u) ++ FST (H (F-d) v),
               SND (H (F-d) v))
    | other => (FST (row_eval F C7 sf.fn_name (bb,d,z0) u),other))` by
    suspend "row_identity" >>
  `!F ent. rooted_eval F C7 levels1 ent =
    (case SND (rooted_eval F C7 levels0 ent) of
      OK v => (FST (rooted_eval F C7 levels0 ent) ++ FST (H (F-d) v), SND (H (F-d) v))
    | other => (FST (rooted_eval F C7 levels0 ent),other))` by
    suspend "root_identity" >>
  qpat_assum `!f. LENGTH M1 = _ /\ _`
    (qspec_then `0` (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
  conj_tac
  >- (pure_rewrite_tac[LENGTH_APPEND] >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`LENGTH M0 = LENGTH E0`,`LENGTH M1 = LENGTH E1`] >> REFL_TAC) >>
  conj_tac
  >- (pure_rewrite_tac[LENGTH_APPEND] >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`LENGTH M0 = LENGTH K0`,`LENGTH M1 = LENGTH K1`] >> REFL_TAC) >>
  rpt gen_tac >> strip_tac >>
  `?gs0 gs1. gs = gs0 ++ gs1 /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs0 /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gs1` by
    (qpat_assum `LIST_REL _ (M0 ++ M1) gs` mp_tac >>
     pure_rewrite_tac[LIST_REL_SPLIT1] >> simp[NoAsms]) >>
  pop_assum strip_assume_tac >>
  rename1 `N <= fuel` >>
  qpat_assum `!F gs tail. _`
    (qspecl_then [`fuel`,`gs0`,`gs1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "valid0")
    (CONJUNCTS_THEN2 (mk_asm "cover0") (mk_asm "old_semantics"))) >>
  `MAP (\(ai,ds,ei,qi,zi). ai) cuts1 = paths` by
    (qpat_x_assum `!F gs tail. _` kall_tac >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
       [`paths = _`,`cuts0 = _`,`cuts1 = _`] >> simp[NoAsms]) >>
  suspend "pointwise")
QED

Resume dft_packet_pseudo_fresh_cut[row_identity]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  qx_gen_tac `fuel` >> qx_gen_tac `ent` >>
  qpat_assum `z1 = z0 ++ segment`
    (mp_then (Pat `z1 = z0 ++ segment`) mp_tac dft_packet_literal_row_extend) >>
  disch_then (qspecl_then [`l`,`bb`,`fuel-d`,`C7`,`sf.fn_name`,
    `\z ent. row_eval fuel C7 sf.fn_name (bb,d,z) ent`,`H (fuel-d)`,`ent`] mp_tac) >>
  (impl_tac
   >- (rpt conj_tac >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- (qpat_assum `LENGTH z1 < _` mp_tac >> decide_tac)
       >- first_assum ACCEPT_TAC
       >- (qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >>
           qpat_assum `l = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms])
       >- (simp[NoAsms,Abbr `H`] >>
           qpat_assum `TAKE l _ ++ z1 = _` (fn th => pure_rewrite_tac[th]) >> REFL_TAC))) >>
  simp[NoAsms])
QED

Resume dft_packet_pseudo_fresh_cut[root_identity]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  qx_gen_tac `fuel` >> qx_gen_tac `ent` >>
  map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
    [`levels1 = _`,`levels0 = _`] >>
  irule dft_packet_rooted_row_extend >>
  qexistsl_tac [`plan_eval fuel C7`,`call_setup C7`,`row_eval fuel C7`] >>
  rpt conj_tac
  >- (first_assum MATCH_ACCEPT_TAC) 
  >- (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms])
QED

Resume dft_packet_pseudo_fresh_cut[pointwise]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  conj_tac
  >- (qpat_assum `MAP _ cuts1 = paths` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `levels1 = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `plan_eval = _` (fn pe =>
        qpat_assum `rooted_eval = _` (fn re =>
          let
            fun pin eq th =
              let val tm = lhs (concl eq)
                  val v = List.find (fn v => fst (dest_var v) = fst (dest_var tm))
                            (free_vars (concl th))
              in INST_TY_TERM (match_term (valOf v) tm) th end
          in irule (pin re (pin pe (SPEC_ALL dft_packet_levels_last_row_replace))) end)) >>
      qpat_assum `l = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      rpt conj_tac
      >- (qpat_assum `LENGTH z1 < LENGTH (DROP l _)` ACCEPT_TAC)
      >- (qexistsl_tac [`plan_eval`,`plan_ok`,`rooted_eval`] >>
          conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)
      >- (qpat_assum `z1 = TAKE _ _` ACCEPT_TAC)
      >- (qpat_assum `EVERY _ z1` ACCEPT_TAC) >>
      qexists_tac `z0` >>
      qpat_assum `gs = gs0 ++ gs1` (fn th => pure_rewrite_tac[th]) >>
      asm "valid0" mp_tac >>
      qpat_assum `levels0 = _` (fn th => pure_rewrite_tac[th]) >>
      simp[NoAsms,APPEND_ASSOC]) >>
  suspend "result_cases")
QED

Resume dft_packet_pseudo_fresh_cut[result_cases]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  qpat_assum `gs = gs0 ++ gs1` (fn th => pure_rewrite_tac[th,GSYM APPEND_ASSOC]) >>
  Cases_on `rooted_eval fuel C7 levels0
    (root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail))` >>
  rename1 `rooted_eval fuel C7 levels0 _ = (old_events,old_result)` >>
  Cases_on `old_result`
  >- suspend "old_success" >> (
  qpat_assum `!F ent. rooted_eval F C7 levels1 ent = _`
    (qspecl_then [`fuel`,`root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail)`] mp_tac) >>
  (qpat_assum `rooted_eval fuel C7 levels0 _ = _`
    (fn th => simp[NoAsms,th])) >>
  disch_then (mk_asm "new_eval") >>
  simp[NoAsms,markerLib.L "new_eval",APPEND_ASSOC] >>
  conj_tac
  >- (asm "cover0" mp_tac >> simp[NoAsms] >> strip_tac >>
      qexists_tac `extra ++ E1` >> simp[NoAsms,APPEND_ASSOC] >> first_assum ACCEPT_TAC) >>
  asm "old_semantics" mp_tac >> simp[NoAsms,APPEND_ASSOC]))
QED

Resume dft_packet_pseudo_fresh_cut[old_success]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  asm "old_semantics" mp_tac >> simp[NoAsms] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `u.vs_gas_readings = gs1 ++ tail` >>
  `u = s with vs_gas_readings := gs1 ++ tail` by
    (qpat_assum `u with vs_gas_readings := _ = s` (fn th =>
       GEN_REWRITE_TAC (RHS_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM th]) >>
     qpat_assum `u.vs_gas_readings = _` (fn th => simp[NoAsms,GSYM th])) >>
  qpat_assum `!f. LENGTH M1 = _ /\ _` (qspec_then `fuel-d` mp_tac) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!gs tail. LIST_REL _ M1 gs ==> _`
    (qspecl_then [`gs1`,`tail`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!F ent. rooted_eval F C7 levels1 ent = _`
    (qspecl_then [`fuel`,`root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail)`] mp_tac) >>
  qpat_assum `rooted_eval fuel C7 levels0 _ = _` (fn th => simp[NoAsms,th]) >>
  qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `old_events = E0` (fn th => pure_rewrite_tac[th]) >>
  disch_then (mk_asm "new_success_eval") >>
  suspend "segment_results")
QED

Resume dft_packet_pseudo_fresh_cut[segment_results]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  `u.vs_inst_idx = k /\ lookup_block u.vs_current_bb sf.fn_blocks = SOME bb` by
    (qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `u.vs_inst_idx + LENGTH segment < LENGTH bb.bb_instructions` by
    (qpat_assum `LENGTH z1 < LENGTH (DROP l _)` mp_tac >>
     pure_rewrite_tac[LENGTH_DROP] >>
     qpat_assum `l + LENGTH z1 = _` mp_tac >>
     qpat_assum `u.vs_inst_idx = k` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `TAKE (LENGTH segment) (DROP u.vs_inst_idx bb.bb_instructions) = segment` by
    (qpat_assum `u.vs_inst_idx = k` (fn th => pure_rewrite_tac[th]) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `H (fuel-d) (s with vs_gas_readings := gs1 ++ tail)` >>
  rename1 `H (fuel-d) _ = (seg_events,seg_result)` >>
  asm "new_success_eval" mp_tac >>
  qpat_assum `H (fuel-d) _ = _` (fn th => simp[NoAsms,th]) >>
  disch_then (mk_asm "new_eval") >>
  simp[NoAsms,markerLib.L "new_eval",APPEND_ASSOC] >>
  conj_tac
  >- (qpat_assum `?extra. E1 = _ ++ extra` mp_tac >>
      qpat_assum `H (fuel-d) _ = _` (fn th => simp[NoAsms,th]) >> strip_tac >>
      qexists_tac `extra` >> simp[NoAsms,APPEND_ASSOC] >> first_assum ACCEPT_TAC) >>
  Cases_on `seg_result`
  >- suspend "segment_success" >> suspend "segment_stopped")
QED

Resume dft_packet_pseudo_fresh_cut[segment_success]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  qpat_assum `!ev u. (seg_events,OK v) = _ ==> _` mp_tac >>
  simp[NoAsms] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[NoAsms] >>
  conj_tac >- suspend "native_success" >>
  conj_tac
  >- (qx_gen_tac `tail'` >>
      qpat_assum `!F ent. rooted_eval F C7 levels1 ent = _`
        (qspecl_then [`fuel`,`root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail')`] mp_tac) >>
      qpat_assum `!tail'. rooted_eval fuel C7 levels0 _ = _`
        (qspec_then `gs1 ++ tail'` (fn th => pure_rewrite_tac[th])) >>
      simp[NoAsms] >>
      qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
      simp[NoAsms] >>
      qpat_assum `!tail'. H (fuel-d) _ = _`
        (qspec_then `tail'` (fn th => pure_rewrite_tac[th])) >>
      simp[NoAsms,APPEND_ASSOC]) >>
  strip_tac >>
  qpat_assum `SUC k < LENGTH ps ==> !gs. _` (drule_then (qspec_then `gs1 ++ tail` mp_tac)) >>
  qpat_assum `H (fuel-d) _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >> strip_tac >> simp[NoAsms])
QED

Resume dft_packet_pseudo_fresh_cut[segment_stopped]:
  rpt gen_tac >> markerLib.RESUME_TAC >> suspend "stopped_join"
QED

Resume dft_packet_pseudo_fresh_cut[native_success]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  `u.vs_inst_idx + LENGTH segment <= LENGTH bb.bb_instructions` by
    (qpat_assum `u.vs_inst_idx + LENGTH segment < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE (LENGTH segment) (DROP u.vs_inst_idx bb.bb_instructions))` by
    (qpat_assum `TAKE (LENGTH segment) _ = segment` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `EVERY _ segment` mp_tac >> simp[NoAsms,EVERY_CONJ]) >>
  `FOLDR (dft_exec_cons (fuel-d) C7) OK
    (TAKE (LENGTH segment) (DROP u.vs_inst_idx bb.bb_instructions)) u = OK v` by
    (qpat_assum `TAKE (LENGTH segment) _ = segment` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `H (fuel-d) _ = (seg_events,OK v)` mp_tac >>
     simp[NoAsms,Abbr `H`]) >>
  drule_all (cj 1 dftPacketNativeSliceTheory.native_trace_block_prefix_split) >> strip_tac >>
  `get_instruction bb v.vs_inst_idx = SOME (EL (LENGTH z1) (DROP l bb.bb_instructions))` by
    (qpat_assum `v.vs_inst_idx = _` mp_tac >>
     qpat_assum `u.vs_inst_idx = k` mp_tac >>
     qpat_assum `u.vs_inst_idx + LENGTH segment < _` mp_tac >>
     qpat_assum `l + LENGTH z1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `LENGTH z1 + l < LENGTH bb.bb_instructions` by decide_tac >>
     simp[get_instruction_def,EL_DROP,ADD_COMM]) >>
  qpat_assum `?before after. _ /\ trace_gas before = _` strip_assume_tac >>
  irule dft_packet_native_row_cut >>
  conj_tac
  >- (qpat_assum `LIST_REL _ M0 gs0` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
      qpat_assum `LENGTH M0 = LENGTH K0` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `LIST_REL _ M1 gs1` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
      qpat_assum `LENGTH M1 = LENGTH K1` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`root_entry with vs_gas_readings := gs0 ++ gs1 ++ tail`,`root_sf`] >>
  simp[NoAsms] >>
  conj_tac >- (qpat_assum `u.vs_inst_idx + LENGTH segment <= _` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  conj_tac
  >- (qpat_assum `u.vs_inst_idx = k` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
      pure_once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC)
QED

Resume dft_packet_pseudo_fresh_cut[stopped_join]:
  rpt gen_tac >> markerLib.RESUME_TAC >> (
  qmatch_asmsub_abbrev_tac `H (fuel-d) _ = (seg_events,rstop)` >>
  `FOLDR (dft_exec_cons (fuel-d) C7) OK
    (TAKE (LENGTH segment) (DROP u.vs_inst_idx bb.bb_instructions)) u = rstop` by
    (qpat_assum `TAKE (LENGTH segment) _ = segment` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `H (fuel-d) _ = (seg_events,rstop)` mp_tac >> simp[NoAsms,Abbr `H`]) >>
  `run_blocks fuel C7 root_sf
      (root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail)) = rstop /\
   gas_events_blocks fuel C7 root_sf
      (root_entry with vs_gas_readings := gs0 ++ (gs1 ++ tail)) =
      E0 ++ gas_events_block (fuel-d) C7 sf.fn_name
        (bb with bb_instructions := TAKE (u.vs_inst_idx + LENGTH segment) bb.bb_instructions) u` by
    (irule dft_packet_rooted_segment_stop >>
     conj_tac >- simp[NoAsms,Abbr `rstop`] >>
     conj_tac >- (qpat_assum `u.vs_inst_idx + LENGTH segment < _` mp_tac >>
                   POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `TAKE (LENGTH segment) _ = segment` (fn th => pure_rewrite_tac[th]) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `levels0 = _` (irule_at Any) >>
     asm "valid0" (irule_at Any) >>
     qpat_assum `levels_ok = _` (irule_at Any) >>
     qpat_assum `plan_ok = _` (irule_at Any) >>
     qpat_assum `plan_eval = _` (irule_at Any) >>
     qpat_assum `rooted_eval = _` (irule_at Any) >>
     qpat_assum `call_setup = _` (irule_at Any) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `rooted_eval fuel C7 levels0 _ = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `old_events = E0` (fn th => pure_rewrite_tac[th]) >> REFL_TAC) >>
  simp[NoAsms,Abbr `rstop`] >> conj_tac
  >- (qpat_assum `run_blocks fuel C7 root_sf _ = rstop` mp_tac >>
      simp[NoAsms,APPEND_ASSOC]) >>
  qpat_assum `gas_events_blocks fuel C7 root_sf _ = _` (fn th =>
    pure_rewrite_tac[th,GSYM APPEND_ASSOC]) >>
  AP_TERM_TAC >>
  qpat_assum `u.vs_inst_idx = k` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u = s with vs_gas_readings := _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `H (fuel-d) _ = (seg_events,rstop)` mp_tac >>
  simp[NoAsms,Abbr `H`])
QED

Finalise dft_packet_pseudo_fresh_cut
