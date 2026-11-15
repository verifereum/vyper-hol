(* Native activation plans project to their own source execution.
   The literal lambda equations below are proof abbreviations, not definitions.
   Proper rows exclude RET, RETFMP and DRET so IntRet cannot escape.
   The stopped branch compares the source prefix with its own same-fuel run. *)
Theory dftNativePlanPrefix
Ancestors
  dftGasFromListTraceDefs dftIndexedExec gasEvents
  venomExecSemantics venomInst venomState opcodeClass list rich_list arithmetic

Theorem native_trace_gas_events:
  (!p d f C sf i s.
    FLAT (MAP (\(key,sf,i,s).
      if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else [])
      (trace_step p d f C sf i s)) =
    if i.inst_opcode = GAS then [] else gas_events_step f C sf.fn_name i s) /\
  (!p d f C sf bb s.
    FLAT (MAP (\(key,sf,i,s).
      if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else [])
      (trace_block p d f C sf bb s)) =
    gas_events_block f C sf.fn_name bb s) /\
  (!p d f C sf s.
    FLAT (MAP (\(key,sf,i,s).
      if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else [])
      (trace_blocks p d f C sf s)) = gas_events_blocks f C sf s)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once trace_defs, Once gas_events_defs] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  gvs[gas_events_step_def]
QED

Theorem native_list_prefix_boundary:
  !z s bb cut rest.
    DROP s.vs_inst_idx bb.bb_instructions = z ++ rest /\
    DROP s.vs_inst_idx cut.bb_instructions = z /\
    EVERY (\i. ~is_terminator i.inst_opcode) z ==>
    case FOLDR (dft_exec_cons f C) OK z s of
      OK u =>
        exec_block f C bb s = exec_block f C bb u /\
        trace_block p d f C sf bb s =
          trace_block p d f C sf cut s ++ trace_block p d f C sf bb u /\
        gas_events_block f C sf.fn_name bb s =
          gas_events_block f C sf.fn_name cut s ++ gas_events_block f C sf.fn_name bb u
    | r => exec_block f C bb s = r /\
        gas_events_block f C sf.fn_name bb s = gas_events_block f C sf.fn_name cut s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[] >>
      `LENGTH cut.bb_instructions <= s.vs_inst_idx` by gvs[DROP_EQ_NIL] >>
      simp[Once trace_defs, Once gas_events_block_def, get_instruction_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH cut.bb_instructions` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ cut.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx cut.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = z ++ rest /\
   DROP (SUC s.vs_inst_idx) cut.bb_instructions = z` by
    gvs[DROP_CONS_EL] >>
  fs[EVERY_DEF] >>
  simp[FOLDR, dft_exec_cons_def] >>
  once_rewrite_tac[exec_block_def, trace_defs, gas_events_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst f C h s` >> simp[] >>
  first_x_assum (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspecl_then [`bb`, `cut`, `rest`] mp_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  strip_tac >> rpt conj_tac >>
  CONV_TAC (LHS_CONV (FIRST_CONV
    [REWR_CONV exec_block_def, REWR_CONV (cj 2 trace_defs),
     REWR_CONV gas_events_block_def])) >>
  simp[get_instruction_def]
QED

Theorem native_terminated_row_boundary:
  !pre i f C bb s.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ [i] /\
    EVERY (\j. ~is_terminator j.inst_opcode) pre /\
    is_terminator i.inst_opcode ==>
    FOLDR (dft_exec_cons f C) OK (pre ++ [i]) s = exec_block f C bb s
Proof
  `!pre i f C s.
    EVERY (\j. ~is_terminator j.inst_opcode) pre /\
    is_terminator i.inst_opcode ==>
    FOLDR (dft_exec_cons f C) OK (pre ++ [i]) s =
      dft_exec_suffix f C (pre ++ [i]) s` suffices_by
    metis_tac[dft_exec_suffix_boundary] >>
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[dft_exec_suffix_def, dft_exec_cons_def] >>
      Cases_on `step_inst f C i s` >> simp[]) >>
  fs[EVERY_DEF] >> simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
  Cases_on `step_inst f C h s` >> simp[]
QED

Theorem native_fold_no_intret:
  !z f C s ir u.
    EVERY (\i. ~MEM i.inst_opcode [RET;RETFMP;DRET]) z ==>
    FOLDR (dft_exec_cons f C) OK z s <> IntRet ir u
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `step_inst f C h s <> IntRet ir u` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (simp[Once step_inst_def] >>
         gvs[AllCaseEqs(), bind_outputs_def]) >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> gvs[]) >>
  simp[dft_exec_cons_def] >>
  Cases_on `step_inst f C h s` >> gvs[] >>
  Cases_on `is_terminator h.inst_opcode` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem native_plan_row_no_intret:
  !A F C owner bb e z s.
    A = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    ((bb.bb_instructions <> [] /\
      EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
      is_terminator (LAST bb.bb_instructions).inst_opcode /\
      ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
      z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) \/
     (LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      EVERY (\i. ~is_terminator i.inst_opcode) z)) ==>
    !ir u. SND (A F C owner (bb,e,z) s) <> IntRet ir u
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `is_terminator RET /\ is_terminator RETFMP /\ is_terminator DRET` by
    simp[is_terminator_def] >>
  `EVERY (\i. ~MEM i.inst_opcode [RET;RETFMP;DRET]) z` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- (gvs[] >> irule EVERY_DROP >>
         drule APPEND_FRONT_LAST >>
         disch_then (fn th => CONV_TAC (RAND_CONV (REWR_CONV (GSYM th)))) >>
         simp[EVERY_APPEND, EVERY_MEM] >> fs[EVERY_MEM] >> metis_tac[]) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs >>
  gvs[] >> simp[native_fold_no_intret]
QED

Theorem native_fold_prefix_index:
  !z f C s u.
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    FOLDR (dft_exec_cons f C) OK z s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH z
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem native_strict_row_residual[local]:
  !A F C sf a bb e z entry es r p.
    A = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    e = SUC a /\ e < F /\
    lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
    ~entry.vs_halted /\
    LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
      bb.bb_instructions) /\
    z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
      bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    A F C sf.fn_name (bb,e,z) entry = (es,r) ==>
    case r of
      OK u =>
        get_instruction bb u.vs_inst_idx = SOME
          (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions)) /\
        (?before.
          trace_blocks p a (F-a) C sf entry =
            before ++ trace_block p e (F-e) C sf bb u ++
            (case exec_block (F-e) C bb u of
               OK v => if v.vs_halted then []
                       else trace_blocks p e (F-e) C sf v
             | _ => []) /\
          FLAT (MAP (\(key,sf,i,s).
            if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) = es) /\
        run_blocks (F-a) C sf entry =
          (case exec_block (F-e) C bb u of
             OK v => if v.vs_halted then Halt v else run_blocks (F-e) C sf v
           | other => other) /\
        gas_events_blocks (F-a) C sf entry =
          es ++ gas_events_block (F-e) C sf.fn_name bb u ++
          (case exec_block (F-e) C bb u of
             OK v => if v.vs_halted then []
                     else gas_events_blocks (F-e) C sf v
           | _ => [])
    | other => run_blocks (F-a) C sf entry = other /\
        gas_events_blocks (F-a) C sf entry = es
Proof
  map_every qx_gen_tac [`A`, `N`, `C`, `sf`, `a`, `bb`, `e`, `z`,
    `entry`, `es`, `r`, `p`] >> strip_tac >>
  qpat_x_assum `A = _` SUBST_ALL_TAC >>
  qpat_x_assum `e = SUC a` SUBST_ALL_TAC >>
  `N-a = SUC (N-SUC a)` by decide_tac >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  qmatch_asmsub_abbrev_tac `DROP k bb.bb_instructions` >>
  `DROP k bb.bb_instructions = z ++ DROP (LENGTH z) (DROP k bb.bb_instructions)` by
    metis_tac[TAKE_DROP] >>
  `DROP k (TAKE k bb.bb_instructions ++ z) = z` by
    simp[DROP_APPEND, LENGTH_TAKE] >>
  qpat_assum `N-a = _` (fn th => rewrite_tac[th]) >>
  simp[Once run_blocks_def, Once gas_events_blocks_def, Once (cj 3 trace_defs)] >>
  qspec_then `entry` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs
  >- (gvs[] >>
      rename1 `eval_phis entry bb.bb_instructions = OK sp` >>
      qspecl_then [`z`, `sp with vs_inst_idx := k`, `bb`,
        `bb with bb_instructions := TAKE k bb.bb_instructions ++ z`,
        `DROP (LENGTH z) (DROP k bb.bb_instructions)`] mp_tac
        (Q.INST [`f` |-> `N-SUC a`, `C` |-> `C`, `p` |-> `p`,
                 `d` |-> `SUC a`, `sf` |-> `sf`] native_list_prefix_boundary) >>
      simp[] >>
      Cases_on `FOLDR (dft_exec_cons (N-SUC a) C) OK z (sp with vs_inst_idx := k)` >>
      fs[] >> strip_tac
      >- (simp[native_trace_gas_events] >>
          drule_all native_fold_prefix_index >> simp[] >> strip_tac >>
          simp[get_instruction_def, EL_DROP]) >>
      simp[Once run_blocks_def, Once gas_events_blocks_def, Abbr `k`]) >>
  gvs[] >>
  qpat_x_assum `Error _ = eval_phis _ _`
    (fn th => rewrite_tac[SYM th] >>
      simp[Once run_blocks_def, Once gas_events_blocks_def, SYM th])
QED

Theorem native_proper_row_entry[local]:
  !A F C sf a bb e z entry es r p.
    A = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    e = SUC a /\ e < F /\
    lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
    ~entry.vs_halted /\ bb.bb_instructions <> [] /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
    z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
    A F C sf.fn_name (bb,e,z) entry = (es,r) ==>
    case r of
      OK u =>
        (?before.
          trace_blocks p a (F-a) C sf entry =
            before ++ trace_blocks p e (F-e) C sf u /\
          FLAT (MAP (\(key,sf,i,s).
            if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) = es) /\
        run_blocks (F-a) C sf entry = run_blocks (F-e) C sf u /\
        gas_events_blocks (F-a) C sf entry =
          es ++ gas_events_blocks (F-e) C sf u
    | other => run_blocks (F-a) C sf entry = other /\
        gas_events_blocks (F-a) C sf entry = es
Proof
  map_every qx_gen_tac [`A`, `N`, `C`, `sf`, `a`, `bb`, `e`, `z`,
    `entry`, `es`, `r`, `p`] >> strip_tac >>
  qpat_x_assum `A = _` SUBST_ALL_TAC >>
  qpat_x_assum `e = SUC a` SUBST_ALL_TAC >>
  qpat_x_assum `z = _` SUBST_ALL_TAC >>
  `N-a = SUC (N-SUC a)` by decide_tac >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (irule venomExecProofsTheory.phi_prefix_length_lt_last_non_phi >>
     simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  qmatch_asmsub_abbrev_tac `k < LENGTH bb.bb_instructions` >>
  `DROP k bb.bb_instructions =
     DROP k (FRONT bb.bb_instructions) ++ [LAST bb.bb_instructions]` by
    (`k - PRE (LENGTH bb.bb_instructions) = 0` by decide_tac >>
     drule APPEND_FRONT_LAST >>
     disch_then (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM th))))) >>
     simp[DROP_APPEND, LENGTH_FRONT]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP k (FRONT bb.bb_instructions))` by
    simp[EVERY_DROP] >>
  `!sp. FOLDR (dft_exec_cons (N-SUC a) C) OK (DROP k bb.bb_instructions)
      (sp with vs_inst_idx := k) = exec_block (N-SUC a) C bb (sp with vs_inst_idx := k)` by
    (gen_tac >> qpat_assum `DROP k bb.bb_instructions = _` (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) empty_rewrites [th]) >>
     irule native_terminated_row_boundary >> simp[]) >>
  qpat_x_assum `DROP k bb.bb_instructions = _` kall_tac >>
  qpat_assum `N-a = _` (fn th => rewrite_tac[th]) >>
  qspec_then `entry` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs
  >- (gvs[TAKE_DROP] >>
      rename1 `eval_phis entry bb.bb_instructions = OK sp` >>
      Cases_on `exec_block (N-SUC a) C bb (sp with vs_inst_idx := k)` >> fs[]
      >- (drule venomExecProofsTheory.exec_block_OK_not_halted >> strip_tac >>
          simp[Once run_blocks_def, Once gas_events_blocks_def,
               Once (cj 3 trace_defs), native_trace_gas_events, Abbr `k`]) >>
      simp[Once run_blocks_def, Once gas_events_blocks_def, Abbr `k`]) >>
  gvs[] >>
  qpat_x_assum `Error _ = eval_phis _ _`
    (fn th => rewrite_tac[SYM th] >>
      simp[Once run_blocks_def, Once gas_events_blocks_def, SYM th])
QED

Theorem native_plan_fold_acc:
  !rows R prior r.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (R row s), SND (R row s))
    | other => (es,other)) (prior,r) rows =
    case r of
      OK s =>
        (prior ++ FST (FOLDL (\(es,r) row. case r of
          OK s => (es ++ FST (R row s), SND (R row s))
        | other => (es,other)) ([],OK s) rows),
         SND (FOLDL (\(es,r) row. case r of
          OK s => (es ++ FST (R row s), SND (R row s))
        | other => (es,other)) ([],OK s) rows))
    | other => (prior,other)
Proof
  Induct >- (rpt gen_tac >> Cases_on `r` >> simp[]) >>
  rpt gen_tac >> Cases_on `r` >> simp[NoAsms]
  >- (Cases_on `R h v` >> rename1 `R h v = (ev,res)` >>
      fs[NoAsms] >>
      first_assum (qspecl_then [`R`, `prior ++ ev`, `res`] mp_tac) >>
      first_x_assum (qspecl_then [`R`, `ev`, `res`] mp_tac) >>
      Cases_on `res` >> simp[APPEND_ASSOC]) >>
  first_x_assum (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem native_plan_fold_cons[local]:
  !A B F C owner row rows entry es r.
    B = (\F C owner plan entry.
      FOLDL (\(es,r) row.
        case r of
          OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
        | other => (es,other)) ([],OK entry) plan) /\
    A F C owner row entry = (es,r) ==>
    B F C owner (row::rows) entry =
      case r of
        OK s => (es ++ FST (B F C owner rows s), SND (B F C owner rows s))
      | other => (es,other)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `B = _` SUBST_ALL_TAC >>
  simp[] >> irule native_plan_fold_acc
QED

Theorem native_plan_tail_alignment[local]:
  !A B plan_ok F C sf a row rows entry es s.
    B = (\F C owner plan entry.
      FOLDL (\(es,r) row.
        case r of
          OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
        | other => (es,other)) ([],OK entry) plan) /\
    plan_ok = (\F C sf a plan entry.
      plan <> [] /\
      MAP (\(bb,e,z). e) plan =
        GENLIST (\r. a + SUC r) (LENGTH plan) /\
      (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
        e < F /\ MEM bb sf.fn_blocks /\
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
        B F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
        lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\ ~s.vs_halted)) /\
    plan_ok F C sf a (row::rows) entry /\ rows <> [] /\
    A F C sf.fn_name row entry = (es,OK s) ==>
    plan_ok F C sf (SUC a) rows s
Proof
  map_every qx_gen_tac [`A`, `B`, `plan_ok`, `N`, `C`, `sf`, `a`,
    `row`, `rows`, `entry`, `es`, `s`] >> strip_tac >>
  qpat_x_assum `plan_ok = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss())
    [GENLIST_CONS, combinTheory.o_DEF, ADD_CLAUSES]) >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  simp[IgnAsm `B = _`, GENLIST_CONS, combinTheory.o_DEF, ADD_CLAUSES] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!r bb e z. _ ==> _`
        (qspecl_then [`SUC r`, `bb`, `e`, `z`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `B N C sf.fn_name (TAKE r rows) s = (ev,OK st)` >>
  `B N C sf.fn_name (row::TAKE r rows) entry = (es ++ ev,OK st)` by
    (drule_all native_plan_fold_cons >>
     disch_then (qspec_then `TAKE r rows` mp_tac) >>
     qpat_assum `B N C sf.fn_name (TAKE r rows) s = _`
       (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_x_assum `!r bb e z es s. _` (qspecl_then
    [`SUC r`, `bb`, `e`, `z`, `es ++ ev`, `st`] mp_tac) >>
  simp[IgnAsm `B = _`]
QED

Theorem native_single_plan_prefix:
  !A B plan_ok.
    A = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    B = (\F C owner plan entry.
      FOLDL (\(es,r) row.
        case r of
          OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
        | other => (es,other)) ([],OK entry) plan) /\
    plan_ok = (\F C sf a plan entry.
      plan <> [] /\
      MAP (\(bb,e,z). e) plan =
        GENLIST (\r. a + SUC r) (LENGTH plan) /\
      (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
        e < F /\ MEM bb sf.fn_blocks /\
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
        B F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
        lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\ ~s.vs_halted)) ==>
    !plan F C sf a entry bb e z x es r p.
      plan_ok F C sf a plan entry /\ LAST plan = (bb,e,z) /\
      x = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      B F C sf.fn_name plan entry = (es,r) ==>
      (!ir u. r <> IntRet ir u) /\
      (case r of
        OK u =>
          get_instruction bb u.vs_inst_idx = SOME x /\
          (?before.
            trace_blocks p a (F-a) C sf entry =
              before ++ trace_block p e (F-e) C sf bb u ++
              (case exec_block (F-e) C bb u of
                 OK v => if v.vs_halted then []
                         else trace_blocks p e (F-e) C sf v
               | _ => []) /\
            FLAT (MAP (\(key,sf,i,s).
              if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) = es) /\
          run_blocks (F-a) C sf entry =
            (case exec_block (F-e) C bb u of
               OK v => if v.vs_halted then Halt v else run_blocks (F-e) C sf v
             | other => other) /\
          gas_events_blocks (F-a) C sf entry =
            es ++ gas_events_block (F-e) C sf.fn_name bb u ++
            (case exec_block (F-e) C bb u of
               OK v => if v.vs_halted then []
                       else gas_events_blocks (F-e) C sf v
             | _ => [])
      | other => run_blocks (F-a) C sf entry = other /\
          gas_events_blocks (F-a) C sf entry = es)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `plan_ok _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `plan_ok = _` (fn th => simp_tac (srw_ss()) [th])) >>
  qx_gen_tac `h` >>
  map_every qx_gen_tac [`N`, `C`, `sf`, `a`, `entry`, `bb`, `e`,
    `z`, `x`, `es`, `r`, `p`] >> strip_tac >>
  PairCases_on `h` >>
  qpat_assum `plan_ok _ _ _ _ _ _` mp_tac >>
  qpat_assum `plan_ok = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [GENLIST_CONS, combinTheory.o_DEF, ADD_CLAUSES] >>
  strip_tac >>
  `B N C sf.fn_name [] entry = ([],OK entry)` by
    (qpat_assum `B = _` (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_assum `!r bb e z. _ ==> _`
    (qspecl_then [`0`, `h0`, `h1`, `h2`] mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `!r bb e z es s. _`
    (qspecl_then [`0`, `h0`, `h1`, `h2`, `[]`, `entry`] mp_tac) >>
  simp[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`] >> strip_tac >>
  `!ir u. SND (A N C sf.fn_name (h0,h1,h2) entry) <> IntRet ir u` by
    (irule native_plan_row_no_intret >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_x_assum `if _ then _ else _` mp_tac >>
     Cases_on `0 < LENGTH plan` >> asm_rewrite_tac[] >>
     simp_tac (srw_ss()) []) >>
  Cases_on `A N C sf.fn_name (h0,h1,h2) entry` >>
  rename1 `A N C sf.fn_name (h0,h1,h2) entry = (ev,res)` >>
  drule_all native_plan_fold_cons >>
  disch_then (qspec_then `plan` assume_tac) >>
  Cases_on `plan = []`
  >- (qpat_x_assum `plan = []` SUBST_ALL_TAC >>
      `!v. B N C sf.fn_name [] v = ([],OK v)` by
        (qpat_assum `B = _` (fn th => simp_tac (srw_ss()) [th])) >>
      fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`] >>
      qpat_x_assum `h0 = bb` SUBST_ALL_TAC >>
      qpat_x_assum `h2 = z` SUBST_ALL_TAC >>
      qpat_x_assum `h1 = SUC a` SUBST_ALL_TAC >>
      qpat_x_assum `SUC a = e` (SUBST_ALL_TAC o SYM) >>
      `(ev,res) = (es,r)` by (Cases_on `res` >> fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`]) >>
      qpat_x_assum `(ev,res) = (es,r)`
        (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      qpat_x_assum `ev = es` SUBST_ALL_TAC >>
      qpat_x_assum `res = r` SUBST_ALL_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule native_strict_row_residual >> gvs[]) >>
  `0 < LENGTH plan` by (Cases_on `plan` >> fs[]) >>
  fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`] >>
  qpat_x_assum `h1 = SUC a` SUBST_ALL_TAC >>
  qpat_x_assum `h2 = _` SUBST_ALL_TAC >>
  drule_at (Pat `A _ _ _ _ _ = _`) native_proper_row_entry >>
  disch_then (qspecl_then [`a`, `p`] mp_tac) >>
  simp[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> Cases_on `res` >>
  fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`]
  >- (rename1 `A N C sf.fn_name _ entry = (ev,OK v)` >>
      `plan_ok N C sf (SUC a) plan v` by
        (irule (INST_TYPE [``:'b`` |-> ``:string # num``] native_plan_tail_alignment) >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qexistsl [`A`, `B`, `entry`, `ev`,
           `(h0,SUC a,DROP (phi_prefix_length h0.bb_instructions) h0.bb_instructions)`] >>
         simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `LAST plan = (bb,e,z)` by (Cases_on `plan` >> fs[]) >>
      Cases_on `B N C sf.fn_name plan v` >>
      rename1 `B N C sf.fn_name plan v = (tailes,tailr)` >>
      qpat_x_assum `!F C sf a entry bb e z es r p. _` drule_all >>
      disch_then (qspec_then `p` mp_tac) >>
      Cases_on `tailr` >>
      fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `plan_ok = _`] >>
      strip_tac >>
      map_every (fn pat => qpat_x_assum pat kall_tac)
        [`A = _`, `B = _`, `plan_ok = _`] >> gvs[] >>
      qexists_tac `before ++ before'` >>
      simp[MAP_APPEND, FLAT_APPEND, APPEND_ASSOC]) >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`A = _`, `B = _`, `plan_ok = _`] >> gvs[]
QED

Theorem native_levels_fold_cons[local]:
  !B T W F C sf plan call ls entry ev r.
    W = (\F C levels entry.
      FOLDL (\(prior,r) (sf,plan,call).
        case r of
          OK ent =>
           (prior ++ FST (B F C sf.fn_name plan ent),
            case SND (B F C sf.fn_name plan ent) of
              OK caller =>
                (case call of NONE => OK caller | SOME c => T C c caller)
            | other => other)
        | other => (prior,other)) ([],OK entry) levels) /\
    B F C sf.fn_name plan entry = (ev,r) ==>
    W F C ((sf,plan,call)::ls) entry =
      case (case r of OK caller =>
        (case call of NONE => OK caller | SOME c => T C c caller)
        | other => other) of
      OK ent => (ev ++ FST (W F C ls ent), SND (W F C ls ent))
    | other => (ev,other)
Proof
  map_every qx_gen_tac [`B`, `tt`, `ww`, `N`, `C`, `sf`, `plan`,
    `call`, `ls`, `entry`, `ev`, `r`] >> strip_tac >>
  qpat_x_assum `ww = _` SUBST_ALL_TAC >> simp[] >>
  qspec_then `ls` (qspec_then
    `\(sf,plan,call) ent.
      (FST (B N C sf.fn_name plan ent),
       case SND (B N C sf.fn_name plan ent) of
         OK caller => (case call of NONE => OK caller | SOME c => tt C c caller)
       | other => other)` mp_tac) native_plan_fold_acc >>
  disch_then (qspecl_then [`ev`,
    `case r of OK caller =>
       (case call of NONE => OK caller | SOME c => tt C c caller)
     | other => other`] mp_tac) >>
  qmatch_goalsub_abbrev_tac `FOLDL op1` >>
  qmatch_goalsub_abbrev_tac `_ ==> FOLDL op2 _ _ = _` >>
  `op1 = op2` by
    (simp_tac (srw_ss()) [Abbr `op1`, Abbr `op2`,
       FUN_EQ_THM, pairTheory.FORALL_PROD] >>
     map_every qx_gen_tac [`es0`, `r0`, `sf0`, `plan0`, `call0`] >>
     Cases_on `r0` >> simp[]) >>
  simp[]
QED

Theorem native_levels_tail_alignment[local]:
  !B tt ww plan_ok levels_ok N C sf plan c ls paths incoming
    root_fn entry root_path root_depth ev caller ent.
    ww = (\F C levels entry.
      FOLDL (\(prior,r) (sf,plan,call).
        case r of
          OK ent =>
           (prior ++ FST (B F C sf.fn_name plan ent),
            case SND (B F C sf.fn_name plan ent) of
              OK caller =>
                (case call of NONE => OK caller | SOME c => tt C c caller)
            | other => other)
        | other => (prior,other)) ([],OK entry) levels) /\
    levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
      levels <> [] /\ LENGTH paths = LENGTH levels /\
      LENGTH incoming = LENGTH levels /\
      HD paths = root_path /\ HD incoming = root_depth /\
      FST (HD levels) = root_fn /\
      (!i sf plan call.
        i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
        plan <> [] /\
        (!prior ent.
          ww F C (TAKE i levels) root_entry = (prior,OK ent) ==>
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
    levels_ok N C ((sf,plan,SOME c)::ls) paths incoming
      root_fn entry root_path root_depth /\
    B N C sf.fn_name plan entry = (ev,OK caller) /\
    tt C c caller = OK ent /\ ls <> [] ==>
    levels_ok N C ls (TL paths) (TL incoming) (FST (HD ls)) ent
      (HD (TL paths)) (HD (TL incoming))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `levels_ok = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  Cases_on `paths` >> fs[IgnAsm `ww = _`] >>
  Cases_on `incoming` >> fs[IgnAsm `ww = _`] >>
  simp[IgnAsm `ww = _`] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i sf plan call. _`
    (qspecl_then [`SUC i`, `sf'`, `plan'`, `call`] mp_tac) >>
  simp[IgnAsm `ww = _`] >> strip_tac >>
  simp[IgnAsm `ww = _`] >>
  rpt gen_tac >> strip_tac >>
  `ww N C ((root_fn,plan,SOME c)::TAKE i ls) entry =
    (ev ++ prior,OK ent')` by
    (drule_all native_levels_fold_cons >>
     disch_then (qspecl_then [`SOME c`, `TAKE i ls`] mp_tac) >>
     simp[IgnAsm `ww = _`]) >>
  first_x_assum irule >> qexists_tac `ev ++ prior` >>
  simp[IgnAsm `ww = _`]
QED

Theorem native_levels_head_alignment[local]:
  !ww plan_ok levels_ok N C sf plan call ls paths incoming
    root_fn entry root_path root_depth.
    levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
      levels <> [] /\ LENGTH paths = LENGTH levels /\
      LENGTH incoming = LENGTH levels /\
      HD paths = root_path /\ HD incoming = root_depth /\
      FST (HD levels) = root_fn /\
      (!i sf plan call.
        i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
        plan <> [] /\
        (!prior ent.
          ww F C (TAKE i levels) root_entry = (prior,OK ent) ==>
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
    levels_ok N C ((sf,plan,call)::ls) paths incoming
      root_fn entry root_path root_depth /\
    ww N C [] entry = ([],OK entry) ==>
    sf = root_fn /\ HD paths = root_path /\ HD incoming = root_depth /\
    LENGTH paths = SUC (LENGTH ls) /\ LENGTH incoming = SUC (LENGTH ls) /\
    plan <> [] /\ plan_ok N C sf root_depth plan entry /\
    (if ls <> [] then
      ?c nm ops bb e z.
        call = SOME c /\ LAST plan = (bb,e,z) /\
        c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
        lookup_function nm C.ctx_functions = SOME (FST (HD ls)) /\
        HD (TL incoming) = e /\ HD (TL paths) = (e,c.inst_id)::root_path
     else call = NONE)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `levels_ok = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  qpat_x_assum `!i sf plan call. _`
    (qspecl_then [`0`, `sf`, `plan`, `call`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `paths` >> fs[] >> Cases_on `incoming` >> fs[] >>
  Cases_on `ls` >> fs[] >>
  Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]
QED

Theorem native_invoke_residual_entry[local]:
  !tt p d fuel C sf bb s c nm ops callee cs.
    tt = (\C c s.
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
    get_instruction bb s.vs_inst_idx = SOME c /\ c.inst_opcode = INVOKE /\
    decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\ tt C c s = OK cs ==>
    ?rest. trace_block p d fuel C sf bb s =
      [((p,d,c.inst_id),sf,c,s)] ++
      trace_blocks ((d,c.inst_id)::p) d fuel C callee cs ++ rest
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `tt = _` SUBST_ALL_TAC >>
  gvs[AllCaseEqs()] >>
  drule trace_block_visit >> disch_then (fn th => simp[Once th]) >>
  drule_all trace_step_invoke >> disch_then (fn th => simp[th])
QED

Theorem native_invoke_residual_stopped[local]:
  !tt fuel C sf bb s c nm ops callee cs r.
    tt = (\C c s.
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
    get_instruction bb s.vs_inst_idx = SOME c /\ c.inst_opcode = INVOKE /\
    decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\ tt C c s = OK cs /\
    run_blocks fuel C callee cs = r /\
    (!u. r <> OK u) /\ (!ir u. r <> IntRet ir u) ==>
    exec_block fuel C bb s = r /\
    gas_events_block fuel C sf.fn_name bb s = gas_events_blocks fuel C callee cs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `tt = _` SUBST_ALL_TAC >> gvs[AllCaseEqs()] >>
  `step_inst fuel C c s = run_blocks fuel C callee cs` by
    (simp[Once step_inst_def] >>
     Cases_on `run_blocks fuel C callee cs` >> fs[]) >>
  conj_tac
  >- (simp[Once exec_block_def] >>
      Cases_on `run_blocks fuel C callee cs` >> fs[]) >>
  simp[Once gas_events_block_def] >>
  simp[Once gas_events_step_def] >>
  Cases_on `run_blocks fuel C callee cs` >> fs[]
QED

Theorem native_invoke_setup_stopped[local]:
  !tt fuel C sf bb s c r.
    tt = (\C c s.
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
    get_instruction bb s.vs_inst_idx = SOME c /\ c.inst_opcode = INVOKE /\
    tt C c s = r /\ (!u. r <> OK u) ==>
    (!ir u. r <> IntRet ir u) /\ exec_block fuel C bb s = r /\
    gas_events_block fuel C sf.fn_name bb s = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `tt = _` SUBST_ALL_TAC >>
  Cases_on `decode_invoke c` >> fs[]
  >- (simp[Once exec_block_def, Once gas_events_block_def,
           Once gas_events_step_def] >> simp[step_inst_def]) >>
  PairCases_on `x` >> fs[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >> fs[]
  >- (simp[Once exec_block_def, Once gas_events_block_def,
           Once gas_events_step_def] >> simp[step_inst_def]) >>
  Cases_on `eval_operands x1 s` >> fs[]
  >- (simp[Once exec_block_def, Once gas_events_block_def,
           Once gas_events_step_def] >> simp[step_inst_def]) >>
  Cases_on `setup_callee x x' s` >> fs[] >>
  simp[Once exec_block_def, Once gas_events_block_def,
       Once gas_events_step_def] >> simp[step_inst_def]
QED

Theorem native_plan_prefix:
 !F C root_fn root_entry root_path root_depth
  levels paths incoming last_fn last_plan last_bb last_depth last_z x
  A B T W plan_ok levels_ok.
  A = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  B = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  T = (\C c s.
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
  W = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (B F C sf.fn_name plan ent),
          case SND (B F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => T C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan =
      GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e < F /\ MEM bb sf.fn_blocks /\
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
      B F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\ ~s.vs_halted)) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        W F C (TAKE i levels) root_entry = (prior,OK ent) ==>
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
  levels_ok F C levels paths incoming root_fn root_entry root_path root_depth /\
  LAST levels = (last_fn,last_plan,NONE) /\
  LAST last_plan = (last_bb,last_depth,last_z) /\
  x = EL (LENGTH last_z)
    (DROP (phi_prefix_length last_bb.bb_instructions) last_bb.bb_instructions)
 ==>
  (!ir u. SND (W F C levels root_entry) <> IntRet ir u) /\
  (!u. SND (W F C levels root_entry) = OK u ==>
    ?before after.
      dftGasFromListTraceDefs$trace_blocks root_path root_depth
        (F-root_depth) C root_fn root_entry =
      before ++ [((LAST paths,last_depth,x.inst_id),last_fn,x,u)] ++ after /\
      FLAT (MAP (\(key,sf,i,s).
        if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) =
      FST (W F C levels root_entry)) /\
  (!r. SND (W F C levels root_entry) = r /\
       (!u. r <> OK u) ==>
    run_blocks (F-root_depth) C root_fn root_entry = r /\
    gas_events_blocks (F-root_depth) C root_fn root_entry =
      FST (W F C levels root_entry))
Proof
  map_every qx_gen_tac [`N`, `C`, `root_fn`, `root_entry`, `root_path`,
    `root_depth`, `levels`, `paths`, `incoming`, `last_fn`, `last_plan`,
    `last_bb`, `last_depth`, `last_z`, `x`, `A`, `B`, `tt`, `ww`,
    `plan_ok`, `levels_ok`] >>
  map_every qid_spec_tac [`N`, `C`, `root_fn`, `root_entry`, `root_path`,
    `root_depth`, `paths`, `incoming`, `last_fn`, `last_plan`, `last_bb`,
    `last_depth`, `last_z`, `x`] >>
  qid_spec_tac `levels` >> Induct
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `levels_ok = _`
        (fn th => simp_tac (srw_ss()) [th])) >>
  qx_gen_tac `h` >> rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `!ent. ww N C [] ent = ([],OK ent)` by
    (qpat_assum `ww = _` (fn th => simp_tac (srw_ss()) [th])) >>
  first_assum (qspec_then `root_entry` assume_tac) >>
  drule_all native_levels_head_alignment >> strip_tac >>
  qspecl_then [`A`, `B`, `plan_ok`] mp_tac native_single_plan_prefix >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  Cases_on `levels = []`
  >- (qpat_x_assum `levels = []` SUBST_ALL_TAC >>
      qpat_x_assum `!x last_z last_depth last_bb last_plan last_fn incoming paths root_depth root_path root_entry root_fn C N. _` kall_tac >>
      fs[IgnAsm `A = _`, IgnAsm `B = _`, IgnAsm `tt = _`,
         IgnAsm `ww = _`, IgnAsm `plan_ok = _`, IgnAsm `levels_ok = _`] >>
      map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
        [`h0 = root_fn`, `root_fn = last_fn`, `h1 = last_plan`] >>
      Cases_on `B N C last_fn.fn_name last_plan root_entry` >>
      rename1 `B N C last_fn.fn_name last_plan root_entry = (ev,res)` >>
      qpat_assum `!plan F C sf a entry bb e z es r p. _` drule_all >>
      disch_then (qspec_then `root_path` mp_tac) >>
      strip_tac >>
      drule_all native_levels_fold_cons >>
      disch_then (qspecl_then [`NONE`, `[]`] mp_tac) >>
      Cases_on `res` >>
      map_every (fn pat => qpat_x_assum pat kall_tac)
        [`A = _`, `B = _`, `tt = _`, `ww = _`, `plan_ok = _`,
         `levels_ok = _`, `!plan F C sf a entry bb e z es r p. _`] >>
      simp[] >> strip_tac >> fs[] >>
      Cases_on `paths` >> fs[] >> Cases_on `t` >> fs[] >>
      drule trace_block_visit >> disch_then (fn th => fs[Once th]) >>
      qexists_tac `before` >>
      pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND_11] >> simp[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  qpat_assum `levels <> []` (fn th => pure_rewrite_tac [th, NOT_CLAUSES, COND_CLAUSES]) >>
  disch_then (qx_choose_then `call_inst` (qx_choose_then `nm`
    (qx_choose_then `ops` (qx_choose_then `bb` (qx_choose_then `e`
      (qx_choose_then `z` (fn th => map_every assume_tac (CONJUNCTS th)))))))) >>
  qpat_x_assum `h2 = SOME call_inst` SUBST_ALL_TAC >>
  qpat_x_assum `h0 = root_fn` (SUBST_ALL_TAC o SYM) >>
  Cases_on `B N C h0.fn_name h1 root_entry` >>
  rename1 `B N C h0.fn_name h1 root_entry = (ev,res)` >>
  qpat_assum `!plan F C sf a entry bb e z es r p. _` drule_all >>
  disch_then (qspec_then `root_path` mp_tac) >> strip_tac >>
  drule_all native_levels_fold_cons >>
  disch_then (qspecl_then [`SOME call_inst`, `levels`] assume_tac) >>
  Cases_on `!v. res <> OK v`
  >- (map_every (fn pat => qpat_x_assum pat kall_tac)
        [`A = _`, `B = _`, `tt = _`, `ww = _`, `plan_ok = _`,
         `levels_ok = _`, `!plan F C sf a entry bb e z es r p. _`,
         `!x last_z last_depth last_bb last_plan last_fn incoming paths root_depth root_path root_entry root_fn C N. _`] >>
      Cases_on `res` >> gvs[]) >>
  qpat_x_assum `~(!v. res <> OK v)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `res = OK _` SUBST_ALL_TAC >>
  rename1 `B N C h0.fn_name h1 root_entry = (ev,OK caller)` >>
  qpat_x_assum `case OK caller of OK uu => _ | Halt aa => _ | Abort ba ca => _ | IntRet da ea => _ | Error fa => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `ww N C ((h0,h1,SOME call_inst)::levels) root_entry = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `call_inst = _`
    (fn th => qpat_x_assum `get_instruction _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [GSYM th])) >>
  Cases_on `!ent. tt C call_inst caller <> OK ent`
  >- (qspecl_then [`tt`, `N-e`, `C`, `h0`, `bb`, `caller`,
        `call_inst`, `tt C call_inst caller`] mp_tac native_invoke_setup_stopped >>
      (impl_tac >- (rpt conj_tac >> FIRST_PROVE [REFL_TAC, first_assum ACCEPT_TAC])) >>
      strip_tac >>
      map_every (fn pat => qpat_x_assum pat kall_tac)
        [`A = _`, `B = _`, `tt = _`, `ww = _`, `plan_ok = _`,
         `levels_ok = _`, `!plan F C sf a entry bb e z es r p. _`,
         `!x last_z last_depth last_bb last_plan last_fn incoming paths root_depth root_path root_entry root_fn C N. _`] >>
      Cases_on `tt C call_inst caller` >> gvs[]) >>
  qpat_x_assum `~(!ent. tt C call_inst caller <> OK ent)` mp_tac >>
  simp_tac (srw_ss()) [] >> disch_then (qx_choose_then `ent` assume_tac) >>
  drule_all native_levels_tail_alignment >> strip_tac >>
  qpat_assum `!x last_z last_depth last_bb last_plan last_fn incoming paths root_depth root_path root_entry root_fn C N. _`
    (qspecl_then [`x`, `last_z`, `last_depth`, `last_bb`, `last_plan`,
      `last_fn`, `TL incoming`, `TL paths`, `HD (TL incoming)`,
      `HD (TL paths)`, `ent`, `FST (HD levels)`, `C`, `N`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST_PROVE [first_assum ACCEPT_TAC,
      (qpat_assum `LAST ((h0,h1,SOME call_inst)::levels) = _` mp_tac >>
       qpat_assum `levels <> []` (fn th => simp_tac (srw_ss()) [th, LAST_DEF]))])) >>
  strip_tac >>
  drule_all native_invoke_residual_entry >>
  disch_then (qspecl_then [`root_path`, `e`, `N-e`, `h0`] mp_tac) >>
  strip_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`A = _`, `B = _`, `ww = _`, `plan_ok = _`, `levels_ok = _`,
     `!plan F C sf a entry bb e z es r p. _`,
     `!x last_z last_depth last_bb last_plan last_fn incoming paths root_depth root_path root_entry root_fn C N. _`] >>
  qpat_assum `tt C call_inst caller = OK ent`
    (fn th => qpat_x_assum `ww N C ((h0,h1,SOME call_inst)::levels) root_entry = _`
      (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
  conj_tac >- simp[] >> conj_tac
  >- (map_every (fn pat => qpat_x_assum pat kall_tac)
        [`tt = _`, `call_inst = _`, `x = _`] >>
      rpt strip_tac >>
      `SND (ww N C levels ent) = OK u` by
        (qpat_x_assum `SND (ww N C ((h0,h1,SOME call_inst)::levels) root_entry) = OK u` mp_tac >> simp[]) >>
      qpat_x_assum `!u. SND (ww N C levels ent) = OK u ==> _` drule >>
      strip_tac >>
      `LAST (TL paths) = LAST paths` by
        (Cases_on `paths` >> fs[] >> Cases_on `t` >> fs[LAST_DEF]) >>
      qexists_tac `before ++ [((root_path,e,call_inst.inst_id),h0,call_inst,caller)] ++ before'` >>
      qmatch_asmsub_abbrev_tac `before ++ trace_block _ _ _ _ _ _ _ ++ suffix` >>
      qexists_tac `after ++ rest ++ suffix` >> conj_tac
      >- (
          qpat_assum `HD (TL paths) = _` (fn th =>
            qpat_assum `HD (TL incoming) = _` (fn th' =>
              qpat_x_assum `trace_blocks (HD (TL paths)) _ _ _ _ _ = _`
                (assume_tac o PURE_REWRITE_RULE [th,th']))) >>
          simp[Abbr `suffix`, APPEND_ASSOC]) >>
      simp[MAP_APPEND, FLAT_APPEND]) >>
  strip_tac >>
  `!u. SND (ww N C levels ent) <> OK u` by
    (qpat_x_assum `!u. SND (ww N C ((h0,h1,SOME call_inst)::levels) root_entry) <> OK u` mp_tac >>
     qpat_assum `ww N C ((h0,h1,SOME call_inst)::levels) root_entry = _`
       (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_x_assum `!r. SND (ww N C levels ent) = r /\ _ ==> _`
    (qspec_then `SND (ww N C levels ent)` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `run_blocks (N-e) C (FST (HD levels)) ent = SND (ww N C levels ent)` by
    metis_tac[] >>
  drule_all native_invoke_residual_stopped >>
  disch_then (qspec_then `h0` mp_tac) >> strip_tac >>
  qpat_x_assum `tt = _` kall_tac >>
  qpat_x_assum `call_inst = _` kall_tac >>
  Cases_on `SND (ww N C levels ent)` >> gvs[]
QED

(* The final entered block may execute its body at fuel zero. *)
Theorem native_plan_prefix_inclusive:
 !F C root_fn root_entry root_path root_depth
  levels paths incoming last_fn last_plan last_bb last_depth last_z x
  A B T W plan_ok levels_ok.
  A = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  B = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  T = (\C c s.
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
  W = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (B F C sf.fn_name plan ent),
          case SND (B F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => T C c caller)
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
      B F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
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
        W F C (TAKE i levels) root_entry = (prior,OK ent) ==>
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
  levels_ok F C levels paths incoming root_fn root_entry root_path root_depth /\
  LAST levels = (last_fn,last_plan,NONE) /\
  LAST last_plan = (last_bb,last_depth,last_z) /\
  x = EL (LENGTH last_z)
    (DROP (phi_prefix_length last_bb.bb_instructions) last_bb.bb_instructions)
 ==>
  (!ir u. SND (W F C levels root_entry) <> IntRet ir u) /\
  (!u. SND (W F C levels root_entry) = OK u ==>
    ?before after.
      dftGasFromListTraceDefs$trace_blocks root_path root_depth
        (F-root_depth) C root_fn root_entry =
      before ++ [((LAST paths,last_depth,x.inst_id),last_fn,x,u)] ++ after /\
      FLAT (MAP (\(key,sf,i,s).
        if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) =
      FST (W F C levels root_entry)) /\
  (!r. SND (W F C levels root_entry) = r /\
       (!u. r <> OK u) ==>
    run_blocks (F-root_depth) C root_fn root_entry = r /\
    gas_events_blocks (F-root_depth) C root_fn root_entry =
      FST (W F C levels root_entry))
Proof
  FAIL_TAC "inclusive boundary proof pending"
QED

Theorem native_single_plan_prefix_inclusive:
  !A B plan_ok.
    A = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    B = (\F C owner plan entry.
      FOLDL (\(es,r) row.
        case r of
          OK s => (es ++ FST (A F C owner row s), SND (A F C owner row s))
        | other => (es,other)) ([],OK entry) plan) /\
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
        B F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
        lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) ==>
    !plan F C sf a entry bb e z x es r p.
      plan_ok F C sf a plan entry /\ LAST plan = (bb,e,z) /\
      x = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
        bb.bb_instructions) /\
      B F C sf.fn_name plan entry = (es,r) ==>
      (!ir u. r <> IntRet ir u) /\
      (case r of
        OK u =>
          get_instruction bb u.vs_inst_idx = SOME x /\
          (?before.
            trace_blocks p a (F-a) C sf entry =
              before ++ trace_block p e (F-e) C sf bb u ++
              (case exec_block (F-e) C bb u of
                 OK v => if v.vs_halted then []
                         else trace_blocks p e (F-e) C sf v
               | _ => []) /\
            FLAT (MAP (\(key,sf,i,s).
              if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) before) = es) /\
          run_blocks (F-a) C sf entry =
            (case exec_block (F-e) C bb u of
               OK v => if v.vs_halted then Halt v else run_blocks (F-e) C sf v
             | other => other) /\
          gas_events_blocks (F-a) C sf entry =
            es ++ gas_events_block (F-e) C sf.fn_name bb u ++
            (case exec_block (F-e) C bb u of
               OK v => if v.vs_halted then []
                       else gas_events_blocks (F-e) C sf v
             | _ => [])
      | other => run_blocks (F-a) C sf entry = other /\
          gas_events_blocks (F-a) C sf entry = es)
Proof
  FAIL_TAC "inclusive single-plan proof pending"
QED
