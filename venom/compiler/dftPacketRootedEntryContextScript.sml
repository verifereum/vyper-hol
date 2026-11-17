Theory dftPacketRootedEntryContext
Ancestors
  dftPacketRootedOperational dftPacketRootedCompose dftAvailability
  gasEvents venomExecSemantics venomExecProofs dftIndexedExec venomInst
  list rich_list

Theorem entry_snoc_success[local]:
  !R P S prefix sf plan call entry events u.
  R = (\levels entry. FOLDL (\(prior,r) (sf,plan,call).
    case r of OK ent =>
      (prior ++ FST (P sf.fn_name plan ent),
       case SND (P sf.fn_name plan ent) of
         OK caller => (case call of NONE => OK caller | SOME c => S c caller)
       | other => other)
    | other => (prior,other)) ([],OK entry) levels) /\
  R (prefix ++ [(sf,plan,call)]) entry = (events,OK u) ==>
  ?prior ent es caller.
    R prefix entry = (prior,OK ent) /\
    P sf.fn_name plan ent = (es,OK caller) /\
    (case call of NONE => OK caller | SOME c => S c caller) = OK u /\
    events = prior ++ es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `R (prefix ++ _) entry = _` mp_tac >>
  qpat_assum `R = _` (fn th => pure_rewrite_tac[th]) >>
  simp[FOLDL_APPEND] >> pairarg_tac >>
  rename1 `_ = (prior,r0)` >> Cases_on `r0` >> gvs[] >>
  Cases_on `P sf.fn_name plan v` >> gvs[] >>
  Cases_on `r` >> gvs[]
QED

Theorem dft_packet_rooted_entry_context:
  !F C row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    levels paths incoming root_fn entry root_path root_depth pre sf plan E ent.
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
  (!f owner b s k t.
    s.vs_inst_idx + k <= LENGTH b.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) /\
    FOLDR (dft_exec_cons f C) OK
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + k /\
    exec_block f C b s = exec_block f C b t /\
    gas_events_block f C owner b s =
      gas_events_block f C owner
        (b with bb_instructions := TAKE (s.vs_inst_idx + k) b.bb_instructions) s ++
      gas_events_block f C owner b t) /\
  levels_ok F C levels paths incoming root_fn entry root_path root_depth /\
  levels = pre ++ [(sf,plan,NONE)] /\
  rooted_eval F C pre entry = (E,OK ent) ==>
  ?K : exec_result -> (string # num) list # exec_result.
    run_blocks (F-root_depth) C root_fn entry =
      SND (K (run_blocks (F-EL (LENGTH pre) incoming) C sf ent)) /\
    gas_events_blocks (F-root_depth) C root_fn entry =
      E ++ gas_events_blocks (F-EL (LENGTH pre) incoming) C sf ent ++
        FST (K (run_blocks (F-EL (LENGTH pre) incoming) C sf ent)) /\
    (!v. K (Halt v) = ([],Halt v)) /\
    (!a v. K (Abort a v) = ([],Abort a v)) /\
    (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `pre = []`
  >- (qpat_x_assum `rooted_eval _ _ pre _ = _` mp_tac >>
      qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
      simp[] >> strip_tac >>
      qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >>
      simp[] >> strip_tac >> qexists_tac `\r. ([],r)` >> simp[EL]) >>
  `?pre0 parent pp call. pre = pre0 ++ [(parent,pp,call)]` by
    (drule APPEND_FRONT_LAST >> strip_tac >>
     Cases_on `LAST pre` >> Cases_on `r` >> metis_tac[]) >>
  `levels <> [] /\ LENGTH paths = LENGTH levels /\ LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\ FST (HD levels) = root_fn` by
    (qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `?c nm ops bb e z.
     call = SOME c /\ pp <> [] /\ LAST pp = (bb,e,z) /\
     c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
     c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
     lookup_function nm C.ctx_functions = SOME sf /\
     EL (LENGTH pre) incoming = e` by suspend "caller" >>
  `levels_ok F' C (pre0 ++ [(parent,pp,NONE)])
     (TAKE (LENGTH pre) paths) (TAKE (LENGTH pre) incoming)
     root_fn entry root_path root_depth` by suspend "truncate" >>
  suspend "compose"
QED

Resume dft_packet_rooted_entry_context[caller]:
  qpat_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >> strip_tac >>
  qpat_assum `!i sf plan call. _`
    (qspecl_then [`LENGTH pre0`,`parent`,`pp`,`call`] mp_tac) >>
  (impl_tac >- simp[EL_APPEND1,EL_APPEND2]) >>
  qpat_assum `levels = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `pre = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms,EL_APPEND2] >> strip_tac >>
  qexistsl_tac [`nm`,`ops`,`bb`,`z`] >>
  qpat_x_assum `lookup_function nm _ = _` mp_tac >>
  simp[NoAsms,arithmeticTheory.ADD1] >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`] >> gvs[arithmeticTheory.ADD1]
QED

Resume dft_packet_rooted_entry_context[truncate]:
  qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`] >>
  `LENGTH pre = SUC (LENGTH pre0) /\ LENGTH levels = SUC (LENGTH pre)` by simp[] >>
  `!i. i <= LENGTH pre0 ==>
     TAKE i (pre0 ++ [(parent,pp,NONE)]) = TAKE i levels /\
     EL i (TAKE (LENGTH pre) incoming) = EL i incoming` by
    (rpt strip_tac >> simp[TAKE_APPEND1,EL_TAKE] >>
     simp[TAKE_APPEND] >> `i - LENGTH pre0 = 0` by decide_tac >> simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[LENGTH_TAKE]) >>
  (conj_tac >- simp[LENGTH_TAKE]) >>
  (conj_tac >- (Cases_on `paths` >> gvs[])) >>
  (conj_tac >- (Cases_on `incoming` >> gvs[])) >>
  (conj_tac >- (Cases_on `pre0` >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH pre0`
  >- suspend "truncate_last" >>
  suspend "truncate_earlier"
QED

Resume dft_packet_rooted_entry_context[truncate_last]:
  `EL (LENGTH pre0) (pre0 ++ [(parent,pp,NONE)]) = (parent,pp,NONE)` by
    simp[EL_APPEND2] >>
  `sf' = parent /\ plan' = pp /\ call' = NONE` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_assum `!i sf plan call. _`
    (qspecl_then [`LENGTH pre0`,`parent`,`pp`,`call`] mp_tac) >>
  (impl_tac >- simp[EL_APPEND1,EL_APPEND2]) >> strip_tac >>
  gvs[EL_TAKE,TAKE_APPEND] >> metis_tac[]
QED

Resume dft_packet_rooted_entry_context[truncate_earlier]:
  `i < LENGTH pre0` by gvs[] >>
  `EL i levels = (sf',plan',call')` by gvs[EL_APPEND1] >>
  qpat_assum `!i sf plan call. _`
    (qspecl_then [`i`,`sf'`,`plan'`,`call'`] mp_tac) >>
  (impl_tac >- (conj_tac >- gvs[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    `i <= LENGTH pre0` by decide_tac >>
    qpat_assum `!i. i <= LENGTH pre0 ==> _` drule >> strip_tac >>
    gvs[] >> metis_tac[])) >>
  Cases_on `SUC i < LENGTH pre0`
  >- (gvs[EL_APPEND1,EL_TAKE] >> metis_tac[]) >>
  `SUC i = LENGTH pre0` by decide_tac >>
  gvs[EL_TAKE,EL_APPEND2] >> metis_tac[]
QED

Resume dft_packet_rooted_entry_context[compose]:
  qpat_assum `rooted_eval = _`
    (fn th => mp_tac (Q.AP_THM (Q.AP_THM th `F'`) `C`)) >> BETA_TAC >> strip_tac >>
  `rooted_eval F' C (pre0 ++ [(parent,pp,call)]) entry = (E,OK ent)` by metis_tac[] >>
  drule_all entry_snoc_success >> strip_tac >>
  `?rs. pp = rs ++ [(bb,e,z)]` by metis_tac[APPEND_FRONT_LAST] >>
  `call_setup C c caller = OK ent` by
    (qpat_x_assum `(case call of NONE => _ | SOME c => _) = _` mp_tac >>
     qpat_assum `call = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  `rooted_eval F' C (pre0 ++ [(parent,pp,NONE)]) entry = (E,OK caller)` by
    (qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms,FOLDL_APPEND] >>
     qpat_assum `rooted_eval F' C pre0 entry = _` mp_tac >>
     qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >> strip_tac >> asm_rewrite_tac[] >> simp[NoAsms]) >>
  drule_all dft_packet_rooted_success_operational >> strip_tac >>
  FAIL_TAC "contexts"
QED

Finalise dft_packet_rooted_entry_context
