Theory dftPacketBlockRootedOperational
Ancestors
  dftPacketRootedEntryContext dftPacketCompletePlanOperational
  gasEvents venomExecSemantics dftIndexedExec venomInst list rich_list

Theorem dft_packet_block_rooted_operational:
  !F C row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    levels paths incoming root_fn entry root_path root_depth
    pre sf rows bb d z0 Z E v.
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
  levels = pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)] /\
  bb.bb_instructions <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  Z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\ d < F /\
  rooted_eval F C (pre ++ [(sf,rows ++ [(bb,d,Z)],NONE)]) entry = (E,OK v) /\
  ~v.vs_halted ==>
  ?K : exec_result -> (string # num) list # exec_result.
    run_blocks (F-root_depth) C root_fn entry =
      SND (K (run_blocks (F-d) C sf v)) /\
    gas_events_blocks (F-root_depth) C root_fn entry =
      E ++ gas_events_blocks (F-d) C sf v ++
        FST (K (run_blocks (F-d) C sf v)) /\
    (!w. K (Halt w) = ([],Halt w)) /\
    (!a w. K (Abort a w) = ([],Abort a w)) /\
    (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  `?prior ent events.
    rooted_eval F' C pre entry = (prior,OK ent) /\
    plan_eval F' C sf.fn_name (rows ++ [(bb,d,Z)]) ent = (events,OK v) /\
    E = prior ++ events` by
    (qpat_x_assum `rooted_eval _ _ (pre ++ _) _ = _` mp_tac >>
     qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
        `plan_ok = _`,`levels_ok = _`,`Z = _`] >>
     simp[NoAsms,FOLDL_APPEND] >> pairarg_tac >>
     rename1 `_ = (prior,r0)` >> Cases_on `r0` >> gvs[] >>
     Cases_on `plan_eval F' C sf.fn_name (rows ++ [(bb,d,Z)]) v'` >> gvs[] >>
     Cases_on `r` >> gvs[]) >>
  `plan_ok F' C sf (EL (LENGTH pre) incoming) (rows ++ [(bb,d,z0)]) ent` by
    (qpat_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> strip_tac >>
     qpat_assum `!i sf plan call. _`
       (qspecl_then [`LENGTH pre`,`sf`,`rows ++ [(bb,d,z0)]`,`NONE`] mp_tac) >>
     (impl_tac >- simp[EL_APPEND2]) >> strip_tac >>
     qpat_assum `!prior ent. _ ==> plan_ok _ _ _ _ _ _` irule >>
     qexists_tac `prior` >>
     qpat_assum `levels = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms,TAKE_APPEND] >> first_assum ACCEPT_TAC) >>
  drule_all dft_packet_rooted_entry_context >> strip_tac >>
  suspend "complete"
QED

Resume dft_packet_block_rooted_operational[complete]:
  `row_eval F' C sf.fn_name = (\(bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (F'-e) C sf.fn_name
          (bb with bb_instructions :=
            TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F'-e) C) OK z
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other))` by
    (qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  `plan_eval F' C sf.fn_name = (\rows s.
    FOLDL (\(es,r) row. case r of
      OK t => (es ++ FST (row_eval F' C sf.fn_name row t),
               SND (row_eval F' C sf.fn_name row t))
    | other => (es,other)) ([],OK s) rows)` by
    (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  qpat_x_assum `plan_ok _ _ _ _ _ _` mp_tac >>
  qpat_assum `plan_ok = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`] >>
  `!i b e z. i < LENGTH (rows ++ [(bb,d,z0)]) /\
    EL i (rows ++ [(bb,d,z0)]) = (b,e,z) ==>
    e = EL (LENGTH pre) incoming + SUC i` by
    (rpt strip_tac >>
     qpat_assum `MAP _ _ = GENLIST _ _`
       (mp_tac o Q.AP_TERM `EL i`) >> simp[EL_MAP,EL_GENLIST]) >>
  `d = EL (LENGTH pre) incoming + SUC (LENGTH rows)` by
    (qpat_assum `!i b e z. _ ==> e = _`
       (qspecl_then [`LENGTH rows`,`bb`,`d`,`z0`] mp_tac) >> simp[EL_APPEND2]) >>
  `run_blocks (F'-EL (LENGTH pre) incoming) C sf ent = run_blocks (F'-d) C sf v /\
   gas_events_blocks (F'-EL (LENGTH pre) incoming) C sf ent =
     events ++ gas_events_blocks (F'-d) C sf v` by
    (irule dft_packet_complete_plan_operational >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- decide_tac) >>
     qexistsl_tac [`plan_eval F' C sf.fn_name`,`row_eval F' C sf.fn_name`,
       `Z`,`bb`,`rows ++ [(bb,d,z0)]`,`rows`,`z0`] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (rpt gen_tac >> strip_tac >>
        `i < LENGTH (rows ++ [(bb,d,z0)])` by
          (qpat_x_assum `SUC i < _` mp_tac >> simp[NoAsms]) >>
        qpat_assum `!r bb e z. _ ==> e <= _ /\ _`
          (qspecl_then [`i`,`b`,`e`,`z`] mp_tac) >>
        (impl_tac >- simp[]) >> pure_asm_rewrite_tac[] >> rewrite_tac[] >> strip_tac >>
        qpat_assum `!i b e z. _ ==> e = _`
          (qspecl_then [`i`,`b`,`e`,`z`] mp_tac) >> simp[])) >>
     rpt conj_tac >> (simp[])) >>
  qexists_tac `K'` >> simp[APPEND_ASSOC]
QED

Finalise dft_packet_block_rooted_operational
