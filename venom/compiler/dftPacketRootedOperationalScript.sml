Theory dftPacketRootedOperational
Ancestors
  dftPacketClosedRowNative dftPacketRootedCompose dftPacketRowAlignment
  dftAvailability gasEvents venomExecSemantics venomExecProofs
  dftIndexedExec venomInst list rich_list

Theorem dft_packet_run_block_context:
  !fuel C sf entry bb sp u E.
    lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    exec_block fuel C bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      exec_block fuel C bb u /\
    gas_events_block fuel C sf.fn_name bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      E ++ gas_events_block fuel C sf.fn_name bb u ==>
    ?K : exec_result -> (string # num) list # exec_result.
      run_blocks (SUC fuel) C sf entry = SND (K (exec_block fuel C bb u)) /\
      gas_events_blocks (SUC fuel) C sf entry =
        E ++ gas_events_block fuel C sf.fn_name bb u ++
          FST (K (exec_block fuel C bb u)) /\
      (!v. K (Halt v) = ([],Halt v)) /\
      (!a v. K (Abort a v) = ([],Abort a v)) /\
      (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def,gas_events_blocks_def] >> simp[] >>
  qexists_tac `\r. case r of
    OK s => if s.vs_halted then ([],Halt s)
      else (gas_events_blocks fuel C sf s,run_blocks fuel C sf s)
  | other => ([],other)` >>
  simp[] >>
  Cases_on `exec_block fuel C bb u` >> simp[APPEND_ASSOC] >>
  Cases_on `v.vs_halted` >> simp[APPEND_ASSOC]
QED

Theorem dft_packet_invoke_context:
  !fuel C owner bb s c nm ops callee args cs.
    get_instruction bb s.vs_inst_idx = SOME c /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    ?K : exec_result -> (string # num) list # exec_result.
      exec_block fuel C bb s = SND (K (run_blocks fuel C callee cs)) /\
      gas_events_block fuel C owner bb s =
        gas_events_blocks fuel C callee cs ++ FST (K (run_blocks fuel C callee cs)) /\
      (!v. K (Halt v) = ([],Halt v)) /\
      (!a v. K (Abort a v) = ([],Abort a v)) /\
      (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[exec_block_def,gas_events_block_def] >> simp[] >>
  simp[step_inst_def,gas_events_step_def,is_terminator_def] >>
  qexists_tac `\r. case r of
    IntRet ret child =>
      (case bind_outputs c.inst_outputs ret.iret_values
          (adopt_return_fmp ret (merge_callee_state s child)) of
        NONE => ([],Error "invoke: return arity mismatch")
      | SOME caller =>
          (gas_events_block fuel C owner bb
             (caller with vs_inst_idx := SUC s.vs_inst_idx),
           exec_block fuel C bb
             (caller with vs_inst_idx := SUC s.vs_inst_idx)))
  | OK v => ([],Error "invoke: callee did not return")
  | other => ([],other)` >>
  simp[] >> Cases_on `run_blocks fuel C callee cs` >> simp[] >>
  Cases_on `bind_outputs c.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >> simp[]
QED

Theorem dft_packet_partial_row_operational:
  !f C owner R bb z entry E u.
    (!b s k t.
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
    R = (\s. case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block f C owner
          (bb with bb_instructions :=
            TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons f C) OK z
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    LENGTH z <= LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    R entry = (E,OK u) ==>
    ?sp.
      eval_phis entry bb.bb_instructions = OK sp /\
      u.vs_inst_idx = phi_prefix_length bb.bb_instructions + LENGTH z /\
      u.vs_current_bb = entry.vs_current_bb /\
      exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
        exec_block f C bb u /\
      gas_events_block f C owner bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
        E ++ gas_events_block f C owner bb u
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `R entry = _` mp_tac >> simp[] >>
  Cases_on `eval_phis entry bb.bb_instructions` >> simp[] >> strip_tac >>
  rename1 `eval_phis entry bb.bb_instructions = OK sp` >>
  `phi_prefix_length bb.bb_instructions + LENGTH z <= LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_length_le) >>
     gvs[LENGTH_DROP]) >>
  first_x_assum (qspecl_then
    [`bb`,`sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`,`LENGTH z`,`u`]
    mp_tac) >>
  simp[] >> impl_tac >- metis_tac[] >> strip_tac >>
  `u.vs_current_bb = entry.vs_current_bb` by
    (drule_all dft_prefix_frame >>
     drule eval_phis_preserves_current_bb >> simp[]) >>
  simp[] >>
  `TAKE (phi_prefix_length bb.bb_instructions + LENGTH z) bb.bb_instructions =
    TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z` by
    metis_tac[TAKE_SUM] >> simp[]
  >> (gvs[])
QED

Theorem dft_packet_complete_row_operational:
  !f C sf bb entry sp u E.
    lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    FOLDR (dft_exec_cons f C) OK
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u /\
    gas_events_block f C sf.fn_name bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = E /\
    ~u.vs_halted ==>
    run_blocks (SUC f) C sf entry = run_blocks f C sf u /\
    gas_events_blocks (SUC f) C sf entry = E ++ gas_events_blocks f C sf u
Proof
  rpt gen_tac >> strip_tac >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    metis_tac[phi_prefix_length_lt_last_non_phi] >>
  `exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    FOLDR (dft_exec_cons f C) OK
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule native_exec_block_terminated_fold >> simp[DROP_EQ_NIL,last_drop]) >>
  conj_tac
  >- (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >> simp[]) >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >> simp[]
QED

Theorem dft_packet_plan_prefix_operational:
  !F C sf a R P plan entry.
    R = (\(bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
          (gas_events_block (F-e) C sf.fn_name
            (bb with bb_instructions :=
              TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
           FOLDR (dft_exec_cons (F-e) C) OK z
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    P = (\rows s. FOLDL (\(es,r) row. case r of
      OK t => (es ++ FST (R row t),SND (R row t))
    | other => (es,other)) ([],OK s) rows) /\
    (!i bb e z. SUC i < LENGTH plan /\ EL i plan = (bb,e,z) ==>
      e = a + SUC i /\ e <= F /\ bb.bb_instructions <> [] /\
      is_terminator (LAST bb.bb_instructions).inst_opcode /\
      z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    (!i bb e z es s. i < LENGTH plan /\ EL i plan = (bb,e,z) /\
      P (TAKE i plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < i ==> ~s.vs_halted)) ==>
    !k E u. k < LENGTH plan /\ P (TAKE k plan) entry = (E,OK u) ==>
      run_blocks (F-a) C sf entry = run_blocks (F-(a+k)) C sf u /\
      gas_events_blocks (F-a) C sf entry =
        E ++ gas_events_blocks (F-(a+k)) C sf u
Proof
  rpt gen_tac >> strip_tac >> Induct_on `k`
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < LENGTH plan` by decide_tac >>
  `TAKE (SUC k) plan = TAKE k plan ++ [EL k plan]` by
    simp[arithmeticTheory.ADD1,TAKE_EL_SNOC,SNOC_APPEND] >>
  qpat_assum `P (TAKE (SUC k) plan) entry = _` mp_tac >>
  qpat_assum `P = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  qpat_assum `TAKE (SUC k) plan = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then (mp_then Any mp_tac dft_packet_plan_last_success) >> strip_tac >>
  `P (TAKE k plan) entry = (prior,OK s)` by (simp[] >> (gvs[])) >>
  `run_blocks (F'-a) C sf entry = run_blocks (F'-(a+k)) C sf s /\
   gas_events_blocks (F'-a) C sf entry = prior ++ gas_events_blocks (F'-(a+k)) C sf s` by
    (qpat_x_assum `!E u. _` (qspecl_then [`prior`,`s`] mp_tac) >> simp[]) >>
  Cases_on `EL k plan` >> Cases_on `r` >> rename1 `EL k plan = (bb,e,z)` >>
  `e = a + SUC k /\ e <= F' /\ bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode /\
   z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` by
    metis_tac[] >>
  `lookup_block s.vs_current_bb sf.fn_blocks = SOME bb` by metis_tac[] >>
  `~u.vs_halted` by
    (Cases_on `EL (SUC k) plan` >> Cases_on `r` >>
     qpat_x_assum `!i bb e z es s. _`
       (qspec_then `SUC k` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `R _ _ = _` mp_tac >> simp[] >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >> strip_tac >>
  `F'-(a+k) = SUC (F'-e)` by decide_tac >>
  drule_all dft_packet_complete_row_operational >>
  simp[APPEND_ASSOC]
QED

Theorem dft_packet_plan_success_operational:
  !F C sf a R P plan entry rows bb e z E u.
    R = (\(bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
          (gas_events_block (F-e) C sf.fn_name
            (bb with bb_instructions :=
              TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
           FOLDR (dft_exec_cons (F-e) C) OK z
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    P = (\rows s. FOLDL (\(es,r) row. case r of
      OK t => (es ++ FST (R row t),SND (R row t))
    | other => (es,other)) ([],OK s) rows) /\
    (!b s k t.
      s.vs_inst_idx + k <= LENGTH b.bb_instructions /\
      EVERY (\i. ~is_terminator i.inst_opcode)
        (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) /\
      FOLDR (dft_exec_cons (F-e) C) OK
        (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) s = OK t ==>
      t.vs_inst_idx = s.vs_inst_idx + k /\
      exec_block (F-e) C b s = exec_block (F-e) C b t /\
      gas_events_block (F-e) C sf.fn_name b s =
        gas_events_block (F-e) C sf.fn_name
          (b with bb_instructions := TAKE (s.vs_inst_idx + k) b.bb_instructions) s ++
        gas_events_block (F-e) C sf.fn_name b t) /\
    (!i b d w. SUC i < LENGTH plan /\ EL i plan = (b,d,w) ==>
      d = a + SUC i /\ d <= F /\ b.bb_instructions <> [] /\
      is_terminator (LAST b.bb_instructions).inst_opcode /\
      w = DROP (phi_prefix_length b.bb_instructions) b.bb_instructions) /\
    (!i b d w es s. i < LENGTH plan /\ EL i plan = (b,d,w) /\
      P (TAKE i plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME b /\
      (0 < i ==> ~s.vs_halted)) /\
    plan = rows ++ [(bb,e,z)] /\ e = a + SUC (LENGTH rows) /\ e <= F /\
    LENGTH z <= LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\ P plan entry = (E,OK u) ==>
    u.vs_inst_idx = phi_prefix_length bb.bb_instructions + LENGTH z /\
    lookup_block u.vs_current_bb sf.fn_blocks = SOME bb /\
    ?K : exec_result -> (string # num) list # exec_result.
      run_blocks (F-a) C sf entry = SND (K (exec_block (F-e) C bb u)) /\
      gas_events_blocks (F-a) C sf entry =
        E ++ gas_events_block (F-e) C sf.fn_name bb u ++
          FST (K (exec_block (F-e) C bb u)) /\
      (!v. K (Halt v) = ([],Halt v)) /\
      (!a v. K (Abort a v) = ([],Abort a v)) /\
      (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `P plan entry = _` mp_tac >>
  qpat_assum `P = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  qpat_assum `plan = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then (mp_then Any mp_tac dft_packet_plan_last_success) >> strip_tac >>
  `TAKE (LENGTH rows) plan = rows` by simp[TAKE_APPEND] >>
  `P (TAKE (LENGTH rows) plan) entry = (prior,OK s)` by (simp[] >> gvs[]) >>
  `run_blocks (F'-a) C sf entry = run_blocks (F'-(a+LENGTH rows)) C sf s /\
   gas_events_blocks (F'-a) C sf entry =
     prior ++ gas_events_blocks (F'-(a+LENGTH rows)) C sf s` by
    (`LENGTH rows < LENGTH plan` by simp[] >>
     irule dft_packet_plan_prefix_operational >>
     qexistsl_tac [`P`,`R`,`plan`] >> simp[NoAsms] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb sf.fn_blocks = SOME bb` by
    (qpat_x_assum `!i b d w es s. _` (qspec_then `LENGTH rows` mp_tac) >>
     simp[EL_APPEND2] >> metis_tac[]) >>
  `?sp. eval_phis s bb.bb_instructions = OK sp /\
    u.vs_inst_idx = phi_prefix_length bb.bb_instructions + LENGTH z /\
    u.vs_current_bb = s.vs_current_bb /\
    exec_block (F'-e) C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      exec_block (F'-e) C bb u /\
    gas_events_block (F'-e) C sf.fn_name bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      es ++ gas_events_block (F'-e) C sf.fn_name bb u` by
    (irule dft_packet_partial_row_operational >> simp[] >> gvs[] >> metis_tac[]) >>
  `F'-(a+LENGTH rows) = SUC (F'-e)` by decide_tac >>
  drule_all dft_packet_run_block_context >>
  strip_tac >> simp[] >> (metis_tac[])
QED

Theorem dft_packet_rooted_snoc_success[local]:
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

Theorem dft_packet_rooted_success_operational:
  !F C row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    levels paths incoming root_fn entry root_path root_depth pre sf rows bb e z E u.
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
  levels = pre ++ [(sf,rows ++ [(bb,e,z)],NONE)] /\
  rooted_eval F C levels entry = (E,OK u) ==>
  u.vs_inst_idx = phi_prefix_length bb.bb_instructions + LENGTH z /\
  lookup_block u.vs_current_bb sf.fn_blocks = SOME bb /\ e <= F /\
  ?K : exec_result -> (string # num) list # exec_result.
    run_blocks (F-root_depth) C root_fn entry = SND (K (exec_block (F-e) C bb u)) /\
    gas_events_blocks (F-root_depth) C root_fn entry =
      E ++ gas_events_block (F-e) C sf.fn_name bb u ++ FST (K (exec_block (F-e) C bb u)) /\
    (!v. K (Halt v) = ([],Halt v)) /\
    (!a v. K (Abort a v) = ([],Abort a v)) /\
    (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  `!sfi a plan ent rowsi b ei zi Di caller.
    plan_ok F' C sfi a plan ent /\ plan = rowsi ++ [(b,ei,zi)] /\
    plan_eval F' C sfi.fn_name plan ent = (Di,OK caller) ==>
    caller.vs_inst_idx = phi_prefix_length b.bb_instructions + LENGTH zi /\
    lookup_block caller.vs_current_bb sfi.fn_blocks = SOME b /\ ei <= F' /\
    LENGTH zi < LENGTH (DROP (phi_prefix_length b.bb_instructions) b.bb_instructions) /\
    ?J : exec_result -> (string # num) list # exec_result.
      run_blocks (F'-a) C sfi ent = SND (J (exec_block (F'-ei) C b caller)) /\
      gas_events_blocks (F'-a) C sfi ent = Di ++
        gas_events_block (F'-ei) C sfi.fn_name b caller ++
        FST (J (exec_block (F'-ei) C b caller)) /\
      (!v. J (Halt v) = ([],Halt v)) /\
      (!a v. J (Abort a v) = ([],Abort a v)) /\
      (!msg. J (Error msg) = ([],Error msg))` by suspend "valid_plan" >>
  `!i sfi plani calli Ei enti.
    i < LENGTH levels /\ EL i levels = (sfi,plani,calli) /\
    rooted_eval F' C (TAKE i levels) entry = (Ei,OK enti) ==>
    ?Ki : exec_result -> (string # num) list # exec_result.
      run_blocks (F'-root_depth) C root_fn entry =
        SND (Ki (run_blocks (F'-EL i incoming) C sfi enti)) /\
      gas_events_blocks (F'-root_depth) C root_fn entry =
        Ei ++ gas_events_blocks (F'-EL i incoming) C sfi enti ++
        FST (Ki (run_blocks (F'-EL i incoming) C sfi enti)) /\
      (!v. Ki (Halt v) = ([],Halt v)) /\
      (!a v. Ki (Abort a v) = ([],Abort a v)) /\
      (!msg. Ki (Error msg) = ([],Error msg))` by suspend "rooted_prefix" >>
  suspend "finish"
QED

Resume dft_packet_rooted_success_operational[valid_plan]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_ok _ _ _ _ _ _` mp_tac >>
  qpat_assum `plan_ok = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  `!i bi di wi. i < LENGTH plan /\ EL i plan = (bi,di,wi) ==> di = a + SUC i` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `MAP _ plan = _` (mp_tac o Q.AP_TERM `EL i`) >>
     simp[EL_MAP,EL_GENLIST]) >>
  `EL (LENGTH rowsi) plan = (b,ei,zi)` by simp[EL_APPEND2] >>
  `LENGTH rowsi < LENGTH plan /\ ~(SUC (LENGTH rowsi) < LENGTH plan)` by simp[] >>
  `ei = a + SUC (LENGTH rowsi)` by metis_tac[] >>
  `ei <= F' /\ LENGTH zi < LENGTH (DROP (phi_prefix_length b.bb_instructions) b.bb_instructions) /\
   zi = TAKE (LENGTH zi) (DROP (phi_prefix_length b.bb_instructions) b.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) zi` by
    (qpat_assum `!r bb e z. _ ==> e <= _ /\ _`
       (qspecl_then [`LENGTH rowsi`,`b`,`ei`,`zi`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `if _ then _ else _` mp_tac >>
     qpat_assum `~(SUC (LENGTH rowsi) < LENGTH plan)`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `caller.vs_inst_idx = phi_prefix_length b.bb_instructions + LENGTH zi /\
   lookup_block caller.vs_current_bb sfi.fn_blocks = SOME b /\
   ?J : exec_result -> (string # num) list # exec_result.
     run_blocks (F'-a) C sfi ent = SND (J (exec_block (F'-ei) C b caller)) /\
     gas_events_blocks (F'-a) C sfi ent = Di ++
       gas_events_block (F'-ei) C sfi.fn_name b caller ++
       FST (J (exec_block (F'-ei) C b caller)) /\
     (!v. J (Halt v) = ([],Halt v)) /\
     (!a v. J (Abort a v) = ([],Abort a v)) /\
     (!msg. J (Error msg) = ([],Error msg))` suffices_by metis_tac[] >>
  irule dft_packet_plan_success_operational >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`plan_eval F' C sfi.fn_name`,`row_eval F' C sfi.fn_name`,`plan`,`rowsi`] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!r bb e z. _ ==> e <= _ /\ _`
      (qspecl_then [`i`,`b'`,`d`,`w`] mp_tac) >>
    (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
    qpat_assum `SUC i < LENGTH plan` (fn th => pure_rewrite_tac[th]) >>
    pure_rewrite_tac[COND_CLAUSES] >> strip_tac >>
    conj_tac >- (qpat_assum `!i bi di wi. _` irule >>
      conj_tac >- decide_tac >> qexistsl_tac [`b'`,`w`] >> first_assum ACCEPT_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms])) >>
  (conj_tac >- (qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms])) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_rooted_success_operational[rooted_prefix]:
  qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  Induct_on `i`
  >- (rpt gen_tac >> strip_tac >>
      `rooted_eval F' C [] entry = ([],OK entry)` by
        (qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
      `Ei = [] /\ enti = entry` by (qpat_x_assum `rooted_eval _ _ (TAKE 0 _) _ = _` mp_tac >> simp[TAKE_0,NoAsms] >>
         qpat_assum `rooted_eval F' C [] entry = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
      `sfi = root_fn /\ EL 0 incoming = root_depth` by
        (qpat_assum `FST (HD levels) = _` mp_tac >>
         qpat_assum `EL 0 levels = _` mp_tac >> simp[NoAsms,EL] >> metis_tac[EL]) >>
      qexists_tac `\r. ([],r)` >> simp[NoAsms] >> (simp[])) >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH levels` by decide_tac >>
  Cases_on `EL i levels` >> Cases_on `r` >> rename1 `EL i levels = (parent,plan,call)` >>
  `TAKE (SUC i) levels = TAKE i levels ++ [(parent,plan,call)]` by
    simp[TAKE_SUC_BY_TAKE,SNOC_APPEND] >>
  qpat_assum `rooted_eval = _`
    (fn th => mp_tac (Q.AP_THM (Q.AP_THM th `F'`) `C`)) >> BETA_TAC >> strip_tac >>
  `rooted_eval F' C (TAKE i levels ++ [(parent,plan,call)]) entry = (Ei,OK enti)` by
    metis_tac[] >>
  drule_all dft_packet_rooted_snoc_success >> strip_tac >>
  qpat_assum `!i sf plan call. _` (qspecl_then [`i`,`parent`,`plan`,`call`] mp_tac) >>
  (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `SUC i < LENGTH levels` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[COND_CLAUSES] >> strip_tac >>
  `plan_ok F' C parent (EL i incoming) plan ent` by
    (first_assum irule >> qexists_tac `prior` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!sfi plani calli Ei enti. _`
    (qspecl_then [`parent`,`plan`,`call`,`prior`,`ent`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (simp[]))) >> strip_tac >>
  `?rs. plan = rs ++ [(bb',e',z')]` by
    metis_tac[APPEND_FRONT_LAST] >>
  qpat_assum `!sfi a plan ent rowsi b ei zi Di caller. _`
    (qspecl_then [`parent`,`EL i incoming`,`plan`,`ent`,`rs`,`bb'`,`e'`,`z'`,`es`,`caller`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `lookup_function nm C.ctx_functions = SOME sfi` by
    (qpat_x_assum `lookup_function nm _ = _` mp_tac >> simp[]) >>
  `call_setup C c caller = OK enti` by
    (qpat_x_assum `(case call of NONE => _ | SOME c => _) = _` mp_tac >> simp[]) >>
  `?args. eval_operands ops caller = SOME args /\ setup_callee sfi args caller = SOME enti` by
    (qpat_x_assum `call_setup C c caller = _` mp_tac >>
     qpat_assum `call_setup = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >>
     qpat_assum `decode_invoke c = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `lookup_function nm _ = SOME sfi` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >> Cases_on `eval_operands ops caller`
     >- simp[] >> rename1 `eval_operands ops caller = SOME args` >>
     Cases_on `setup_callee sfi args caller` >> simp[]) >>
  `get_instruction bb' caller.vs_inst_idx = SOME c` by
    (`LENGTH z' + phi_prefix_length bb'.bb_instructions < LENGTH bb'.bb_instructions` by
       (qpat_x_assum `LENGTH z' < _` mp_tac >> simp[NoAsms,LENGTH_DROP] >> decide_tac) >>
     simp[get_instruction_def,listTheory.EL_DROP,arithmeticTheory.ADD_COMM]) >>
  qspecl_then [`F'-e'`,`C`,`parent.fn_name`,`bb'`,`caller`,`c`,`nm`,`ops`,`sfi`,`args`,`enti`]
    mp_tac dft_packet_invoke_context >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `H` strip_assume_tac) >>
  qexists_tac `\r. (FST (H r) ++ FST (J (SND (H r))) ++
    FST (Ki (SND (J (SND (H r))))), SND (Ki (SND (J (SND (H r))))))` >>
  simp[NoAsms] >>
  qpat_x_assum `run_blocks (F'-root_depth) _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `gas_events_blocks (F'-root_depth) _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Resume dft_packet_rooted_success_operational[finish]:
  qpat_assum `rooted_eval = _`
    (fn th => mp_tac (Q.AP_THM (Q.AP_THM th `F'`) `C`)) >> BETA_TAC >> strip_tac >>
  `rooted_eval F' C (pre ++ [(sf,rows ++ [(bb,e,z)],NONE)]) entry = (E,OK u)` by
    metis_tac[] >>
  drule_all dft_packet_rooted_snoc_success >> strip_tac >>
  `LENGTH pre < LENGTH levels /\ EL (LENGTH pre) levels = (sf,rows ++ [(bb,e,z)],NONE) /\
   TAKE (LENGTH pre) levels = pre` by simp[EL_APPEND2,TAKE_APPEND] >>
  qpat_assum `levels_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `levels_ok = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
  qpat_assum `!i sf plan call. _`
    (qspecl_then [`LENGTH pre`,`sf`,`rows ++ [(bb,e,z)]`,`NONE`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `plan_ok F' C sf (EL (LENGTH pre) incoming) (rows ++ [(bb,e,z)]) ent` by
    (qpat_assum `!prior ent. _ ==> plan_ok _ _ _ _ _ _` irule >>
     qexists_tac `prior` >>
     qpat_assum `TAKE (LENGTH pre) levels = pre` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `caller = u` by
    (qpat_x_assum `(case NONE of NONE => _ | SOME c => _) = _` mp_tac >> simp[NoAsms]) >>
  qpat_assum `!sfi a plan ent rowsi b ei zi Di caller. _`
    (qspecl_then [`sf`,`EL (LENGTH pre) incoming`,`rows ++ [(bb,e,z)]`,`ent`,`rows`,`bb`,`e`,`z`,`es`,`u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!i sfi plani calli Ei enti. _`
    (qspecl_then [`LENGTH pre`,`sf`,`rows ++ [(bb,e,z)]`,`NONE`,`prior`,`ent`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `TAKE (LENGTH pre) levels = pre` (fn th => pure_rewrite_tac[th]) >>
    first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists_tac `\r. (FST (J r) ++ FST (Ki (SND (J r))), SND (Ki (SND (J r))))` >>
  simp[NoAsms] >>
  qpat_x_assum `run_blocks (F'-root_depth) _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `gas_events_blocks (F'-root_depth) _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Finalise dft_packet_rooted_success_operational
