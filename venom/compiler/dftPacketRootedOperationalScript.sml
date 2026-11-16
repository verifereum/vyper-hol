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

Theorem dft_packet_plan_prefix_operational[local]:
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
