Theory dftPacketCallFreshEntry
Ancestors
  dftPacketCalleeAlignment dftPacketFreshCut dftPacketFillingBoundary
  dftRunRel dftIndexedExec dftGasFromListTraceDefs gasEvents
  venomExecSemantics venomInst venomState venomExecProofs list rich_list arithmetic

Theorem dft_packet_call_source_setup:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME child_entry /\
  (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
  (!callee argv.
    setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0) /\
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
          | SOME cs => OK cs) ==>
  ?csf. lookup_function nm C7.ctx_functions = SOME csf /\
    ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
    eval_operands ops u = SOME args /\
    call_setup C7 c u = OK (child_entry with vs_gas_readings := u.vs_gas_readings)
Proof
  strip_tac >> drule_all dft_packet_callee_alignment >> strip_tac >>
  qexists_tac `csf` >> simp[]
QED


Theorem dft_packet_call_singleton_cut:
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
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  MEM bb sf.fn_blocks /\
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis entry (ps ++ ys) = OK sp /\ e = SUC d ==>
  ((!be q z ms ess ks.
    FOLDR (dft_exec_cons g C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
    ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs) /\
    ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(a,e,(EL r xs).inst_id)] else []) (LENGTH xs) ==>
    !F gs tail. e <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) gs ==>
      plan_ok F C7 sf d [(bb,e,z)] (entry with vs_gas_readings := gs ++ tail) /\
      (?extra. FLAT (TAKE q ess) = FST (plan_eval F C7 sf.fn_name [(bb,e,z)]
        (entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (!events u. plan_eval F C7 sf.fn_name [(bb,e,z)]
          (entry with vs_gas_readings := gs ++ tail) = (events,OK u) ==>
        events = FLAT (TAKE q ess) /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block a e (F-e) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
          (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT (TAKE q ks),gs) /\
        !tail'. plan_eval F C7 sf.fn_name [(bb,e,z)]
          (entry with vs_gas_readings := gs ++ tail') =
          (events,OK (u with vs_gas_readings := tail')))) /\
   (!k z t.
    phi_prefix_length (ps ++ ys) <= k /\ k < LENGTH ps /\
    z = DROP (phi_prefix_length bb.bb_instructions) (TAKE k ps) /\
    FOLDR (dft_exec_cons g C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) (TAKE k ps))
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK t ==>
    !F tail. e <= F ==>
      plan_ok F C7 sf d [(bb,e,z)] (entry with vs_gas_readings := tail) /\
      plan_eval F C7 sf.fn_name [(bb,e,z)] (entry with vs_gas_readings := tail) =
        ([],OK (t with vs_gas_readings := tail))))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  conj_tac >- suspend "body" >> suspend "pseudo"
QED

Resume dft_packet_call_singleton_cut[body]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >- suspend "body_valid" >> suspend "body_eval"
QED

Resume dft_packet_call_singleton_cut[pseudo]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >- suspend "pseudo_valid" >> suspend "pseudo_eval"
QED

Resume dft_packet_call_singleton_cut[body_valid]:
  qpat_x_assum `plan_ok = _` (fn th => rewrite_tac[th]) >>
  simp[dft_phi_prefix_append] >>
  `phi_prefix_length ps <= LENGTH ps` by simp[phi_prefix_length_le] >>
  simp[DROP_APPEND1, TAKE_APPEND2, EVERY_DROP] >>
  gvs[EVERY_CONJ]
QED

Resume dft_packet_call_singleton_cut[pseudo_valid]:
  qpat_x_assum `plan_ok = _` (fn th => rewrite_tac[th]) >>
  simp[dft_phi_prefix_append] >>
  gvs[dft_phi_prefix_append] >>
  simp[DROP_TAKE, DROP_APPEND1, TAKE_APPEND1, EVERY_DROP, EVERY_TAKE]
QED

Resume dft_packet_call_singleton_cut[body_eval]:
  drule dft_packet_flat_filling_split >> strip_tac >>
  qabbrev_tac `R = row_eval F' C7 sf.fn_name (bb,e,z)` >>
  `!ent. plan_eval F' C7 sf.fn_name [(bb,e,z)] ent = R ent` by
    simp[Abbr `R`] >>
  `R = (\ent. case eval_phis ent bb.bb_instructions of
      OK sp =>
        (gas_events_block (F'-e) C7 sf.fn_name
          (bb with bb_instructions :=
            TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F'-e) C7) OK z
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other))` by simp[Abbr `R`] >>
  drule_all dft_packet_fresh_body_cut >>
  disch_then (qspec_then `tail` strip_assume_tac) >>
  qpat_x_assum `R = _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `row_eval = _` kall_tac >>
  gvs[]
QED

Resume dft_packet_call_singleton_cut[pseudo_eval]:
  qabbrev_tac `R = row_eval F' C7 sf.fn_name (bb,e,z)` >>
  `!ent. plan_eval F' C7 sf.fn_name [(bb,e,z)] ent = R ent` by
    simp[Abbr `R`] >>
  `R = (\ent. case eval_phis ent bb.bb_instructions of
      OK sp =>
        (gas_events_block (F'-e) C7 sf.fn_name
          (bb with bb_instructions :=
            TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F'-e) C7) OK z
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other))` by simp[Abbr `R`] >>
  drule_all dft_packet_fresh_pseudo_cut >>
  disch_then (qspec_then `tail` assume_tac) >>
  qpat_x_assum `R = _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `row_eval = _` kall_tac >>
  gvs[]
QED

Finalise dft_packet_call_singleton_cut
