Theory dftPacketRootedSegmentStop
Ancestors
  dftPacketRootedOperational dftPacketRootedPlainStop
  dftPacketOperationalPrefix

Theorem dft_packet_rooted_segment_stop:
  !F C row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    levels paths incoming root_fn entry pre sf rows bb e z E u k r.
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
  levels_ok F C levels paths incoming root_fn entry [] 0 /\
  levels = pre ++ [(sf,rows ++ [(bb,e,z)],NONE)] /\
  rooted_eval F C levels entry = (E,OK u) /\
  u.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
    (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) /\
  FOLDR (dft_exec_cons (F-e) C) OK
    (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) u = r /\
  ~(?v. r = OK v) ==>
  run_blocks F C root_fn entry = r /\
  gas_events_blocks F C root_fn entry =
    E ++ gas_events_block (F-e) C sf.fn_name
      (bb with bb_instructions := TAKE (u.vs_inst_idx + k) bb.bb_instructions) u
Proof
  rpt gen_tac >> strip_tac >>
  `!f owner b s k t.
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
      gas_events_block f C owner b t` by
    (rpt gen_tac >> strip_tac >>
     drule_all dft_packet_block_prefix_operational >>
     disch_then (qspecl_then [`f`,`C`,`owner`] mp_tac) >> simp[]) >>
  drule_all dft_packet_rooted_success_operational >>
  rewrite_tac[arithmeticTheory.SUB_0] >> strip_tac >>
  irule dft_packet_rooted_plain_prefix_stop >>
  metis_tac[]
QED
