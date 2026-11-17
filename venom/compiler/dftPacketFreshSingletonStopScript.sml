Theory dftPacketFreshSingletonStop
Ancestors
  dftPacketFreshSingletonNormalize dftPacketFreshChildStop
  dftIndexedExec gasEvents venomExecSemantics venomInst venomState
  list rich_list arithmetic

Theorem dft_packet_fresh_singleton_root_stop:
  !row_eval plan_eval cb cps cxs cys child_entry csp m z k F C7 csf
    readings child_events r e root_sf root_entry' K bb u E sf c nm ops args.
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
  cb.bb_instructions = cps ++ cxs /\
  EVERY (\i. is_pseudo i.inst_opcode) cps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cxs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cys /\
  eval_phis child_entry (cps ++ cys) = OK csp /\
  m = phi_prefix_length cb.bb_instructions /\
  z = TAKE k (DROP m cb.bb_instructions) /\
  k < LENGTH (DROP m cb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) z /\
  plan_eval F C7 csf.fn_name [(cb,SUC e,z)]
    (child_entry with vs_gas_readings := readings) = (child_events,r) /\
  ~(?v. r = OK v) /\ e < F /\
  run_blocks F C7 root_sf root_entry' = SND (K (exec_block (F-e) C7 bb u)) /\
  gas_events_blocks F C7 root_sf root_entry' =
    E ++ gas_events_block (F-e) C7 sf.fn_name bb u ++
      FST (K (exec_block (F-e) C7 bb u)) /\
  (!v. K (Halt v) = ([],Halt v)) /\
  (!a v. K (Abort a v) = ([],Abort a v)) /\
  (!msg. K (Error msg) = ([],Error msg)) /\
  get_instruction bb u.vs_inst_idx = SOME c /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C7.ctx_functions = SOME csf /\
  eval_operands ops u = SOME args /\
  setup_callee csf args u = SOME (child_entry with vs_gas_readings := readings) /\
  lookup_block child_entry.vs_current_bb csf.fn_blocks = SOME cb ==>
  run_blocks F C7 root_sf root_entry' = r /\
  gas_events_blocks F C7 root_sf root_entry' = E ++ child_events
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `plan_eval fuel C7 csf.fn_name _ _ = _` >>
  `k <= LENGTH (DROP m cb.bb_instructions)` by decide_tac >>
  drule_all dft_packet_fresh_singleton_source_prefix >>
  disch_then (qspecl_then [`fuel`,`C7`,`csf.fn_name`,`SUC e`,`readings`]
    (qx_choose_then `sp'` strip_assume_tac)) >>
  qpat_x_assum `row_eval = _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  `phi_prefix_length cb.bb_instructions + k <= LENGTH cb.bb_instructions` by
    (gvs[LENGTH_DROP] >> decide_tac) >>
  `lookup_block (child_entry with vs_gas_readings := readings).vs_current_bb
    csf.fn_blocks = SOME cb` by simp[] >>
  `FOLDR (dft_exec_cons (fuel-SUC e) C7) OK
    (TAKE k (DROP (phi_prefix_length cb.bb_instructions) cb.bb_instructions))
    (sp' with vs_inst_idx := phi_prefix_length cb.bb_instructions) = r` by
    metis_tac[pairTheory.PAIR_EQ] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
    (TAKE k (DROP (phi_prefix_length cb.bb_instructions) cb.bb_instructions))` by
    metis_tac[] >>
  drule_all dft_packet_fresh_child_root_stop >>
  strip_tac >> gvs[]
QED
