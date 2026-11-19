Theory requestCutPacketExecution
Ancestors
  requestCutNativeBoundary dftGasFromListTraceDefs dftGasFromListReadings
  venomExecSemantics venomInst venomState list rich_list arithmetic

Theorem request_cut_native_block_stopped:
  lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp /\
  exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r /\
  ~(?t. r = OK t) ==>
  run_blocks (SUC f) C sf s = r /\
  trace_gas (trace_blocks a d (SUC f) C sf s) =
    trace_gas (trace_block a (SUC d) f C sf bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  rpt strip_tac >>
  once_rewrite_tac[run_blocks_def, cj 3 trace_defs] >>
  Cases_on `r` >> gvs[]
QED

Theorem request_cut_plan_fold_result:
  !(row_eval:'row -> venom_state -> 'event list # exec_result) rows events r.
    SND (FOLDL (\(es,v) row. case v of
      OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
    | stopped => (es,stopped)) (events,r) rows) =
    FOLDL (\v row. case v of OK s => SND (row_eval row s) | stopped => stopped) r rows
Proof
  gen_tac >> Induct >> simp[] >> rpt gen_tac >> Cases_on `r` >> simp[]
QED

(* Active instructions transfer no GAS key at an INVOKE head. A callee
   that stops can contribute keys only through its own native trace. *)
Theorem request_cut_packet_call_stopped:
  lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis hin bb.bb_instructions = OK sp /\
  exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    exec_block f C bb caller /\
  MAP FST (trace_gas (trace_block a (SUC d) f C sf bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))) =
    prefix ++ MAP FST (trace_gas (trace_block a (SUC d) f C sf bb caller)) /\
  get_instruction bb caller.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\ lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME entry /\
  run_blocks f C callee entry = stopped /\ ~(?u. stopped = OK u) /\
  ~(?ir u. stopped = IntRet ir u) /\
  ks = MAP FST (trace_gas (trace_blocks ((SUC d,inst.inst_id)::a) (SUC d) f C callee entry)) ++ extra ==>
  run_blocks (SUC f) C sf hin = stopped /\
  prefix ++ ks = MAP FST (trace_gas (trace_blocks a d (SUC f) C sf hin)) ++ extra
Proof
  strip_tac >>
  `exec_block f C bb caller = stopped /\
   trace_gas (trace_block a (SUC d) f C sf bb caller) =
     trace_gas (trace_blocks ((SUC d,inst.inst_id)::a) (SUC d) f C callee entry)` by
    (irule request_cut_native_invoke_stopped >> rpt (first_assum (irule_at Any))) >>
  `exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = stopped` by
    metis_tac[] >>
  drule_all request_cut_native_block_stopped >>
  disch_then (qspecl_then [`d`,`a`] strip_assume_tac) >>
  gvs[APPEND_ASSOC]
QED
