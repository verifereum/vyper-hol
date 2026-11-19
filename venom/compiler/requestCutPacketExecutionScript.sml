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
