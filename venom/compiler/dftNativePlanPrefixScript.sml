(* Native activation plans project to their own source execution.
   The literal lambda equations below are proof abbreviations, not definitions.
   Proper rows exclude RET, RETFMP and DRET so IntRet cannot escape.
   The stopped branch compares the source prefix with its own same-fuel run. *)
Theory dftNativePlanPrefix
Ancestors
  dftGasFromListTraceDefs dftIndexedExec gasEvents
  venomExecSemantics venomInst venomState opcodeClass list rich_list arithmetic

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

