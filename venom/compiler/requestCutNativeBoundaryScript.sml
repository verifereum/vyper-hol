Theory requestCutNativeBoundary
Ancestors
  dftPacketClosedRowNative dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomInst venomState list rich_list arithmetic

Theorem request_cut_native_trace_stopped:
  !z s bb cut rest.
    DROP s.vs_inst_idx bb.bb_instructions = z ++ rest /\
    DROP s.vs_inst_idx cut.bb_instructions = z /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    ~(?u. FOLDR (dft_exec_cons f C) OK z s = OK u) ==>
    trace_block p d f C sf bb s = trace_block p d f C sf cut s
Proof
  Induct >> rpt gen_tac >> strip_tac >> gvs[] >>
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
  once_rewrite_tac[cj 2 trace_defs] >> simp[get_instruction_def] >>
  Cases_on `step_inst f C h s` >>
  gvs[dft_exec_cons_def] >> metis_tac[]
QED

Theorem request_cut_native_body_projection:
  !bb ps xs s be.
    bb.bb_instructions = ps ++ xs /\ s.vs_inst_idx <= LENGTH ps /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    FOLDR (dft_exec_cons f C) OK (DROP s.vs_inst_idx ps) s = OK be ==>
    exec_block f C bb s = exec_block f C bb be /\
    trace_gas (trace_block p d f C sf bb s) =
      trace_gas (trace_block p d f C sf bb be)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `k = LENGTH ps - s.vs_inst_idx` >>
  `s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
   TAKE k (DROP s.vs_inst_idx bb.bb_instructions) = DROP s.vs_inst_idx ps` by
    simp[Abbr `k`, DROP_APPEND, TAKE_APPEND, LENGTH_DROP] >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP s.vs_inst_idx ps)` by
    simp[EVERY_DROP] >>
  conj_tac
  >- (irule native_exec_block_prefix_skip >> qexists_tac `k` >> simp[] >>
      irule EVERY_MONOTONIC >> qexists_tac `\i. is_pseudo i.inst_opcode` >>
      simp[] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
      simp[is_pseudo_def,is_terminator_def]) >>
  irule native_trace_block_pseudo_skip >> qexists_tac `k` >> simp[]
QED

Theorem request_cut_native_invoke_stopped:
  !f C sf bb s inst nm ops callee args cs result.
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks f C callee cs = result /\
    ~(?u. result = OK u) /\ ~(?ir u. result = IntRet ir u) ==>
    exec_block f C bb s = result /\
    trace_gas (trace_block p d f C sf bb s) =
      trace_gas (trace_blocks ((d,inst.inst_id)::p) d f C callee cs)
Proof
  rpt strip_tac >>
  once_rewrite_tac[exec_block_def, cj 2 trace_defs] >>
  simp[Once step_inst_def, cj 1 trace_defs, trace_gas_def, visit_gas_def] >>
  Cases_on `result` >> gvs[]
QED
