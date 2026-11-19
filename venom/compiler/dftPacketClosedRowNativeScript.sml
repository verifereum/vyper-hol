Theory dftPacketClosedRowNative
Ancestors
  dftGasFromListTraceDefs dftIndexedExec venomExecSemantics
  rich_list list arithmetic venomInst venomState

Theorem native_trace_block_suffix_cong:
  !a e fuel C sf bb bc s.
    DROP s.vs_inst_idx bb.bb_instructions =
      DROP s.vs_inst_idx bc.bb_instructions ==>
    trace_block a e fuel C sf bb s = trace_block a e fuel C sf bc s
Proof
  rpt gen_tac >>
  qsuff_tac `!xs bb bc s.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    DROP s.vs_inst_idx bc.bb_instructions = xs ==>
    trace_block a e fuel C sf bb s = trace_block a e fuel C sf bc s`
  >- metis_tac[] >>
  Induct_on `xs`
  >- (rpt strip_tac >>
      `LENGTH bb.bb_instructions <= s.vs_inst_idx /\
       LENGTH bc.bb_instructions <= s.vs_inst_idx` by
        (gvs[DROP_EQ_NIL]) >>
      once_rewrite_tac[trace_defs] >> simp[get_instruction_def]) >>
  rpt strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH bc.bb_instructions` by
    (gvs[LIST_EQ_REWRITE, LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx bc.bb_instructions = h` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _` (mp_tac o AP_TERM ``HD:instruction list -> instruction``) >>
     qpat_x_assum `DROP _ bc.bb_instructions = _` (mp_tac o AP_TERM ``HD:instruction list -> instruction``) >>
     simp[HD_DROP]) >>
  once_rewrite_tac[trace_defs] >> simp[get_instruction_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  IF_CASES_TAC >- simp[] >> simp[] >>
  first_x_assum irule >>
  qpat_x_assum `DROP _ bb.bb_instructions = _` (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
  qpat_x_assum `DROP _ bc.bb_instructions = _` (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
  simp[DROP_DROP, ADD1]
QED

Theorem native_trace_block_pseudo_skip:
  !a e fuel C sf bb k s t.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. is_pseudo i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t ==>
    trace_gas (trace_block a e fuel C sf bb s) =
      trace_gas (trace_block a e fuel C sf bb t)
Proof
  rpt gen_tac >> map_every qid_spec_tac [`t`,`s`,`k`] >>
  Induct_on `k` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by simp[DROP_CONS_EL] >>
  gvs[TAKE_def] >>
  qmatch_asmsub_abbrev_tac `is_pseudo i.inst_opcode` >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
   ~is_terminator i.inst_opcode` by
    (Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  rename1 `step_inst fuel C i s = OK u` >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    simp[get_instruction_def,Abbr `i`] >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`a`,`fuel`,`sf`,`e`,`C`] mp_tac) >>
  simp[trace_step_noninvoke] >> strip_tac >>
  simp[trace_gas_def, visit_gas_def] >>
  gvs[trace_gas_def]
QED

Theorem native_exec_block_prefix_skip:
  !fuel C bb k s t.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t ==>
    exec_block fuel C bb s = exec_block fuel C bb t
Proof
  rpt gen_tac >> map_every qid_spec_tac [`t`,`s`,`k`] >>
  Induct_on `k` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by simp[DROP_CONS_EL] >>
  gvs[TAKE_def,dft_exec_cons_def,AllCaseEqs()] >>
  rename1 `step_inst fuel C _ s = OK u` >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem native_exec_block_terminated_fold:
  !fuel C bb s xs.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    xs <> [] /\ is_terminator (LAST xs).inst_opcode ==>
    exec_block fuel C bb s = FOLDR (dft_exec_cons fuel C) OK xs s
Proof
  rpt gen_tac >>
  qsuff_tac `!xs s. xs <> [] /\ is_terminator (LAST xs).inst_opcode ==>
    dft_exec_suffix fuel C xs s = FOLDR (dft_exec_cons fuel C) OK xs s`
  >- (rpt strip_tac >> drule dft_exec_suffix_boundary >> simp[]) >>
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> Cases_on `xs` >>
  simp[dft_exec_suffix_def,dft_exec_cons_def] >>
  rpt strip_tac >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED
