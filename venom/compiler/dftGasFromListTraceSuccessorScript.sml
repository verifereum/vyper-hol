Theory dftGasFromListTraceSuccessor
Ancestors
  dftGasFromListTraceLift dftGasFromListTraceExtend dftGasFromListLookup
  dftGasFromListTracePrefix frameExecutionPrefix frameInvokeReturn
  dftGasFromListOpenTrace dftGasFromListTraceDefs venomInstProofs
  venomExecProofs venomExecSemantics venomWf contextCodegenRel
  venomInst venomState list rich_list arithmetic

Theorem trace_context_next:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  wf_function fn /\ active_inst fn inst t /\
  ~is_terminator inst.inst_opcode /\ step_inst f ctx inst t = OK u /\
  active_inst fn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  !b. ?m. b <= m /\
    MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
      (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all wf_active_lookup >> strip_tac >> gvs[] >>
  `MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
    (open_trace p d f ctx fn bb t)` by
    (drule_all open_trace_next >>
     disch_then (qspecl_then [`p`,`fn`,`d`] SUBST1_TAC) >>
     `MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
       (trace_block p d f ctx fn bb (u with vs_inst_idx := SUC t.vs_inst_idx))` by
       simp[Once trace_defs] >>
     simp[open_trace_def]) >>
  gen_tac >> qpat_x_assum `!k b. _` (qspecl_then [`f`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED

Theorem trace_context_next_cut:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
               f.fn_blocks) ctx.ctx_functions /\
  j < LENGTH (trace_context n ctx vs0) /\
  EL j (trace_context n ctx vs0) = ((p,d,inst.inst_id),fn,inst,t) /\
  wf_function fn /\ active_inst fn inst t /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst f ctx inst t = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  !b. ?m. MAX n b <= m /\
    SUC j < LENGTH (trace_context m ctx vs0) /\
    EL (SUC j) (trace_context m ctx vs0) =
      ((p,d,next.inst_id),fn,next,u with vs_inst_idx := SUC t.vs_inst_idx) /\
    TAKE (SUC j) (trace_context m ctx vs0) =
      TAKE j (trace_context n ctx vs0) ++ [((p,d,inst.inst_id),fn,inst,t)]
Proof
  strip_tac >>
  `MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx vs0)` by
    metis_tac[EL_MEM] >>
  drule trace_context_cofinal_factor >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all wf_active_lookup >> strip_tac >> gvs[] >> gen_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`f`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  `n <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `LENGTH pre = j /\ pre = TAKE j (trace_context n ctx vs0)` by
    (drule_all trace_context_factor_cursor >> simp[]) >>
  `step_inst remain ctx inst t = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `f` >> simp[]) >>
  `?rest. open_trace p d remain ctx fn bb t =
    ((p,d,inst.inst_id),fn,inst,t)::
    ((p,d,next.inst_id),fn,next,u with vs_inst_idx := SUC t.vs_inst_idx)::rest` by
    (drule_all open_trace_next >>
     disch_then (qspecl_then [`p`,`fn`,`d`] SUBST1_TAC) >>
     simp[trace_step_noninvoke, open_trace_def, Once (cj 2 trace_defs)]) >>
  qexists_tac `m` >> conj_tac >- (gvs[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `pre = TAKE j (trace_context n ctx vs0)`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `LENGTH pre = j` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `trace_context m ctx vs0 =
    pre ++ open_trace p d remain ctx fn bb t ++ post` SUBST1_TAC >>
  qpat_x_assum `open_trace p d remain ctx fn bb t = _` SUBST1_TAC >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, ADD1]
QED

Theorem trace_context_block:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  wf_function fn /\ is_terminator inst.inst_opcode /\
  step_inst f ctx inst t = OK u /\ ~u.vs_halted /\
  enters_block fn u z /\ active_inst fn j z ==>
  !b. ?m. b <= m /\
    MEM ((p,SUC d,j.inst_id),fn,j,z) (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `MEM ((p,SUC d,j.inst_id),fn,j,z)
    (trace_blocks p d (SUC f) ctx fn u)` by
    (irule trace_entered_head >> simp[]) >>
  `step_inst (SUC f) ctx inst t = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `f` >> simp[]) >>
  `exec_block (SUC f) ctx bb t = OK u` by
    simp[Once exec_block_def] >>
  `MEM ((p,SUC d,j.inst_id),fn,j,z)
    (open_trace p d (SUC f) ctx fn bb t)` by simp[open_trace_def] >>
  gen_tac >> qpat_x_assum `!k b. _`
    (qspecl_then [`SUC f`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED

Theorem trace_context_block_cut:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
               f.fn_blocks) ctx.ctx_functions /\
  j < LENGTH (trace_context n ctx vs0) /\
  EL j (trace_context n ctx vs0) = ((p,d,inst.inst_id),fn,inst,t) /\
  wf_function fn /\ is_terminator inst.inst_opcode /\
  step_inst f ctx inst t = OK u /\ ~u.vs_halted /\
  enters_block fn u entered /\ active_inst fn next entered ==>
  !b. ?m. MAX n b <= m /\
    SUC j < LENGTH (trace_context m ctx vs0) /\
    EL (SUC j) (trace_context m ctx vs0) =
      ((p,SUC d,next.inst_id),fn,next,entered) /\
    TAKE (SUC j) (trace_context m ctx vs0) =
      TAKE j (trace_context n ctx vs0) ++ [((p,d,inst.inst_id),fn,inst,t)]
Proof
  strip_tac >>
  `MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx vs0)` by
    metis_tac[EL_MEM] >>
  drule trace_context_cofinal_factor >> strip_tac >>
  drule_all entered_active_lookup >>
  disch_then (qx_choosel_then [`dest`,`sp`] strip_assume_tac) >>
  `get_instruction dest (phi_prefix_length dest.bb_instructions) = SOME next` by gvs[] >>
  gen_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`SUC f`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  `n <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `LENGTH pre = j /\ pre = TAKE j (trace_context n ctx vs0)` by
    (drule_all trace_context_factor_cursor >> simp[]) >>
  `step_inst remain ctx inst t = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `f` >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `remain = SUC (PRE remain)` by decide_tac >>
  `?rest. trace_blocks p d remain ctx fn u =
      ((p,SUC d,next.inst_id),fn,next,entered)::rest` by
    (qpat_assum `remain = SUC (PRE remain)` (fn th => once_rewrite_tac[th]) >>
     drule_all trace_blocks_open >>
     disch_then (qspecl_then [`p`,`PRE remain`,`d`,`ctx`] SUBST1_TAC) >>
     simp[open_trace_def, Once (cj 2 trace_defs)]) >>
  `?rest. open_trace p d remain ctx fn bb t =
      ((p,d,inst.inst_id),fn,inst,t)::
      ((p,SUC d,next.inst_id),fn,next,entered)::rest` by
    simp[open_trace_def, Once (cj 2 trace_defs), Once exec_block_def,
         trace_step_noninvoke] >>
  qexists_tac `m` >> conj_tac >- (gvs[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `pre = TAKE j (trace_context n ctx vs0)`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `LENGTH pre = j` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `trace_context m ctx vs0 =
    pre ++ open_trace p d remain ctx fn bb t ++ post` SUBST1_TAC >>
  qpat_x_assum `open_trace p d remain ctx fn bb t = _` SUBST1_TAC >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, ADD1]
QED

Theorem trace_context_callee_cut:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
               f.fn_blocks) ctx.ctx_functions /\
  j < LENGTH (trace_context n ctx vs0) /\
  EL j (trace_context n ctx vs0) = ((p,d,inst.inst_id),fn,inst,t) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\ wf_function callee /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs /\
  enters_block callee cs entered /\ active_inst callee next entered ==>
  !b. ?m. MAX n b <= m /\
    SUC j < LENGTH (trace_context m ctx vs0) /\
    EL (SUC j) (trace_context m ctx vs0) =
      ((((d,inst.inst_id)::p),SUC d,next.inst_id),callee,next,entered) /\
    TAKE (SUC j) (trace_context m ctx vs0) =
      TAKE j (trace_context n ctx vs0) ++ [((p,d,inst.inst_id),fn,inst,t)]
Proof
  strip_tac >>
  `MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx vs0)` by
    metis_tac[EL_MEM] >>
  drule trace_context_cofinal_factor >> strip_tac >>
  drule_all entered_active_lookup >>
  disch_then (qx_choosel_then [`dest`,`sp`] strip_assume_tac) >>
  `get_instruction dest (phi_prefix_length dest.bb_instructions) = SOME next` by gvs[] >>
  gen_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`1`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  `n <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `LENGTH pre = j /\ pre = TAKE j (trace_context n ctx vs0)` by
    (drule_all trace_context_factor_cursor >> simp[]) >>
  `remain = SUC (PRE remain)` by decide_tac >>
  `?rest. trace_step p d remain ctx fn inst t =
      ((((d,inst.inst_id)::p),SUC d,next.inst_id),callee,next,entered)::rest` by
    (simp[Once (cj 1 trace_defs)] >>
     qpat_assum `remain = SUC (PRE remain)` (fn th => once_rewrite_tac[th]) >>
     drule_all trace_blocks_open >>
     disch_then (qspecl_then [`(d,inst.inst_id)::p`,`PRE remain`,`d`,`ctx`] SUBST1_TAC) >>
     simp[open_trace_def, Once (cj 2 trace_defs)]) >>
  `?rest. open_trace p d remain ctx fn bb t =
      ((p,d,inst.inst_id),fn,inst,t)::
      ((((d,inst.inst_id)::p),SUC d,next.inst_id),callee,next,entered)::rest` by
    simp[open_trace_def, Once (cj 2 trace_defs), APPEND_ASSOC] >>
  qexists_tac `m` >> conj_tac >- (gvs[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `pre = TAKE j (trace_context n ctx vs0)`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `LENGTH pre = j` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `trace_context m ctx vs0 =
    pre ++ open_trace p d remain ctx fn bb t ++ post` SUBST1_TAC >>
  qpat_x_assum `open_trace p d remain ctx fn bb t = _` SUBST1_TAC >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, ADD1]
QED

Theorem actual_return_trace_stable[local]:
  wf_function fn /\ execution_prefix ctx fn entry inst t /\
  MEM ((p,h,inst.inst_id),fn,inst,t) (trace_blocks p d n ctx fn entry) /\
  inst.inst_opcode = RET /\ step_inst ret_fuel ctx inst t = IntRet ret send ==>
  ?done pre. run_blocks done ctx fn entry = IntRet ret send /\
    !m. done <= m ==>
      trace_blocks p d m ctx fn entry = pre ++ [((p,h,inst.inst_id),fn,inst,t)]
Proof
  strip_tac >> drule_all execution_prefix_return >>
  disch_then (qx_choose_then `completed` strip_assume_tac) >>
  drule_all trace_blocks_actual_return_suffix >>
  disch_then (qspec_then `completed`
    (qx_choosel_then [`done`,`pre`] strip_assume_tac)) >>
  `run_blocks done ctx fn entry = IntRet ret send` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `completed` >> simp[]) >>
  qexistsl_tac [`done`,`pre`] >> simp[] >> rpt strip_tac >>
  `trace_blocks p d m ctx fn entry = trace_blocks p d done ctx fn entry` by
    (irule (cj 3 trace_stable) >> simp[]) >> simp[]
QED

Theorem trace_context_return_cut:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
               f.fn_blocks) ctx.ctx_functions /\
  j < LENGTH (trace_context n ctx vs0) /\
  EL j (trace_context n ctx vs0) =
    ((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t) /\
  MEM ((p,d,callinst.inst_id),caller_fn,callinst,caller)
    (trace_context n ctx vs0) /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\
  setup_callee callee args caller = SOME cs /\
  wf_function caller_fn /\ wf_function callee /\
  execution_prefix ctx callee cs retinst t /\
  MEM ((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)
    (trace_blocks ((d,callinst.inst_id)::p) d child_fuel ctx callee cs) /\
  retinst.inst_opcode = RET /\
  step_inst ret_fuel ctx retinst t = IntRet ret send /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller send)) = SOME post /\
  active_inst caller_fn next (post with vs_inst_idx := SUC caller.vs_inst_idx) ==>
  !b. ?m. MAX n b <= m /\
    SUC j < LENGTH (trace_context m ctx vs0) /\
    EL (SUC j) (trace_context m ctx vs0) =
      ((p,d,next.inst_id),caller_fn,next,post with vs_inst_idx := SUC caller.vs_inst_idx) /\
    TAKE (SUC j) (trace_context m ctx vs0) =
      TAKE j (trace_context n ctx vs0) ++
      [((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)]
Proof
  strip_tac >> drule_all actual_return_trace_stable >>
  disch_then (qx_choosel_then [`done`,`childpre`] strip_assume_tac) >>
  `active_inst callee retinst t` by metis_tac[execution_prefix_active] >>
  drule_all wf_active_lookup >>
  disch_then (qx_choose_then `retbb` strip_assume_tac) >>
  `open_trace ((d,callinst.inst_id)::p) h ret_fuel ctx callee retbb t =
      [((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)]` by
    simp[open_trace_def, Once (cj 2 trace_defs), Once exec_block_def,
         trace_step_noninvoke] >>
  drule trace_context_cofinal_factor >>
  disch_then (qx_choose_then `callbb` strip_assume_tac) >> gen_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`done`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`outer_suffix`] strip_assume_tac)) >>
  `n <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `run_blocks remain ctx callee cs = IntRet ret send` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `done` >> simp[]) >>
  `step_inst remain ctx callinst caller = OK post` by
    (drule_all matched_run_invoke_return >> simp[]) >>
  `~is_terminator callinst.inst_opcode` by simp[is_terminator_def] >>
  `post.vs_current_bb = caller.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `get_instruction callbb (SUC caller.vs_inst_idx) = SOME next` by
    (mp_tac (Q.INST [`fn` |-> `caller_fn`, `inst` |-> `next`,
       `s` |-> `post with vs_inst_idx := SUC caller.vs_inst_idx`] wf_active_lookup) >>
     simp[]) >>
  `trace_step p d remain ctx caller_fn callinst caller = childpre ++
      [((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)]` by
    simp[Once (cj 1 trace_defs)] >>
  `?rest. open_trace p d remain ctx caller_fn callbb caller =
      ((p,d,callinst.inst_id),caller_fn,callinst,caller)::
      (childpre ++
        ((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)::
        ((p,d,next.inst_id),caller_fn,next,
          post with vs_inst_idx := SUC caller.vs_inst_idx)::rest)` by
    (drule_all open_trace_next >>
     disch_then (qspecl_then [`p`,`caller_fn`,`d`] SUBST1_TAC) >>
     simp[open_trace_def, Once (cj 2 trace_defs), APPEND_ASSOC]) >>
  qabbrev_tac `before_ret = pre ++
    [((p,d,callinst.inst_id),caller_fn,callinst,caller)] ++ childpre` >>
  `trace_context m ctx vs0 = before_ret ++
      open_trace ((d,callinst.inst_id)::p) h ret_fuel ctx callee retbb t ++
      (((p,d,next.inst_id),caller_fn,next,
          post with vs_inst_idx := SUC caller.vs_inst_idx)::rest ++ outer_suffix)` by
    simp[Abbr `before_ret`, APPEND_ASSOC] >>
  `LENGTH before_ret = j /\ before_ret = TAKE j (trace_context n ctx vs0)` by
    (drule_all trace_context_factor_cursor >> simp[]) >>
  `trace_context m ctx vs0 = before_ret ++
      ((((d,callinst.inst_id)::p),h,retinst.inst_id),callee,retinst,t)::
      ((p,d,next.inst_id),caller_fn,next,
        post with vs_inst_idx := SUC caller.vs_inst_idx)::(rest ++ outer_suffix)` by
    simp[Abbr `before_ret`, APPEND_ASSOC] >>
  qexists_tac `m` >> conj_tac >- (gvs[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `before_ret = TAKE j (trace_context n ctx vs0)`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `LENGTH before_ret = j` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `trace_context m ctx vs0 = before_ret ++ _::_` SUBST1_TAC >>
  rpt (pop_assum kall_tac) >>
  simp[EL_APPEND2, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, ADD1]
QED

Theorem trace_context_callee:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\ wf_function callee /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs /\
  enters_block callee cs z /\ active_inst callee j z ==>
  !b. ?m. b <= m /\
    MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
      (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (trace_blocks ((d,inst.inst_id)::p) d 1 ctx callee cs)` by
    (irule (SRULE [] (Q.INST [`fuel` |-> `0`] trace_entered_head)) >> simp[]) >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (trace_step p d 1 ctx fn inst t)` by simp[Once trace_defs] >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (open_trace p d 1 ctx fn bb t)` by
    (simp[open_trace_def] >> disj1_tac >> simp[Once trace_defs]) >>
  gen_tac >> qpat_x_assum `!k b. _`
    (qspecl_then [`1`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED
