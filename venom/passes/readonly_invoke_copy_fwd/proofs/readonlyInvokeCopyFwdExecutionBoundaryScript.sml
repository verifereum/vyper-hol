(* Reachable boundaries retain the full operational witnesses across recursion. *)
Theory readonlyInvokeCopyFwdExecutionBoundary
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdDefs
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdHistory stateEquivProps passSharedProps
  reachableFnSim o1PassContract venomWf venomWfProps unitShapeDefs
  contextCodegenRel venomExecSemantics venomState venomInst
  finite_map list option

Definition ricf_execution_boundary_def:
  ricf_execution_boundary vs C mid_of log_of D a U B0 E0
      outer_history outer_certificates sites maps targets
      stk PG G tn fn s t <=>
    !s1 inst. enters_block fn s s1 /\ active_inst fn inst s1 ==>
      ?t1 n B HP H history certificates E.
        enters_block (mid_of fn) t t1 /\
        DRESTRICT B {id | FST id <> a} = B0 /\
        {id | id IN E /\ FST id <> a} = E0 /\
        FILTER (\entry. SND entry <> []) history = outer_history /\
        FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
        ricf_execution_invariant vs C D stk PG G tn fn inst s1 t1
          n a U B HP H certificates E sites maps targets tn /\
        ricf_mapped_support a B E PG G sites /\
        ricf_analyzed_origins vs C stk PG G tn fn inst s1 a U B history sites maps /\
        ricf_history_certificates vs C log_of stk PG G tn fn inst s1 a U B
          history certificates /\
        ricf_chosen_support vs C log_of a fn B E
End

Definition ricf_execution_return_def:
  ricf_execution_return vs C Ct mid_of log_of D a U B0 E0
      outer_history outer_certificates sites maps targets
      stk PG G tn fn ret se te <=>
    ?inst sr tr rawte sfuel tfuel n B HP H history certificates E.
      active_inst fn inst sr /\ active_inst (mid_of fn) inst tr /\
      DRESTRICT B {id | FST id <> a} = B0 /\
      {id | id IN E /\ FST id <> a} = E0 /\
      FILTER (\entry. SND entry <> []) history = outer_history /\
      FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
      ricf_execution_invariant vs C D stk PG G tn fn inst sr tr
        n a U B HP H certificates E sites maps targets tn /\
      ricf_mapped_support a B E PG G sites /\
      ricf_analyzed_origins vs C stk PG G tn fn inst sr a U B history sites maps /\
      ricf_history_certificates vs C log_of stk PG G tn fn inst sr a U B
        history certificates /\
      ricf_chosen_support vs C log_of a fn B E /\
      step_inst sfuel C inst sr = IntRet ret se /\
      step_inst tfuel Ct inst tr = IntRet ret rawte /\
      execution_equiv {} rawte te /\
      rawte.vs_current_bb = te.vs_current_bb /\
      rawte.vs_prev_bb = te.vs_prev_bb
End

Theorem ricf_execution_return_transport:
  ricf_execution_return vs C Ct mid_of log_of D a U B0 E0
    outer_history outer_certificates sites maps targets
    stk PG G tn fn ret se te /\
  execution_equiv {} te u /\ te.vs_current_bb = u.vs_current_bb /\
  te.vs_prev_bb = u.vs_prev_bb ==>
  ricf_execution_return vs C Ct mid_of log_of D a U B0 E0
    outer_history outer_certificates sites maps targets
    stk PG G tn fn ret se u
Proof
  rw[ricf_execution_return_def] >>
  qexistsl_tac [`inst`,`sr`,`tr`,`rawte`,`sfuel`,`tfuel`,`n`,`B`,`HP`,`H`,
                `history`,`certificates`,`E`] >>
  simp[] >> metis_tac[execution_equiv_trans]
QED

Theorem ricf_inst_edits_phis:
  !xs ys. LIST_REL ricf_inst_edit xs ys ==>
    phi_prefix_length xs = phi_prefix_length ys /\
    !s. eval_phis s xs = eval_phis s ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  rename1 `LIST_REL ricf_inst_edit xs rest` >>
  qpat_x_assum `!ys. _` (qspec_then `rest` mp_tac) >> simp[] >> strip_tac >>
  `h.inst_opcode = PHI <=> h'.inst_opcode = PHI` by
    (fs[ricf_inst_edit_def] >> metis_tac[]) >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def, eval_phis_def] >>
  `h' = h` by fs[ricf_inst_edit_def] >> gvs[]
QED

Theorem ricf_transform_ctx_lookup:
  lookup_function name C.ctx_functions = SOME fn ==>
  lookup_function name (ricf_transform_ctx fn_meta rma C).ctx_functions =
    SOME (ricf_transform_function fn_meta C.ctx_functions rma fn)
Proof
  strip_tac >> simp[ricf_transform_ctx_def, lookup_function_map,
    ricf_transform_function_fn_name]
QED

(* Choose the raw positional function once for each source function.  The
   later NOP-clearing bridge uses this same choice at every block/call. *)
Theorem ricf_context_midpoints:
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling C.ctx_functions /\
  EVERY ricf_src_alloca C.ctx_functions ==>
  ?mid_of log_of. !fn. MEM fn C.ctx_functions ==>
    ricf_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn)
      fn (mid_of fn) /\
    ricf_logged_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn)
      fn (log_of fn) (mid_of fn) /\
    ricf_function_edit fn (mid_of fn) /\
    LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts (mid_of fn)) /\
    ricf_transform_function fn_meta C.ctx_functions rma fn =
      if (mid_of fn).fn_blocks <> fn.fn_blocks
      then clear_nops_function (mid_of fn) else mid_of fn
Proof
  strip_tac >>
  `!fn. ?mid log. MEM fn C.ctx_functions ==>
    ricf_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn) fn mid /\
    ricf_logged_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn) fn log mid /\
    ricf_function_edit fn mid /\
    LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts mid) /\
    ricf_transform_function fn_meta C.ctx_functions rma fn =
      if mid.fn_blocks <> fn.fn_blocks then clear_nops_function mid else mid` suffices_by
    metis_tac[SKOLEM_THM] >>
  gen_tac >>
  Cases_on `MEM fn C.ctx_functions` >> simp[] >>
  `ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
   ricf_full_alloca_copies fn /\ ricf_no_derived_mutable_sibling fn /\
   ricf_src_alloca fn` by
    (fs[EVERY_MEM, o1_ctx_shape_def, o1_fn_shape_def, wf_ssa_def,
      wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  drule_all ricf_transform_function_edit_interface >>
  disch_then (qspecl_then [`rma`,`fn_meta`,`C.ctx_functions`] strip_assume_tac) >>
  drule ricf_logged_function_trace_exists >> strip_tac >>
  qexistsl_tac [`mid`,`log`] >> simp[]
QED

Theorem ricf_block_edits_lookup:
  !bbs cs. LIST_REL ricf_block_edit bbs cs ==>
    !lbl bb. lookup_block lbl bbs = SOME bb ==>
      ?bc. lookup_block lbl cs = SOME bc /\ ricf_block_edit bb bc
Proof
  Induct >> Cases_on `cs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  `h.bb_label = h'.bb_label` by fs[ricf_block_edit_def] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem ricf_function_edit_enters_block:
  ricf_function_edit fn mid /\ enters_block fn s s1 ==>
  enters_block mid s s1
Proof
  rw[ricf_function_edit_def, enters_block_def] >>
  drule_all ricf_block_edits_lookup >> strip_tac >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length bc.bb_instructions /\
   eval_phis s bb.bb_instructions = eval_phis s bc.bb_instructions` by
    metis_tac[ricf_block_edit_def, ricf_inst_edits_phis] >>
  metis_tac[]
QED

Theorem ricf_execution_boundary_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ ricf_function_edit fn (mid_of fn) ==>
  ricf_execution_boundary vs C mid_of log_of D 0 [] FEMPTY {} [] [] FEMPTY [] []
    [] [] FEMPTY entry_taint fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  rw[ricf_execution_boundary_def] >>
  qexistsl_tac [`s1`,`1`,`FEMPTY`,`[]`,`FEMPTY`,`[]`,`[]`,`{}`] >> simp[] >>
  conj_tac >- metis_tac[ricf_function_edit_enters_block] >>
  irule ricf_execution_initial >> metis_tac[]
QED
