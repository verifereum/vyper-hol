(* Runtime entry preparation and the chronological cut on the selected activation. *)
Theory entryCreateRuntimeBodyCut
Ancestors
  loweringRuntimeCorrect entryCreateFocusSpec entryCreateLiveResume
  entryCreateLockExit entryCreateExternalTail acceptedContextPhi
  ctorDeployMemoryRunMemEntryStmtFirstEmission nonreentrantExit
  runtimeEntryEndpoint vyperLoweringCorrect venomWf vyperCompiler
  gasOutcomeFull fragGasOriginPtr fragExec venomExecProofs
  venomInst venomInstProofs venomState compileEnv emitHelperProps rich_list arithmetic
  list moduleLowering nonreentrantEquiv stmtLowering vyperAST
  dftGasFromListTraceDefs loweringStateRelDefs bodyPtrDefs gasContext
  vyperState externalEntryBound vyperInterpreter finite_map
  gasFocusVisitSiteProjection fragGasOrigin createSizePrefixReplay createSizeCutRegion
  venomExecSemantics blockSimHelpers relation pair pred_set
  entryCreateBodyCut entryCreateNativeResume gasEvents

Theorem runtime_body_entry_no_phi[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" ==>
  (?bb. lookup_block "__entry" func.fn_blocks = SOME bb) /\
  (!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0)
Proof
  strip_tac >> conj_tac
  >- (Cases_on `func.fn_blocks` >>
      fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  rpt strip_tac >> irule no_phis_phi_prefix_length_zero >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >>
  metis_tac[venomFnInstsProofsTheory.MEM_fn_insts]
QED

Theorem runtime_guarded_tail_code[local]:
  compile_guarded_body ce nr nkey T iv stmts rt sa = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) sa =
    ((),sl) /\
  compile_stmts ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty)
    stmts sl = ((),sb) /\ ~block_is_terminated sb ==>
  ?su. (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) sb =
      ((),su) /\
    emit_inst (case rt of NONE => STOP | SOME _ => INVALID) [] [] su = ((),st')
Proof
  strip_tac >>
  qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_guarded_body_def, comp_ignore_bind_def, comp_bind_def, comp_get_def] >>
  Cases_on `rt` >> gvs[] >> pairarg_tac >> gvs[] >> Cases_on `q` >> gvs[]
QED

Theorem runtime_guarded_body_live[local]:
  compile_guarded_body ce nr nkey T iv stmts rt sa = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) sa =
    ((),sl) /\
  compile_stmts ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty)
    stmts sl = ((),sb) /\
  ~block_is_terminated sl /\ fn_has_code sl sb func /\ fn_has_code sb st' func /\
  u.vs_current_bb = sl.cs_current_bb /\ u.vs_inst_idx = LENGTH sl.cs_current_insts ==>
  ?bb i. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb u.vs_inst_idx = SOME i
Proof
  strip_tac >> drule ctor_compile_stmts_first_emission >> strip_tac
  >- (`~block_is_terminated sb` by (fs[block_is_terminated_def]) >>
      drule_all runtime_guarded_tail_code >> strip_tac >>
      drule loweringHaltTheory.optional_unlock_code >> simp[] >> strip_tac >>
      drule emit_inst_extends >> strip_tac >>
      `?is. is <> [] /\ st'.cs_current_bb = sb.cs_current_bb /\
         st'.cs_current_insts = sb.cs_current_insts ++ is` by
        (Cases_on `nr /\ ~iv` >> gvs[APPEND_ASSOC]) >>
      pop_assum strip_assume_tac >> drule_all fn_has_code_same_block >>
      disch_then (qx_choose_then `bb` strip_assume_tac) >>
      qpat_x_assum `!i. i < _ ==> _` (qspec_then `0` mp_tac) >>
      Cases_on `is` >> gvs[]) >>
  first_x_assum drule >> strip_tac >>
  fs[IS_PREFIX_APPEND, get_instruction_def] >>
  gvs[] >> simp[EL_LENGTH_APPEND]
QED

(* Suffix fuel is chosen large enough for further confined replay, while the
   terminal instruction and visit key are preserved by the native splitter. *)
Theorem runtime_terminal_visit_after_entry[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
  lookup_block s_b.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s_b.vs_inst_idx = SOME i /\
  (!fuel. bound <= fuel ==>
    ?p d pre. trace_context fuel unit.cu_context vs =
      pre ++ [((p,d,inst.inst_id),fn',inst,s)]) ==>
  !m. ?d k before hit. m <= k /\
    (?p d'. hit = ((p,d',inst.inst_id),fn',inst,s)) /\
    create_trace_from [] d k unit.cu_context func s_b = before ++ [hit]
Proof
  strip_tac >> gen_tac >> drule_all runtime_body_entry_no_phi >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule_all_then (qspec_then `m` (qx_choose_then `b` (mk_asm "resume")))
    create_terminal_hit_after_live_prefix >>
  qabbrev_tac `k0 = MAX b bound` >>
  `b <= k0 /\ bound <= k0` by simp[Abbr `k0`] >>
  `bound <= SUC k0` by decide_tac >>
  qpat_x_assum `!fuel. bound <= fuel ==> _` (qspec_then `SUC k0` mp_tac) >>
  simp[] >> disch_then (qx_choosel_then [`p`,`d`,`pre`] assume_tac) >>
  asm_x "resume" drule_all >> metis_tac[]
QED

Theorem runtime_rejected_lock_no_create[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  is_view_mut mut = (mut = View) /\
  (initial_evaluation_context am.sources am.layouts td NONE).nonreentrant_slot =
    SOME global_nonreentrant_slot /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts td NONE) T
    (is_view_mut mut) es0 = (INR exc,es_abort) /\
  compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
    fbody rt sa = ((),st') /\
  fn_has_code sa st' func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H unit.cu_context func cenv
      (initial_evaluation_context am.sources am.layouts td NONE) es0 s0 /\
    ghost_inv H NONE cenv (initial_evaluation_context am.sources am.layouts td NONE)
      es0 G0 tn0 s0) /\
  (!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) marks0 (OK s0,G0,tn0)) /\
  (!fuel. bound <= fuel ==>
    ?p d pre. trace_context fuel unit.cu_context vs =
      pre ++ [((p,d,inst.inst_id),fn',inst,s)]) ==>
  inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  strip_tac >> drule_all runtime_body_entry_no_phi >> strip_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections o SPEC_ALL) >>
  drule_all rejected_lock_excludes_create_last >> simp[]
QED

(* An actual next caller cursor, or the entire trace stays on the first
   instruction and its (possibly still pending) callee. *)
Theorem create_native_first_chunk[local]:
  ~s.vs_halted /\ create_trace_from p d k C f s <> [] ==>
  ?bb i. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    let chunk = ((p,d,i.inst_id),f,i,s)::trace_step p d k C f i s in
      create_trace_from p d k C f s = chunk \/
      ?dd kk t. ~t.vs_halted /\
        gas_origin_edge F explicit C f s (create_cut_marks explicit chunk) (OK t) /\
        create_trace_from p d k C f s = chunk ++ create_trace_from p dd kk C f t
Proof
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >> gvs[Once create_trace_from_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  gvs[Once (cj 2 trace_defs), Once exec_block_def] >>
  rename1 `get_instruction _ _ = SOME i` >>
  qabbrev_tac `chunk = ((p,d,i.inst_id),f,i,s)::trace_step p d k C f i s` >>
  `create_cut_marks explicit chunk = MAP (\key. key IN explicit)
    (gas_events_step k C f.fn_name i s)` by
    (simp_tac bool_ss [Abbr `chunk`, create_cut_marks_def] >>
     pure_rewrite_tac [GSYM (cj 1 focus_visit_site_projection), MAP_MAP_o] >>
     simp[combinTheory.o_DEF, ETA_THM] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     simp[MAP_CONG, pairTheory.FORALL_PROD]) >>
  Cases_on `step_inst k C i s` >> gvs[] >>
  TRY (disj1_tac >> simp[Once create_trace_from_def, Abbr `chunk`,
    Once (cj 2 trace_defs), Once exec_block_def] >> NO_TAC) >>
  rename1 `step_inst k C i s = OK u` >>
  reverse (Cases_on `is_terminator i.inst_opcode`) >- suspend "next" >>
  suspend "jump"
QED

Resume create_native_first_chunk[next]:
  disj2_tac >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted,step_preserves_control_flow] >>
  qexistsl_tac [`d`,`k`,`u with vs_inst_idx := SUC s.vs_inst_idx`] >> simp[] >>
  conj_tac
  >- (simp[gas_origin_edge_def] >> metis_tac[]) >>
  drule_all create_trace_from_next >> simp[]
QED

Resume create_native_first_chunk[jump]:
  Cases_on `u.vs_halted`
  >- (disj1_tac >> simp[Once create_trace_from_def, Abbr `chunk`,
      Once (cj 2 trace_defs), Once exec_block_def]) >>
  namedCases_on `k` ["", "k"]
  >- (disj1_tac >> simp[Once create_trace_from_def, Abbr `chunk`,
      Once (cj 2 trace_defs), Once exec_block_def]) >>
  Cases_on `lookup_block u.vs_current_bb f.fn_blocks`
  >- (disj1_tac >> simp[Once create_trace_from_def, Abbr `chunk`,
      Once (cj 2 trace_defs), Once exec_block_def, Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block u.vs_current_bb f.fn_blocks = SOME dest` >>
  reverse (Cases_on `eval_phis u dest.bb_instructions`) >>
  TRY (disj1_tac >> simp[Once create_trace_from_def, Abbr `chunk`,
      Once (cj 2 trace_defs), Once exec_block_def, Once (cj 3 trace_defs)] >> NO_TAC) >>
  rename1 `eval_phis u dest.bb_instructions = OK v` >>
  `v.vs_current_bb = u.vs_current_bb /\ ~v.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  rename1 `step_inst (SUC fuel) C i s = OK u` >>
  disj2_tac >>
  qexistsl_tac [`SUC d`,`fuel`,`v with vs_inst_idx := phi_prefix_length dest.bb_instructions`] >>
  simp[] >> conj_tac
  >- (simp[gas_origin_edge_def] >> metis_tac[]) >>
  drule_all create_trace_from_enter >> disch_then (fn eq => rewrite_tac[GSYM eq]) >>
  simp[Once create_trace_from_def, Once (cj 2 trace_defs), Once exec_block_def]
QED
Finalise create_native_first_chunk

(* Continue only when the chosen hit is strictly past the first caller
   chunk.  A terminal or pending callee need not produce a caller result. *)
Theorem create_native_region_walk[local]:
  fn_has_code sa sb f /\ create_cut_code {} sa sb /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_at sa s0 /\
  create_trace_from p d0 k0 C f s0 = before0 ++ [hit] ==>
  !n d k u left before.
    LENGTH before = n /\ before0 = left ++ before /\
    RTC (create_operand_native_step sa sb explicit C f p)
      (d0,k0,s0,[]) (d,k,u,left) /\
    ~u.vs_halted /\ create_cut_region sa sb u /\
    create_trace_from p d k C f u = before ++ [hit] ==>
    create_interior_visit sa sb explicit C f (p,d0,k0) s0 (before0,hit,[]) \/
    ?dd kk t prior. ~t.vs_halted /\ create_operand_at sb t /\
      create_trace_from p dd kk C f t = prior ++ [hit]
Proof
  strip_tac >> drule_all create_cut_region_rules >> strip_tac >>
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `create_operand_at sb u`
  >- (disj2_tac >> metis_tac[]) >>
  `create_trace_from p d k C f u <> []` by simp[] >>
  drule_all create_native_first_chunk >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME i` >>
  `create_operand_fetch sa sb f u i` by
    (fs[create_operand_fetch_def, create_operand_at_def] >> metis_tac[]) >>
  suspend "walk"
QED

Resume create_native_region_walk[walk]:
  qabbrev_tac `visit = ((p,d,i.inst_id),f,i,u)` >>
  qabbrev_tac `chunk = visit::trace_step p d k C f i u` >>
  `before ++ [hit] = chunk \/
    ?dd kk t. ~t.vs_halted /\
      gas_origin_edge F explicit C f u (create_cut_marks explicit chunk) (OK t) /\
      before ++ [hit] = chunk ++ create_trace_from p dd kk C f t` by
    (qpat_x_assum `let _ = _ in _` mp_tac >> simp[Abbr `chunk`, Abbr `visit`])
  >- (disj1_tac >> simp[create_interior_visit_def] >>
      qexistsl_tac [`d`,`k`,`u`,`left`,`i`] >> simp[] >>
      Cases_on `before` >> fs[Abbr `chunk`, Abbr `visit`] >> metis_tac[]) >>
  Cases_on `create_trace_from p dd kk C f t = []`
  >- (disj1_tac >> simp[create_interior_visit_def] >>
      qexistsl_tac [`d`,`k`,`u`,`left`,`i`] >> simp[] >>
      Cases_on `before` >> fs[Abbr `chunk`, Abbr `visit`] >> metis_tac[]) >>
  `?prior. before = chunk ++ prior /\
    create_trace_from p dd kk C f t = prior ++ [hit]` by
    (Cases_on `create_trace_from p dd kk C f t = []` >- fs[] >>
     qspec_then `create_trace_from p dd kk C f t` mp_tac SNOC_CASES >>
     simp[SNOC_APPEND] >> disch_then (qx_choosel_then [`last`,`prior`] assume_tac) >>
     `before ++ [hit] = (chunk ++ prior) ++ [last]` by fs[APPEND_ASSOC] >>
     fs[APPEND_11_LENGTH] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `create_cut_region sa sb t` by
    (fs[create_operand_at_def] >> metis_tac[lookup_block_MEM, ZERO_LESS_EQ]) >>
  `create_operand_native_step sa sb explicit C f p (d,k,u,left)
     (dd,kk,t,left ++ chunk)` by
    (simp[create_operand_native_step_def] >> qexists_tac `i` >>
     fs[Abbr `chunk`, Abbr `visit`, create_prefix_step_def,
       create_operand_fetch_def, create_operand_at_def] >> metis_tac[]) >>
  `RTC (create_operand_native_step sa sb explicit C f p)
    (d0,k0,s0,[]) (dd,kk,t,left ++ chunk)` by metis_tac[RTC_SINGLE, RTC_TRANS] >>
  `LENGTH prior < n` by fs[Abbr `chunk`] >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `LENGTH prior` mp_tac) >>
  simp[] >> disch_then irule >>
  simp[] >> qexistsl_tac [`dd`,`kk`,`t`] >> simp[]
QED
Finalise create_native_region_walk

Theorem create_native_first_exit:
  fn_has_code sa sb f /\ create_cut_code {} sa sb /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_at sa s0 /\ ~s0.vs_halted /\
  create_trace_from p d k C f s0 = before ++ [hit] ==>
  create_interior_visit sa sb explicit C f (p,d,k) s0 (before,hit,[]) \/
  ?dd kk t prior. ~t.vs_halted /\ create_operand_at sb t /\
    create_trace_from p dd kk C f t = prior ++ [hit]
Proof
  strip_tac >> drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region sa sb s0` by fs[create_operand_at_def] >>
  irule (Q.INST [`n` |-> `LENGTH before`] (SPEC_ALL
    (REWRITE_RULE [AND_IMP_INTRO] create_native_region_walk))) >>
  simp[] >> qexistsl_tac [`before`,`d`,`k`,`[]`,`s0`] >> simp[]
QED

Theorem terminated_boundary_trace_nil[local]:
  wf_function func /\ fn_has_code sb st' func /\
  st' = sb /\ block_is_terminated sb /\ create_operand_at sb t ==>
  create_trace_from p d k C func t = []
Proof
  strip_tac >> gvs[create_operand_at_def, fn_has_code_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, lookup_block_MEM] >>
  `0 < LENGTH sb.cs_current_insts /\ is_terminator (LAST sb.cs_current_insts).inst_opcode` by
    (Cases_on `sb.cs_current_insts` >> fs[block_is_terminated_def]) >>
  `LENGTH sb.cs_current_insts <= LENGTH bb.bb_instructions` by
    metis_tac[IS_PREFIX_LENGTH] >>
  `PRE (LENGTH sb.cs_current_insts) < LENGTH sb.cs_current_insts /\
   PRE (LENGTH sb.cs_current_insts) < LENGTH bb.bb_instructions` by decide_tac >>
  `LAST sb.cs_current_insts = EL (PRE (LENGTH sb.cs_current_insts)) bb.bb_instructions` by
    (`sb.cs_current_insts <> []` by (strip_tac >> fs[]) >>
     simp[LAST_EL] >> irule is_prefix_el >> simp[]) >>
  `LENGTH sb.cs_current_insts = LENGTH bb.bb_instructions` by
    (fs[bb_well_formed_def] >> res_tac >> decide_tac) >>
  simp[create_trace_from_def, Once (cj 2 trace_defs), Once exec_block_def, get_instruction_def]
QED

Theorem short_tail_no_create_last[local]:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst stop_id opc [] []) /\
  (opc = STOP \/ opc = INVALID) /\ (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) ==>
  create_trace_from p d k C func t <> pre ++ [((p',d',i.inst_id),hit,i,u)]
Proof
  strip_tac >>
  `create_trace_from p d k C func t =
    [((p,d,stop_id),func,mk_inst stop_id opc [] [],t)]` by
    (gvs[create_trace_from_def, Once (cj 2 trace_defs), Once exec_block_def,
         trace_step_noninvoke, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  strip_tac >>
  `LAST (pre ++ [((p',d',i.inst_id),hit,i,u)]) =
     ((p',d',i.inst_id),hit,i,u)` by simp[] >>
  gvs[mk_inst_def]
QED

Theorem unlock_tail_no_create_last[local]:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst un_id TSTORE [Lit key; Lit 0w] []) /\
  get_instruction bb (SUC t.vs_inst_idx) = SOME (mk_inst stop_id opc [] []) /\
  (opc = STOP \/ opc = INVALID) /\ (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) ==>
  create_trace_from p d k C func t <> pre ++ [((p',d',i.inst_id),hit,i,u)]
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `un = mk_inst un_id TSTORE [Lit key; Lit 0w] []` >>
  Cases_on `t.vs_call_ctx.cc_static`
  >- (`create_trace_from p d k C func t = [((p,d,un_id),func,un,t)]` by
        simp[Once create_trace_from_def, Once (cj 2 trace_defs), Once exec_block_def,
             trace_step_noninvoke, Abbr `un`, mk_inst_def, step_inst_non_invoke,
             step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def, eval_operands_def] >>
      strip_tac >>
      `LAST (pre ++ [((p',d',i.inst_id),hit,i,u)]) = ((p',d',i.inst_id),hit,i,u)` by simp[] >>
      gvs[Abbr `un`, mk_inst_def]) >>
  `step_inst k C un t = OK (tstore key 0w t) /\ ~is_terminator un.inst_opcode /\
   un.inst_opcode <> INVOKE /\ (tstore key 0w t).vs_current_bb = t.vs_current_bb` by
    simp[Abbr `un`, tstore_def, mk_inst_def, is_terminator_def, step_inst_non_invoke,
         step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def, eval_operands_def] >>
  drule_all create_trace_from_next >> simp[trace_step_noninvoke] >> strip_tac >>
  qabbrev_tac `t' = (tstore key 0w t) with vs_inst_idx := SUC t.vs_inst_idx` >>
  `lookup_block t'.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb t'.vs_inst_idx = SOME (mk_inst stop_id opc [] [])` by simp[Abbr `t'`] >>
  drule_all short_tail_no_create_last >>
  Cases_on `pre` >> simp[]
  >- (rpt strip_tac >> gvs[Abbr `un`, mk_inst_def] >>
      qpat_x_assum `<|inst_id := _; inst_opcode := TSTORE; inst_operands := _;
        inst_outputs := _|> = i` (mp_tac o AP_TERM ``instruction_inst_opcode``) >> simp[]) >>
  metis_tac[]
QED

Theorem runtime_guarded_tail_no_create[local]:
  wf_function func /\
  compile_guarded_body ce nr nkey T iv stmts rt sa = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) sa =
    ((),sl) /\
  compile_stmts ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty)
    stmts sl = ((),sb) /\ fn_has_code sb st' func /\ create_operand_at sb t /\
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) ==>
  create_trace_from p d k C func t <> pre ++ [((p',d',i.inst_id),hit,i,u)]
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `block_is_terminated sb`
  >- (`st' = sb` by
        (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
         simp[compile_guarded_body_def, comp_ignore_bind_def, comp_bind_def,
              comp_return_def, comp_get_def] >> Cases_on `rt` >> gvs[]) >>
      drule_all terminated_boundary_trace_nil >> simp[]) >>
  drule_all runtime_guarded_tail_code >> strip_tac >>
  qabbrev_tac `opc = case rt of NONE => STOP | SOME _ => INVALID` >>
  drule loweringHaltTheory.optional_unlock_code >> simp[] >> disch_tac >>
  drule emit_inst_extends >> strip_tac >>
  Cases_on `nr /\ ~iv`
  >- (`st'.cs_current_bb = sb.cs_current_bb /\ st'.cs_current_insts =
     sb.cs_current_insts ++ [mk_inst sb.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] [];
         mk_inst su.cs_next_id opc [] []]` by fs[APPEND_ASSOC] >>
      drule_all fn_has_code_same_block >>
      disch_then (qx_choose_then `bb` (CONJUNCTS_THEN2 assume_tac (mk_asm "reads"))) >>
      asm "reads" (qspec_then `0` mp_tac) >>
      asm "reads" (qspec_then `1` mp_tac) >> simp[] >> ntac 2 disch_tac >>
      irule unlock_tail_no_create_last >>
      Cases_on `rt` >> fs[create_operand_at_def, ADD1, Abbr `opc`] >> metis_tac[]) >>
  `st'.cs_current_bb = sb.cs_current_bb /\ st'.cs_current_insts =
   sb.cs_current_insts ++ [mk_inst su.cs_next_id opc [] []]` by fs[] >>
  drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_x_assum `!i. i < _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule short_tail_no_create_last >> Cases_on `rt` >>
  fs[create_operand_at_def, Abbr `opc`] >> metis_tac[]
QED

(* The post-lock prefix and code ownership agree on the selected terminal
   visit.  Only the first-exit alternative is discharged by the epilogue. *)
Theorem runtime_live_body_interior[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  compile_guarded_body ce nr nkey T iv stmts rt sa = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) sa = ((),sl) /\
  compile_stmts ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty)
    stmts sl = ((),sb) /\ fn_has_code sl sb func /\ fn_has_code sb st' func /\
  create_cut_code {} sl sb /\ ~block_is_terminated sl /\ ~s_b.vs_halted /\
  s_b.vs_current_bb = sl.cs_current_bb /\ s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
  gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
  (!fuel. bound <= fuel ==>
    ?p d pre. trace_context fuel unit.cu_context vs =
      pre ++ [((p,d,inst.inst_id),fn',inst,s)]) /\
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) ==>
  ?key d k before. create_interior_visit sl sb explicit unit.cu_context func
    ([],d,k) s_b (before,(key,fn',inst,s),[])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all runtime_body_entry_no_phi >> strip_tac >>
  `wf_function func` by
    (drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
     drule lookup_function_MEM >> strip_tac >>
     fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all runtime_guarded_body_live >> strip_tac >>
  drule_all_then (qspec_then `0` strip_assume_tac) runtime_terminal_visit_after_entry >>
  `create_operand_at sl s_b` by simp[create_operand_at_def] >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) create_native_first_exit
  >- metis_tac[] >>
  drule_all runtime_guarded_tail_no_create >> metis_tac[]
QED

(* A generic statement-list producer, applied only after locating the
   terminal visit in the actual post-lock activation.  Its ghost pair is
   shared across all valid horizons of that frame. *)
Definition runtime_body_create_cut_rule_with_def:
  runtime_body_create_cut_rule_with L tops unit am td ret <=>
    let C = unit.cu_context;
        cx = initial_evaluation_context am.sources am.layouts td NONE;
        st0 = initial_state am [] in
    !Csh func shadow_func body cenv cenv' bindings env_t env' sl sb sha shb
      s_b es_lock G_b tn_b RetQ d k before key hit inst s.
      body_inv tops C cenv cx /\ cx_tops cx = tops /\
      shadow_body_inv tops C Csh /\ struct_args_unique tops /\
      supported_stmts tops bindings body /\
      (!vis mut nr raw fn args dflts ret stmts.
        MEM (FunctionDecl vis mut nr raw fn args dflts ret stmts) tops ==>
        stmts_loop_calls_ok [(NONE,tops)] stmts) /\
      stmts_loop_calls_ok [(NONE,tops)] body /\
      (!tgt. supported_stmts_expr_exists (expr_abi_decode_target_root tgt) body ==>
        occurs_abi_decode_target tgt tops) /\
      body_const_cells_agree [(NONE,tops)] cx env_t es_lock /\
      expr_sim_inv cenv cx env_t es_lock /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret body = SOME env' /\ stmts_exprs_ok cenv body /\
      call_evaluation_safe cx (int_calls_stmts body) /\
      frame_ret_ok_full ((\H. cx_dead H cx),0,NONE,C,Csh,[],func,shadow_func)
        cx RetQ cenv ret /\
      ~cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
      stmts_env cenv NoLoop ret body sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt body)
        sha = (gas_shadow_env T cenv',shb) /\
      create_cut_code {} sl sb /\ L sl sb /\
      gas_shadow_state sl sha /\ gas_shadow_state sb shb /\
      gas_shadow_context C Csh /\ gas_shadow_function func shadow_func /\
      MEM func C.ctx_functions /\ MEM shadow_func Csh.ctx_functions /\
      fn_has_code sl sb func /\ fn_has_code sha shb shadow_func /\
      ctx_inst_ids_distinct C /\ fn_inst_ids_distinct func /\
      (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      alloca_history func s_b /\ return_buf_frame NONE cenv sl s_b /\
      local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
      ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
      s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
      (ctx_has_dalloca C ==> allocas_below_fmp s_b) /\
      (!fn i u. frag_reachable C func s_b fn i u ==> dalloca_fmp_headroom i u) /\
      (!H. valid_horizon cx st0 H es_lock.storage_trace ==>
        storage_well_formed_on cx es_lock (FST H) /\
        stmt_state_rel H C func cenv cx es_lock s_b /\
        ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b) /\
      create_interior_visit sl sb (gas_explicit_sites C Csh) C func
        ([],d,k) s_b (before,(key,hit,inst,s),[]) /\
      ~inst_create_size_ok inst s ==>
      create_body_cut (gas_explicit_sites C Csh) tops cx st0 (eval_stmts cx body)
        (es_lock,s_b) (before,(key,hit,inst,s))
End

Definition runtime_body_create_cut_rule_def:
  runtime_body_create_cut_rule tops unit am td ret <=>
    runtime_body_create_cut_rule_with (\a b. T) tops unit am td ret
End

Theorem runtime_bad_create_opcode[local]:
  ~inst_create_size_ok inst s ==>
  inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2
Proof
  rpt strip_tac >> fs[venomRunBoundedTheory.inst_create_size_ok_def] >> metis_tac[]
QED

Theorem selected_runtime_endpoint_body_cut_with:
  !L tops rpolicy unit am td ret vi mut nr args dflts fbody es0 bound fn inst s.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    source_typing_ok tops am td /\ source_deployment_rel tops am td /\
    initial_venom_state_rel tops am td vi /\ outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !f i u. raw_reachable vi unit.cu_context f i u ==> dalloca_fmp_headroom i u) /\
    vyperInterpreter$lookup_function NONE td.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint_with L tops rpolicy unit am td vi es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody) /\
    (!a b c d. cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ L a d ==>
       L b c) /\
    (!gs. call_storage_ok am td vi.vs_outcomes gs) /\
    (!fuel. bound <= fuel ==>
      ?p d pre. trace_context fuel unit.cu_context vi =
        pre ++ [((p,d,inst.inst_id),fn,inst,s)]) /\
    ~inst_create_size_ok inst s /\
    (!ce ty ss a b. compile_stmts ce NoLoop ty ss a = ((),b) /\
      ce.ce_ctor_exit_label = NONE ==> create_cut_code {} a b) /\
    runtime_body_create_cut_rule_with L tops unit am td ret ==>
    let cx = initial_evaluation_context am.sources am.layouts td NONE in
    ?shadow_unit marks0 compiled_body es_lock s_b before key.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      (!gx. external_entry_bound tops am td vi.vs_outcomes
        (gas_explicit marks0 vi.vs_gas_readings ++ gx) mut args dflts
        (es0 with gas_obs := gx)) /\
      lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
      (!gx. eval_stmts cx compiled_body (es_lock with gas_obs := gx) =
            eval_stmts cx fbody (es_lock with gas_obs := gx)) /\
      s_b.vs_gas_readings = DROP (LENGTH marks0) vi.vs_gas_readings /\
      create_body_cut (gas_explicit_sites unit.cu_context shadow_unit.cu_context)
        tops cx (initial_state am []) (eval_stmts cx compiled_body)
        (es_lock,s_b) (before,(key,fn,inst,s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac runtime_bad_create_opcode >>
  drule_all runtime_body_endpoint_prepare_with_cases >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`shadow_unit`,`marks0`,`func`,`sa`,`st'`,`cenv`,`s0`,
      `G0`,`tn0`,`exc`,`es_abort`,`a`,`t`,`G`,`tn`]
      (map_every assume_tac o CONJUNCTS))
    (DISJ_CASES_THEN2 strip_assume_tac
      (qx_choosel_then [`cx`,`compiled_body`,`entry`,`explicit`,`prefix`,`marks0`,
        `shadow_unit`,`func`,`shadow_func`,`cenv`,`cenv'`,`bindings`,`env_t`,`env'`,
        `es_lock`,`sa`,`sl`,`sb`,`st'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`]
        (map_every assume_tac o CONJUNCTS))))
  >- (`nr = T` by
        (Cases_on `nr` >> fs[lock_if_nr_def, return_def]) >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _ /\ _`
        (assume_tac o GEN_ALL o CONJUNCT1 o SPEC_ALL) >>
      drule_all runtime_rejected_lock_no_create >> metis_tac[])
  >- (qpat_x_assum `!tail. ~call_storage_ok _ _ _ _` (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `entry = _` SUBST_ALL_TAC >>
  qpat_x_assum `explicit = _` SUBST_ALL_TAC >>
  qpat_x_assum `prefix = _` SUBST_ALL_TAC >>
  `create_cut_code {} sl sb` by
    (qpat_x_assum `!ce ty ss a b. _ ==> create_cut_code {} a b` irule >>
     qexistsl_tac [`cenv`,`compiled_body`,
       `case if ret = NoneT then NONE else SOME ret of
          NONE => BaseT BoolT | SOME ty => ty`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx (initial_state am []) (storage_trace_horizon es_lock.storage_trace)
    es_lock.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon es_lock.storage_trace` mp_tac) >>
  disch_then (fn th => drule th) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac runtime_live_body_interior >>
  drule_all_then strip_assume_tac runtime_body_entry_no_phi >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
     storage_well_formed_on cx es_lock (FST H) /\
     stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
     ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> storage_well_formed_on _ _ _`
       (drule_then assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then (CONJUNCTS_THEN assume_tac)) >> simp[]) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  simp_tac std_ss [LET_THM] >>
  qexistsl_tac [`shadow_unit`,`marks0`,`compiled_body`,`es_lock`,`s_b`,`before`,`key`] >>
  qpat_x_assum `compiled_body = _` kall_tac >>
  asm_simp_tac std_ss [] >>
  qpat_x_assum `runtime_body_create_cut_rule_with _ _ _ _ _ _`
    (fn rule => qpat_assum `create_interior_visit _ _ _ _ _ _ _ _`
       (mp_then (Pat `create_interior_visit _ _ _ _ _ _ _ _`) irule
          (SIMP_RULE std_ss [runtime_body_create_cut_rule_with_def, LET_THM] rule))) >>
  rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC)
  >- (goal_assum (drule_at (Pat `supported_stmts _ _ _`)) >> simp[]) >>
  goal_assum (drule_at (Pat `frame_ret_ok_full _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmts_env (gas_shadow_env T _) _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >>
  goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  qexistsl_tac [`G_b`,`tn_b`] >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

(* The legacy adapter is the unrestricted instance of the same classifier. *)
local
  val unrestricted_cut =
    Q.SPEC `\a b. T` selected_runtime_endpoint_body_cut_with
    |> PURE_REWRITE_RULE [GSYM runtime_body_endpoint_unrestricted_def,
                          GSYM runtime_body_create_cut_rule_def]
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
    |> PURE_REWRITE_RULE [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP]
in
Theorem selected_runtime_endpoint_body_cut:
  ^(concl unrestricted_cut)
Proof
  ACCEPT_TAC unrestricted_cut
QED
end
