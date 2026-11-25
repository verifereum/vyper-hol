(* A reverting entry cannot have visited an oversized CREATE instruction. *)
Theory linkedDeployRevertSize
Ancestors
  venomRunBounded unitMemInv requestCutNativeAbortVisit dftGasFromListLocator
  dftGasFromListTraceDefs dftGasFromListTracePrefix
  contextCodegenRel venomExecSemantics venomInst venomState venomWf
  list rich_list arithmetic pair option

Theorem revert_run_create_size_ok:
  EVERY wf_function ctx.ctx_functions /\
  run_context fuel ctx vs = Abort Revert_abort post ==>
  mem_inv (\ctx fn inst s. inst_create_size_ok inst s) ctx vs
Proof
  strip_tac >>
  `(!p d n c f outer s key g i t err.
       MEM (key,g,i,t) (trace_step p d n c f outer s) /\
       i.inst_opcode <> INVOKE /\ step_inst_base i t = Error err ==>
       step_inst n c outer s = Error err) /\
    (!p d n c f bb s key g i t err.
       MEM (key,g,i,t) (trace_block p d n c f bb s) /\
       i.inst_opcode <> INVOKE /\ step_inst_base i t = Error err ==>
       exec_block n c bb s = Error err) /\
    (!p d n c f s key g i t err.
       MEM (key,g,i,t) (trace_blocks p d n c f s) /\
       i.inst_opcode <> INVOKE /\ step_inst_base i t = Error err ==>
       run_blocks n c f s = Error err)` by
    (ho_match_mp_tac trace_defs_ind >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
         Cases_on `outer.inst_opcode = INVOKE`
         >- (Cases_on `decode_invoke outer` >- simp[Once trace_defs] >>
             rename1 `decode_invoke outer = SOME pair` >> PairCases_on `pair` >>
             Cases_on `lookup_function pair0 c.ctx_functions`
             >- simp[Once trace_defs] >>
             rename1 `lookup_function pair0 c.ctx_functions = SOME callee` >>
             Cases_on `eval_operands pair1 s` >- simp[Once trace_defs] >>
             rename1 `eval_operands pair1 s = SOME args` >>
             Cases_on `setup_callee callee args s` >- simp[Once trace_defs] >>
             simp[Once trace_defs] >> strip_tac >>
             gvs[] >> first_x_assum drule_all >> strip_tac >>
             simp[step_inst_def]) >>
         simp[trace_step_noninvoke, step_inst_non_invoke])
     >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
         Cases_on `get_instruction bb s.vs_inst_idx` >- simp[Once trace_defs] >>
         rename1 `get_instruction bb s.vs_inst_idx = SOME outer` >>
         once_rewrite_tac[cj 2 trace_defs, exec_block_def] >> simp[MEM_APPEND] >>
         strip_tac
         >- (gvs[] >> simp[step_inst_non_invoke])
         >- (gvs[] >> first_x_assum drule_all >> simp[]) >>
         Cases_on `step_inst n c outer s` >> gvs[] >>
         Cases_on `is_terminator outer.inst_opcode` >> gvs[] >>
         metis_tac[]) >>
     rpt gen_tac >> strip_tac >> rpt gen_tac >>
     namedCases_on `n` ["", "small"] >- simp[] >>
     Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
     >- simp[Once (cj 3 trace_defs)] >>
     rename1 `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` >>
     Cases_on `eval_phis s bb.bb_instructions` >>
     once_rewrite_tac[cj 3 trace_defs, run_blocks_def] >> simp[MEM_APPEND] >>
     strip_tac
     >- (gvs[] >> first_x_assum drule_all >> simp[]) >>
     rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
     qmatch_asmsub_abbrev_tac `exec_block small c bb entry` >>
     Cases_on `exec_block small c bb entry` >> gvs[] >>
     rename1 `exec_block small c bb entry = OK result` >>
     Cases_on `result.vs_halted` >> gvs[] >>
     metis_tac[]) >>
  `?name fn lbl. ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl` by
    (Cases_on `ctx.ctx_entry` >- fs[run_context_def] >>
     rename1 `ctx.ctx_entry = SOME entry` >>
     Cases_on `lookup_function entry ctx.ctx_functions` >- fs[run_context_def] >>
     rename1 `lookup_function entry ctx.ctx_functions = SOME root` >>
     Cases_on `fn_entry_label root` >> fs[run_context_def, run_function_def]) >>
  simp[NoAsms, mem_inv_raw_reachable] >>
  conj_tac >- (qexistsl_tac [`name`,`fn`,`lbl`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  simp[inst_create_size_ok_def] >> rpt gen_tac >> strip_tac >>
  CCONTR_TAC >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  (Q.SUBGOAL_THEN `(?err. step_inst_base inst s = Error err) \/
     (?u. step_inst_base inst s = Abort ExHalt_abort u)` assume_tac
   >- (simp[step_inst_base_opcode_eqs, eval_operands_def, exec_create_def] >>
       rpt (COND_CASES_TAC ORELSE CASE_TAC) >> fs[exec_create_def])) >>
  drule_all raw_reachable_trace >> strip_tac >>
  rename1 `MEM ((p,d,inst.inst_id),f,inst,s) (trace_context reach_fuel ctx vs)` >>
  `trace_context (MAX fuel reach_fuel) ctx vs = trace_context fuel ctx vs` by
    (simp[trace_context_def, trace_function_def] >>
     irule (cj 3 trace_stable) >> fs[run_context_def, run_function_def]) >>
  `reach_fuel <= MAX fuel reach_fuel` by simp[] >>
  drule trace_context_prefix >>
  disch_then (qspecl_then [`vs`,`ctx`] strip_assume_tac) >>
  `MEM ((p,d,inst.inst_id),f,inst,s) (trace_context fuel ctx vs)` by
    metis_tac[MEM_APPEND] >>
  (qpat_x_assum `(?err. step_inst_base inst s = Error err) \/ _` strip_assume_tac
  >- (qabbrev_tac `start =
        (vs with vs_prev_bb := NONE) with <|vs_current_bb := lbl; vs_inst_idx := 0|>` >>
      `MEM ((p,d,inst.inst_id),f,inst,s) (trace_blocks [] 0 fuel ctx fn start)` by
        (qpat_assum `MEM _ (trace_context fuel ctx vs)` mp_tac >>
         fs[trace_context_def, trace_function_def, venom_state_accfupds, Abbr `start`]) >>
      `run_blocks fuel ctx fn start = Error err` by
        (qpat_assum `!p d n c f s key g i t err. _ ==> run_blocks _ _ _ _ = _`
           (qspecl_then [`[]`,`0`,`fuel`,`ctx`,`fn`,`start`,
              `(p,d,inst.inst_id)`,`f`,`inst`,`s`,`err`] mp_tac) >>
         simp[]) >>
      qpat_x_assum `run_context fuel ctx vs = Abort Revert_abort post` mp_tac >>
      fs[run_context_def, run_function_def, venom_state_accfupds, Abbr `start`]) >>
  qpat_assum `MEM ((p,d,inst.inst_id),f,inst,s) (trace_context fuel ctx vs)`
    (mp_then Any mp_tac native_trace_context_primitive_abort) >>
  simp[])
QED
