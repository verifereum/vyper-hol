Theory requestCutNativeTraceOrder
Ancestors
  dftGasFromListTraceDefs dftGasRequestObservation jointRequestCut
  concretizeLayoutRequestRelations venomExecSemantics venomState venomInst
  sorting relation list rich_list

val requestCount = ``\row:list_visit. LENGTH (SND (SND (SND row))).vs_requests``;
val requestUpper = ``\row:list_visit.
  if (FST (SND (SND row))).inst_opcode = INVOKE then ^requestCount row
  else case step_inst_base (FST (SND (SND row))) (SND (SND (SND row))) of
    OK t => LENGTH t.vs_requests | _ => ^requestCount row``;
val requestOrder = ``\left right:list_visit. ^requestUpper left <= ^requestCount right``;

Theorem visit_request_count_le[local]:
  ^requestCount row <= ^requestUpper row
Proof
  BETA_TAC >>
  Cases_on `(FST (SND (SND row))).inst_opcode = INVOKE` >> simp[] >>
  Cases_on `step_inst_base (FST (SND (SND row))) (SND (SND (SND row)))` >> simp[] >>
  drule step_inst_base_requests_prefix >> disch_then (mp_tac o MATCH_MP IS_PREFIX_LENGTH) >>
  simp[]
QED

Theorem native_requests_transitive[local,simp]:
  transitive ^requestOrder
Proof
  gvs[transitive_def] >> metis_tac[BETA_RULE visit_request_count_le,
    arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem bind_outputs_requests[local]:
  bind_outputs outs vals s = SOME t ==> t.vs_requests = s.vs_requests
Proof
  `!xs s. (FOLDL (\u (x,v). update_var x v u) s xs).vs_requests = s.vs_requests` by
    (Induct >> simp[] >> Cases >> simp[update_var_def]) >>
  simp[bind_outputs_def] >> strip_tac >> gvs[]
QED

Theorem invoke_not_terminator[local,simp]:
  ~is_terminator INVOKE
Proof
  simp[is_terminator_def]
QED

(* The visited requests are chronological, including the children of
   INVOKE and the following blocks of the caller. *)
Theorem native_trace_request_order[local]:
  (!p d fuel C fn i s.
    SORTED ^requestOrder (trace_step p d fuel C fn i s) /\
    EVERY (\row. LENGTH s.vs_requests <= ^requestCount row) (trace_step p d fuel C fn i s) /\
    (!t. (step_inst fuel C i s = OK t \/ ?v. step_inst fuel C i s = IntRet v t) ==>
      LENGTH s.vs_requests <= LENGTH t.vs_requests /\
      EVERY (\row. ^requestUpper row <= LENGTH t.vs_requests) (trace_step p d fuel C fn i s))) /\
  (!p d fuel C fn bb s.
    SORTED ^requestOrder (trace_block p d fuel C fn bb s) /\
    EVERY (\row. LENGTH s.vs_requests <= ^requestCount row) (trace_block p d fuel C fn bb s) /\
    (!t. (exec_block fuel C bb s = OK t \/ ?v. exec_block fuel C bb s = IntRet v t) ==>
      LENGTH s.vs_requests <= LENGTH t.vs_requests /\
      EVERY (\row. ^requestUpper row <= LENGTH t.vs_requests) (trace_block p d fuel C fn bb s))) /\
  (!p d fuel C fn s.
    SORTED ^requestOrder (trace_blocks p d fuel C fn s) /\
    EVERY (\row. LENGTH s.vs_requests <= ^requestCount row) (trace_blocks p d fuel C fn s) /\
    (!t. (run_blocks fuel C fn s = OK t \/ ?v. run_blocks fuel C fn s = IntRet v t) ==>
      LENGTH s.vs_requests <= LENGTH t.vs_requests /\
      EVERY (\row. ^requestUpper row <= LENGTH t.vs_requests) (trace_blocks p d fuel C fn s)))
Proof
  BETA_TAC >> ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_request_order[step]:
  rpt gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (rewrite_tac[Q.SPECL [`p`, `d`, `fuel`, `C`, `fn`, `i`, `s`] (cj 1 trace_defs),
                 Q.SPECL [`fuel`, `C`, `i`, `s`] step_inst_def] >> simp[] >>
      Cases_on `decode_invoke i` >> simp[] >>
      rename1 `decode_invoke i = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 C.ctx_functions` >> simp[] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s` >> simp[] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >> simp[] >>
      rename1 `setup_callee callee args s = SOME cs` >>
      `cs.vs_requests = s.vs_requests` by gvs[setup_callee_def, AllCaseEqs()] >>
      qpat_assum `!v nm ops f args cs. _`
        (qspecl_then [`(decoded0,decoded1)`, `decoded0`, `decoded1`, `callee`, `args`, `cs`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `run_blocks fuel C callee cs` >> gvs[] >>
      rename1 `run_blocks fuel C callee cs = IntRet ret out` >>
      Cases_on `bind_outputs i.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state s out))` >> simp[] >>
      drule bind_outputs_requests >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >> metis_tac[]) >>
  simp[trace_step_noninvoke] >> rpt strip_tac
  >- (drule_all step_inst_requests_prefix >> disch_then (mp_tac o MATCH_MP IS_PREFIX_LENGTH) >> simp[])
  >> drule step_inst_intret_requests >> simp[]
QED

Resume native_trace_request_order[block]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cj 2 trace_defs, exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[] >>
  `(^requestUpper ((p,d,inst.inst_id),fn,inst,s)) =
    (case step_inst fuel C inst s of
       OK u => if inst.inst_opcode = INVOKE then LENGTH s.vs_requests else LENGTH u.vs_requests
     | _ => LENGTH s.vs_requests)` by
    (BETA_TAC >> Cases_on `inst.inst_opcode = INVOKE` >>
     simp[step_inst_non_invoke] >>
     Cases_on `step_inst fuel C inst s` >> simp[]) >>
  Cases_on `step_inst fuel C inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  TRY (qmatch_goalsub_abbrev_tac `if v.vs_halted then Halt v else OK v` >>
       Cases_on `v.vs_halted` >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[trace_step_noninvoke, invoke_not_terminator] >>
  simp[SORTED_EQ, SORTED_APPEND, EVERY_MEM, MEM_APPEND,
       BETA_RULE native_requests_transitive] >>
  fs[EVERY_MEM] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Resume native_trace_request_order[blocks]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cj 3 trace_defs, run_blocks_def] >>
  Cases_on `fuel` >- simp[] >>
  rename1 `SUC f` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `sp.vs_requests = s.vs_requests` by metis_tac[eval_phis_requests] >>
  Cases_on `run_block_non_phis f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  simp[SORTED_APPEND, EVERY_MEM, MEM_APPEND, BETA_RULE native_requests_transitive] >>
  fs[EVERY_MEM] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise native_trace_request_order[local]

Theorem native_trace_context_request_order[local]:
  SORTED ^requestOrder (trace_context fuel C s)
Proof
  BETA_TAC >> Cases_on `C.ctx_entry` >> simp[trace_context_def, trace_function_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rename1 `fn_entry_label fn = SOME label` >>
  mp_tac (CONJUNCT1 (Q.SPECL [`[]`, `0`, `fuel`, `C`, `fn`,
    `s with <|vs_prev_bb := NONE; vs_current_bb := label; vs_inst_idx := 0|>`]
    (cj 3 native_trace_request_order))) >> simp[]
QED

Theorem native_trace_requests_after_step:
  trace_context fuel C v = rows /\ a < b /\ b < LENGTH rows /\
  EL a rows = (key,fn,i,s) /\ EL b rows = (key',fn',i',t) /\
  i.inst_opcode <> INVOKE /\ step_inst n C i s = OK u ==>
  LENGTH u.vs_requests <= LENGTH t.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base i s = OK u` by metis_tac[step_inst_non_invoke] >>
  mp_tac (Q.INST [`fuel` |-> `fuel`, `C` |-> `C`, `s` |-> `v`]
    native_trace_context_request_order) >>
  simp[SORTED_EL_LESS, BETA_RULE native_requests_transitive] >>
  disch_then (qspecl_then [`a`,`b`] mp_tac) >>
  simp[]
QED
