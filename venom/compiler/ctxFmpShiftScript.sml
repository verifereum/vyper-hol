(*
 * A context none of whose instructions reads or writes the FMP state runs
 * alike from two states that differ only there.
 *
 * fmp_shift s s' says s and s' are equal up to vs_fmp, vs_initial_fmp
 * and vs_call_entry_fmp, and fmp_shift_result lifts it to results of the
 * same shape.  Only the raw FMP operations (is_raw_fmp_opcode) and
 * INITIAL_FMP read those fields; INVOKE copies vs_fmp into the callee's
 * frame and back, which keeps the relation.  So in a context without
 * them a run from shifted states ends in shifted results
 * (run_defs_fmp_shift, run_context_fmp_shift), each raw-reachable state
 * from one initial state has a shifted twin from the other
 * (raw_reachable_fmp_shift), and a memory fact that does not look at the
 * FMP fields transports (mem_inv_fmp_shift).
 *
 * FmpLowering's stage before it lowers anything is an instance: its raw
 * input runs at a different free-memory pointer from the lowered code.
 *
 * TOP-LEVEL:
 *   run_context_fmp_shift   - context runs end in shifted results
 *   raw_reachable_fmp_shift - reachable states correspond
 *   mem_inv_fmp_shift       - the memory invariant transports
 *)
Theory ctxFmpShift
Ancestors
  venomExecSemantics venomInst venomState contextRawReachable
  contextCodegenRel unitMemInv list
  ctxFmpBaseHelpers ctxFmpControlHelpers ctxFmpMembershipHelpers
  ctxFmpUpdateHelpers instIdxIndep ctxLookupAgreeHelpers

Definition fmp_shift_def:
  fmp_shift (s : venom_state) s' <=>
    s' = s with <| vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
                   vs_call_entry_fmp := s'.vs_call_entry_fmp |>
End

Definition fmp_shift_result_def:
  (fmp_shift_result (OK s) r <=> ?s'. r = OK s' /\ fmp_shift s s') /\
  (fmp_shift_result (Halt s) r <=> ?s'. r = Halt s' /\ fmp_shift s s') /\
  (fmp_shift_result (Abort a s) r <=>
     ?s'. r = Abort a s' /\ fmp_shift s s') /\
  (fmp_shift_result (IntRet ir s) r <=>
     ?s'. r = IntRet ir s' /\ fmp_shift s s') /\
  (fmp_shift_result (Error e) r <=> r = Error e)
End

(* An instruction that neither reads nor writes the FMP state. *)
Definition fmp_blind_inst_def:
  fmp_blind_inst inst <=>
    ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INITIAL_FMP
End

Definition fmp_blind_ctx_def:
  fmp_blind_ctx C <=>
    EVERY (\fn. EVERY fmp_blind_inst (fn_insts fn)) C.ctx_functions
End

Theorem fmp_shift_refl:
  fmp_shift s s
Proof
  simp[fmp_shift_def, venom_state_component_equality]
QED

Theorem fmp_shift_sym:
  fmp_shift s s' ==> fmp_shift s' s
Proof
  simp[fmp_shift_def, venom_state_component_equality] >> rw[]
QED

Theorem fmp_shift_fields[local]:
  fmp_shift s t ==>
  t.vs_inst_idx = s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_halted = s.vs_halted
Proof
  simp[fmp_shift_def] >> strip_tac >> once_asm_rewrite_tac[] >> simp[]
QED

Theorem fmp_shift_eval_operands[local]:
  fmp_shift s t ==> eval_operands ops t = eval_operands ops s
Proof
  simp[fmp_shift_def] >> strip_tac >> once_asm_rewrite_tac[] >>
  simp[SRULE [] eval_operands_fmp_update]
QED

Theorem fmp_shift_base[local]:
  fmp_blind_inst inst /\ fmp_shift s t ==>
  fmp_shift_result (step_inst_base inst s) (step_inst_base inst t)
Proof
  simp[fmp_blind_inst_def, fmp_shift_def] >> strip_tac >>
  once_asm_rewrite_tac[] >> simp[SRULE [] step_inst_base_fmp_update] >>
  Cases_on `step_inst_base inst s` >>
  simp[exec_result_map_def, fmp_shift_result_def, fmp_shift_def]
QED

(* The run of each instruction, block and function of such a context. *)
Theorem run_defs_fmp_shift:
  (!fuel C inst s s'.
     fmp_blind_ctx C /\ fmp_blind_inst inst /\ fmp_shift s s' ==>
     fmp_shift_result (step_inst fuel C inst s)
                      (step_inst fuel C inst s')) /\
  (!fuel C bb s s'.
     fmp_blind_ctx C /\ EVERY fmp_blind_inst bb.bb_instructions /\
     fmp_shift s s' ==>
     fmp_shift_result (exec_block fuel C bb s)
                      (exec_block fuel C bb s')) /\
  (!fuel C fn s s'.
     fmp_blind_ctx C /\ EVERY fmp_blind_inst (fn_insts fn) /\
     fmp_shift s s' ==>
     fmp_shift_result (run_blocks fuel C fn s)
                      (run_blocks fuel C fn s'))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_fmp_shift[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >> simp[] >> metis_tac[fmp_shift_base]
QED

Resume run_defs_fmp_shift[invoke]:
  simp[] >> Cases_on `decode_invoke inst` >- simp[fmp_shift_result_def] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  rename1 `decode_invoke inst = SOME (nm,ops)` >> simp[] >>
  Cases_on `lookup_function nm C.ctx_functions` >- simp[fmp_shift_result_def] >>
  rename1 `lookup_function nm C.ctx_functions = SOME fn` >>
  `EVERY fmp_blind_inst (fn_insts fn)` by
    (gvs[fmp_blind_ctx_def] >> drule_all EVERY_lookup_function >> simp[]) >>
  `eval_operands ops s' = eval_operands ops s` by metis_tac[fmp_shift_eval_operands] >>
  simp[] >> Cases_on `eval_operands ops s` >- simp[fmp_shift_result_def] >>
  rename1 `eval_operands ops s = SOME args` >> simp[] >>
  drule (SRULE [GSYM fmp_shift_def] setup_callee_fmp_none) >>
  disch_then (qspecl_then [`fn`,`args`] assume_tac) >>
  Cases_on `setup_callee fn args s` >- gvs[fmp_shift_result_def] >>
  rename1 `setup_callee fn args s = SOME cs` >>
  drule_all (SRULE [GSYM fmp_shift_def] setup_callee_fmp_some) >> strip_tac >>
  `fmp_shift_result (run_blocks fuel C fn cs) (run_blocks fuel C fn t')`
    by (first_x_assum irule >> metis_tac[]) >>
  qpat_x_assum `!a b c d e f. _` kall_tac >>
  simp[] >> Cases_on `run_blocks fuel C fn cs` >>
  gvs[fmp_shift_result_def] >>
  `fmp_shift (adopt_return_fmp i (merge_callee_state s v))
             (adopt_return_fmp i (merge_callee_state s' s''))` by
    metis_tac[SRULE [GSYM fmp_shift_def] merge_callee_state_fmp_shift,
              SRULE [GSYM fmp_shift_def] adopt_return_fmp_shift] >>
  qabbrev_tac `a = adopt_return_fmp i (merge_callee_state s v)` >>
  qabbrev_tac `b = adopt_return_fmp i (merge_callee_state s' s'')` >>
  qabbrev_tac `outs = inst.inst_outputs` >>
  qabbrev_tac `vals = i.iret_values` >>
  Cases_on `bind_outputs outs vals a`
  >- (drule_all (SRULE [GSYM fmp_shift_def] bind_outputs_fmp_none) >>
      disch_then (qspecl_then [`vals`,`outs`] mp_tac) >>
      simp[fmp_shift_result_def]) >>
  drule_all (SRULE [GSYM fmp_shift_def] bind_outputs_fmp_some) >>
  strip_tac >> simp[fmp_shift_result_def]
QED

Resume run_defs_fmp_shift[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule fmp_shift_fields >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[fmp_shift_result_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `fmp_blind_inst inst` by metis_tac[EVERY_get_instruction] >>
  `fmp_shift_result (step_inst fuel C inst s) (step_inst fuel C inst s')`
    by (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!inst. _` kall_tac >>
  simp[] >> Cases_on `step_inst fuel C inst s` >>
  gvs[fmp_shift_result_def] >>
  rename1 `fmp_shift v t` >> drule fmp_shift_fields >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (simp[] >> IF_CASES_TAC >> simp[fmp_shift_result_def]) >>
  simp[] >> first_x_assum irule >>
  simp[] >> gvs[fmp_shift_def, venom_state_component_equality]
QED
Resume run_defs_fmp_shift[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule fmp_shift_fields >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  Cases_on `fuel` >- simp[fmp_shift_result_def] >>
  rename1 `SUC n` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[fmp_shift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `EVERY fmp_blind_inst bb.bb_instructions` by metis_tac[EVERY_fn_lookup_block] >>
  `eval_phis s' bb.bb_instructions =
   exec_result_map (\t. t with <|vs_fmp := s'.vs_fmp;
     vs_initial_fmp := s'.vs_initial_fmp; vs_call_entry_fmp := s'.vs_call_entry_fmp|>)
     (eval_phis s bb.bb_instructions)` by
    (qpat_x_assum `fmp_shift s s'` mp_tac >> simp[fmp_shift_def] >> strip_tac >>
     once_asm_rewrite_tac[] >> simp[SRULE [] eval_phis_fmp_update]) >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[exec_result_map_def, fmp_shift_result_def] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `fmp_shift_result
     (exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     (exec_block n C bb (sp with <|vs_fmp := s'.vs_fmp;
       vs_initial_fmp := s'.vs_initial_fmp; vs_call_entry_fmp := s'.vs_call_entry_fmp;
       vs_inst_idx := phi_prefix_length bb.bb_instructions|>))` by
    (first_x_assum irule >> simp[fmp_shift_def]) >>
  qpat_x_assum `!t. fmp_shift _ t ==> _` kall_tac >>
  Cases_on `exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[fmp_shift_result_def] >>
  rename1 `fmp_shift v t` >> drule fmp_shift_fields >> strip_tac >>
  Cases_on `v.vs_halted` >- simp[fmp_shift_result_def] >>
  simp[] >> first_x_assum irule >> simp[]
QED
Finalise run_defs_fmp_shift

Theorem run_context_fmp_shift:
  fmp_blind_ctx C /\ fmp_shift s s' ==>
  fmp_shift_result (run_context fuel C s) (run_context fuel C s')
Proof
  strip_tac >> simp[run_context_def] >>
  Cases_on `C.ctx_entry` >- simp[fmp_shift_result_def] >>
  Cases_on `lookup_function x C.ctx_functions` >- simp[fmp_shift_result_def] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  `EVERY fmp_blind_inst (fn_insts fn)` by
    (gvs[fmp_blind_ctx_def] >> drule_all EVERY_lookup_function >> simp[]) >>
  simp[run_function_def] >> Cases_on `fn_entry_label fn`
  >- simp[fmp_shift_result_def] >>
  simp[] >> irule (cj 3 run_defs_fmp_shift) >>
  simp[] >> gvs[fmp_shift_def, venom_state_component_equality]
QED

Theorem fmp_shift_enters_block[local]:
  fmp_shift s t /\ enters_block fn s u ==>
  ?v. fmp_shift u v /\ enters_block fn t v
Proof
  strip_tac >>
  qexists `u with <|vs_fmp := t.vs_fmp; vs_initial_fmp := t.vs_initial_fmp;
                   vs_call_entry_fmp := t.vs_call_entry_fmp|>` >>
  conj_tac >- simp[fmp_shift_def] >>
  qpat_x_assum `fmp_shift s t` mp_tac >> simp[fmp_shift_def] >> strip_tac >>
  once_asm_rewrite_tac[] >>
  metis_tac[SRULE [] enters_block_fmp_update]
QED

Theorem fmp_shift_active_inst[local]:
  fmp_shift s t ==> (active_inst fn inst t <=> active_inst fn inst s)
Proof
  simp[fmp_shift_def] >> strip_tac >> once_asm_rewrite_tac[] >>
  simp[SRULE [] active_inst_fmp_update]
QED

Theorem raw_reachable_fmp_shift_ind[local]:
  !vs C fn inst t. raw_reachable vs C fn inst t ==>
  !vs'. fmp_blind_ctx C /\ fmp_shift vs vs' ==>
    ?t'. fmp_shift t t' /\ raw_reachable vs' C fn inst t'
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume raw_reachable_fmp_shift_ind[entry]:
  rpt strip_tac >>
  `fmp_shift (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
             (vs' with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)`
    by gvs[fmp_shift_def, venom_state_component_equality] >>
  drule_all fmp_shift_enters_block >> strip_tac >>
  qexists `v` >> simp[] >> irule raw_reachable_entry >>
  metis_tac[fmp_shift_active_inst]
QED
Resume raw_reachable_fmp_shift_ind[next]:
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac >>
  `fmp_blind_inst inst` by
    (drule EVERY_raw_reachable >> disch_then (qspec_then `fmp_blind_inst` mp_tac) >>
     simp[GSYM fmp_blind_ctx_def]) >>
  `fmp_shift_result (step_inst fuel C inst t) (step_inst fuel C inst t')`
    by metis_tac[run_defs_fmp_shift] >>
  gvs[fmp_shift_result_def] >> rename1 `fmp_shift s' u` >>
  `fmp_shift (s' with vs_inst_idx := SUC t.vs_inst_idx)
             (u with vs_inst_idx := SUC t'.vs_inst_idx)`
    by gvs[fmp_shift_def, venom_state_component_equality] >>
  qexists `u with vs_inst_idx := SUC t'.vs_inst_idx` >> simp[] >>
  irule raw_reachable_next >> metis_tac[fmp_shift_active_inst]
QED
Resume raw_reachable_fmp_shift_ind[block]:
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac >>
  `fmp_blind_inst inst` by
    (drule EVERY_raw_reachable >> disch_then (qspec_then `fmp_blind_inst` mp_tac) >>
     simp[GSYM fmp_blind_ctx_def]) >>
  `fmp_shift_result (step_inst fuel C inst t) (step_inst fuel C inst t'')`
    by metis_tac[run_defs_fmp_shift] >>
  gvs[fmp_shift_result_def] >>
  drule_all fmp_shift_enters_block >> strip_tac >>
  qexists `v` >> simp[] >> irule raw_reachable_block >>
  metis_tac[fmp_shift_active_inst, fmp_shift_fields]
QED
Resume raw_reachable_fmp_shift_ind[callee]:
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac >>
  rename1 `fmp_shift t u` >>
  drule_all (SRULE [GSYM fmp_shift_def] setup_callee_fmp_some) >> strip_tac >>
  drule_all fmp_shift_enters_block >> strip_tac >>
  qexists `v` >> simp[] >> irule raw_reachable_callee >>
  metis_tac[fmp_shift_active_inst, fmp_shift_eval_operands]
QED
Finalise raw_reachable_fmp_shift_ind

(* Reachability from the second state is reachability from the first, at
   a shifted state. *)
Theorem raw_reachable_fmp_shift:
  fmp_blind_ctx C /\ fmp_shift vs vs' /\ raw_reachable vs' C fn inst s' ==>
  ?s. fmp_shift s s' /\ raw_reachable vs C fn inst s
Proof
  metis_tac[raw_reachable_fmp_shift_ind, fmp_shift_sym]
QED

Theorem mem_inv_fmp_shift:
  fmp_blind_ctx C /\ fmp_shift vs vs' /\
  (!fn inst s s'. fmp_shift s s' /\ M C fn inst s ==> M' C fn inst s') /\
  mem_inv M C vs ==>
  mem_inv M' C vs'
Proof
  rw[mem_inv_raw_reachable] >>
  TRY (drule_all raw_reachable_fmp_shift >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED
