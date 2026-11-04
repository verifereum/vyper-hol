(*
 * Two contexts that agree on the functions a run can reach run alike.
 *
 * ctx_agree R ctx ctx' says the contexts resolve every name in R to the
 * same function, and R is closed under the INVOKE targets of those
 * functions.  Then a run from a function whose calls stay in R is the
 * same in both contexts (run_defs_ctx_agree), so is the context run when
 * the entry is in R (run_context_ctx_agree), and so are the raw-reachable
 * states (raw_reachable_ctx_agree), which transports the shared memory
 * invariant (mem_inv_ctx_agree).  Pruning a unit's unreachable functions
 * is an instance (prune_unit_ctx_agree).
 *
 * Also here: the semantics never writes the initial frame pointer, so
 * every raw-reachable state carries the initial state's
 * (raw_reachable_initial_fmp).
 *)
Theory ctxLookupAgree
Ancestors
  venomExecSemantics venomInst venomState contextRawReachable
  contextCodegenRel unitMemInv fcgPruning fcgDefs fcgAnalysisProps
  fcgCorrectnessProof venomWf list ctxLookupAgreeHelpers

(* ===== Agreement ===== *)

Definition inst_calls_within_def:
  inst_calls_within R inst <=>
    !nm ops. inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops)
             ==> R nm
End

Definition fn_calls_within_def:
  fn_calls_within R fn <=> EVERY (inst_calls_within R) (fn_insts fn)
End

Definition ctx_agree_def:
  ctx_agree R ctx ctx' <=>
    !name. R name ==>
      lookup_function name ctx.ctx_functions =
        lookup_function name ctx'.ctx_functions /\
      !fn. lookup_function name ctx.ctx_functions = SOME fn ==>
           fn_calls_within R fn
End

Theorem ctx_agree_sym:
  ctx_agree R ctx ctx' ==> ctx_agree R ctx' ctx
Proof
  rw[ctx_agree_def] >> res_tac >> gvs[]
QED

Theorem ctx_agree_invoke:
  ctx_agree R ctx ctx' ==>
  !i nm ops. inst_calls_within R i /\ i.inst_opcode = INVOKE /\
    decode_invoke i = SOME (nm,ops) ==>
    lookup_function nm ctx.ctx_functions = lookup_function nm ctx'.ctx_functions /\
    (!fn. lookup_function nm ctx.ctx_functions = SOME fn ==>
          EVERY (inst_calls_within R) (fn_insts fn))
Proof
  rw[ctx_agree_def, inst_calls_within_def, fn_calls_within_def] >> metis_tac[]
QED

(* ===== Runs agree ===== *)

Theorem run_defs_ctx_agree:
  ctx_agree R ctx ctx' ==>
  (!fuel inst s. inst_calls_within R inst ==>
     step_inst fuel ctx inst s = step_inst fuel ctx' inst s) /\
  (!fuel bb s. EVERY (inst_calls_within R) bb.bb_instructions ==>
     exec_block fuel ctx bb s = exec_block fuel ctx' bb s) /\
  (!fuel fn s. fn_calls_within R fn ==>
     run_blocks fuel ctx fn s = run_blocks fuel ctx' fn s)
Proof
  strip_tac >> drule ctx_agree_invoke >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (irule (cj 1 run_defs_predicate_cong) >>
      qexists_tac `inst_calls_within R` >> simp[] >> first_assum ACCEPT_TAC)
  >- (irule (cj 2 run_defs_predicate_cong) >>
      qexists_tac `inst_calls_within R` >> simp[] >> first_assum ACCEPT_TAC)
  >> irule (cj 3 run_defs_predicate_cong) >>
  qexists_tac `inst_calls_within R` >> gvs[fn_calls_within_def] >>
  first_assum ACCEPT_TAC
QED

Theorem run_context_ctx_agree:
  ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> R entry) ==>
  run_context fuel ctx s = run_context fuel ctx' s
Proof
  strip_tac >> drule run_defs_ctx_agree >> strip_tac >>
  simp[run_context_def] >>
  Cases_on `ctx.ctx_entry` >> simp[] >>
  rename1 `ctx.ctx_entry = SOME entry` >>
  `lookup_function entry ctx.ctx_functions =
     lookup_function entry ctx'.ctx_functions /\
   !fn. lookup_function entry ctx.ctx_functions = SOME fn ==>
        fn_calls_within R fn` by (fs[ctx_agree_def] >> metis_tac[]) >>
  simp[] >> Cases_on `lookup_function entry ctx'.ctx_functions` >> simp[] >>
  simp[run_function_def] >> CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem ctx_agree_selected_calls:
  ctx_agree R ctx ctx' /\ R fn.fn_name /\
  lookup_function fn.fn_name ctx.ctx_functions = SOME fn ==>
  fn_calls_within R fn
Proof rw[ctx_agree_def] >> metis_tac[]
QED

Theorem fn_calls_within_active:
  fn_calls_within R fn /\ active_inst fn inst s ==> inst_calls_within R inst
Proof simp[fn_calls_within_def] >> metis_tac[EVERY_active_inst]
QED

Theorem ctx_agree_active_step:
  ctx_agree R ctx ctx' /\ R fn.fn_name /\
  lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
  active_inst fn inst s ==>
  step_inst fuel ctx inst s = step_inst fuel ctx' inst s
Proof
  strip_tac >> drule_all ctx_agree_selected_calls >> strip_tac >>
  drule_all fn_calls_within_active >> strip_tac >>
  drule run_defs_ctx_agree >> strip_tac >> metis_tac[]
QED

(* ===== Reachable states agree ===== *)

Theorem raw_reachable_ctx_agree:
  !R ctx ctx' vs.
    ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
    (!entry. ctx.ctx_entry = SOME entry ==> R entry) ==>
    !fn inst s. raw_reachable vs ctx fn inst s ==>
      raw_reachable vs ctx' fn inst s /\ R fn.fn_name /\
      lookup_function fn.fn_name ctx.ctx_functions = SOME fn
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `ctx_agree _ _ _ /\ _` mp_tac >>
  map_every qid_spec_tac [`ctx'`, `R`] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`s`, `inst`, `fn`, `ctx`, `vs`] >>
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume raw_reachable_ctx_agree[entry]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `ctx.ctx_entry = SOME name` >>
  `R name` by metis_tac[] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  gvs[] >> irule raw_reachable_entry >> metis_tac[ctx_agree_def]
QED

Resume raw_reachable_ctx_agree[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s`
    by metis_tac[ctx_agree_active_step] >>
  conj_tac >- (irule raw_reachable_next >> metis_tac[]) >> simp[]
QED

Resume raw_reachable_ctx_agree[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s`
    by metis_tac[ctx_agree_active_step] >>
  conj_tac >- (irule raw_reachable_block >> metis_tac[]) >> simp[]
QED

Resume raw_reachable_ctx_agree[callee]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ctx_agree_selected_calls >> strip_tac >>
  drule_all fn_calls_within_active >> strip_tac >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME callee` >>
  `R nm` by metis_tac[inst_calls_within_def] >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  gvs[] >> irule raw_reachable_callee >> metis_tac[ctx_agree_def]
QED

Finalise raw_reachable_ctx_agree

Theorem mem_inv_ctx_agree:
  ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> R entry) /\
  (!fn inst s. M ctx fn inst s ==> M ctx' fn inst s) /\
  mem_inv M ctx vs ==>
  mem_inv M ctx' vs
Proof
  strip_tac >> fs[mem_inv_raw_reachable] >>
  `ctx_agree R ctx' ctx` by metis_tac[ctx_agree_sym] >>
  conj_tac
  >- (fs[ctx_agree_def] >> metis_tac[])
  >> rpt strip_tac >>
  qspecl_then [`R`, `ctx'`, `ctx`, `vs`] mp_tac raw_reachable_ctx_agree >>
  impl_tac >- metis_tac[] >>
  disch_then drule >> strip_tac >> metis_tac[]
QED

(* ===== The initial frame pointer is constant ===== *)

Theorem raw_reachable_initial_fmp:
  raw_reachable vs ctx fn inst s ==> s.vs_initial_fmp = vs.vs_initial_fmp
Proof
  map_every qid_spec_tac [`s`, `inst`, `fn`, `ctx`, `vs`] >>
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (drule enters_block_initial_fmp >> simp[])
  >- (drule step_inst_initial_fmp >> simp[])
  >- metis_tac[enters_block_initial_fmp, step_inst_initial_fmp]
  >> metis_tac[enters_block_initial_fmp, setup_callee_initial_fmp]
QED

(* ===== Pruning ===== *)

Theorem fcg_analyze_entry_reachable:
  ctx_wf ctx /\ ctx.ctx_entry = SOME entry ==>
  fcg_is_reachable (fcg_analyze ctx) entry
Proof
  strip_tac >> irule fcg_analyze_reachable_complete_proof >>
  simp[fcg_path_def] >>
  fs[ctx_wf_def, ctx_has_entry_def] >> metis_tac[]
QED

Theorem prune_unit_ctx_agree:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context ==>
  ctx_agree (fcg_is_reachable fcg) unit.cu_context
    (prune_unit_fcg_unreachable unit fcg).cu_context
Proof
  rw[ctx_agree_def]
  >- simp[lookup_function_prune_fcg_reachable]
  >> rw[fn_calls_within_def, EVERY_MEM, inst_calls_within_def] >>
  irule prune_fcg_reachable_direct_callee >>
  qexistsl_tac [`name`, `unit.cu_context`] >> simp[] >>
  simp[fn_directly_calls_def] >>
  gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[]
QED
