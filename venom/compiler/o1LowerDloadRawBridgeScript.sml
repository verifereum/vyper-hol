Theory o1LowerDloadRawBridge
Ancestors
  o1PassLift venomExecProps venomExecSemantics venomWf contextCodegenRel list venomInst

(* An existential finite return from an already-entered instruction boundary.
   run_blocks alone would re-evaluate this block's PHIs. *)
Definition ld_returns_def:
  ld_returns C fn s ret se <=>
    ?bb k. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      (exec_block k C bb s = IntRet ret se \/
       ?u. exec_block k C bb s = OK u /\ ~u.vs_halted /\
         run_blocks k C fn u = IntRet ret se)
End

Theorem ld_active_block[local]:
  wf_function fn /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[wf_function_def, active_inst_def, fn_labels_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem ld_returns_enter:
  enters_block fn cs s /\ ld_returns C fn s ret se ==>
  ?k. run_blocks k C fn cs = IntRet ret se
Proof
  simp[enters_block_def, ld_returns_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `SUC k` >> simp[Once run_blocks_def] >>
  imp_res_tac venomExecProofsTheory.eval_phis_preserves_current_bb >> gvs[]
QED

Theorem ld_returns_immediate:
  wf_function fn /\ active_inst fn inst s /\
  step_inst k C inst s = IntRet ret se ==>
  ld_returns C fn s ret se
Proof
  strip_tac >> drule_all ld_active_block >> strip_tac >>
  simp[ld_returns_def] >> qexists_tac `k` >>
  simp[Once exec_block_def]
QED

Theorem ld_returns_next:
  wf_function fn /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst k C inst s = OK u /\
  ld_returns C fn (u with vs_inst_idx := SUC s.vs_inst_idx) ret se ==>
  ld_returns C fn s ret se
Proof
  strip_tac >> drule_all ld_active_block >> strip_tac >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
  qpat_x_assum `ld_returns _ _ _ _ _` mp_tac >>
  simp[ld_returns_def] >> strip_tac >> gvs[] >>
  `step_inst (k + k') C inst s = OK u` by
    (`terminates (step_inst k C inst s)` by simp[terminates_not_error] >>
     drule step_inst_terminates_mono >>
     disch_then (qspec_then `k + k'` mp_tac) >> simp[]) >>
  `terminates (exec_block k' C bb
     (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    simp[terminates_not_error] >>
  drule exec_block_terminates_mono >>
  disch_then (qspec_then `k + k'` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `k + k'` >>
  simp[Once exec_block_def] >> simp[Once exec_block_def] >>
  `terminates (run_blocks k' C fn u')` by simp[terminates_not_error] >>
  drule run_blocks_terminates_mono >>
  disch_then (qspec_then `k + k'` mp_tac) >> simp[]
QED

Theorem ld_returns_block:
  wf_function fn /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst k C inst s = OK u /\
  ~u.vs_halted /\ enters_block fn u v /\ ld_returns C fn v ret se ==>
  ld_returns C fn s ret se
Proof
  strip_tac >> drule_all ld_active_block >> strip_tac >>
  drule_all ld_returns_enter >> strip_tac >>
  `terminates (step_inst k C inst s)` by simp[terminates_not_error] >>
  drule step_inst_terminates_mono >>
  disch_then (qspec_then `k + k'` mp_tac) >> simp[] >> strip_tac >>
  `terminates (run_blocks k' C fn u)` by simp[terminates_not_error] >>
  drule run_blocks_terminates_mono >>
  disch_then (qspec_then `k + k'` mp_tac) >> simp[] >> strip_tac >>
  simp[ld_returns_def] >> qexists_tac `k + k'` >>
  simp[Once exec_block_def] >> qexists_tac `u` >>
  simp[Once exec_block_def]
QED

Theorem ld_returns_invoke:
  call_inst.inst_opcode = INVOKE /\
  decode_invoke call_inst = SOME (name, arg_ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  enters_block callee cs v /\ ld_returns C callee v ret se /\
  bind_outputs call_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' ==>
  ?k. step_inst k C call_inst s = OK s'
Proof
  strip_tac >> drule_all ld_returns_enter >> strip_tac >>
  qexists_tac `k` >> simp[Once step_inst_def]
QED
