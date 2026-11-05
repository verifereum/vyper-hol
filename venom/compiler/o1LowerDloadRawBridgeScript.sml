Theory o1LowerDloadRawBridge
Ancestors
  ptrDiscipline contextRawReachable o1PassLift venomExecProps venomExecSemantics venomWf contextCodegenRel list venomInst

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

Definition ld_raw_stack_def:
  (ld_raw_stack vs C [] fn s <=>
    !i. active_inst fn i s ==> raw_reachable vs C fn i s) /\
  (ld_raw_stack vs C (f::fs) fn s <=>
    (!i. active_inst fn i s ==> raw_reachable vs C fn i s) /\
    !ret se s' i'. ld_returns C fn s ret se /\
      bind_outputs f.cf_inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
      active_inst f.cf_fn i' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
      ld_raw_stack vs C fs f.cf_fn
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

Theorem ld_raw_stack_active:
  ld_raw_stack vs C stk fn s /\ active_inst fn i s ==>
  raw_reachable vs C fn i s
Proof
  Cases_on `stk` >> simp[ld_raw_stack_def]
QED

Theorem ld_frame_raw_stack:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    (!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f) ==>
    wf_function fn /\ ld_raw_stack vs C stk fn s
Proof
  `!vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    (!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f) ==>
    wf_function fn /\ EVERY (\f. wf_function f.cf_fn) stk /\
      ld_raw_stack vs C stk fn s` suffices_by metis_tac[] >>
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_frame_raw_stack[entry]:
  rpt gen_tac >> strip_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  simp[ld_raw_stack_def] >> rpt strip_tac >>
  irule raw_reachable_entry >> metis_tac[]
QED

Resume ld_frame_raw_stack[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `stk`
  >- (gvs[ld_raw_stack_def] >> rpt strip_tac >>
      irule raw_reachable_next >> metis_tac[]) >>
  gvs[ld_raw_stack_def] >> conj_tac
  >- (rpt strip_tac >> irule raw_reachable_next >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[ld_returns_next]
QED

Resume ld_frame_raw_stack[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `stk`
  >- (gvs[ld_raw_stack_def] >> rpt strip_tac >>
      irule raw_reachable_block >> metis_tac[]) >>
  gvs[ld_raw_stack_def] >> conj_tac
  >- (rpt strip_tac >> irule raw_reachable_block >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[ld_returns_block]
QED

Resume ld_frame_raw_stack[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[ld_raw_stack_def] >>
  `ld_returns C fn s ret s_end` by metis_tac[ld_returns_immediate] >>
  metis_tac[]
QED

Resume ld_frame_raw_stack[call]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  qpat_x_assum `_ ==> _ /\ _ /\ _` drule >> strip_tac >>
  `wf_function fn'` by metis_tac[] >>
  simp[ld_raw_stack_def] >> conj_tac
  >- (rpt strip_tac >> irule raw_reachable_callee >>
      metis_tac[ld_raw_stack_active]) >>
  rpt strip_tac >>
  `?k. step_inst k C inst s = OK s'` by
    (irule ld_returns_invoke >> metis_tac[]) >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  Cases_on `stk`
  >- (gvs[ld_raw_stack_def] >> rpt strip_tac >>
      irule raw_reachable_next >> metis_tac[]) >>
  gvs[ld_raw_stack_def] >> conj_tac
  >- (rpt strip_tac >> irule raw_reachable_next >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[ld_returns_next]
QED

Finalise ld_frame_raw_stack

Theorem ld_frame_raw_reachable:
  (!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f) /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  raw_reachable vs C fn inst s
Proof
  strip_tac >> drule_all ld_frame_raw_stack >> strip_tac >>
  irule ld_raw_stack_active >>
  conj_tac
  >- (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[Once frame_reachable_cases] >> metis_tac[]) >>
  metis_tac[]
QED
