Theory lowerDloadPtrRawReachable
Ancestors
  contextRawReachable ptrDiscipline venomExecSemantics venomInst contextCodegenRel
  crossBlockSimProps passSimulationDefs venomExecProofs o1PassContract venomWf list

Theorem raw_reachable_completed_invoke:
  !vs ctx caller callinst s nm ops callee args cs fuel ret se sr inst'.
  raw_reachable vs ctx caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret se /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME sr /\
  active_inst caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx) ==>
  raw_reachable vs ctx caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx callinst s = OK sr` by
    simp[Once step_inst_def] >>
  irule raw_reachable_next >>
  conj_tac >- simp[] >>
  qexistsl [`fuel`,`callinst`] >> simp[is_terminator_def]
QED

(* The block lookup is explicit: active_inst alone uses membership, which
   need not identify the block returned by lookup_block without uniqueness. *)
Theorem run_blocks_immediate_return:
  !ctx fn cs bb sp s1 rinst fuel ret se.
  lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis cs bb.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  get_instruction bb s1.vs_inst_idx = SOME rinst /\
  step_inst fuel ctx rinst s1 = IntRet ret se ==>
  run_blocks (SUC fuel) ctx fn cs = IntRet ret se
Proof
  rpt strip_tac >> gvs[] >>
  `exec_block fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret se` by
    simp[Once exec_block_def] >>
  simp[Once run_blocks_unfold, run_block_def]
QED

Theorem frame_step_fuel_mono:
  !f ctx inst s. (!e. step_inst f ctx inst s <> Error e) ==>
  !k. step_inst (f+k) ctx inst s = step_inst f ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    qpat_x_assum `!e. _` mp_tac >>
    simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst` >- simp[] >>
    PairCases_on `x` >> simp[] >>
    Cases_on `lookup_function x0 ctx.ctx_functions` >- simp[] >>
    rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
    Cases_on `eval_operands x1 s` >- simp[] >>
    rename1 `eval_operands x1 s = SOME args` >>
    Cases_on `setup_callee callee args s` >- simp[] >>
    rename1 `setup_callee callee args s = SOME cs` >>
    strip_tac >>
    `terminates (run_blocks f ctx callee cs)` by
      (Cases_on `run_blocks f ctx callee cs` >> gvs[terminates_def]) >>
    drule run_blocks_fuel_mono >> disch_then (qspec_then `k` assume_tac) >>
    simp[step_inst_def]) >>
  simp[step_inst_def]
QED

Theorem frame_exec_fuel_mono:
  !f ctx bb s. (!e. exec_block f ctx bb s <> Error e) ==>
  !k. exec_block (f+k) ctx bb s = exec_block f ctx bb s
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `!e. _` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[] >> strip_tac >>
  `!e. step_inst f ctx inst s <> Error e` by
    (spose_not_then strip_assume_tac >> gvs[]) >>
  drule frame_step_fuel_mono >> disch_then (qspec_then `k` assume_tac) >>
  simp[] >>
  Cases_on `step_inst f ctx inst s` >> gvs[] >>
  rename1 `step_inst f ctx inst s = OK s'` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()]) >>
  first_x_assum irule >> simp[]
QED

Theorem frame_exec_prepend:
  !ctx bb inst s s' f g r.
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst f ctx inst s = OK s' /\
  exec_block g ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx) = r /\
  (!e. r <> Error e) ==>
  ?h. exec_block h ctx bb s = r
Proof
  rpt strip_tac >>
  `!e. step_inst f ctx inst s <> Error e` by simp[] >>
  drule frame_step_fuel_mono >> disch_then (qspec_then `g` assume_tac) >>
  `!e. exec_block g ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx) <> Error e`
    by simp[] >>
  drule frame_exec_fuel_mono >> disch_then (qspec_then `f` assume_tac) >>
  qexists_tac `f+g` >> once_rewrite_tac[exec_block_def] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem frame_run_prepend_block:
  !ctx fn cs bb f g s' ret se.
  lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block f ctx bb cs = OK s' /\ ~s'.vs_halted /\
  run_blocks g ctx fn s' = IntRet ret se ==>
  ?h. run_blocks h ctx fn cs = IntRet ret se
Proof
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >>
  mp_tac (Q.SPECL [`cs`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> gvs[] >>
  rename1 `eval_phis cs bb.bb_instructions = OK sp` >>
  strip_tac >>
  `!e. exec_block f ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) <> Error e`
    by simp[] >>
  drule frame_exec_fuel_mono >> disch_then (qspec_then `g` assume_tac) >>
  `terminates (run_blocks g ctx fn s')` by simp[terminates_def] >>
  drule run_blocks_fuel_mono >> disch_then (qspec_then `f` assume_tac) >>
  qexists_tac `SUC (f+g)` >>
  simp[Once run_blocks_unfold, run_block_def] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem frame_run_from_exec_return:
  !ctx fn cs bb sp f ret se.
  lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis cs bb.bb_instructions = OK sp /\
  exec_block f ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret se ==>
  run_blocks (SUC f) ctx fn cs = IntRet ret se
Proof
  rpt strip_tac >> simp[Once run_blocks_unfold, run_block_def]
QED

Definition frame_tail_returns_def:
  frame_tail_returns ctx fn s ret se <=>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    ((?k. exec_block k ctx bb s = IntRet ret se) \/
     (?k t h. exec_block k ctx bb s = OK t /\ ~t.vs_halted /\
              run_blocks h ctx fn t = IntRet ret se))
End

Definition frame_prefix_def:
  frame_prefix ctx fn cs s <=>
  !ret se. frame_tail_returns ctx fn s ret se ==>
    ?h. run_blocks h ctx fn cs = IntRet ret se
End

Theorem frame_prefix_entry:
  enters_block fn cs s ==> frame_prefix ctx fn cs s
Proof
  rw[enters_block_def, frame_prefix_def, frame_tail_returns_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[]
  >- (qexists_tac `SUC k` >> irule frame_run_from_exec_return >>
      qexistsl [`bb`,`s_phi`] >> simp[]) >>
  irule frame_run_prepend_block >>
  qexistsl [`bb`,`k`,`h`,`t`] >> simp[run_block_def]
QED

Theorem frame_prefix_next:
  frame_prefix ctx fn cs s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst f ctx inst s = OK t /\
  lookup_block (t with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
    fn.fn_blocks = SOME bb ==>
  frame_prefix ctx fn cs (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rw[frame_prefix_def, frame_tail_returns_def] >> gvs[] >>
  first_x_assum irule >> simp[frame_tail_returns_def] >>
  all_tac
  >- (disj1_tac >> irule frame_exec_prepend >>
      conj_tac >- simp[] >>
      qexistsl [`f`,`k`,`inst`,`t`] >> simp[]) >>
  disj2_tac >>
  `?j. exec_block j ctx bb s = OK t'` by
    (irule frame_exec_prepend >> conj_tac >- simp[] >>
     qexistsl [`f`,`k`,`inst`,`t`] >> simp[]) >>
  qexistsl [`j`,`t'`,`h`] >> simp[]
QED

Theorem frame_prefix_return:
  frame_prefix ctx fn cs s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst k ctx inst s = IntRet ret se ==>
  ?h. run_blocks h ctx fn cs = IntRet ret se
Proof
  rw[frame_prefix_def] >> first_x_assum irule >>
  simp[frame_tail_returns_def] >> disj1_tac >>
  qexists_tac `k` >> simp[Once exec_block_def]
QED

Theorem frame_prefix_block:
  frame_prefix ctx fn cs s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t /\
  ~t.vs_halted /\ enters_block fn t s1 ==>
  frame_prefix ctx fn cs s1
Proof
  rpt strip_tac >>
  drule frame_prefix_entry >>
  rw[frame_prefix_def] >>
  `?h. run_blocks h ctx fn t = IntRet ret se` by metis_tac[] >>
  qpat_x_assum `frame_prefix ctx fn cs s` mp_tac >>
  rewrite_tac[frame_prefix_def] >> disch_then irule >>
  simp[frame_tail_returns_def] >> disj2_tac >>
  qexistsl [`k`,`t`,`h`] >> simp[Once exec_block_def]
QED

(* active_inst uses membership; distinct labels identify the selected block. *)
Theorem active_inst_block_lookup:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem o1_ctx_shape_function_wf:
  o1_ctx_shape ctx /\ MEM fn ctx.ctx_functions ==> wf_function fn
Proof
  simp[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]
QED

Theorem o1_ctx_shape_active_lookup:
  o1_ctx_shape ctx /\ MEM fn ctx.ctx_functions /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rpt strip_tac >> irule active_inst_block_lookup >> simp[] >>
  drule_all o1_ctx_shape_function_wf >> simp[wf_function_def]
QED

Definition frame_stack_prefix_def:
  (frame_stack_prefix vs ctx [] fn s <=> T) /\
  (frame_stack_prefix vs ctx (f::stk) fn s <=>
    ?nm ops args cs.
      MEM fn ctx.ctx_functions /\ MEM f.cf_fn ctx.ctx_functions /\
      raw_reachable vs ctx f.cf_fn f.cf_inst f.cf_state /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      f.cf_inst.inst_opcode = INVOKE /\
      decode_invoke f.cf_inst = SOME (nm,ops) /\
      lookup_function nm ctx.ctx_functions = SOME fn /\
      eval_operands ops f.cf_state = SOME args /\
      setup_callee fn args f.cf_state = SOME cs /\
      frame_prefix ctx fn cs s /\
      frame_stack_prefix vs ctx stk f.cf_fn f.cf_state)
End

Theorem frame_stack_prefix_next:
  o1_ctx_shape ctx /\ MEM fn ctx.ctx_functions /\
  frame_stack_prefix vs ctx stk fn s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t ==>
  frame_stack_prefix vs ctx stk fn (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all o1_ctx_shape_active_lookup >> strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  Cases_on `stk` >> fs[frame_stack_prefix_def] >>
  irule frame_prefix_next >> simp[] >>
  qexists_tac `k` >> simp[]
QED

Theorem frame_stack_prefix_block:
  o1_ctx_shape ctx /\ MEM fn ctx.ctx_functions /\
  frame_stack_prefix vs ctx stk fn s /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t /\
  ~t.vs_halted /\ enters_block fn t s1 ==>
  frame_stack_prefix vs ctx stk fn s1
Proof
  rpt strip_tac >>
  drule_all o1_ctx_shape_active_lookup >> strip_tac >>
  Cases_on `stk` >> fs[frame_stack_prefix_def] >>
  irule frame_prefix_block >> simp[] >> metis_tac[]
QED

Theorem frame_stack_prefix_pop:
  o1_ctx_shape ctx /\ frame_stack_prefix vs ctx (f::stk) fn s /\
  active_inst fn rinst s /\ step_inst k ctx rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME sr /\
  active_inst f.cf_fn inst' (sr with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  MEM f.cf_fn ctx.ctx_functions /\
  raw_reachable vs ctx f.cf_fn inst'
    (sr with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  frame_stack_prefix vs ctx stk f.cf_fn
    (sr with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> fs[frame_stack_prefix_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME rinst` by
    (irule o1_ctx_shape_active_lookup >> metis_tac[]) >>
  `?h. run_blocks h ctx fn cs = IntRet ret se` by
    (irule frame_prefix_return >> metis_tac[]) >>
  `step_inst h ctx f.cf_inst f.cf_state = OK sr` by
    simp[Once step_inst_def] >>
  conj_tac
  >- (irule raw_reachable_completed_invoke >> metis_tac[]) >>
  irule frame_stack_prefix_next >> simp[] >>
  qexistsl [`f.cf_inst`,`h`] >> simp[is_terminator_def]
QED

Theorem frame_reachable_raw_certificate:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  o1_ctx_shape ctx ==>
  MEM fn ctx.ctx_functions /\ raw_reachable vs ctx fn inst s /\
  frame_stack_prefix vs ctx stk fn s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      simp[frame_stack_prefix_def] >> conj_tac
      >- metis_tac[lookup_function_MEM] >>
      irule raw_reachable_entry >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      conj_tac >- (irule raw_reachable_next >> metis_tac[]) >>
      irule frame_stack_prefix_next >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      conj_tac >- (irule raw_reachable_block >> metis_tac[]) >>
      irule frame_stack_prefix_block >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      drule lookup_function_MEM >> strip_tac >>
      simp[] >> conj_tac
      >- (irule raw_reachable_callee >> metis_tac[]) >>
      simp[frame_stack_prefix_def] >>
      irule frame_prefix_entry >> simp[])
  >> rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  irule frame_stack_prefix_pop >> metis_tac[]
QED

Theorem frame_reachable_raw:
  o1_ctx_shape ctx /\ frame_reachable vs ctx stk PG G tn fn inst s ==>
  raw_reachable vs ctx fn inst s
Proof
  metis_tac[frame_reachable_raw_certificate]
QED


Theorem frame_reachable_functions_member:
  !vs ctx ds PH H un g j t.
    frame_reachable vs ctx ds PH H un g j t ==>
    MEM g ctx.ctx_functions /\ EVERY (\d. MEM d.cf_fn ctx.ctx_functions) ds
Proof
  ho_match_mp_tac frame_reachable_ind >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[lookup_function_MEM]
QED
