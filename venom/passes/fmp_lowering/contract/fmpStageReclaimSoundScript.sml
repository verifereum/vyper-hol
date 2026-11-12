(*
 * Reclaim soundness for FmpLowering's stage simulation: the facts about
 * the source run and the reclaim analysis that let a restore drop sites
 * no live pointer uses.
 *
 * TOP-LEVEL:
 *   fmp_stage_frame_sites    - a frame_reachable state's sites lie between
 *                              fmp and its frontier, a frame's own above its
 *                              entry fmp and its parameters' below
 *   fmp_stage_covers_step    - an ordinary step keeps base coverage
 *   fmp_stage_covers_dalloca - a DALLOCA step keeps it, with its new site
 *   fmp_stage_covers_phis    - block entry keeps it
 *   fmp_stage_live_edge      - a variable live after a successor's PHIs is
 *                              its PHI operand's or live itself at the
 *                              predecessor's terminator
 *   fmp_stage_out_not_kept   - a DALLOCA's output is not on the analysis
 *                              stack before it
 *)
Theory fmpStageReclaimSound
Ancestors
  fmpStageRel ptrStaticDiscipline cfgWf venomWf livenessProofs
  ptrDisciplineEmptyTaint lowerDloadPtrSourceInv lowerDloadPtrRawReachable
  o1PassContract unitMemInv venomExecSemantics venomState contextCodegenRel
  list venomInst opcodeClass words finite_map arithmetic

Theorem fmp_source_memory[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp
Proof
  strip_tac >>
  `mem_inv (static_mem_ok eom) C vs /\ o1_ctx_shape C` by
    gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def] >>
  drule_all mem_inv_frame_reachable >> simp[static_mem_ok_def]
QED

Theorem fmp_source_opcodes[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  inst.inst_opcode <> ALLOCA /\ pre_fmp_opcode inst.inst_opcode
Proof
  strip_tac >>
  `o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions` by
    gvs[fmp_stage_ctx_def, o1_pre_def] >>
  drule_all lowerDloadPtrRawReachableTheory.frame_reachable_raw_certificate >>
  strip_tac >>
  `o1_fn_row 3 fn` by gvs[EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  gvs[o1_fn_row_def, pre_fmp_ops_def, EVERY_MEM]
QED

Theorem fmp_eval_phis_frontier[local]:
  !s t. eval_phis s insts = OK t ==> t.vs_fmp = s.vs_fmp
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >> simp[Once eval_phis_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  gvs[AllCaseEqs(), update_var_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem fmp_enters_block_frontier[local]:
  enters_block fn s t ==> t.vs_fmp = s.vs_fmp
Proof
  rw[enters_block_def] >> drule fmp_eval_phis_frontier >> simp[]
QED

Theorem fmp_source_return[local]:
  inst.inst_opcode <> INVOKE /\ pre_fmp_opcode inst.inst_opcode /\
  step_inst fuel C inst s = IntRet ret t ==>
  t = s /\ ret.iret_adopt_fmp = NONE
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >>
  gvs[pre_fmp_opcode_def] >> strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs()]
QED

Theorem fmp_return_caller_frontier[local]:
  ret.iret_adopt_fmp = NONE /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME t ==>
  t.vs_fmp = caller.vs_fmp
Proof
  strip_tac >> drule bind_outputs_allocation_frame >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem fmp_source_nonalloc_frontier[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> DALLOCA /\ pre_fmp_opcode inst.inst_opcode /\
  step_inst fuel C inst s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> irule allocation_free_step_fmp_ok >>
  gvs[allocation_free_opcode_def, pre_fmp_opcode_def] >> metis_tac[]
QED

Theorem fmp_source_dalloca[local]:
  inst.inst_opcode = DALLOCA /\ dalloca_no_wrap inst s /\
  step_inst fuel C inst s = OK t ==>
  ?size_op sz out.
    inst.inst_operands = [size_op] /\ inst.inst_outputs = [out] /\
    eval_operand size_op s = SOME sz /\
    lookup_var out t = SOME s.vs_fmp /\
    w2n t.vs_fmp = w2n s.vs_fmp + ceil32 (w2n sz)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  gvs[dalloca_no_wrap_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w,
       w2n_n2w] >>
  simp[w2n_add_2]
QED

Theorem fmp_source_step_frontier[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  pre_fmp_opcode inst.inst_opcode /\ dalloca_no_wrap inst s /\
  step_inst fuel C inst s = OK t ==>
  w2n s.vs_fmp <= w2n t.vs_fmp
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DALLOCA`
  >- (drule_all fmp_source_dalloca >> strip_tac >> simp[]) >>
  drule_all fmp_source_nonalloc_frontier >> simp[]
QED

Theorem fmp_stage_frame_sites:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  w2n fmp <= fmp_frame_base (w2n fmp) stk /\
  fmp_frame_base (w2n fmp) stk <= w2n s.vs_fmp /\
  EVERY (\f. w2n f.cf_state.vs_fmp <= w2n s.vs_fmp) stk /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     w2n fmp <= b /\ b + z <= w2n s.vs_fmp) /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
               b + z <= fmp_frame_base (w2n fmp) stk) PG
Proof
  cheat
QED

Theorem fmp_stage_covers_step:
  fmp_base_analyze (fn_insts fn) = SOME env /\ fn_static_ptr_ok P fn /\
  fn_inst_wf fn /\ EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  pre_fmp_ops fn /\
  wf_function fn /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; PHI] /\
  step_inst k C inst s = OK s1 /\
  fmp_frame_covers sm env eb lo G /\
  EVERY (\h. !b z. h = SOME (b,z) ==> b < eb) PG ==>
  fmp_frame_covers sm env eb lo (step_prov PG G inst s1)
Proof
  cheat
QED

Theorem fmp_stage_covers_dalloca:
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = DALLOCA /\
  step_inst k C inst s = OK s1 /\
  fmp_frame_covers sm env eb lo G /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
     0 < z /\ b + z <= w2n s.vs_fmp /\ c + z <= lo) /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==> b + z <= w2n s.vs_fmp) ==>
  fmp_frame_covers
    (if w2n s1.vs_fmp = w2n s.vs_fmp then sm
     else sm |+ ((w2n s.vs_fmp, w2n s1.vs_fmp - w2n s.vs_fmp),
                (lo, inst.inst_id)))
    env eb (lo + (w2n s1.vs_fmp - w2n s.vs_fmp))
    (step_prov PG G inst s1)
Proof
  cheat
QED

Theorem fmp_stage_covers_phis:
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  fmp_frame_covers sm env eb lo G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  fmp_frame_covers sm env eb lo (entry_prov fn s G)
Proof
  cheat
QED

Theorem fmp_stage_live_edge:
  wf_function fn /\ fn_inst_wf fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pbb /\
  lookup_block sl fn.fn_blocks = SOME sbb /\
  pbb.bb_instructions <> [] /\
  MEM v (live_vars_at (liveness_analyze fn) sl
           (phi_prefix_length sbb.bb_instructions)) ==>
  (?phi. MEM phi (collect_phis sbb.bb_instructions) /\
         MEM v phi.inst_outputs /\
         !u. resolve_phi pl phi.inst_operands = SOME (Var u) ==>
             MEM u (live_vars_at (liveness_analyze fn) pl
                      (PRE (LENGTH pbb.bb_instructions)))) \/
  (MEM v (live_vars_at (liveness_analyze fn) pl
            (PRE (LENGTH pbb.bb_instructions))) /\
   EVERY (\q. ~MEM v q.inst_outputs) (collect_phis sbb.bb_instructions))
Proof
  cheat
QED

Theorem fmp_stage_out_not_kept:
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = DALLOCA /\
  (EL k bb.bb_instructions).inst_outputs = [out] /\
  df_at NONE states bb.bb_label k = SOME st ==>
  ~MEM out st.frs_stack
Proof
  cheat
QED
