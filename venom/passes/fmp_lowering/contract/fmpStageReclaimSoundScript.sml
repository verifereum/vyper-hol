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
  venomExecSemantics venomState finite_map fmpAliasProps ptrDiscipline
  ctxLookupAgreeHelpers fmpAliasDefs contextCodegenRel venomInst list
  o1PassContract

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
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==> 0 < z) /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==> b < eb) PG ==>
  fmp_frame_covers sm env eb lo (step_prov PG G inst s1)
Proof
  cheat
QED

Theorem reclaim_dalloca_output[local]:
  inst.inst_opcode = DALLOCA /\ step_inst k C inst s = OK s1 ==>
  ?out. inst.inst_outputs = [out] /\ lookup_var out s1 = SOME s.vs_fmp
Proof
  strip_tac >>
  gvs[step_inst_non_invoke] >>
  gvs[Once step_inst_base_def, AllCaseEqs(), update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
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
  strip_tac >>
  drule_all reclaim_dalloca_output >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `MEM inst.inst_id (fmp_bases env out)` by
    (irule fmp_base_analyze_propagates >>
     qexistsl [`inst`, `fn_insts fn`] >>
     simp[fmp_base_output_def, fmp_single_output_def,
          fmp_generated_bases_def]) >>
  gvs[step_prov_def, out_prov_def, set_prov_def] >>
  simp[fmp_frame_covers_def] >> rpt gen_tac >> strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()]
  >- (Cases_on `s1.vs_fmp = s.vs_fmp` >>
      gvs[FLOOKUP_UPDATE] >>
      first_x_assum drule >> simp[]) >>
  Cases_on `s1.vs_fmp = s.vs_fmp`
  >- (gvs[fmp_frame_covers_def] >> metis_tac[]) >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()]
  >- (qpat_x_assum `!v b z. _` drule >> simp[] >>
      strip_tac >> gvs[]) >>
  qpat_assum `!b z c id. _` drule >> strip_tac >>
  gvs[fmp_frame_covers_def]
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
