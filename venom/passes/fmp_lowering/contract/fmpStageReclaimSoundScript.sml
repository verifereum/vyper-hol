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
  concretizeAnalysisRoots fmpAliasProps fmpAliasDefs livenessTransferProofs
  ctxLookupAgreeHelpers pointerClosure pointerConfinedDefs ptrDiscipline o1PassContract
  list finite_map pred_set venomInst

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

Theorem reclaim_operand_origin[local]:
  MEM id (fmp_operand_bases env op) ==>
  ?u. op = Var u /\ MEM id (fmp_bases env u)
Proof
  Cases_on `op` >> simp[fmp_operand_bases_def]
QED

Theorem reclaim_generated_origin[local]:
  ~MEM inst.inst_opcode [ALLOCA; DALLOCA; BUMP] /\
  MEM id (fmp_generated_bases env inst) ==>
  is_pointer_preserving_op inst.inst_opcode /\
  ?u. MEM (Var u) inst.inst_operands /\ MEM id (fmp_bases env u)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (gvs[fmp_generated_bases_def, is_pointer_preserving_op_def] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      rename1 `MEM id (case rest of [] => _ | _ => _)` >>
      Cases_on `rest` >> gvs[] >> metis_tac[reclaim_operand_origin]) >>
  Cases_on `inst.inst_opcode = PHI`
  >- (gvs[fmp_generated_bases_def, is_pointer_preserving_op_def,
          mem_foldl_list_union, MEM_MAP] >>
      metis_tac[reclaim_operand_origin]) >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB` >>
  gvs[fmp_generated_bases_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = lhs::rest` >>
  Cases_on `rest` >> gvs[] >>
  rename1 `inst.inst_operands = lhs::rhs::tail` >>
  Cases_on `tail` >> gvs[] >>
  Cases_on `fmp_operand_bases env lhs = []` >>
  Cases_on `fmp_operand_bases env rhs = []` >>
  gvs[fmp_arithmetic_bases_def, is_pointer_preserving_op_def] >>
  metis_tac[reclaim_operand_origin]
QED

Theorem reclaim_transfer_support[local]:
  MEM inst (fn_insts fn) /\
  ~MEM inst.inst_opcode [ALLOCA; BUMP] /\
  (!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn) ==>
  !v id. MEM id (fmp_bases (fmp_base_transfer inst env) v) ==>
    v IN fn_pv P fn
Proof
  rpt strip_tac >>
  Cases_on `fmp_base_output inst` >>
  gvs[fmp_base_transfer_def, fmp_bases_accumulate]
  >- metis_tac[]
  >- metis_tac[] >>
  rename1 `fmp_base_output inst = SOME out` >>
  `inst.inst_outputs = [out]` by
    (gvs[fmp_base_output_def, fmp_single_output_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (`out IN ptr_roots P fn` by
        (simp[ptr_roots_def] >> disj1_tac >> disj2_tac >>
         qexists `inst` >> simp[inst_output_def]) >>
      metis_tac[fn_pv_def, pointer_derived_vars_roots,
                ptr_roots_finite, SUBSET_DEF]) >>
  drule_at (Pos last) reclaim_generated_origin >> simp[] >> strip_tac >>
  simp[fn_pv_def] >> irule pointer_derived_vars_closed >>
  simp[ptr_roots_finite] >> qexistsl [`inst`, `u`] >>
  simp[] >> metis_tac[fn_pv_def]
QED

Theorem reclaim_sweep_support[local]:
  !insts env. EVERY (\i. MEM i (fn_insts fn) /\
      ~MEM i.inst_opcode [ALLOCA; BUMP]) insts /\
  (!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn) ==>
  !v id. MEM id (fmp_bases (fmp_base_sweep insts env) v) ==>
    v IN fn_pv P fn
Proof
  Induct >> simp[fmp_base_sweep_def] >> rpt strip_tac >>
  rename1 `MEM i (fn_insts fn)` >>
  qpat_x_assum `!e. EVERY _ _ /\ _ ==> _`
    (qspec_then `fmp_base_transfer i env` mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule_at (Pos last) reclaim_transfer_support >> simp[] >>
      disch_then (qspecl_then [`fn`, `P`] mp_tac) >> simp[] >>
      metis_tac[]) >>
  disch_then irule >> goal_assum drule
QED

Theorem reclaim_iter_support[local]:
  !n env. EVERY (\i. MEM i (fn_insts fn) /\
      ~MEM i.inst_opcode [ALLOCA; BUMP]) insts /\
  (!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn) ==>
  !v id. MEM id (fmp_bases (fmp_base_iter n insts env) v) ==>
    v IN fn_pv P fn
Proof
  Induct >> simp[fmp_base_iter_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >- gvs[] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!e. EVERY _ _ /\ _ ==> _`
    (qspec_then `fmp_base_sweep insts env` mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule_at (Pos last) reclaim_sweep_support >>
      disch_then (qspecl_then [`fn`, `P`] mp_tac) >> simp[] >>
      metis_tac[]) >>
  disch_then irule >> goal_assum drule
QED

Theorem reclaim_analyze_support[local]:
  fmp_base_analyze (fn_insts fn) = SOME env /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
  pre_fmp_ops fn ==>
  !v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn
Proof
  simp[fmp_base_analyze_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  drule_at (Pos last) reclaim_iter_support >>
  disch_then (qspecl_then [`fn`, `P`] mp_tac) >>
  impl_tac
  >- (gvs[fmp_bases_def, pre_fmp_ops_def, pre_fmp_opcode_def,
           EVERY_MEM] >> metis_tac[]) >> simp[]
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
