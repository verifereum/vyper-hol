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
 *   fmp_source_memory        - a reachable source state's DALLOCA can't
 *                              wrap, and its fmp is above the initial one
 *)
Theory fmpStageReclaimSound
Ancestors
  fmpStageRel ptrStaticDiscipline cfgWf venomWf livenessProofs
  ptrDisciplineEmptyTaint lowerDloadPtrSourceInv lowerDloadPtrRawReachable
  o1PassContract unitMemInv venomExecSemantics venomState contextCodegenRel
  list venomInst opcodeClass words finite_map arithmetic
  frameAllocationOwnership ptrDiscipline
  concretizeAnalysisRoots fmpAliasProps fmpAliasDefs livenessTransferProofs
  ctxLookupAgreeHelpers pointerClosure pointerConfinedDefs pred_set
  dftCommutation
  fmpReclaimDefs venomExecProofs While basePtrProofs
  fnBlockPlanStaticOffsetLive fnPlanLineageLiveness fnBlockPlanStatic
  pair indexedLists livenessDefs venomFnInstsProofs fnLineageStatic
  fmpLowerReclaimPlan venomWfProps removeUnusedProofs
  fnFrameSinglePred fmpStageReclaimFresh fnFrameStepsPhi

Theorem fmp_source_memory:
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

Theorem fmp_sites_out[local]:
  prov_sites P G /\ param_sites P PG /\
  inst.inst_opcode <> ALLOCA /\
  (inst.inst_opcode = DALLOCA ==>
    !site. out_prov PG G inst s' = SOME site ==> P site) /\
  out_prov PG G inst s' = SOME site ==> P site
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DALLOCA`
  >- metis_tac[] >>
  qpat_x_assum `out_prov _ _ _ _ = _` mp_tac >>
  simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = PARAM` >> simp[]
  >- (gvs[AllCaseEqs(), param_sites_def] >> metis_tac[MEM_EL]) >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN` >> simp[] >>
  metis_tac[prov_sites_first]
QED

Theorem fmp_sites_step[local]:
  prov_sites P G /\ param_sites P PG /\
  inst.inst_opcode <> ALLOCA /\
  (inst.inst_opcode = DALLOCA ==>
    !site. out_prov PG G inst s' = SOME site ==> P site) ==>
  prov_sites P (step_prov PG G inst s')
Proof
  strip_tac >> simp[step_prov_def] >> irule prov_sites_set >>
  simp[] >> metis_tac[fmp_sites_out]
QED

Theorem fmp_sites_params[local]:
  prov_sites P G ==> param_sites P (MAP (op_prov G) ops)
Proof
  simp[param_sites_def, MEM_MAP] >> rpt strip_tac >>
  metis_tac[prov_sites_op]
QED

Theorem fmp_frame_sites_invariant[local]:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  !rpolicy D C' vs' fmp eom.
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  (w2n fmp <= fmp_frame_base (w2n fmp) stk /\
   fmp_frame_base (w2n fmp) stk <= w2n s.vs_fmp /\
   EVERY (\f. w2n f.cf_state.vs_fmp <= w2n s.vs_fmp) stk /\
   prov_sites (\(b,z). 0 < z ==> w2n fmp <= b /\ b + z <= w2n s.vs_fmp) G /\
   param_sites (\(b,z). 0 < z ==> w2n fmp <= b /\
                  b + z <= fmp_frame_base (w2n fmp) stk) PG) /\
  (!pre f rest. stk = pre ++ f::rest ==>
   w2n fmp <= fmp_frame_base (w2n fmp) rest /\
   fmp_frame_base (w2n fmp) rest <= w2n f.cf_state.vs_fmp /\
   EVERY (\g. w2n g.cf_state.vs_fmp <= w2n f.cf_state.vs_fmp) rest /\
   prov_sites (\(b,z). 0 < z ==> w2n fmp <= b /\
                     b + z <= w2n f.cf_state.vs_fmp) f.cf_prov /\
   param_sites (\(b,z). 0 < z ==> w2n fmp <= b /\
                  b + z <= fmp_frame_base (w2n fmp) rest) f.cf_params)
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume fmp_frame_sites_invariant[entry]:
  rpt strip_tac >>
  imp_res_tac fmp_enters_block_frontier >>
  gvs[fmp_stage_ctx_def, fmp_frame_base_def, prov_sites_def,
      param_sites_def]
QED

Resume fmp_frame_sites_invariant[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `inst.inst_opcode <> ALLOCA /\ pre_fmp_opcode inst.inst_opcode` by
    (drule_all fmp_source_opcodes >> simp[]) >>
  `dalloca_no_wrap inst s` by
    (drule_all fmp_source_memory >> simp[]) >>
  `w2n s.vs_fmp <= w2n s'.vs_fmp` by
    (irule fmp_source_step_frontier >> metis_tac[]) >>
  reverse conj_tac >- (qpat_x_assum `!pre f rest. _` ACCEPT_TAC) >>
  pure_rewrite_tac [venom_state_accfupds, venom_state_accessors] >>
  rpt conj_tac
  >- simp[]
  >- decide_tac
  >- (gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS])
  >- (irule fmp_sites_step >> conj_tac >- simp[] >>
      conj_tac
      >- (strip_tac >> rpt strip_tac >>
          drule_all fmp_source_dalloca >> strip_tac >>
          gvs[out_prov_def, AllCaseEqs()] >> decide_tac) >>
      conj_tac
      >- (gvs[param_sites_def] >> rpt strip_tac >>
          first_x_assum drule >> Cases_on `site` >> simp[] >> decide_tac) >>
      irule prov_sites_mono >> goal_assum (drule_at Any) >>
      Cases >> simp[] >> decide_tac)
  >> simp[]
QED

Resume fmp_frame_sites_invariant[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `inst.inst_opcode <> ALLOCA /\ pre_fmp_opcode inst.inst_opcode` by
    (drule_all fmp_source_opcodes >> simp[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA` by
    metis_tac[is_terminator_def] >>
  `s'.vs_fmp = s.vs_fmp` by
    (irule fmp_source_nonalloc_frontier >> metis_tac[]) >>
  drule fmp_enters_block_frontier >> strip_tac >>
  reverse conj_tac >- (qpat_x_assum `!pre f rest. _` ACCEPT_TAC) >>
  simp[] >> irule prov_sites_entry >> simp[]
QED

Resume fmp_frame_sites_invariant[call]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule setup_callee_frame >> strip_tac >>
  drule fmp_enters_block_frontier >> strip_tac >>
  conj_tac
  >- (simp[fmp_frame_base_def, prov_sites_def] >>
      irule fmp_sites_params >> simp[]) >>
  rpt gen_tac >> namedCases_on `pre` ["", "head tail"]
  >- (simp[] >> strip_tac >> gvs[] >> simp[]) >>
  pure_rewrite_tac [APPEND, CONS_11] >> strip_tac >>
  qpat_x_assum `!pre f rest. _`
    (qspecl_then [`tail`, `f`, `rest`] mp_tac) >>
  simp[]
QED

Resume fmp_frame_sites_invariant[ret]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `inst.inst_opcode <> ALLOCA /\ pre_fmp_opcode inst.inst_opcode` by
    (drule_all fmp_source_opcodes >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by
    metis_tac[ptrSafeRunTheory.step_inst_intret_not_invoke] >>
  `ret.iret_adopt_fmp = NONE` by
    (drule_all fmp_source_return >> simp[]) >>
  `s'.vs_fmp = f.cf_state.vs_fmp` by
    (irule fmp_return_caller_frontier >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `!pre f rest. _`
        (qspecl_then [`[]`, `f`, `stk`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      irule prov_sites_restrict >> simp[]) >>
  map_every qx_gen_tac [`pre`, `saved`, `rest`] >> strip_tac >>
  qpat_x_assum `!pre f rest. _`
    (qspecl_then [`f::pre`, `saved`, `rest`] mp_tac) >> simp[]
QED

Finalise fmp_frame_sites_invariant[local]

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
  strip_tac >> drule fmp_frame_sites_invariant >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `!pre f rest. _` kall_tac >>
  gvs[prov_sites_def, param_sites_def, EVERY_MEM] >>
  conj_tac >> rpt strip_tac
  >- (qpat_x_assum `!v site. _` drule >> simp[])
  >- (qpat_x_assum `!v site. _` drule >> simp[])
  >> gvs[] >> first_x_assum drule >> simp[]
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

Theorem reclaim_arithmetic_member[local]:
  (!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn) /\
  affine_pointer_ops fn (ptr_roots P fn) /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [lhs;rhs] /\
  MEM id (fmp_operand_bases env lhs) ==>
  MEM id (fmp_generated_bases env inst)
Proof
  strip_tac >>
  `fmp_operand_bases env rhs = []` by
    (spose_not_then assume_tac >>
     `?j. MEM j (fmp_operand_bases env rhs)` by simp[MEMBER_NOT_EMPTY] >>
     Cases_on `lhs` >> gvs[fmp_operand_bases_def] >>
     Cases_on `rhs` >> gvs[fmp_operand_bases_def] >>
     gvs[affine_pointer_ops_def, fn_pv_def, fn_insts_def,
         fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[fmp_generated_bases_def, fmp_arithmetic_bases_def] >>
  metis_tac[MEM]
QED

Theorem reclaim_first_bases[local]:
  (!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn) /\
  affine_pointer_ops fn (ptr_roots P fn) /\ MEM inst (fn_insts fn) /\
  inst_wf inst /\
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  first_prov G inst.inst_operands = SOME site /\
  (!u. FLOOKUP G u = SOME site ==> MEM id (fmp_bases env u)) ==>
  MEM id (fmp_generated_bases env inst)
Proof
  strip_tac
  >- (gvs[inst_wf_def] >>
      `?op. inst.inst_operands = [op]` by gvs[LENGTH_EQ_NUM_compute] >>
      gvs[first_prov_def, fmp_generated_bases_def] >>
      Cases_on `op` >> gvs[op_prov_def, fmp_operand_bases_def, AllCaseEqs()])
  >> (gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      rename1 `inst.inst_operands = [lhs;rhs]` >>
      Cases_on `op_prov G lhs`
      >- (gvs[first_prov_def] >>
          `MEM id (fmp_operand_bases env rhs)` by
            (Cases_on `rhs` >> gvs[op_prov_def, fmp_operand_bases_def,
                                  AllCaseEqs()]) >>
          `fmp_operand_bases env lhs = []` by
            (spose_not_then assume_tac >>
             `?j. MEM j (fmp_operand_bases env lhs)` by simp[MEMBER_NOT_EMPTY] >>
             Cases_on `lhs` >> Cases_on `rhs` >>
             gvs[fmp_operand_bases_def, affine_pointer_ops_def, fn_pv_def,
                 fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
          `inst.inst_opcode = ADD` by
            (Cases_on `rhs` >>
             gvs[fmp_operand_bases_def, affine_pointer_ops_def, fn_pv_def,
                 fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
          gvs[fmp_generated_bases_def, fmp_arithmetic_bases_def] >>
          metis_tac[MEM]) >>
      `MEM id (fmp_operand_bases env lhs)` by
        (Cases_on `lhs` >>
         gvs[first_prov_def, op_prov_def, fmp_operand_bases_def] >> metis_tac[]) >>
      irule reclaim_arithmetic_member >>
      metis_tac[])
QED

Theorem reclaim_set_covers[local]:
  fmp_frame_covers sm env eb lo G /\
  (!out b z c id. outs = [out] /\ p = SOME (b,z) /\
    FLOOKUP sm (b,z) = SOME (c,id) /\ eb <= b /\ c < lo ==>
    MEM id (fmp_bases env out)) ==>
  fmp_frame_covers sm env eb lo (set_prov G outs p)
Proof
  strip_tac >>
  Cases_on `outs` >> Cases_on `p` >>
  gvs[set_prov_def, fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
  qmatch_goalsub_rename_tac `case rest of [] => _ | _ => _` >>
  Cases_on `rest` >>
  gvs[set_prov_def, fmp_frame_covers_def, FLOOKUP_DRESTRICT,
      FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
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
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
         fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> ALLOCA` by gvs[EVERY_MEM] >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `!v id. MEM id (fmp_bases env v) ==> v IN fn_pv P fn` by
    metis_tac[reclaim_analyze_support] >>
  simp[step_prov_def] >> irule reclaim_set_covers >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[out_prov_def, AllCaseEqs()] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      `0 < z` by metis_tac[] >>
      qpat_x_assum `EVERY _ PG` mp_tac >> simp[EVERY_EL] >>
      disch_then (qspec_then `w2n idx` mp_tac) >> simp[]) >>
  `first_prov G inst.inst_operands = SOME (b,z) /\
   (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB)` by
    (gvs[out_prov_def, AllCaseEqs()] >> metis_tac[]) >>
  (irule fmp_base_analyze_propagates >>
  qexistsl [`inst`, `fn_insts fn`] >>
  simp[fmp_base_output_def, fmp_single_output_def] >>
  irule reclaim_first_bases >> simp[] >> conj_tac
  >- (qexistsl [`G`, `(b,z)`] >> simp[] >>
      gvs[fmp_frame_covers_def] >> metis_tac[]) >>
  qexistsl [`P`, `fn`] >> gvs[fn_static_ptr_ok_def] >> gvs[])
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

Theorem covers_phi_bases[local]:
  fmp_base_analyze insts = SOME env /\ MEM inst insts /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  phi_prov prev G inst = SOME (b,z) /\
  fmp_frame_covers sm env eb lo G /\
  FLOOKUP sm (b,z) = SOME (c,id) /\ eb <= b /\ c < lo ==>
  MEM id (fmp_bases env out)
Proof
  rpt strip_tac >>
  gvs[phi_prov_def, AllCaseEqs()] >>
  rename1 `resolve_phi lbl inst.inst_operands = SOME op` >>
  Cases_on `op` >> gvs[op_prov_def] >>
  rename1 `FLOOKUP G u = SOME (b,z)` >>
  `MEM id (fmp_bases env u)` by metis_tac[fmp_frame_covers_def] >>
  `MEM (Var u) inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  irule fmp_base_analyze_propagates >>
  qexistsl [`inst`, `insts`] >>
  simp[fmp_base_output_def, fmp_single_output_def,
       fmp_generated_bases_def, mem_foldl_list_union, MEM_MAP] >>
  metis_tac[fmp_operand_bases_def]
QED

Theorem covers_phis_list[local]:
  !insts. fmp_base_analyze allinsts = SOME env /\
  EVERY (\i. MEM i allinsts) insts /\
  fmp_frame_covers sm env eb lo G ==>
  fmp_frame_covers sm env eb lo (phis_prov prev G insts)
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phis_prov_def] >>
  `fmp_frame_covers sm env eb lo (phis_prov prev G insts)` by gvs[] >>
  Cases_on `h.inst_outputs`
  >- (gvs[set_prov_def, fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
      metis_tac[]) >>
  rename1 `h.inst_outputs = out::outs` >>
  Cases_on `outs`
  >- (Cases_on `phi_prov prev G h`
      >- (gvs[set_prov_def, fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
          metis_tac[]) >>
      simp[set_prov_def, fmp_frame_covers_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `out = v` >> gvs[]
      >- (irule covers_phi_bases >> metis_tac[]) >>
      metis_tac[fmp_frame_covers_def]) >>
  Cases_on `phi_prov prev G h` >>
  gvs[set_prov_def, fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

Theorem fmp_stage_covers_phis:
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  fmp_frame_covers sm env eb lo G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  fmp_frame_covers sm env eb lo (entry_prov fn s G)
Proof
  rpt strip_tac >> simp[entry_prov_def] >>
  irule covers_phis_list >>
  reverse conj_tac >- simp[] >>
  qexists_tac `fn_insts fn` >> simp[EVERY_MEM] >>
  drule lookup_block_mem >> strip_tac >>
  simp[venomInstTheory.fn_insts_def] >>
  metis_tac[venomInstTheory.fmp_fn_insts_blocks_intro]
QED

Theorem fmp_ready_phi_other_source[local]:
  fmp_phi_ready_block live bb /\
  MEM phi (collect_phis bb.bb_instructions) /\
  LENGTH phi.inst_outputs = 1 /\ MEM v phi.inst_outputs /\
  MEM v (live_vars_at live bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions))) /\
  MEM u (inst_uses phi) /\ u <> v ==>
  EVERY (\q. ~MEM u q.inst_outputs) (collect_phis bb.bb_instructions)
Proof
  strip_tac >>
  `phi.inst_outputs = [v]` by
    (Cases_on `phi.inst_outputs` >> gvs[] >>
     rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]) >>
  gvs[fmp_phi_ready_block_def, EVERY_MEM] >>
  first_x_assum (qspec_then `phi` mp_tac) >> simp[] >>
  disch_then (qspec_then `u` mp_tac) >> simp[]
QED

Theorem fmp_ready_phi_earliest_source[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
  (!k. k < j ==> ~MEM v (EL k (collect_phis bb.bb_instructions)).inst_outputs) /\
  resolve_phi pred (EL j (collect_phis bb.bb_instructions)).inst_operands = SOME (Var u) ==>
  MEM u (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `EL j (collect_phis bb.bb_instructions) = EL j bb.bb_instructions /\
   (EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[collect_phis_index] >>
  `j < LENGTH bb.bb_instructions` by
    metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `MEM u (inst_uses (EL j bb.bb_instructions))` by
    metis_tac[resolve_phi_MEM, operand_var_in_inst_uses] >>
  `MEM u (live_vars_at (liveness_analyze fn) lbl j)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >> metis_tac[]) >>
  `!k. k < j ==> ~MEM u (inst_defs (EL k bb.bb_instructions))` by
    (Cases_on `u = v`
     >- (gvs[inst_defs_def] >> rpt strip_tac >>
         `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
         metis_tac[collect_phis_index]) >>
     `inst_wf (EL j bb.bb_instructions)` by
       metis_tac[fn_inst_wf_def, lookup_block_mem, EL_MEM] >>
     `LENGTH (EL j bb.bb_instructions).inst_outputs = 1` by
       gvs[inst_wf_def] >>
     `EVERY (\q. ~MEM u q.inst_outputs) (collect_phis bb.bb_instructions)` by
       (irule fmp_ready_phi_other_source >> goal_assum (drule_at Any) >>
        qexistsl_tac [`liveness_analyze fn`, `v`] >> simp[] >> metis_tac[EL_MEM]) >>
     rpt strip_tac >>
     `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
     `EL k (collect_phis bb.bb_instructions) = EL k bb.bb_instructions` by
       metis_tac[collect_phis_index] >>
     `MEM (EL k bb.bb_instructions) (collect_phis bb.bb_instructions)` by
       metis_tac[EL_MEM] >>
     gvs[EVERY_MEM, inst_defs_def] >> metis_tac[]) >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
  simp[] >> qexists_tac `j` >> simp[]
QED

Theorem fmp_ready_phi_witness[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs) ==>
  ?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs /\
    !pred u. resolve_phi pred phi.inst_operands = SOME (Var u) ==>
      MEM u (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `?j. j < LENGTH (collect_phis bb.bb_instructions) /\
       MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs` by
    metis_tac[MEM_EL] >>
  rename1 `j < LENGTH (collect_phis bb.bb_instructions)` >>
  `?m. (m < LENGTH (collect_phis bb.bb_instructions) /\
         MEM v (EL m (collect_phis bb.bb_instructions)).inst_outputs) /\
       !k. k < m ==> ~(k < LENGTH (collect_phis bb.bb_instructions) /\
         MEM v (EL k (collect_phis bb.bb_instructions)).inst_outputs)` by
    (ho_match_mp_tac arithmeticTheory.WOP >> qexists_tac `j` >> simp[]) >>
  qpat_x_assum `j < LENGTH _` kall_tac >>
  qpat_x_assum `MEM v (EL j _).inst_outputs` kall_tac >>
  rename1 `m < LENGTH (collect_phis bb.bb_instructions)` >>
  qexists_tac `EL m (collect_phis bb.bb_instructions)` >>
  simp[EL_MEM] >> rpt strip_tac >>
  irule fmp_ready_phi_earliest_source >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`m`, `pred`, `v`] >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem fmp_phi_index_unique[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  EL i (collect_phis bb.bb_instructions) =
    EL j (collect_phis bb.bb_instructions) ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\q. q.inst_id) bb.bb_instructions)` by
    (irule all_distinct_flat_mem >>
     qexists_tac `MAP (\b. MAP (\q. q.inst_id) b.bb_instructions) fn.fn_blocks` >>
     conj_tac >- gvs[wf_function_def, fn_inst_ids_distinct_def] >>
     simp[MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
  `EL i (collect_phis bb.bb_instructions) = EL i bb.bb_instructions /\
   EL j (collect_phis bb.bb_instructions) = EL j bb.bb_instructions`
    by metis_tac[collect_phis_index] >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`,`j`] mp_tac) >>
  simp[EL_MAP] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions`
    by simp[current_collect_phis_length] >>
  gvs[]
QED

Theorem fmp_ready_source_index[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  idx < LENGTH (collect_phis bb.bb_instructions) /\
  MEM u (MAP SND (phi_pairs
    (EL idx (collect_phis bb.bb_instructions)).inst_operands)) ==>
  !i. i < LENGTH (collect_phis bb.bb_instructions) /\
    MEM u (MAP SND (phi_pairs
      (EL i (collect_phis bb.bb_instructions)).inst_operands)) ==> i = idx
Proof
  strip_tac >> rpt strip_tac >>
  irule fmp_phi_index_unique >> qexistsl_tac [`bb`,`fn`] >> simp[] >>
  `MEM u (inst_uses (EL idx (collect_phis bb.bb_instructions))) /\
   MEM u (inst_uses (EL i (collect_phis bb.bb_instructions)))`
    by metis_tac[inst_uses_def, phi_pairs_mem_operand_vars] >>
  gvs[fmp_phi_ready_block_def, EVERY_MEM] >>
  metis_tac[EL_MEM]
QED

Theorem fmp_ready_selected_input[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM phi (collect_phis bb.bb_instructions) /\
  resolve_phi pred phi.inst_operands = SOME (Var u) /\ MEM u live ==>
  MEM u (input_vars_from pred bb.bb_instructions live)
Proof
  strip_tac >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI`
    by metis_tac[collect_phis_mem] >>
  `inst_wf phi` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed phi.inst_operands` by gvs[inst_wf_def] >>
  drule phi_resolve_find_pairs >>
  disch_then (qspec_then `pred` mp_tac) >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands)` >>
  gvs[] >> rename1 `FIND _ _ = SOME found` >> Cases_on `found` >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `FIND _ _ = SOME (label,u)` >>
  `label = pred` by (drule venomInstTheory.FIND_P >> simp[]) >> gvs[] >>
  `MEM u (MAP SND (phi_pairs phi.inst_operands))`
    by (drule venomInstTheory.FIND_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
  qpat_x_assum `MEM phi (collect_phis _)`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> rename1 `idx < LENGTH _` >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) /\
     MEM u (MAP SND (phi_pairs
       (EL i (collect_phis bb.bb_instructions)).inst_operands)) ==> i = idx`
    by metis_tac[fmp_ready_source_index] >>
  rename1 `resolve_phi pred _ = _` >>
  mp_tac (Q.SPECL [`MAPi (\i phi. (i,phi)) (collect_phis bb.bb_instructions)`,
    `FEMPTY`, `FEMPTY`, `pred`, `u`, `idx`, `u`] phi_maps_fold_selected) >>
  impl_tac
  >- (conj_tac
      >- (simp[EVERY_MEM, MEM_MAPi, FORALL_PROD] >> rpt strip_tac >> gvs[])
      >> simp[MEM_MAP, MEM_MAPi] >> qexists_tac `(idx,phi)` >> simp[] >>
      qexists_tac `idx` >> simp[]) >>
  strip_tac >> irule input_vars_from_trigger_maps >>
  qexistsl_tac [`idx`,
    `SND (build_phi_maps pred (collect_phis bb.bb_instructions))`,
    `FST (build_phi_maps pred (collect_phis bb.bb_instructions))`, `u`] >>
  simp[build_phi_maps_def]
QED

Theorem fmp_ready_nonphi_input[local]:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_label = lbl /\ fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  EVERY (\q. ~MEM v q.inst_outputs) (collect_phis bb.bb_instructions) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  strip_tac >> irule input_vars_from_non_phi >> conj_tac
  >~ [`!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v (MAP SND (phi_pairs inst.inst_operands))`]
  >- (gvs[fmp_phi_ready_block_def, EVERY_MEM, inst_uses_def] >>
      metis_tac[phi_pairs_mem_operand_vars]) >>
  drule live_vars_at_propagate_range >> simp[] >>
  disch_then irule >> simp[] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
  simp[current_collect_phis_length] >> rpt strip_tac >>
  drule collect_phis_index >> strip_tac >>
  gvs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]
QED

Theorem fmp_input_at_terminator[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pbb /\
  lookup_block sl fn.fn_blocks = SOME sbb /\
  pbb.bb_instructions <> [] /\
  MEM x (input_vars_from pl sbb.bb_instructions
    (live_vars_at (liveness_analyze fn) sl 0)) ==>
  MEM x (live_vars_at (liveness_analyze fn) pl
    (PRE (LENGTH pbb.bb_instructions)))
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pl` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) pl
     (LENGTH pbb.bb_instructions))` by
    (drule_all analyzed_live_out_edge_subset >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `MEM pbb fn.fn_blocks` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `bb_well_formed pbb` by gvs[wf_function_def] >>
  `inst_wf (LAST pbb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, rich_listTheory.MEM_LAST_NOT_NIL] >>
  `(LAST pbb.bb_instructions).inst_outputs = []` by
    metis_tac[venomExecProofsTheory.terminator_no_outputs, bb_well_formed_def] >>
  drule live_vars_at_propagate >> simp[] >> disch_then irule >>
  `0 < LENGTH pbb.bb_instructions` by
    (Cases_on `pbb.bb_instructions` >> gvs[]) >>
  `SUC (PRE (LENGTH pbb.bb_instructions)) = LENGTH pbb.bb_instructions` by decide_tac >>
  simp[inst_defs_def, GSYM LAST_EL]
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
  strip_tac >>
  `MEM sbb fn.fn_blocks /\ sbb.bb_label = sl` by
    metis_tac[lookup_block_mem, lookup_block_label] >>
  `fmp_phi_ready_block (liveness_analyze fn) sbb` by
    (drule fmp_reclaim_states_phi_ready >> simp[EVERY_MEM]) >>
  `MEM v (live_vars_at (liveness_analyze fn) sl
    (LENGTH (collect_phis sbb.bb_instructions)))` by
    metis_tac[regional_collect_phis_length] >>
  Cases_on `?phi. MEM phi (collect_phis sbb.bb_instructions) /\
                     MEM v phi.inst_outputs`
  >- (disj1_tac >>
      drule_all fmp_ready_phi_witness >> strip_tac >>
      rename1 `MEM phi (collect_phis sbb.bb_instructions)` >>
      qexists_tac `phi` >> simp[] >> rpt strip_tac >>
      irule fmp_input_at_terminator >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[fmp_ready_selected_input]) >>
  `EVERY (\q. ~MEM v q.inst_outputs) (collect_phis sbb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  irule fmp_input_at_terminator >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[fmp_ready_nonphi_input]
QED

Theorem fresh_transfer[local]:
  ~MEM v inst.inst_outputs /\ ~MEM v st.frs_stack /\
  fmp_transfer infos fn live env p inst (SOME st) = SOME st' ==>
  ~MEM v st'.frs_stack
Proof
  strip_tac >>
  Cases_on `fmp_pop_at infos fn live env p inst st` >>
  rename1 `fmp_pop_at infos fn live env p inst st = (popped,kept)` >>
  drule fmp_pop_at_kept >> strip_tac >>
  gvs[fmp_transfer_def, fmp_reclaim_step_def] >>
  Cases_on `fmp_clears_marks infos inst` >>
  gvs[fmp_apply_effect_def, fmp_empty_reclaim_state_def] >>
  Cases_on `inst.inst_opcode = DALLOCA` >> gvs[] >>
  Cases_on `inst.inst_outputs` >>
  gvs[fmpAliasDefsTheory.fmp_single_output_def] >>
  rename1 `inst.inst_outputs = h::tail` >>
  Cases_on `tail` >> gvs[fmpAliasDefsTheory.fmp_single_output_def]
QED

Theorem fresh_block_prefix[local]:
  !n st. fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks /\
  n <= LENGTH bb.bb_instructions /\
  (!j. j < n ==> ~MEM v (EL j bb.bb_instructions).inst_outputs) /\
  df_at NONE states bb.bb_label 0 = SOME start /\ ~MEM v start.frs_stack /\
  df_at NONE states bb.bb_label n = SOME st ==> ~MEM v st.frs_stack
Proof
  Induct >> rpt gen_tac >> strip_tac >- gvs[] >>
  `n < LENGTH bb.bb_instructions` by simp[] >>
  drule_all fmp_reclaim_states_df_at_suc >> strip_tac >>
  Cases_on `df_at NONE states bb.bb_label n`
  >- gvs[fmp_transfer_def, fmp_reclaim_step_def] >>
  rename1 `df_at NONE states bb.bb_label n = SOME prev` >>
  `~MEM v prev.frs_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `~MEM v (EL n bb.bb_instructions).inst_outputs` by simp[] >>
  metis_tac[fresh_transfer]
QED

Theorem fresh_first_hit[local]:
  !R a b. RTC R a b ==> !P.
  P a /\ (!x y. R x y /\ x <> b /\ P x ==> P y) ==> P b
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >>
  rpt strip_tac >> metis_tac[]
QED

Theorem fresh_edge_step[local]:
  wf_function fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  MEM out (EL k bb.bb_instructions).inst_outputs /\
  (!pb n s. MEM pb fn.fn_blocks /\ n <= LENGTH pb.bb_instructions /\
    df_at NONE states pb.bb_label 0 = SOME s ==>
    ?t. df_at NONE states pb.bb_label n = SOME t) /\
  (!pb sb t. MEM pb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
    MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
    df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t ==>
    ?s ks. df_at NONE states sb.bb_label 0 = SOME s /\
           t.frs_stack = s.frs_stack ++ ks) /\
  fn_cfg_edge fn a b /\ a <> bb.bb_label /\
  df_at NONE states a 0 = SOME start /\ ~MEM out start.frs_stack ==>
  ?s. df_at NONE states b 0 = SOME s /\ ~MEM out s.frs_stack
Proof
  strip_tac >>
  `?sb. lookup_block b fn.fn_blocks = SOME sb` by
    metis_tac[fn_cfg_edge_target_block] >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = b` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM b (cfg_succs_of (cfg_analyze fn) a)` by
    metis_tac[fn_cfg_edge_succs] >>
  qpat_x_assum `fn_cfg_edge fn a b` mp_tac >>
  simp[fn_cfg_edge_def] >> strip_tac >>
  rename1 `MEM pb fn.fn_blocks` >>
  `?t. df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t` by
    metis_tac[LESS_EQ_REFL] >>
  `!j. j < LENGTH pb.bb_instructions ==>
       ~MEM out (EL j pb.bb_instructions).inst_outputs` by
    metis_tac[ssa_form_position] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `~MEM out t.frs_stack` by
    (gvs[] >>
     `LENGTH pb.bb_instructions <= LENGTH pb.bb_instructions` by simp[] >>
     drule_all fresh_block_prefix >> simp[]) >>
  metis_tac[MEM_APPEND]
QED

Theorem fresh_out_conditional[local]:
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = DALLOCA /\
  (EL k bb.bb_instructions).inst_outputs = [out] /\
  df_at NONE states bb.bb_label k = SOME st /\
  (!ebb. entry_block fn = SOME ebb ==>
    ?s. df_at NONE states ebb.bb_label 0 = SOME s /\ s.frs_stack = []) /\
  (!pb n s. MEM pb fn.fn_blocks /\ n <= LENGTH pb.bb_instructions /\
    df_at NONE states pb.bb_label 0 = SOME s ==>
    ?t. df_at NONE states pb.bb_label n = SOME t) /\
  (!pb sb t. MEM pb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
    MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
    df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t ==>
    ?s ks. df_at NONE states sb.bb_label 0 = SOME s /\
           t.frs_stack = s.frs_stack ++ ks) ==>
  ~MEM out st.frs_stack
Proof
  strip_tac >>
  `?env. fmp_base_analyze (fn_insts fn) = SOME env` by
    metis_tac[fmpReclaimPropsTheory.fmp_reclaim_states_has_bases] >>
  `fn_reachable fn bb.bb_label` by metis_tac[all_reachable_def] >>
  gvs[fn_reachable_def] >>
  qpat_x_assum `fn_entry_label fn = SOME entry` mp_tac >>
  simp[venomInstTheory.fn_entry_label_def, AllCaseEqs()] >> strip_tac >>
  rename1 `entry_block fn = SOME ebb` >>
  `?start. df_at NONE states ebb.bb_label 0 = SOME start /\
           ~MEM out start.frs_stack` by metis_tac[MEM] >>
  `?s. df_at NONE states bb.bb_label 0 = SOME s /\ ~MEM out s.frs_stack` by
    (drule fresh_first_hit >>
     disch_then (qspec_then
       `\l. ?s. df_at NONE states l 0 = SOME s /\ ~MEM out s.frs_stack`
       (irule o BETA_RULE)) >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `MEM out (EL k bb.bb_instructions).inst_outputs` by simp[] >>
     drule_all fresh_edge_step >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `!j. j < k ==> ~MEM out (EL j bb.bb_instructions).inst_outputs` by
    (rpt strip_tac >>
     `j < LENGTH bb.bb_instructions` by simp[] >>
     `MEM out (EL k bb.bb_instructions).inst_outputs` by simp[] >>
     `j = k` by metis_tac[ssa_form_position] >> gvs[]) >>
  `k <= LENGTH bb.bb_instructions` by simp[] >>
  drule_all fresh_block_prefix >> simp[]
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
  strip_tac >> irule fresh_out_conditional >>
  qexistsl [`bb`, `fn`, `infos`, `k`, `states`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac
  >- metis_tac[reclaim_fresh_edge]
  >- metis_tac[reclaim_fresh_index_some]
  >> metis_tac[reclaim_fresh_entry]
QED
