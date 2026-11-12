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
  frameAllocationOwnership ptrDiscipline
  concretizeAnalysisRoots fmpAliasProps fmpAliasDefs livenessTransferProofs
  ctxLookupAgreeHelpers pointerClosure pointerConfinedDefs pred_set
  dftCommutation

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

Finalise fmp_frame_sites_invariant

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
