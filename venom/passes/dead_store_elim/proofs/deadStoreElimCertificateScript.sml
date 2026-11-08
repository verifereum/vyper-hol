Theory deadStoreElimCertificate
Ancestors
  decoratedExecution decoratedClearing deadStoreElimExecution deadStoreElimSafety
  deadStoreElimDefs basePtrDefs venomMemDefs venomExecSemantics venomState
  finite_map words deadStoreElimStructure memLocDefs passSimulationDefs
  venomInst list passSharedDefs deadStoreElimStepSimulation deadStoreElimLocal
  deadStoreElimPending deadStoreElimContinuation deadStoreElimJumpSteps
  venomInstProps venomExecProofs venomExecProps stateEquiv deadStoreElimUnsupported deadStoreElimEquiv
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

(* Concrete field-dependent decoration: caller safe_inv is used only in
   the initial construction, never asserted on transformed states. *)
Definition dse_occ_safe_def:
  dse_occ_safe fn inst s <=>
    ~s.vs_call_ctx.cc_static /\
    alloca_inv s /\
    (!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
                   base + sz < dimword (:256)) /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s
End

Definition dse_run_certificate_def:
  dse_run_certificate fn fuel ctx s r <=>
    decorated_run (dse_occ_safe fn) fuel ctx fn s r
End

Theorem eval_phis_preserves_call_ctx[local]:
  eval_phis s insts = OK s1 ==> s1.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o AP_TERM ``\st:venom_state. st.vs_call_ctx``) >> simp[]
QED

Theorem step_inst_ok_preserves_call_ctx[local]:
  step_inst fuel ctx inst s = OK s1 ==> s1.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (`inst.inst_opcode IN {JMP; JNZ; DJMP}` by
        (drule_all step_inst_ok_terminator_jump >> simp[]) >>
      fs[] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
                  AllCaseEqs(), jump_to_def]) >>
  metis_tac[step_preserves_call_ctx]
QED

Theorem dse_certificate_initial:
  s.vs_inst_idx = 0 /\ ~s.vs_call_ctx.cc_static /\ safe_inv s /\
  (!bb s0 s1.
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    s0.vs_inst_idx = 0 /\ safe_inv s0 /\
    eval_phis s0 bb.bb_instructions = OK s1 ==>
    safe_inv (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!bb inst fuel' s0 s1.
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s0.vs_inst_idx = SOME inst /\ safe_inv s0 /\
    step_inst fuel' ctx inst s0 = OK s1 ==>
    safe_inv (if is_terminator inst.inst_opcode then s1
              else s1 with vs_inst_idx := SUC s0.vs_inst_idx)) /\
  (!s0. safe_inv s0 ==>
    alloca_inv s0 /\
    (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                   base + sz < dimword (:256)) /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
    (!bb inst. lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s0.vs_inst_idx = SOME inst ==>
       bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s0)) /\
  run_blocks fuel ctx fn s = r /\ ~(?e. r = Error e) ==>
  dse_run_certificate fn fuel ctx s r
Proof
  strip_tac >> gvs[dse_run_certificate_def] >>
  irule decorated_run_invariant >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `\s0. ~s0.vs_call_ctx.cc_static /\ safe_inv s0` >>
  simp[dse_occ_safe_def] >> rpt conj_tac
  >- (rpt strip_tac
      >- (drule step_inst_ok_preserves_call_ctx >> strip_tac >>
          Cases_on `is_terminator inst.inst_opcode` >> gvs[])
      >> first_x_assum irule >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >> res_tac)
  >> rpt strip_tac
  >- (drule eval_phis_preserves_call_ctx >> strip_tac >> gvs[])
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* NOP replacement introduces no new static access footprint. *)
Theorem dse_inst_mem_ops:
  (mem_write_ops (dse_inst ids sp inst) = SOME ops \/
   mem_read_ops (dse_inst ids sp inst) = SOME ops) ==>
  (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops)
Proof
  simp[dse_inst_def] >> IF_CASES_TAC >>
  simp[mk_nop_inst_def, mem_write_ops_def, mem_read_ops_def]
QED

Theorem bp_ptrs_bounded_dse:
  bp_ptrs_bounded bp fn s ==>
  bp_ptrs_bounded bp (dse_single_pass ids sp fn) s
Proof
  simp[bp_ptrs_bounded_def, dse_single_pass_def,
       function_map_transform_def, block_map_transform_def, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  metis_tac[dse_inst_mem_ops]
QED

Theorem dse_inst_accesses:
  bp_accesses_in_own_alloca bp inst s ==>
  bp_accesses_in_own_alloca bp (dse_inst ids sp inst) s
Proof
  simp[dse_inst_def] >> IF_CASES_TAC >> simp[] >>
  simp[bp_accesses_in_own_alloca_def, bp_access_ops_def,
       mk_nop_inst_def, mem_write_ops_def, mem_read_ops_def] >>
  rpt strip_tac >> Cases_on `sp'` >> gvs[]
QED

Theorem dse_occ_safe_agrees:
  dse_safety_agrees s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  dse_occ_safe fn inst s ==>
  dse_occ_safe fn inst t
Proof
  strip_tac >> gvs[dse_occ_safe_def] >>
  metis_tac[dse_safety_agrees_alloca_inv,
    dse_safety_agrees_alloca_bounds, dse_safety_agrees_ptr_sound,
    dse_safety_agrees_ptrs_bounded, dse_safety_agrees_accesses]
QED

Theorem dse_occ_safe_single_pass:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  dse_safety_agrees s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  dse_occ_safe fn inst s ==>
  dse_occ_safe (dse_single_pass ids sp fn) (dse_inst ids sp inst) t
Proof
  strip_tac >>
  `dse_occ_safe fn inst t` by (irule dse_occ_safe_agrees >> metis_tac[]) >>
  `bp_analyze (cfg_analyze fn) (dse_single_pass ids sp fn) =
   bp_analyze (cfg_analyze fn) fn` by
    (irule bp_analyze_dse_sound >> metis_tac[]) >>
  gvs[dse_occ_safe_def, cfg_analyze_dse_single_pass] >>
  rpt conj_tac
  >- metis_tac[]
  >- (irule bp_ptrs_bounded_dse >> simp[]) >>
  irule dse_inst_accesses >> simp[]
QED

(* A successful block carries pending regions to any subsequently fetched
   block. Terminal results need only the public state relation. *)
Definition dse_block_post_def:
  dse_block_post sp fn u v <=>
    ?P. dse_local_agrees sp P u v /\
      (!bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
        dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
          sp fn bb 0 P u)
End

Theorem dse_decorated_block:
  !Q fuel ctx bb s r. decorated_block Q fuel ctx bb s r ==>
  !fn ids sp P t.
    sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
    wf_function fn /\
    all_dead_stores ids (cfg_analyze fn) FEMPTY
      (bp_analyze (cfg_analyze fn) fn) sp fn /\
    (!inst u. Q inst u ==> dse_occ_safe fn inst u) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    dse_local_agrees sp P s t /\
    dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
      sp fn bb s.vs_inst_idx P s ==>
    ?r'. decorated_block (dse_occ_safe (dse_single_pass ids sp fn)) fuel ctx
        (block_map_transform (dse_inst ids sp) bb) t r' /\
      lift_result (dse_block_post sp fn) (dse_equiv sp) (dse_equiv sp) r r'
Proof
  ho_match_mp_tac decorated_block_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `dse_occ_safe fn inst s` by metis_tac[] >>
  `dse_safety_agrees s t /\ s.vs_inst_idx = t.vs_inst_idx /\
   s.vs_call_ctx = t.vs_call_ctx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def,
       dse_pending_space_def, dse_equiv_def] >>
  `dse_occ_safe (dse_single_pass ids sp fn) (dse_inst ids sp inst) t` by
    (irule dse_occ_safe_single_pass >> metis_tac[]) >>
  `get_instruction (block_map_transform (dse_inst ids sp) bb)
     t.vs_inst_idx = SOME (dse_inst ids sp inst)` by
    (simp[get_instruction_dse] >> qexists_tac `inst` >> metis_tac[])
  >- suspend "continue"
  >- suspend "jump"
  >- suspend "halt"
  >- suspend "abort" >>
  suspend "intret"
QED

Resume dse_decorated_block[continue]:
  `alloca_inv s /\ bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
   bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s` by
    fs[dse_occ_safe_def] >>
  drule_all dse_nonterminator_step >> strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
     sp fn bb (SUC s.vs_inst_idx) P1
       (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[dse_pending_at_inst_idx] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  qpat_x_assum `!fn ids sp P t. _`
    (drule_at (Pat `dse_local_agrees _ _ _ _`)) >>
  simp_tac pure_ss [venom_state_accfupds, combinTheory.K_THM] >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `r'` >> simp[] >>
  irule (cj 1 decorated_block_rules) >>
  qexistsl_tac [`dse_inst ids sp inst`, `t1`] >>
  simp[dse_inst_is_terminator]
QED

Resume dse_decorated_block[jump]:
  `inst.inst_opcode IN {JMP; JNZ; DJMP}` by
    (drule_all step_inst_ok_terminator_jump >> simp[]) >>
  `dse_inst ids sp inst = inst` by metis_tac[dse_jump_retained] >>
  drule_all dse_jump_local_step >> strip_tac >>
  `dse_equiv sp s1 t1` by
    fs[dse_local_agrees_def, dse_pending_space_def] >>
  `s1.vs_halted = t1.vs_halted` by
    fs[dse_equiv_def] >>
  qexists_tac `if t1.vs_halted then Halt t1 else OK t1` >>
  conj_tac
  >- (irule (cj 2 decorated_block_rules) >>
      qexists_tac `inst` >> simp[] >> metis_tac[]) >>
  Cases_on `t1.vs_halted` >> simp[lift_result_def] >>
  simp[dse_block_post_def] >> qexists_tac `P` >> simp[] >>
  rpt strip_tac >> irule dse_jump_pending_step >>
  metis_tac[lookup_block_MEM]
QED
Resume dse_decorated_block[halt]:
  `~s.vs_call_ctx.cc_static /\ alloca_inv s /\
   bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
   bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s` by
    fs[dse_occ_safe_def] >>
  drule_all dse_halt_step >> strip_tac >>
  qexists_tac `Halt t1` >> simp[lift_result_def] >>
  irule (cj 3 decorated_block_rules) >> metis_tac[]
QED
Resume dse_decorated_block[abort]:
  `~s.vs_call_ctx.cc_static /\ alloca_inv s /\
   bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
   bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s` by
    fs[dse_occ_safe_def] >>
  drule_all dse_abort_step >> strip_tac >>
  qexists_tac `Abort a t1` >> simp[lift_result_def] >>
  irule (cj 4 decorated_block_rules) >> metis_tac[]
QED
Resume dse_decorated_block[intret]:
  `~s.vs_call_ctx.cc_static /\ alloca_inv s /\
   bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
   bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s` by
    fs[dse_occ_safe_def] >>
  drule_all dse_intret_step >> strip_tac >>
  qexists_tac `IntRet vals t1` >> simp[lift_result_def] >>
  irule (cj 5 decorated_block_rules) >> metis_tac[]
QED
Finalise dse_decorated_block

Theorem dse_decorated_run:
  !Q fuel ctx fn s r. decorated_run Q fuel ctx fn s r ==>
  !ids sp P t.
    sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
    wf_function fn /\
    all_dead_stores ids (cfg_analyze fn) FEMPTY
      (bp_analyze (cfg_analyze fn) fn) sp fn /\
    (!inst u. Q inst u ==> dse_occ_safe fn inst u) /\
    s.vs_inst_idx = 0 /\ dse_local_agrees sp P s t /\
    (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
      dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
        sp fn bb 0 P s) ==>
    ?r'. decorated_run (dse_occ_safe (dse_single_pass ids sp fn)) fuel ctx
        (dse_single_pass ids sp fn) t r' /\
      lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp) r r'
Proof
  ho_match_mp_tac decorated_run_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
     sp fn bb 0 P s` by metis_tac[] >>
  drule_all dse_local_agrees_eval_phis >> strip_tac >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `lookup_block s_phi.vs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  `dse_pending_at (cfg_analyze fn) (bp_analyze (cfg_analyze fn) fn)
     sp fn bb (phi_prefix_length bb.bb_instructions) P
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[dse_pending_at_inst_idx] >>
  drule dse_decorated_block >>
  disch_then (drule_at (Pat `dse_local_agrees _ _ _ _`)) >>
  simp_tac pure_ss [venom_state_accfupds, combinTheory.K_THM] >>
  disch_then drule_all >> strip_tac >>
  `lookup_block t.vs_current_bb (dse_single_pass ids sp fn).fn_blocks =
     SOME (block_map_transform (dse_inst ids sp) bb)` by
    (fs[dse_local_agrees_def, dse_operational_agrees_def] >>
     simp[lookup_block_dse_single_pass]) >>
  `eval_phis t (block_map_transform (dse_inst ids sp) bb).bb_instructions = OK t1` by
    simp[block_map_transform_def, eval_phis_dse] >>
  `phi_prefix_length (block_map_transform (dse_inst ids sp) bb).bb_instructions =
     phi_prefix_length bb.bb_instructions` by
    simp[block_map_transform_def, phi_prefix_length_dse]
  >- suspend "continue"
  >- suspend "halted"
  >- suspend "halt"
  >- suspend "abort" >>
  suspend "intret"
QED
Resume dse_decorated_run[continue]:
  rename1 `decorated_block Q fuel ctx bb _ (OK next)` >>
  `next.vs_inst_idx = 0` by
    metis_tac[decorated_block_erase, exec_block_OK_inst_idx_0] >>
  qpat_x_assum `lift_result _ _ _ (OK _) _` mp_tac >>
  Cases_on `r'` >> simp[lift_result_def] >> strip_tac >>
  rename1 `dse_block_post sp fn next target` >>
  qpat_x_assum `dse_block_post _ _ _ _`
    (strip_assume_tac o SRULE [dse_block_post_def]) >>
  `~target.vs_halted` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  qpat_x_assum `!ids sp P t. _` drule_all >> strip_tac >>
  qexists_tac `r'` >> simp[] >>
  irule (cj 1 decorated_run_rules) >>
  qexistsl_tac [`block_map_transform (dse_inst ids sp) bb`, `target`, `t1`] >>
  simp[]
QED
Resume dse_decorated_run[halted]:
  qpat_x_assum `lift_result _ _ _ (OK _) _` mp_tac >>
  Cases_on `r'` >> simp[lift_result_def] >> strip_tac >>
  rename1 `dse_block_post sp fn next target` >>
  `dse_equiv sp next target` by
    fs[dse_block_post_def, dse_local_agrees_def, dse_pending_space_def] >>
  `target.vs_halted` by fs[dse_equiv_def] >>
  qexists_tac `Halt target` >> simp[lift_result_def] >>
  irule (cj 2 decorated_run_rules) >> simp[] >>
  qexistsl_tac [`block_map_transform (dse_inst ids sp) bb`, `t1`] >>
  simp[]
QED
Resume dse_decorated_run[halt]:
  qpat_x_assum `lift_result _ _ _ (Halt _) _` mp_tac >>
  Cases_on `r'` >> simp[lift_result_def] >> strip_tac >>
  rename1 `dse_equiv sp source target` >>
  qexists_tac `Halt target` >> simp[lift_result_def] >>
  irule (cj 3 decorated_run_rules) >>
  qexistsl_tac [`block_map_transform (dse_inst ids sp) bb`, `t1`] >> simp[]
QED
Resume dse_decorated_run[abort]:
  qpat_x_assum `lift_result _ _ _ (Abort _ _) _` mp_tac >>
  Cases_on `r'` >> simp[lift_result_def] >> strip_tac >>
  rename1 `decorated_block _ fuel ctx _ _ (Abort reason target)` >>
  qexists_tac `Abort reason target` >> simp[lift_result_def] >>
  irule (cj 4 decorated_run_rules) >>
  qexistsl_tac [`block_map_transform (dse_inst ids sp) bb`, `t1`] >> simp[]
QED
Resume dse_decorated_run[intret]:
  qpat_x_assum `lift_result _ _ _ (IntRet _ _) _` mp_tac >>
  Cases_on `r'` >> simp[lift_result_def] >> strip_tac >>
  rename1 `decorated_block _ fuel ctx _ _ (IntRet values target)` >>
  qexists_tac `IntRet values target` >> simp[lift_result_def] >>
  irule (cj 5 decorated_run_rules) >>
  qexistsl_tac [`block_map_transform (dse_inst ids sp) bb`, `t1`] >> simp[]
QED
Finalise dse_decorated_run

Theorem dse_single_pass_unsupported:
  sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_single_pass ids sp fn = fn
Proof
  strip_tac >>
  `!inst. dse_inst ids sp inst = inst` by
    (gen_tac >> simp[dse_inst_def] >>
     metis_tac[dse_unsupported_memory_def]) >>
  `dse_inst ids sp = I` by simp[FUN_EQ_THM] >>
  `block_map_transform (dse_inst ids sp) = I` by
    simp[FUN_EQ_THM, block_map_transform_def, MAP_ID] >>
  simp[dse_single_pass_def, function_map_transform_def, MAP_ID]
QED

Theorem dse_certificate_round:
  wf_function fn /\ s.vs_inst_idx = 0 /\
  all_dead_stores ids (cfg_analyze fn) FEMPTY
    (bp_analyze (cfg_analyze fn) fn) sp fn /\
  dse_run_certificate fn fuel ctx s r ==>
  ?r'. dse_run_certificate (dse_single_pass ids sp fn) fuel ctx s r' /\
    lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp) r r'
Proof
  strip_tac >>
  Cases_on `sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient}`
  >- (gvs[dse_run_certificate_def] >>
      drule dse_decorated_run >>
      disch_then (drule_at (Pat `all_dead_stores _ _ _ _ _ _`)) >>
      disch_then (qspec_then `[]` mp_tac) >>
      simp[dse_local_agrees_refl, dse_pending_at_empty]) >>
  `dse_single_pass ids sp fn = fn` by metis_tac[dse_single_pass_unsupported] >>
  qexists_tac `r` >> simp[] >>
  Cases_on `r` >> simp[lift_result_def, dse_equiv_refl]
QED

Theorem bp_ptrs_bounded_clear_nops:
  bp_ptrs_bounded bp fn s ==>
  bp_ptrs_bounded bp (clear_nops_function fn) s
Proof
  simp[bp_ptrs_bounded_def, clear_nops_function_def,
       clear_nops_block_def, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem dse_occ_safe_clear_nops:
  wf_function fn /\ dse_safety_agrees s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  dse_occ_safe fn inst s ==>
  dse_occ_safe (clear_nops_function fn) inst t
Proof
  strip_tac >>
  `dse_occ_safe fn inst t` by (irule dse_occ_safe_agrees >> metis_tac[]) >>
  drule cfg_analyze_clear_nops >> strip_tac >>
  gvs[dse_occ_safe_def, bp_analyze_clear_nops] >>
  conj_tac >- metis_tac[] >>
  irule bp_ptrs_bounded_clear_nops >> simp[]
QED

Theorem dse_certificate_clear_nops:
  wf_function fn /\ dse_run_certificate fn fuel ctx s r ==>
  ?r'. dse_run_certificate (clear_nops_function fn) fuel ctx s r' /\
    !sp. lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp) r r'
Proof
  simp[dse_run_certificate_def] >> strip_tac >>
  drule decorated_run_clear_nops >>
  disch_then (qspec_then `dse_occ_safe (clear_nops_function fn)` mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> irule dse_occ_safe_clear_nops >> simp[] >>
      qexists_tac `u` >> simp[dse_safety_agrees_def, lookup_var_def]) >>
  strip_tac >> goal_assum (drule_at Any) >>
  metis_tac[result_equiv_empty_implies_lift_result_dse_equiv]
QED
