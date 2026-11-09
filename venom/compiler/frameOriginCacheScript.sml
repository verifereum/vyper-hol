Theory frameOriginCache
Ancestors
  frameOriginUpdates ptrDisciplineEmptyTaint concretizePtrAllocationOrigins
  venomMemProps venomExecSemantics venomState finite_map list

Definition local_cache_ok_def:
  local_cache_ok om s <=>
    !v aid site. FLOOKUP om v = SOME (OriginLocal aid,site) ==>
      FLOOKUP s.vs_allocas aid = SOME site
End

Theorem step_inst_cache_preserved:
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode <> INVOKE /\
  FLOOKUP s.vs_allocas aid = SOME site ==>
  FLOOKUP s'.vs_allocas aid = SOME site
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      metis_tac[exec_alloca_lookup_preserved]) >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >> simp[]
QED

Theorem local_cache_ok_restrict:
  local_cache_ok om s ==> local_cache_ok (DRESTRICT om keys) s
Proof
  simp[local_cache_ok_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem local_cache_ok_transport:
  local_cache_ok om s /\
  (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP s'.vs_allocas aid = SOME site) ==>
  local_cache_ok om s'
Proof
  simp[local_cache_ok_def] >> metis_tac[]
QED

Theorem local_cache_ok_out:
  local_cache_ok om s /\
  origin_out PG om inst s = SOME (OriginLocal aid,site) ==>
  FLOOKUP s.vs_allocas aid = SOME site
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- gvs[origin_out_alloca] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- gvs[origin_out_dalloca] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- gvs[origin_out_param] >>
  drule_all origin_out_inherited >> strip_tac >>
  gvs[origin_op_some, local_cache_ok_def] >> metis_tac[]
QED

Theorem local_cache_ok_step:
  local_cache_ok om s /\ step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE ==>
  local_cache_ok (origin_step PG om inst s') s'
Proof
  strip_tac >>
  `local_cache_ok om s'` by
    (irule local_cache_ok_transport >> qexists_tac `s` >>
     simp[] >> metis_tac[step_inst_cache_preserved]) >>
  simp[local_cache_ok_def] >> rpt strip_tac >>
  drule origin_step_lookup >> strip_tac
  >- (gvs[local_cache_ok_def] >> metis_tac[]) >>
  metis_tac[local_cache_ok_out]
QED

Theorem local_cache_ok_phis:
  local_cache_ok om s ==> local_cache_ok (origin_phis prev om insts) s
Proof
  simp[local_cache_ok_def] >> rpt strip_tac >>
  drule origin_phis_lookup >> strip_tac
  >- metis_tac[] >>
  gvs[origin_phi_some, origin_op_some] >> metis_tac[]
QED

Theorem local_cache_ok_entry:
  local_cache_ok om s /\ enters_block fn s s1 ==>
  local_cache_ok (origin_entry fn s om) s1
Proof
  strip_tac >> drule enters_block_allocas >> strip_tac >>
  `local_cache_ok om s1` by
    (irule local_cache_ok_transport >> qexists_tac `s` >> simp[]) >>
  simp[origin_entry_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[local_cache_ok_phis]
QED

Theorem return_bind_cache:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  (s' with vs_inst_idx := idx).vs_allocas = caller.vs_allocas
Proof
  strip_tac >> drule bind_outputs_allocation_frame >>
  simp[merge_callee_state_allocas]
QED
