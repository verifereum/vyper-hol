(* Allocation syntax ownership at reachable current and suspended frames. *)
Theory frameAllocationHistory
Ancestors
  allocationLookup o1LowerDloadOccurrence allocaFrontierBound contextCodegenRel venomExecProofs
  venomExecSemantics venomState venomInstProofs1 finite_map list

Theorem occ_frame_reachable_allocation_syntax:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    vs.vs_allocas = FEMPTY ==>
    (!id off sz. FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
      ?ai w. MEM ai (fn_insts fn) /\ ai.inst_id = id /\
        ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w) /\
    (!f. MEM f stk ==> !id off sz.
      FLOOKUP f.cf_state.vs_allocas id = SOME (off,sz) ==>
      ?ai w. MEM ai (fn_insts f.cf_fn) /\ ai.inst_id = id /\
        ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w)
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> rpt strip_tac >> gvs[]
  >- (gvs[enters_block_def] >>
      drule eval_phis_preserves_alloca_fields >> simp[] >>
      strip_tac >> gvs[])
  >- (drule_all step_inst_alloca_lookup_origin >> strip_tac
      >- metis_tac[] >>
      metis_tac[active_inst_mem_fn_insts])
  >- (`inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
      gvs[enters_block_def] >>
      drule eval_phis_preserves_alloca_fields >> strip_tac >> gvs[] >>
      drule_all step_inst_alloca_lookup_origin >> strip_tac
      >- metis_tac[] >> metis_tac[active_inst_mem_fn_insts])
  >- (gvs[enters_block_def] >>
      drule eval_phis_preserves_alloca_fields >> strip_tac >>
      gvs[setup_callee_def, AllCaseEqs()])
  >> mp_tac (Q.ISPEC `\s:venom_state. s.vs_allocas` bind_outputs_preserves)
  >> simp[update_var_def] >> disch_then drule >>
  simp[merge_callee_state_def] >> strip_tac >> metis_tac[]
QED

Theorem occ_frame_reachable_current_allocation_syntax:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
  ?ai w. MEM ai (fn_insts fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w
Proof
  metis_tac[occ_frame_reachable_allocation_syntax]
QED

Theorem occ_frame_reachable_saved_allocation_syntax:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ MEM f stk /\
  FLOOKUP f.cf_state.vs_allocas id = SOME (off,sz) ==>
  ?ai w. MEM ai (fn_insts f.cf_fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w
Proof
  metis_tac[occ_frame_reachable_allocation_syntax]
QED

Theorem frame_reachable_current_allocation_syntax:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
  ?ai w. MEM ai (fn_insts fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w
Proof
  strip_tac >> drule frame_reachable_occurrence_lift >> strip_tac >>
  drule_all occ_frame_reachable_current_allocation_syntax >> simp[]
QED

Theorem frame_reachable_saved_allocation_syntax:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ MEM f stk /\
  FLOOKUP f.cf_state.vs_allocas id = SOME (off,sz) ==>
  ?ai w. MEM ai (fn_insts f.cf_fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w
Proof
  strip_tac >> drule frame_reachable_occurrence_lift >> strip_tac >>
  drule_all occ_frame_reachable_saved_allocation_syntax >> simp[]
QED
