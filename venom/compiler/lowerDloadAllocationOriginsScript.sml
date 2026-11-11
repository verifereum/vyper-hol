(* Allocation identities of reachable source frames. *)
Theory lowerDloadAllocationOrigins
Ancestors
  lowerDloadSafetyAllocation lowerDloadSafetyRelation ptrDiscipline irSupply
  venomMemProps venomExecProofs contextCodegenRel
  venomExecSemantics venomState venomInst finite_map list pred_set

Theorem ld_step_alloca_domain:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t ==>
  FDOM t.vs_allocas SUBSET FDOM s.vs_allocas UNION {inst.inst_id}
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, Once step_inst_base_def,
        exec_alloca_def, AllCaseEqs(), update_var_def] >>
      simp[SUBSET_DEF]) >>
  `t.vs_allocas = s.vs_allocas` by
    (irule step_inst_base_preserves_allocas >>
     qexists_tac `inst` >> simp[] >>
     gvs[step_inst_non_invoke]) >>
  simp[SUBSET_DEF]
QED

Theorem ld_enters_block_allocas:
  enters_block fn s t ==> t.vs_allocas = s.vs_allocas
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem ld_foldl_outputs_allocas[local]:
  !xs s. (FOLDL (\s (out,v). update_var out v s) s xs).vs_allocas =
    s.vs_allocas
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[update_var_def]
QED

Theorem ld_bind_outputs_allocas:
  bind_outputs outs vals s = SOME t ==> t.vs_allocas = s.vs_allocas
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[ld_foldl_outputs_allocas]
QED

Theorem ld_active_inst_id[local]:
  active_inst fn inst s ==> MEM inst.inst_id (fn_ir_inst_ids fn)
Proof
  simp[active_inst_def] >> strip_tac >>
  simp[fn_ir_inst_ids_def, block_ir_inst_ids_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `MAP (\i. i.inst_id) bb.bb_instructions` >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  simp[MEM_MAP] >> qexists_tac `inst` >> simp[] >>
  rewrite_tac[MEM_EL] >> qexists_tac `s.vs_inst_idx` >> simp[]
QED

Theorem ld_frame_allocation_origins:
  !vs0 C stk PG G tn fn inst s.
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  vs0.vs_allocas = FEMPTY ==>
  FDOM s.vs_allocas SUBSET set (fn_ir_inst_ids fn) /\
  EVERY (\cf. FDOM cf.cf_state.vs_allocas SUBSET
    set (fn_ir_inst_ids cf.cf_fn)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule ld_enters_block_allocas >> simp[])
  >- (rpt strip_tac >> drule_all ld_step_alloca_domain >>
      `MEM inst.inst_id (fn_ir_inst_ids fn)` by
        (irule ld_active_inst_id >> qexists_tac `s` >> simp[]) >>
      gvs[] >> ASM_SET_TAC[])
  >- (rpt strip_tac >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      drule_all ld_step_alloca_domain >>
      drule ld_enters_block_allocas >>
      `MEM inst.inst_id (fn_ir_inst_ids fn)` by
        (irule ld_active_inst_id >> qexists_tac `s` >> simp[]) >>
      gvs[] >> ASM_SET_TAC[])
  >- (rpt strip_tac >> drule ld_enters_block_allocas >>
      gvs[setup_callee_def, AllCaseEqs()])
  >> rpt strip_tac >> drule ld_bind_outputs_allocas >>
  gvs[merge_callee_state_def]
QED

Theorem ld_sync_private_source_absent:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  vs0.vs_allocas = FEMPTY /\ ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ld_private f d ai ==> FLOOKUP s.vs_allocas ai = NONE
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_frame_allocation_origins >> simp[] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas ai` >> simp[] >>
  `MEM ai (fn_ir_inst_ids f.lf_fn)` by
    (gvs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  drule_all ld_original_not_private >>
  disch_then (qspec_then `d` mp_tac) >> simp[]
QED

val _ = app (fn th => if null (hyp th) then () else
  raise Fail "allocation origin theorem has hypotheses")
  [ld_step_alloca_domain, ld_enters_block_allocas, ld_bind_outputs_allocas,
   ld_frame_allocation_origins, ld_sync_private_source_absent];
