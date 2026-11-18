(* The recorded GAS path and its pointer ghost survive outcome replacement. *)
Theory deployOutcomesFreeOrigins
Ancestors
  deployOutcomesFreeSafety deployOutcomesFreeStep deployOutcomesFreeFrames
  loweringBudgetFrameOracleTransport
  fragGasOrigin fragGasOriginPtr fragGasPathPtr fragExec fragFuel gasCount gasEvents
  ptrSafeRun ptrDiscipline ctxLookupAgreeHelpers venomExecProofs
  venomExecSemantics venomState venomInst dftCommutation list

Theorem outcomes_exit_result[simp]:
  exit_result (map_result_state (\t. t with vs_outcomes := os) r) =
    exit_result r
Proof
  Cases_on `r` >> simp[exit_result_def, map_result_state_def]
QED

Theorem outcomes_origin_edge:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_origin_edge memory explicit ctx fn s marks r ==>
  gas_origin_edge memory explicit ctx fn (s with vs_outcomes := os) marks
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  rewrite_tac[gas_origin_edge_def] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  `~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
    fs[EVERY_MEM] >>
  `step_inst fuel ctx inst (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) middle` by
    simp[outcomes_step_inst] >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `memory ==> revert_forward_at bb s.vs_inst_idx \/
    mem_safe_step fuel ctx inst (s with vs_outcomes := os)` by
    simp[outcomes_mem_safe_step] >>
  gvs[]
  >- (qexists_tac `fuel` >> simp[gas_events_step_outcomes_update, map_result_state_def])
  >- (qexists_tac `fuel` >> simp[gas_events_step_outcomes_update, map_result_state_def])
  >- (qexists_tac `fuel` >>
      simp[gas_events_step_outcomes_update, outcomes_eval_phis,
           map_result_state_def])
  >- (qexists_tac `fuel` >>
      simp[gas_events_step_outcomes_update, jump_to_def] >> metis_tac[]) >>
  qexists_tac `fuel` >> simp[gas_events_step_outcomes_update]
QED

Theorem outcomes_origin_path:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s marks r. gas_origin_path memory explicit ctx fn s marks r ==>
  gas_origin_path memory explicit ctx fn (s with vs_outcomes := os) marks
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  strip_tac >>
  qsuff_tac `!memory' explicit' ctx' fn' s marks r.
    gas_origin_path memory' explicit' ctx' fn' s marks r ==>
    memory' = memory /\ explicit' = explicit /\ ctx' = ctx /\ fn' = fn ==>
    gas_origin_path memory explicit ctx fn (s with vs_outcomes := os) marks
      (map_result_state (\t. t with vs_outcomes := os) r)`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
  >- (simp[map_result_state_def] >> irule (cj 1 gas_origin_path_rules) >> simp[])
  >- (drule_all (SRULE [] outcomes_origin_edge) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_path_rules]) >>
  drule_all (SRULE [] outcomes_origin_edge) >> strip_tac >>
  metis_tac[cj 3 gas_origin_path_rules, outcomes_exit_result]
QED

Theorem outcomes_pointer_edge:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  gas_path_ptr_edge D lo ctx fn PG G tn (s with vs_outcomes := os) n G' tn'
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  rewrite_tac[gas_path_ptr_edge_def] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  `~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
    fs[EVERY_MEM] >>
  `step_inst fuel ctx inst (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) middle` by
    simp[outcomes_step_inst] >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `ptr_safe_step D lo fuel ctx fn PG G tn inst (s with vs_outcomes := os)` by
    simp[cj 1 outcomes_ptr_safe_defs] >>
  `gas_count_step fuel ctx inst (s with vs_outcomes := os) =
    gas_count_step fuel ctx inst s` by
    metis_tac[cj 1 gas_events_length, gas_events_step_outcomes_update] >>
  gvs[]
  >- (qexists_tac `fuel` >> simp[outcomes_ghost_step, map_result_state_def])
  >- (qexists_tac `fuel` >> simp[map_result_state_def])
  >- (qexists_tac `fuel` >>
      simp[outcomes_eval_phis, map_result_state_def,
           entry_prov_outcomes_update, entry_taint_outcomes_update])
  >- (qexists_tac `fuel` >> simp[jump_to_def] >> metis_tac[]) >>
  qexists_tac `fuel` >> simp[]
QED

Theorem outcomes_origin_pointer_edge:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s with vs_outcomes := os,G,tn) marks
    (map_result_state (\t. t with vs_outcomes := os) r,G',tn')
Proof
  simp[gas_origin_ptr_edge_def] >> strip_tac >>
  conj_tac >- metis_tac[SRULE [] outcomes_origin_edge] >>
  metis_tac[SRULE [] outcomes_pointer_edge]
QED

Theorem outcomes_origin_pointer_path:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s G tn marks r G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s with vs_outcomes := os,G,tn) marks
      (map_result_state (\t. t with vs_outcomes := os) r,G',tn')
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !s G tn r G' tn'.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\ out = (r,G',tn') ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s with vs_outcomes := os,G,tn) marks
        (map_result_state (\t. t with vs_outcomes := os) r,G',tn')`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (simp[map_result_state_def] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (drule_all (SRULE [] outcomes_origin_pointer_edge) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_ptr_path_rules]) >>
  drule_all (SRULE [] outcomes_origin_pointer_edge) >> strip_tac >>
  metis_tac[cj 3 gas_origin_ptr_path_rules, outcomes_exit_result]
QED

Theorem outcomes_origin_pointer_focus:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s G tn marks leaf leaf_pg leaf_g leaf_tn finish.
    gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
    gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
      (s with vs_outcomes := os,G,tn) marks
      (leaf,leaf_pg,leaf_g,leaf_tn,finish with vs_outcomes := os)
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_focus cx st marks out ==>
    !s G tn leaf leaf_pg leaf_g leaf_tn finish.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\
      out = (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
      gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
        (s with vs_outcomes := os,G,tn) marks
        (leaf,leaf_pg,leaf_g,leaf_tn,finish with vs_outcomes := os)`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all (SRULE [] outcomes_origin_pointer_path) >>
      simp[map_result_state_def] >> metis_tac[cj 1 gas_origin_ptr_focus_rules])
  >- (drule_all (SRULE [] outcomes_origin_pointer_path) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_ptr_focus_rules]) >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  qpat_x_assum `EVERY _ (fn_insts fn)` (mp_tac o SRULE [EVERY_MEM]) >>
  disch_then (qspec_then `inst` mp_tac) >> simp[]
QED
