(* The source oracle transition paired with its counted, checked CALL edge.
   The full boundary discharges local-memory and ghost frames using the
   predecessor-relative separation exported by output allocation. *)
Theory rawCallOracleProofPtr
Ancestors
  oracleCallStepPtr extCallOracleStep rawCallAllocationProofPtr
  appendStorageGhostPtr decoderGhostFramePtr ptrDiscipline
  rawCallMemoryFramePtr exprLoweringProps
  venomExecSemantics venomState venomCallOracleDefs bodyPtrDefs

Theorem oracle_call_checked_step:
  state_rel func cenv cx es s /\ inst.inst_outputs = [out] /\
  ((~stat /\ inst.inst_opcode = CALL /\
      inst.inst_operands = [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) \/
   (stat /\ inst.inst_opcode = STATICCALL /\
      inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op])) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  access_ok 0 G func inst s /\ taint_ok func tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?s'.
    exec_ext_call inst s gas aw (if stat then 0w else vw) ao az ro rz stat =
      OK (update_var out (if outcome.co_success then 1w else 0w) s') /\
    s' = s with <| vs_outcomes := s'.vs_outcomes; vs_requests := s'.vs_requests;
      vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient;
      vs_logs := s'.vs_logs; vs_pending_deletions := s'.vs_pending_deletions;
      vs_returndata := s'.vs_returndata; vs_memory := s'.vs_memory |> /\
    s'.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    s'.vs_returndata = outcome.co_returnData /\
    (local_ptrs_rel func cenv es.scopes s' /\
      immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s' ==>
      state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) s') /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0
      (step_prov PG G inst (update_var out (if outcome.co_success then 1w else 0w) s'))
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (OK ((update_var out (if outcome.co_success then 1w else 0w) s')
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stor_taint_ok cx
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (update_var out (if outcome.co_success then 1w else 0w) s') /\
    op_taint
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (Var out) = {} /\
    op_prov
      (step_prov PG G inst (update_var out (if outcome.co_success then 1w else 0w) s'))
      (Var out) = NONE
Proof
  strip_tac >> (
  `~s.vs_call_ctx.cc_static` by fs[compileEnvTheory.state_rel_def] >>
  drule_all exec_ext_call_oracle_step >>
  disch_then (strip_assume_tac o Q.ISPECL [`gas:bytes32`, `ro:bytes32`, `rz:bytes32`]) >>
  qexists_tac `s'` >> gvs[] >>
  `step_inst_base inst s =
    OK (update_var out (if outcome.co_success then 1w else 0w) s')` by
    (gvs[step_inst_base_def]) >>
  conj_tac
  >- (irule call_gas_path_ptr_edge >> simp[] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[exec_ext_call_stor_taint_ok] >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
    step_prov_def, set_prov_def, out_prov_def, op_prov_def,
    finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE])
QED

Theorem oracle_effect_stmt_frame[local]:
  stmt_state_rel ctx func cenv cx es s /\ state_rel func cenv cx ee t /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp ==>
  stmt_state_rel ctx func cenv cx ee t
Proof
  strip_tac >> irule stmt_state_rel_allocas_frame >> simp[] >>
  conj_tac
  >- (fs[stmt_state_rel_def] >> irule immutable_base_zero_frame >>
      qexists_tac `s` >> simp[lookup_var_def]) >>
  conj_tac
  >- (fs[stmt_state_rel_def] >> irule immutable_alloca_sep_fields >>
      simp[compileEnvTheory.local_region_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem oracle_call_checked_full:
  stmt_state_rel ctx func cenv cx es s /\ inst.inst_outputs = [out] /\
  ((~stat /\ inst.inst_opcode = CALL /\
      inst.inst_operands = [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) \/
   (stat /\ inst.inst_opcode = STATICCALL /\
      inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op])) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  access_ok 0 G func inst s /\ taint_ok func tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~cenv.ce_is_ctor /\ not_local_ptr cenv es.scopes out /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) (w2n rz) a len) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) (w2n rz) a len) ==>
  ?s' t H un.
    exec_ext_call inst s gas aw (if stat then 0w else vw) ao az ro rz stat = OK t /\
    t = update_var out (if outcome.co_success then 1w else 0w) s' /\
    s'.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    s'.vs_returndata = outcome.co_returnData /\
    H = step_prov PG G inst t /\ un = step_taint inst s t tn /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0 H un
      (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1))
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_inv d cenv cx (SND (adopt_call_outcome rq outcome es1)) H un
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept cenv es sa G tn s H un /\
    wb_frame cenv es sa s (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    op_taint un (Var out) = {} /\ op_prov H (Var out) = NONE
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `state_rel func cenv cx es s` by fs[stmt_state_rel_def] >>
  drule_all oracle_call_checked_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `s'.vs_vars = s.vs_vars /\ s'.vs_labels = s.vs_labels /\
   s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
   s'.vs_fmp = s.vs_fmp /\ s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `s' = _` mp_tac >> simp[venom_state_component_equality]) >>
  `local_ptrs_rel func cenv es.scopes s /\
   immutables_rel cenv cx.txn.target cenv.ce_module F es s /\
   not_scope_ptr cenv es.scopes out` by
    (qpat_x_assum `state_rel _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[compileEnvTheory.state_rel_def] >> strip_tac >>
     gvs[compileEnvTheory.not_local_ptr_def, compileEnvTheory.not_scope_ptr_def]) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) (LENGTH (TAKE (w2n rz) outcome.co_returnData)) a len` by
    (`LENGTH (TAKE (w2n rz) outcome.co_returnData) <= w2n rz` by
       (simp[listTheory.LENGTH_TAKE_EQ] >> rw[] >> decide_tac) >>
     rpt strip_tac >> first_x_assum drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all oracle_write_semantic_frame >>
  disch_then (qspecl_then [`if outcome.co_success then 1w else 0w`,
    `SUC s.vs_inst_idx`] strip_assume_tac) >>
  `state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) s'` by
    (first_x_assum irule >> simp[]) >>
  drule_all oracle_take_adoption_locals >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) s'` by
    (irule oracle_effect_stmt_frame >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1))
    ((update_var out (if outcome.co_success then 1w else 0w) s')
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[]) >>
  `source_memory_write_ranges inst s = [(w2n ro,w2n rz)]` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     simp[codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def]) >>
  qexistsl_tac [`s'`, `update_var out (if outcome.co_success then 1w else 0w) s'`,
    `step_prov PG G inst (update_var out (if outcome.co_success then 1w else 0w) s')`,
    `step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn`] >>
  simp[Excl "ghost_inv_inst_idx"] >> irule oracle_call_ghost_frame >>
  simp[update_var_def] >> conj_tac
  >- (first_assum (irule_at (Pat `source_memory_write_ranges _ _ = _`)) >>
      qexistsl_tac [`if outcome.co_success then 1w else 0w`, `out`, `PG`] >>
      simp[] >> metis_tac[]) >> metis_tac[]
QED
