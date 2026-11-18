(* Exact owned registration endpoints initialize both body relations.
   Execution is deliberately not reconstructed here: all resources refer to
   the same caller-chosen endpoint, before any horizon is introduced. *)
Theory defaultRegistrationState
Ancestors entryStateRel calldataRegistrationLocals bodyPtrDefs
  exprLoweringProps abiAllocationHistory externalCallSelected memoryValueEncoding
  valueEncodingProps venomMemProofs loweringPosts loweringStateRelDefs
  exprSimMemoryTransport ptrSafeRun ptrDiscipline list valueEncodingProofs
  vyperState vyperInterpreter

Theorem default_registration_clean_ghost:
  local_ptrs_rel fn ce es.scopes s /\
  (!name entry. lookup_scopes name es.scopes = SOME entry ==>
     value_has_type entry.type entry.value) /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz) /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
  ce.ce_return_pc = NONE ==>
  ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn s
Proof
  strip_tac >>
  simp[ghost_inv_at_def, return_buf_ptr_def, stor_taint_ok_at_def,
       allocas_from_def] >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    metis_tac[memory_value_rel_val_in_memory] >>
  irule val_in_memory_relocate_footprint >> conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `w2n w`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint entry.type entry.value` >>
  `mem_bytes_at (w2n w+j) 1 s.vs_memory =
   mem_bytes_at (w2n w+j) 1 mem` by
    gvs[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

(* The owner list and all the resource/frame facts below concern s,G,tn.
   No existential execution endpoint is chosen under the horizon quantifiers. *)
Theorem default_registration_endpoint_state:
  initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
  send_call_value mut cx
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  MAP (\(x,dst,p,id). x) outputs = tx.args /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv).
    evaluate_type (type_env tops) ty = SOME tv) args tys /\
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    val_wf tv x /\ val_in_memory tv x p s.vs_memory /\
    eval_operand dst s = SOME (n2w p) /\ p < dimword (:256) /\
    FLOOKUP s.vs_allocas id = SOME (p,type_memory_size tv) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id))
      (ZIP (args,MAP SND tys)) outputs /\
  (!name entry p sz.
    FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz) /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
  alloca_inv s /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved ce st /\
  alloca_room ctx fn s /\ fmp_room ctx fn s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_history fn s /\
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops /\
  s.vs_accounts = vs.vs_accounts /\ s.vs_transient = vs.vs_transient /\
  s.vs_logs = vs.vs_logs /\ s.vs_call_ctx = vs.vs_call_ctx /\
  s.vs_tx_ctx = vs.vs_tx_ctx /\ s.vs_block_ctx = vs.vs_block_ctx /\
  s.vs_outcomes = vs.vs_outcomes /\ s.vs_requests = vs.vs_requests /\
  s.vs_pending_deletions = vs.vs_pending_deletions /\
  s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section ==>
  alloca_history fn s /\ return_buf_frame NONE ce st s /\
  !st0 H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn s /\
    stmt_state_rel H ctx fn ce cx es s
Proof
  strip_tac >>
  `local_ptrs_rel fn ce [env] s` by
    (irule decoded_arguments_local_ptrs >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`args`,`outputs`,`type_env tops`,`tys`] >> simp[]) >>
  `es.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  simp[return_buf_frame_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- suspend "ghost" >>
  `state_rel H fn ce cx es s` by
    (irule body_entry_state_rel_runtime >> simp[] >>
     metis_tac[]) >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       immutable_base_zero_def] >>
  rpt strip_tac >> drule_all abi_alloca_history_function_size >> simp[]
QED

Resume default_registration_endpoint_state[ghost]:
  irule default_registration_clean_ghost >> simp[] >> conj_tac
  >- (rpt gen_tac >> simp[lookup_scopes_def, AllCaseEqs()] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> simp[lookup_scopes_def, AllCaseEqs()] >> strip_tac >>
      drule_all decoded_arguments_scope_lookup >> strip_tac >>
      drule_then (qspec_then `i` mp_tac) entryDecodePropsTheory.bind_arguments_word_arg >>
      simp[] >> strip_tac >> gvs[]) >>
  metis_tac[]
QED

Finalise default_registration_endpoint_state
