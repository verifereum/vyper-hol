(* Raw accepted calldata: reconstruct the endpoint relations from the
   registration fold's concrete resources, without canonical call encoding. *)
Theory dispatchedSelectedRelations
Ancestors
  entryPtrSeamRegister

Theorem dispatched_selected_actual_endpoint_relations:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  ALL_DISTINCT (MAP FST args) /\
  unit_alloca_budget unit.cu_context < dimword (:256) /\
  tx.function_name <> "__default__" /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,mincd,pay,F,key,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  ~ctx_has_dalloca unit.cu_context /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
  local_ptrs_rel efn cenv [env] s0 /\
  (!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
  cenv = cenv0 with ce_vars := cenv.ce_vars /\
  alloca_inv s0 /\ alloca_frontier_inv unit.cu_context efn site s0 /\
  tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {} /\
  s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
  s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
  s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
  s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
  s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_data_section = s1.vs_data_section /\
  s0.vs_code = s1.vs_code /\
  (!inst w b n. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
  stmt_state_rel H unit.cu_context efn cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
  ghost_inv H NONE cenv (initial_evaluation_context am.sources am.layouts tx NONE)
    es0 G0 tn0 s0
Proof
  strip_tac >>
  drule_all_then MATCH_ACCEPT_TAC registration_actual_endpoint_relations_from_prefix
QED
