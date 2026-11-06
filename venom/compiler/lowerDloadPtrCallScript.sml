Theory lowerDloadPtrCall
Ancestors
  lowerDloadPtrRel ptrDiscipline venomExecSemantics venomState
  unitShapeDefs list finite_map words

(* Field audit for the boundary invariant:
   control: vs_prev_bb, vs_current_bb agree; vs_inst_idx is related by
     dload_control_match, not equality;
   allocation: vs_allocas, vs_alloca_next are related by dload_table_stack;
   memory: vs_memory is related by dload_memory_match;
   variables: vs_vars agrees on non-opaque original variables through
     dload_vars_match (RETPC_PARAM-derived opaque values must be excluded);
   arguments/token: vs_params has provenance-indexed word agreement;
     vs_return_pc_token is the final argument, not necessarily equal;
   masked shared store: vs_accounts, vs_transient, vs_immutables;
   equal environment: vs_returndata, vs_halted, vs_call_ctx, vs_tx_ctx,
     vs_block_ctx, vs_logs, vs_outcomes, vs_pending_deletions,
     vs_data_section, vs_labels, vs_code, vs_fmp, vs_call_entry_fmp,
     vs_initial_fmp, vs_prev_hashes.
   history: vs_requests is independent bookkeeping; adoption compares each
     run's successor with its own predecessor, not with the other run.
   Saved callers keep variable/argument/control snapshots only: their
   memory, shared store and external-side-effect fields are stale. *)
Definition dload_equal_environment_def:
  dload_equal_environment s t <=>
    s with <|vs_memory := t.vs_memory;
             vs_transient := t.vs_transient;
             vs_requests := t.vs_requests;
             vs_vars := t.vs_vars;
             vs_inst_idx := t.vs_inst_idx;
             vs_accounts := t.vs_accounts;
             vs_immutables := t.vs_immutables;
             vs_params := t.vs_params;
             vs_return_pc_token := t.vs_return_pc_token;
             vs_allocas := t.vs_allocas;
             vs_alloca_next := t.vs_alloca_next|> = t
End

Theorem dload_equal_environment_refl:
  dload_equal_environment s s
Proof
  simp[dload_equal_environment_def]
QED

Theorem dload_setup_pointer_token:
  dload_pointer_word fs (b,n) (c,n) x y /\
  setup_callee fn (args ++ [x]) s = SOME cs /\
  setup_callee gn (bargs ++ [y]) t = SOME ct ==>
  dload_pointer_word fs (b,n) (c,n)
    cs.vs_return_pc_token ct.vs_return_pc_token
Proof
  strip_tac >> imp_res_tac setup_callee_frame >> gvs[]
QED

(* RETPC_PARAM does not use parameter provenance.  Its result is opaque
   under fn_shape_ok, rather than an ordinary equal nonpointer word. *)
Theorem dload_retpc_provenance:
  inst.inst_opcode = RETPC_PARAM ==>
  out_prov PG G inst s = NONE
Proof
  simp[out_prov_def]
QED

Theorem dload_retpc_read:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] ==>
  step_inst_base inst s = OK (update_var out s.vs_return_pc_token s)
Proof
  simp[step_inst_base_def]
QED

(* An entry frame can have external parameters but PG=[]; absent provenance
   positions mean ordinary words.  Calls instead use MAP op_prov arguments,
   whose length is exactly the number of argument values. *)
Definition dload_param_values_def:
  dload_param_values fs PG PH xs ys <=>
    LENGTH PG <= LENGTH xs /\ LENGTH PH <= LENGTH ys /\
    LIST_REL (\(p,x) (q,y). dload_value_word fs {} p q x y)
      (GENLIST (\k. (if k < LENGTH PG then EL k PG else NONE, EL k xs))
        (LENGTH xs))
      (GENLIST (\k. (if k < LENGTH PH then EL k PH else NONE, EL k ys))
        (LENGTH ys))
End

Theorem dload_param_values_unprovenanced_refl:
  dload_param_values fs [] [] xs xs
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN, EL_GENLIST,
       dload_value_word_def, word_agree_except_def]
QED

Theorem dload_param_values_length:
  dload_param_values fs PG PH xs ys ==> LENGTH xs = LENGTH ys
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN]
QED

Theorem dload_param_values_lookup:
  dload_param_values fs PG PH xs ys /\ k < LENGTH xs ==>
  k < LENGTH ys /\
  dload_value_word fs {}
    (if k < LENGTH PG then EL k PG else NONE)
    (if k < LENGTH PH then EL k PH else NONE) (EL k xs) (EL k ys)
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[EL_GENLIST]
QED

(* Only caller-local metadata is compared here.  Shared mutable fields of
   these snapshots must not be compared after the callee has executed. *)
Definition dload_saved_metadata_def:
  dload_saved_metadata fs V f g <=>
    dload_vars_match fs V f.cf_prov g.cf_prov
      (entry_taint with t_var := f.cf_tvar)
      (entry_taint with t_var := g.cf_tvar) f.cf_state g.cf_state /\
    dload_param_values fs f.cf_params g.cf_params
      f.cf_state.vs_params g.cf_state.vs_params
End

Theorem dload_saved_metadata_unprovenanced_refl:
  f.cf_prov = FEMPTY /\ f.cf_params = [] ==>
  dload_saved_metadata [] V f f
Proof
  simp[dload_saved_metadata_def, dload_vars_match_empty_provenance,
       dload_param_values_unprovenanced_refl]
QED

Theorem dload_setup_parameters:
  setup_callee fn xs s = SOME cs /\ setup_callee gn ys t = SOME ct /\
  dload_param_values fs PG PH xs ys ==>
  dload_param_values fs PG PH cs.vs_params ct.vs_params
Proof
  strip_tac >> imp_res_tac setup_callee_frame >> gvs[]
QED

Theorem dload_merge_local_metadata:
  (merge_callee_state caller callee).vs_vars = caller.vs_vars /\
  (merge_callee_state caller callee).vs_params = caller.vs_params /\
  (merge_callee_state caller callee).vs_prev_bb = caller.vs_prev_bb /\
  (merge_callee_state caller callee).vs_current_bb = caller.vs_current_bb
Proof
  simp[merge_callee_state_def]
QED

Definition dload_shared_store_def:
  dload_shared_store tn un s t <=>
    tn.t_stor = un.t_stor /\ tn.t_trans = un.t_trans /\
    tn.t_imm = un.t_imm /\
    (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
           t.vs_accounts a /\
         storage_agree_except
           (if a = s.vs_call_ctx.cc_address then tn.t_stor else {})
           (s.vs_accounts a).storage (t.vs_accounts a).storage /\
         storage_agree_except
           (if a = s.vs_call_ctx.cc_address then tn.t_trans else {})
           (s.vs_transient a) (t.vs_transient a)) /\
    FDOM s.vs_immutables = FDOM t.vs_immutables /\
    (!k x y. FLOOKUP s.vs_immutables k = SOME x /\
             FLOOKUP t.vs_immutables k = SOME y ==>
       word_agree_except {i | (k,i) IN tn.t_imm} x y)
End

Theorem dload_shared_store_refl:
  dload_shared_store tn tn s s
Proof
  simp[dload_shared_store_def, storage_agree_except_def,
       word_agree_except_def] >> rpt strip_tac >> gvs[]
QED

Theorem dload_equal_environment_code:
  dload_equal_environment s t ==>
  s.vs_code = t.vs_code /\ s.vs_labels = t.vs_labels /\
  s.vs_data_section = t.vs_data_section /\
  s.vs_fmp = t.vs_fmp /\ s.vs_initial_fmp = t.vs_initial_fmp
Proof
  simp[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_equal_environment_merge:
  dload_equal_environment s t /\ dload_equal_environment u v ==>
  dload_equal_environment (merge_callee_state s u) (merge_callee_state t v)
Proof
  simp[dload_equal_environment_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem dload_equal_environment_setup:
  dload_equal_environment s t /\
  (HD fn.fn_blocks).bb_label = (HD gn.fn_blocks).bb_label /\
  setup_callee fn xs s = SOME cs /\ setup_callee gn ys t = SOME ct ==>
  dload_equal_environment cs ct
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[] >>
  fs[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_shared_store_merge:
  dload_shared_store tn un u v /\
  s.vs_call_ctx.cc_address = u.vs_call_ctx.cc_address ==>
  dload_shared_store tn un (merge_callee_state s u) (merge_callee_state t v)
Proof
  simp[dload_shared_store_def, merge_callee_state_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_shared_store_setup:
  dload_shared_store tn un s t /\
  setup_callee fn xs s = SOME cs /\ setup_callee gn ys t = SOME ct ==>
  dload_shared_store tn un cs ct
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[] >>
  fs[dload_shared_store_def] >> rpt strip_tac >> gvs[]
QED

Theorem dload_setup_local_frame:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_vars = FEMPTY /\ callee.vs_allocas = FEMPTY /\
  callee.vs_alloca_next = caller.vs_alloca_next /\
  callee.vs_prev_bb = NONE /\ callee.vs_inst_idx = 0
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED

Theorem dload_invoke_operand_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  simp[taint_ok_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum drule_all >> simp[]
QED

(* Neither run's absolute request history is an environment observation. *)
Theorem dload_equal_environment_requests:
  dload_equal_environment (s with vs_requests := xs) (t with vs_requests := ys) <=>
  dload_equal_environment s t
Proof
  simp[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_equal_environment_outcomes:
  dload_equal_environment s t ==> s.vs_outcomes = t.vs_outcomes
Proof
  simp[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_equal_environment_call_ctx:
  dload_equal_environment s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof
  simp[dload_equal_environment_def, venom_state_component_equality]
QED
