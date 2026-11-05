Theory bodyPtrBytestringBuiltinsPtrFrame
Ancestors
  bodyPtrBytestringBuiltinsPtrRun bodyPtrBytestringBuiltinsSourceFrame
  bodyPtrBytestringBuiltinsOrderRun vyperTypeInvariants bodySim

(* A single-local typing environment for the compatible PtrVar fixture. *)
Definition order_ptr_tenv_def:
  order_ptr_tenv = <|
    current_src := NONE;
    var_types := FEMPTY |+ ("arr", ArrayT (BaseT AddressT) (Dynamic 2));
    var_assignable := FEMPTY |+ ("arr", T);
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY; event_fields := FEMPTY |>
End

Theorem order_ptr_frame_body_inv:
  body_inv [] order_frame_unit.cu_context order_ptr_env order_frame_cx
Proof
  mp_tac order_frame_body_inv >>
  simp[bodySimTheory.body_inv_def, order_ptr_env_def] >>
  metis_tac[]
QED

Theorem order_ptr_frame_local_bindings:
  (!id ty. FLOOKUP order_ptr_tenv.var_types id = SOME ty ==>
    ?p sz. FLOOKUP order_ptr_env.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP order_ptr_tenv.var_types id = SOME ty ==>
    order_ptr_env.ce_var_type id = SOME ty)
Proof
  simp[order_ptr_tenv_def, order_ptr_env_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> EVAL_TAC
QED

Theorem order_ptr_frame_scopes:
  env_scopes_consistent order_ptr_tenv order_frame_cx
    (st with scopes := bodyPtrBytestringBuiltinsOrderProbe$order_probe_scopes)
Proof
  simp[env_scopes_consistent_def, order_ptr_tenv_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem order_ptr_frame_context:
  env_context_consistent order_ptr_tenv order_frame_cx
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUNION_FEMPTY_1] >>
  rw[] >> gvs[AllCaseEqs()] >> EVAL_TAC
QED

(* Fix the source state to the same accounts as the initialized runtime. *)
Definition order_ptr_source_def:
  order_ptr_source = vyperState$empty_state with <|
    scopes := bodyPtrBytestringBuiltinsOrderProbe$order_probe_scopes;
    accounts := order_run_start.vs_accounts;
    outcomes := SOME [] |>
End

Theorem order_ptr_frame_env:
  env_consistent order_ptr_tenv order_frame_cx order_ptr_source
Proof
  simp[env_consistent_def, order_ptr_frame_context,
       order_ptr_source_def, order_ptr_frame_scopes,
       env_immutables_consistent_def, order_ptr_tenv_def,
       env_scopes_consistent_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem order_ptr_frame_state_typed:
  state_well_typed order_ptr_source
Proof
  EVAL_TAC >> rw[] >> gvs[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> CONV_TAC wordsLib.WORD_EVAL_CONV
QED

Theorem order_ptr_frame_context_typed:
  context_well_typed order_frame_cx /\ functions_well_typed order_frame_cx
Proof
  EVAL_TAC >> rw[] >> gvs[AllCaseEqs()] >>
  fs[vyperInterpreterTheory.lookup_function_def]
QED

Theorem order_ptr_frame_accounts_typed:
  accounts_well_typed order_ptr_source.accounts
Proof
  EVAL_TAC >> rw[] >> EVAL_TAC
QED

Theorem order_ptr_frame_outcomes:
  exprSimHypsDefs$outcomes_accounts_typed order_ptr_source.outcomes /\
  IS_SOME order_ptr_source.outcomes /\
  exprSimHypsDefs$popped_keys_indexed order_ptr_source.scopes
Proof
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem order_ptr_frame_storage:
  contract_storage_well_formed order_frame_cx order_ptr_source /\
  storage_layout_safe order_frame_cx
Proof
  EVAL_TAC >> rw[] >> gvs[AllCaseEqs()]
QED

Theorem order_ptr_frame_oracle:
  oracle_storage_ok order_frame_cx order_ptr_source
Proof
  EVAL_TAC >> simp[]
QED

Theorem order_ptr_frame_sim_inv:
  exprSimHypsDefs$expr_sim_inv order_ptr_env order_frame_cx
    order_ptr_tenv order_ptr_source
Proof
  simp[exprSimHypsDefsTheory.expr_sim_inv_def,
       order_ptr_frame_env, order_ptr_frame_state_typed,
       order_ptr_frame_accounts_typed, order_ptr_frame_context_typed,
       order_ptr_frame_local_bindings, order_ptr_frame_outcomes,
       order_ptr_frame_storage, order_ptr_frame_oracle] >>
  EVAL_TAC >> rw[] >> gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def] >>
  EVAL_TAC
QED

Theorem order_ptr_frame_expr_typed:
  well_typed_expr order_ptr_tenv
    bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr
Proof
  qspec_then `order_ptr_tenv` mp_tac
    bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_well_typed >>
  simp[order_ptr_tenv_def]
QED

Theorem order_ptr_frame_no_call_safety:
  ~call_evaluation_safe order_frame_cx []
Proof
  EVAL_TAC >> simp[]
QED

Theorem order_ptr_frame_no_body_pre:
  ~exprSimHypsDefs$expr_body_pre order_ptr_env order_frame_cx order_ptr_tenv
    bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr order_ptr_source
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_no_internal_calls,
       order_ptr_frame_no_call_safety]
QED

(* A distinct context retains the empty module but supplies the current owner
   required by call_evaluation_safe, even for expressions without calls. *)
Definition order_ptr_cx_def:
  order_ptr_cx = order_frame_cx with stk := [(NONE, "probe")]
End

Theorem order_ptr_call_safety:
  call_evaluation_safe order_ptr_cx []
Proof
  simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
       order_ptr_cx_def] >>
  qexists_tac `[]` >> EVAL_TAC >> rw[] >> gvs[AllCaseEqs()] >>
  fs[vyperInterpreterTheory.lookup_function_def] >>
  simp[relationTheory.irreflexive_def, Once relationTheory.TC_CASES1,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem order_ptr_body_inv:
  body_inv [] order_frame_unit.cu_context order_ptr_env order_ptr_cx
Proof
  mp_tac order_ptr_frame_body_inv >>
  simp[bodySimTheory.body_inv_def, order_ptr_cx_def,
       vyperLookupStorageTheory.get_tenv_stk,
       vyperLookupStorageTheory.get_module_code_stk]
QED

Theorem order_ptr_sim_inv:
  exprSimHypsDefs$expr_sim_inv order_ptr_env order_ptr_cx
    order_ptr_tenv order_ptr_source
Proof
  mp_tac order_ptr_frame_sim_inv >>
  simp[exprSimHypsDefsTheory.expr_sim_inv_def, order_ptr_cx_def,
       vyperLookupStorageTheory.get_tenv_stk,
       vyperLookupStorageTheory.get_module_code_stk] >>
  strip_tac >> simp[] >>
  EVAL_TAC >> simp[finite_mapTheory.FUNION_FEMPTY_1] >>
  rw[] >> gvs[AllCaseEqs()] >> EVAL_TAC >>
  fs[vyperInterpreterTheory.lookup_function_def] >>
  simp[wordsTheory.dimword_def]
QED

Theorem order_ptr_body_pre:
  exprSimHypsDefs$expr_body_pre order_ptr_env order_ptr_cx order_ptr_tenv
    bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr order_ptr_source
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, order_ptr_sim_inv,
       order_ptr_frame_expr_typed, order_ptr_call_safety,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_no_internal_calls,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_byte_widths,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_alloc_limits,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_no_evm_run] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[order_ptr_cx_def, order_frame_cx_def,
       gasContextTheory.cx_tops_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def] >>
  EVAL_TAC >> simp[]
QED
