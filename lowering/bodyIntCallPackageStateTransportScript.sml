(* Empty source scopes remove all function-local representation obligations. *)
Theory bodyIntCallPackageStateTransport
Ancestors
  bodyIntCallPackageRootResource compileEnv loweringStateRelDefs vyperState

Theorem state_rel_empty_scopes_env:
  ce1.ce_module_vars = ce2.ce_module_vars /\
  ce1.ce_module = ce2.ce_module /\
  ce1.ce_is_ctor = ce2.ce_is_ctor /\
  state_rel f ce1 cx (es with scopes := []) s ==>
  state_rel g ce2 cx (es with scopes := []) s
Proof
  strip_tac >>
  `log_entry_equiv ce1 cx.txn.target = log_entry_equiv ce2 cx.txn.target` by
    simp[FUN_EQ_THM, log_entry_equiv_def] >>
  gvs[state_rel_def, local_ptrs_rel_def, local_region_def,
       lookup_scopes_def, storage_vars_rel_def, transient_vars_rel_def,
       immutables_rel_def, logs_rel_def, log_entry_equiv_def] >>
  gvs[]
QED
