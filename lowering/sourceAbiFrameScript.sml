(* Source ABI capture bookkeeping is not part of the compiler state relation.
   Shared by expression mutations and statement assignments. *)
Theory sourceAbiFrame
Ancestors
  exprLoweringProps compileEnv vyperState venomState

Theorem stmt_state_rel_abi_memory[simp]:
  stmt_state_rel func cenv cx (es with abi_memory := abi) s <=>
  stmt_state_rel func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def]
QED

Theorem stmt_state_rel_scopes_abi_memory[simp]:
  stmt_state_rel func cenv cx (es with <|scopes := scopes; abi_memory := abi|>) s <=>
  stmt_state_rel func cenv cx (es with scopes := scopes) s
Proof
  simp[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def]
QED
