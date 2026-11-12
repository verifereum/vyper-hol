(* Export the general declaration interfaces that S1 kept local. *)
Theory augAssignPtrToplevelMetadata
Ancestors
  bodyStorageMetadata compileEnv supportedStmts supportedTypes vyperTypeEnv
  exprSimDefs vyperTypeInvariants vyperState vyperAST list finite_map

Theorem augassign_env_assignable_find_none:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem augassign_find_var_decl_storage_some:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem augassign_supported_scalar_target_decl:
  !tops src id.
    supported_scalar_target tops (src,id) ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\ is_word_type ty
Proof
  rpt gen_tac >> simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[augassign_find_var_decl_storage_some] >>
  gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
  simp[is_word_type_def]
QED
