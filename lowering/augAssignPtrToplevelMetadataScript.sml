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

