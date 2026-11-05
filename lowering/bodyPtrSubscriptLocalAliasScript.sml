(* Retained local pointers describe the later value, not a snapshot. *)
Theory bodyPtrSubscriptLocalAlias
Ancestors
  compileEnv exprLowering finite_map

Theorem local_ptrs_rel_retained_root:
  local_ptrs_rel func cenv scopes' ss' /\
  lookup_scopes name scopes' = SOME entry' /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p ss = SOME w /\
  lookup_var p ss' = lookup_var p ss ==>
  val_in_memory entry'.type entry'.value (w2n w) ss'.vs_memory
Proof
  strip_tac >>
  fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >>
  simp[]
QED

Theorem compile_name_vv_ptr_alias:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar ptr_op sz) ==>
  compile_name_vv cenv ty name =
    comp_return (LocatedValue ty (mk_ptr ptr_op LocMemory))
Proof
  simp[compile_name_vv_def]
QED
