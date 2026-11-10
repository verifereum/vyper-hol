Theory entryReachBodySourceMemory
Ancestors
  abiCallerTypeEnv structFieldsProps finite_map

(* The existing caller boundary already restores arbitrary subenvironments. *)
Theorem entry_source_memory_size:
  struct_args_unique tops /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  env SUBMAP type_env tops /\
  evaluate_type env ty = SOME tv ==>
  type_memory_size tv = type_memory_bytes ce ty
Proof
  strip_tac >> drule_all abi_caller_type_submap >> strip_tac >>
  sym_tac >> irule make_struct_fields_map_memory_size >>
  goal_assum (drule_at Any) >> simp[]
QED
