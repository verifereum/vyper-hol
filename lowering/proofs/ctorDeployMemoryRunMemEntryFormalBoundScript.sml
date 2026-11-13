Theory ctorDeployMemoryRunMemEntryFormalBound
Ancestors
  compileVyper structFieldsProps list

Theorem ctor_formal_type_memory_bound:
  !tops mut nr rr fname fargs dflts ret body name ty tv.
  fn_allocs_ok tops (mut,nr,rr,fname,fargs,dflts,ret,body) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  MEM (name,ty) fargs /\ evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_size tv < 2 ** 64
Proof
  simp[fn_allocs_ok_def, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e fargs ==> _` (qspec_then `(name,ty)` mp_tac) >>
  simp[] >>
  `type_memory_bytes (build_compile_env tops Internal mut fname fargs ret body' F) ty =
   type_memory_size tv` by
    (irule make_struct_fields_map_memory_size >>
     simp[build_compile_env_ce_struct_fields] >>
     metis_tac[typedCopyProducerTheory.distinct_type_keys_struct_args_unique]) >> simp[]
QED
