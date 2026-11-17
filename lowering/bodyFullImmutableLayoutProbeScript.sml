(* Body-level layout agreement does not need global struct-name uniqueness. *)
Theory bodyFullImmutableLayoutProbe
Ancestors
  bodySim exprSimHyps structFieldsProps vyperContext compileEnv
  bodyFullImmutableStoreProbe finite_map list

Theorem immutable_body_layout_sizes:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es ==>
  !ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv
Proof
  strip_tac >>
  `ce.ce_struct_fields = make_struct_fields_map tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by fs[body_inv_def] >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, GSYM type_env_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  metis_tac[type_mem_bytes_type_memory_bytes]
QED
