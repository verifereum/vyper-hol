(* Body-independent runtime compiler operation boundaries. *)
Theory gasShadowRuntimeOps
Ancestors
  gasShadowModuleOps gasShadowModuleArgs gasShadowCompileAbi gasShadowCompileContext gasShadowState moduleLowering compileEnv emitHelper context finite_map list

Theorem gas_shadow_compiles_emit_data_section:
  gas_shadow_compiles (emit_data_section label) (emit_data_section label)
Proof
  rw[gas_shadow_compiles_def, emit_data_section_def, gas_shadow_state_def]
QED

Theorem gas_shadow_compiles_emit_data_item:
  gas_shadow_compiles (emit_data_item item) (emit_data_item item)
Proof
  rw[gas_shadow_compiles_def] >>
  `s.cs_data_sections = t.cs_data_sections` by fs[gas_shadow_state_def] >>
  Cases_on `t.cs_data_sections` >>
  fs[emit_data_item_def, gas_shadow_state_def]
QED

Theorem gas_shadow_compiles_foldl:
  gas_shadow_compiles m n /\
  (!x. MEM x xs ==> gas_shadow_compiles (f x) (g x)) ==>
  gas_shadow_compiles
    (FOLDL (\a x. comp_bind a (\_. f x)) m xs)
    (FOLDL (\a x. comp_bind a (\_. g x)) n xs)
Proof
  map_every qid_spec_tac [`m`, `n`] >> Induct_on `xs` >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_compile_register_positional_args:
  !args cenv offset.
  gas_shadow_compiles (compile_register_positional_args cenv args offset)
    (compile_register_positional_args cenv args offset)
Proof
  Induct >> simp[compile_register_positional_args_def, gas_shadow_compiles_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
       gas_shadow_compiles_decode_args]
QED

Theorem gas_shadow_compiles_compile_entry_checks:
  gas_shadow_compiles (compile_entry_checks min_cds payable)
    (compile_entry_checks min_cds payable)
Proof
  Cases_on `payable` >> Cases_on `min_cds > 4` >>
  simp[compile_entry_checks_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_void]
QED
