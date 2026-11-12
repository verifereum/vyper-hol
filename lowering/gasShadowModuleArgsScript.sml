(* Constructor argument operations on arbitrary descriptors. *)
Theory gasShadowModuleArgs
Ancestors
  gasShadowModuleOps gasShadowCompileAbi gasShadowCompileContext gasShadowState
  moduleLowering compileEnv gasShadowCompile gasShadowCompileHelpers

Theorem gas_shadow_compiles_decode_args:
  !args ce off opc hi base.
    gas_shadow_compiles (compile_decode_args ce args off opc hi base)
      (compile_decode_args ce args off opc hi base)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_decode_args_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  Cases_on `h1` >> Cases_on `h2` >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op,
               gas_shadow_compiles_abi_clamp_basetype] >> gen_tac) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return] >>
  rename1 `SOME loc` >>
  Cases_on `var_location_decode_operand loc` >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return, gas_shadow_compiles_emit_op,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_abi_decode_to_buf]
QED

Theorem gas_shadow_compiles_register_constructor_args:
  !args ce off size.
    gas_shadow_compiles (compile_register_constructor_args ce args off size)
      (compile_register_constructor_args ce args off size)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_register_constructor_args_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >> simp[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return, gas_shadow_compiles_alloc_buffer,
       gas_shadow_compiles_decode_args]
QED

Theorem gas_shadow_compile_create_kwarg_allocas:
  !xs ce s t. gas_shadow_state s t ==>
    FST (compile_create_kwarg_allocas ce
      (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) xs) t) =
      MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e))
        (FST (compile_create_kwarg_allocas ce xs s)) /\
    gas_shadow_state (SND (compile_create_kwarg_allocas ce xs s))
      (SND (compile_create_kwarg_allocas ce
        (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) xs) t))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  PairCases_on `h` >> strip_tac >>
  mp_tac (Q.INST [`nbytes` |-> `type_memory_bytes ce h1`]
    gas_shadow_compiles_alloc_buffer) >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum (qspec_then `ce` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) s` >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) t` >>
  Cases_on `compile_create_kwarg_allocas ce xs r` >>
  gvs[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def,
      pairTheory.UNCURRY]
QED

Theorem gas_shadow_compiles_init_kwargs:
  !xs ce off k hi.
    gas_shadow_compiles (compile_init_kwargs ce xs off k hi)
      (compile_init_kwargs ce
        (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) xs) off k hi)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_init_kwargs_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  simp[compile_init_kwargs_def] >> IF_CASES_TAC
  >- (simp[comp_ignore_bind_def] >>
      ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
      >- simp[gas_shadow_compiles_emit_op] >> gen_tac >>
      ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
      >- (IF_CASES_TAC >>
          simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_return]) >> gen_tac >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_abi_decode_to_buf]) >>
  simp[comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[gas_shadow_compile_expr,
               Q.INST [`sh` |-> `T`] gas_shadow_compiles_lower_value] >>
  gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[gas_shadow_compiles_emit_void,
           gas_shadow_compiles_store_bytestring]) >>
  simp[]
QED

Theorem gas_shadow_compiles_entry_point_kwargs:
  gas_shadow_compiles (compile_entry_point_kwargs ce xs off k lbl)
    (compile_entry_point_kwargs ce
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) xs) off k lbl)
Proof
  simp[compile_entry_point_kwargs_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_init_kwargs,
       gas_shadow_compiles_emit_inst]
QED
