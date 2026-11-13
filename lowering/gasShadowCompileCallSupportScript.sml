(* Value-list staging and dynamic-array compiler boundaries. *)
Theory gasShadowCompileCallSupport
Ancestors
  gasShadowCompileConvert gasShadowCompileContext gasShadowCompileBase
  gasShadowState exprLowering compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_store_multi_results:
  !ops buf_op offset. gas_shadow_compiles (store_multi_results buf_op ops offset)
    (store_multi_results buf_op ops offset)
Proof
  Induct >> rpt gen_tac >> once_rewrite_tac[store_multi_results_def] >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_extcall_store_values:
  !cenv vals buf_op offset.
    gas_shadow_compiles (compile_extcall_store_values cenv vals buf_op offset)
      (compile_extcall_store_values cenv vals buf_op offset)
Proof
  recInduct compile_extcall_store_values_ind >> rpt strip_tac >>
  gvs[LET_THM] >>
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
  once_rewrite_tac[compile_extcall_store_values_def] >>
  simp[LET_THM, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt IF_CASES_TAC >> asm_rewrite_tac[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_store_bytestring]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_dynarray_pop:
  gas_shadow_compiles (compile_dynarray_pop base_op stride elem_size is_ctor imm loc)
    (compile_dynarray_pop base_op stride elem_size is_ctor imm loc)
Proof
  simp[compile_dynarray_pop_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_ptr_load,
               gas_shadow_compiles_ptr_store] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_dynarray_append:
  gas_shadow_compiles
    (compile_dynarray_append cenv base_op val_op stride elem_size dst_ty src_ty
      capacity prim load_opc store_opc)
    (compile_dynarray_append cenv base_op val_op stride elem_size dst_ty src_ty
      capacity prim load_opc store_opc)
Proof
  Cases_on `prim` >>
  simp[compile_dynarray_append_def, LET_THM, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> asm_rewrite_tac[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_bind,
               gas_shadow_compiles_store_memory, gas_shadow_compiles_word_copy_loop,
               gas_shadow_compiles_return,
               cj 1 gas_shadow_compiles_store_slots]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_void] >>
  qmatch_goalsub_abbrev_tac `if dst_loc = LocMemory then _ else _` >>
  Cases_on `dst_loc = LocMemory` >> simp[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_store_memory,
               gas_shadow_compiles_word_copy_loop, gas_shadow_compiles_return,
               cj 1 gas_shadow_compiles_store_slots]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_create_snapshot:
  gas_shadow_compiles (compile_create_snapshot cenv vv bytecode_ty)
    (compile_create_snapshot cenv vv bytecode_ty)
Proof
  Cases_on `vv_location vv` >>
  simp[compile_create_snapshot_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_bind,
               gas_shadow_compiles_copy_memory_dynamic]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
               gas_shadow_compiles_slot_to_memory, gas_shadow_compiles_imm_copy_to_memory,
               gas_shadow_compiles_copy_memory_dynamic]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_stage_intcall_args:
  !cenv vals flags tys.
    gas_shadow_compiles (compile_stage_intcall_args cenv vals flags tys)
      (compile_stage_intcall_args cenv vals flags tys)
Proof
  recInduct compile_stage_intcall_args_ind >> rpt strip_tac >> gvs[LET_THM] >>
  once_rewrite_tac[compile_stage_intcall_args_def] >>
  simp[LET_THM, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_alloc_buffer]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_bind,
           gas_shadow_compiles_store_bytestring, gas_shadow_compiles_store_memory,
           gas_shadow_compiles_return]) >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return]
QED
