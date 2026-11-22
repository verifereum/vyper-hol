(* The entry cut, before the nonreentrant lock or body. *)
Theory bodyFullIntCallEntryShadow
Ancestors
  intCallCallee gasShadowInternal gasShadowModuleOps gasShadowCompileContext
  gasShadowCompileStmtBase gasShadowCompileBase gasShadowState compileEnv
  emitHelper venomInst pair

Theorem intcall_shadow_entry_prefix[local]:
  !a aS. gas_shadow_state a aS ==>
    FST (compile_internal_entry_prefix (gas_shadow_env sd ce) params has_rb aS) =
      (\p. (gas_shadow_env sd (FST p), SND p))
        (FST (compile_internal_entry_prefix ce params has_rb a)) /\
    gas_shadow_state (SND (compile_internal_entry_prefix ce params has_rb a))
      (SND (compile_internal_entry_prefix (gas_shadow_env sd ce) params has_rb aS))
Proof
  rewrite_tac[GSYM gas_shadow_compiles_mapped_result_iff,
              compile_internal_entry_prefix_def, comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `has_rb` >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
           gas_shadow_compiles_return]) >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_internal_param_decls] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_emit_op] >>
  gen_tac >>
  simp[gas_shadow_compiles_def, comp_bind_def, comp_return_def] >>
  rw[gas_shadow_env_def, compile_env_component_equality]
QED

Theorem intcall_shadow_entry_cut:
  gas_shadow_state entry entryS /\
  compile_internal_function_entry ce params has_rb ctor ilen rt entry =
    ((ce0,rpc,imm),prologue) ==>
  ?prologueS.
    compile_internal_function_entry (gas_shadow_env sd ce) params has_rb
      ctor ilen rt entryS = ((gas_shadow_env sd ce0,rpc,imm),prologueS) /\
    gas_shadow_state prologue prologueS
Proof
  `!a aS. gas_shadow_state a aS ==>
    FST (compile_internal_function_entry (gas_shadow_env sd ce) params has_rb
          ctor ilen rt aS) =
      (\p. (gas_shadow_env sd (FST p), SND p))
        (FST (compile_internal_function_entry ce params has_rb ctor ilen rt a)) /\
    gas_shadow_state
      (SND (compile_internal_function_entry ce params has_rb ctor ilen rt a))
      (SND (compile_internal_function_entry (gas_shadow_env sd ce) params has_rb
              ctor ilen rt aS))` suffices_by
    (strip_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     Cases_on `compile_internal_function_entry (gas_shadow_env sd ce)
       params has_rb ctor ilen rt entryS` >> gvs[]) >>
  rewrite_tac[GSYM gas_shadow_compiles_mapped_result_iff,
              compile_internal_function_entry_def, comp_bind_assoc,
              comp_ignore_bind_def] >>
  irule gas_shadow_compiles_bind_mapped >>
  qexists_tac `\p. (gas_shadow_env sd (FST p), SND p)` >>
  reverse conj_tac >- simp[intcall_shadow_entry_prefix] >>
  gen_tac >> simp[comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
                           gas_shadow_compiles_fixed_region_with_id]) >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_env_bind >> conj_tac
  >- simp[gas_shadow_compiles_env_materialize_internal_params] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_bind_assoc] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `rt` >> simp[gas_shadow_compiles_return] >>
      IF_CASES_TAC >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_alloc_buffer]) >>
  simp[gas_shadow_compiles_def, comp_bind_def, comp_return_def]
QED
