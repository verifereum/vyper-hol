(* Split a grouped initializer at the corresponding real and shadow stores. *)
Theory groupedDefaultCode
Ancestors
  groupedInternalLabels runtimeDefaultCompile gasShadowModuleArgs
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileContext gasShadowCompileBase
  gasShadowState emitHelperProps exprSimFullBundleProps moduleLowering
  exprLoweringProps exprLowering compileEnv list pair

Theorem grouped_default_initializer_intervals:
  compile_init_kwargs ce ((name,dst,ty,e)::vars) off 0 hi sa = ((),sb) /\
  compile_init_kwargs ce
    ((name,dst,ty,gas_shadow_expr e)::MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
    off 0 hi sha = ((),shb) /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha ==>
  ?op mid last shmid shlast.
    lower_value compile_expr ce ty e sa = (op,mid) /\
    lower_value compile_expr ce ty (gas_shadow_expr e) sha = (op,shmid) /\
    (if is_word_type ty then emit_void MSTORE [dst;op]
     else if is_bytestring_type ty then compile_store_bytestring op dst
     else emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes ce ty))]) mid = ((),last) /\
    compile_init_kwargs ce vars off 0 hi last = ((),sb) /\
    compile_init_kwargs ce (MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
      off 0 hi shlast = ((),shb) /\
    fn_has_code sa mid fn /\ fn_has_code sha shmid shfn /\
    fn_has_code mid last fn /\ fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\
    gas_shadow_state mid shmid /\ gas_shadow_state last shlast /\
    ci_mono sa last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_init_kwargs ce ((name,dst,ty,e)::vars) off 0 hi sa = _`
    (mp_then Any (drule_then strip_assume_tac) compile_init_kwargs_omitted_intervals) >>
  qpat_assum `compile_init_kwargs ce ((name,dst,ty,gas_shadow_expr e)::_) off 0 hi sha = _`
    (mp_then Any (drule_then strip_assume_tac) compile_init_kwargs_omitted_intervals) >>
  rename1 `lower_value compile_expr ce ty e sa = (op,mid)` >>
  rename1 `lower_value compile_expr ce ty (gas_shadow_expr e) sha = (shop,shmid)` >>
  rename1 `compile_init_kwargs ce vars off 0 hi last = ((),sb)` >>
  rename1 `compile_init_kwargs ce _ off 0 hi shlast = ((),shb)` >>
  `gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr ce ty (gas_shadow_expr e))` by
    (mp_tac (Q.INST [`sh` |-> `T`, `cenv` |-> `ce`]
       (MATCH_MP gas_shadow_compiles_lower_value (CONJUNCT1 gas_shadow_compile_expr))) >>
     simp[]) >>
  `shop = op /\ gas_shadow_state mid shmid` by
    (qpat_assum `gas_shadow_compiles (lower_value _ _ _ _) _`
       (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE[gas_shadow_compiles_def]) >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `shop = op` SUBST_ALL_TAC >>
  `gas_shadow_state last shlast` by
    (Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
     fs[] >> metis_tac[gas_shadow_compiles_emit_void, gas_shadow_compiles_store_bytestring,
		     gas_shadow_compiles_def, pairTheory.SND]) >>
  `ci_mono mid last` by
    (Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
     fs[] >> metis_tac[ci_mono_emit_void, ci_mono_compile_store_bytestring, pairTheory.SND]) >>
  `ci_mono sa last` by
    metis_tac[ci_mono_lower_value_compile_expr, ci_mono_trans, pairTheory.SND] >>
  qexistsl_tac [`op`,`mid`,`last`,`shmid`,`shlast`] >> asm_rewrite_tac[]
QED
