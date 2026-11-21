(* Split a grouped initializer at the corresponding real and shadow stores. *)
Theory groupedDefaultCode
Ancestors
  groupedInternalLabels runtimeDefaultCompile gasShadowModuleArgs
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileContext gasShadowCompileBase
  gasShadowState emitHelperProps exprSimFullBundleProps moduleLowering
  exprLoweringProps exprLowering compileEnv list pair
  gasShadowCompileAbi abiEncoder calldataRegistrationExec

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

Theorem grouped_supplied_initializer_shadow:
  0 < k /\
  compile_getelemptr_abi (Lit 4w) (is_abi_dynamic ce.ce_struct_fields ty)
    (off - 4) CALLDATALOAD (Lit 0w) (Lit 0w) sa = (src,mid) /\
  (if is_abi_dynamic ce.ce_struct_fields ty then
     compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
   else first = mid) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
  compile_init_kwargs ce
    ((name,dst,ty,gas_shadow_expr e)::MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
    off k hi sha = ((),shb) /\
  fn_has_code sha shb shfn /\ gas_shadow_state sa sha ==>
  ?shadow_last.
    compile_init_kwargs ce (MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
      (off + abi_embedded_static_size ce.ce_struct_fields ty) (k - 1) hi shadow_last = ((),shb) /\
    fn_has_code shadow_last shb shfn /\ gas_shadow_state last shadow_last /\ ci_mono sa last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`sa` |-> `sha`,`sb` |-> `shb`,`fn` |-> `shfn`,
    `default_e` |-> `gas_shadow_expr e`,
    `vars` |-> `MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars`]
    (SPEC_ALL compile_init_kwargs_supplied_intervals)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`shadow_src`,`shadow_mid`,`shadow_first`,`shadow_last`]
    strip_assume_tac) >>
  `shadow_src = src /\ gas_shadow_state mid shadow_mid` by
    (mp_tac (Q.SPECL [`sa`,`sha`]
       (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`src` |-> `Lit 4w`,`dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`,
            `off` |-> `off-4`,`opc` |-> `CALLDATALOAD`,`base_op` |-> `Lit 0w`,
            `hi` |-> `Lit 0w`] gas_shadow_compiles_getelemptr_abi))) >>
     asm_rewrite_tac[pairTheory.FST,pairTheory.SND] >> simp[]) >>
  qpat_x_assum `shadow_src = src` SUBST_ALL_TAC >>
  `gas_shadow_state first shadow_first` by
    (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >> gvs[] >>
     `gas_shadow_compiles (compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w))
       (compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w))` by
       (simp[compile_abi_arg_ptr_guard_def, comp_ignore_bind_def] >>
        rpt (ho_match_mp_tac gas_shadow_compiles_bind >> rpt strip_tac) >>
        simp[gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void]) >>
     qpat_assum `gas_shadow_compiles _ _`
       (qspecl_then [`mid`,`shadow_mid`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     asm_rewrite_tac[pairTheory.FST,pairTheory.SND]) >>
  `gas_shadow_state last shadow_last` by
    (mp_tac (Q.SPECL [`first`,`shadow_first`]
       (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`opc` |-> `CALLDATALOAD`,`base_op` |-> `Lit 0w`,
           `hi` |-> `Lit 0w`,`info` |-> `type_to_abi_dec_info ce.ce_struct_fields ce ty`]
           gas_shadow_compiles_abi_decode_to_buf))) >>
     simp[]) >>
  `ci_mono sa mid` by
    (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ sa = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
     simp[compile_getelemptr_abi_def,compile_abi_dec_addr_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,pairTheory.ELIM_UNCURRY] >>
     strip_tac >> gvs[] >> metis_tac[ci_mono_refl,ci_mono_trans,ci_mono_emit_op,pairTheory.SND]) >>
  `ci_mono mid first` by
    (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >> gvs[ci_mono_refl] >>
     qpat_assum `compile_abi_arg_ptr_guard CALLDATALOAD _ _ mid = _`
       (fn th => assume_tac (MATCH_MP registration_ptr_guard_extends th) >>
         strip_assume_tac (MATCH_MP registration_ptr_guard_code th)) >>
     simp[ci_mono_def]) >>
  `ci_mono first last` by metis_tac[ci_mono_compile_abi_decode,pairTheory.SND] >>
  qexists_tac `shadow_last` >> asm_rewrite_tac[] >> metis_tac[ci_mono_trans]
QED
