(* Execute the array allocation, optional length store, and the element loop
   at successive cuts of one joint path. *)
Theory bodyFullMakeArrayArray
Ancestors
  bodyFullShadowBodyInv
  bodyFullMakeArrayResultDefs bodyFullMakeArrayInit bodyFullMakeArrayHeader
  bodyFullMakeArrayElements exprOperandVar gasShadowState gasShadow
  exprSimCopy exprSimAggregateLoops exprSimDefs[qualified,ignore_grammar]
  bodyMemArrayLayout exprSimAggregateEncoding
  exprSimAggregateSource exprSimAggregateLayout gasOutcomeFullStmts
  gasOutcomeFullCompose gasShadowCompileContext exprSimSource
  exprLoweringProps emitHelperProps exprSimHyps exprSimHypsDefs bodySimFull
  vyperTypeSystem bodyFullPreds stateRelProj vyperStorageTrace
  bodyFullIfExpReach
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

val _ = Parse.hide "base";

Theorem make_array_vv_sim_full_conditional:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann et n args es.
    ^(rhs (concl (PURE_REWRITE_RULE [make_array_completed_def]
      make_array_packaging_ok_def))) /\
    (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
       body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  pure_once_rewrite_tac [GSYM (PURE_REWRITE_RULE [make_array_completed_def]
    make_array_packaging_ok_def)] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,cj 9 vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `body_exprs_full_ok cx args` by
    (first_x_assum irule >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[cj 5 evaluate_storage_trace_frame] >> strip_tac >>
  drule_all array_body_allocation_layout >> strip_tac >> gvs[] >>
  `?sba ssm su.
    compile_alloc_buffer (type_memory_bytes cenv (ArrayT et n)) shadow_sa = (sba,ssm) /\
    compile_make_array compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) et
      (type_memory_bytes cenv et) (case n of Dynamic _ => T | _ => F)
      sba.buf_operand ssm = (su,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_array_literal,
          gasShadowCompileBaseTheory.type_memory_bytes_gas_shadow_env] >>
     Cases_on `compile_alloc_buffer (type_memory_bytes cenv (ArrayT et n)) shadow_sa` >>
     simp[] >>
     Cases_on `compile_make_array compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) et
       (type_memory_size tv) (case n of Dynamic _ => T | _ => F)
       q.buf_operand r` >>
     gvs[exprLoweringTheory.as_ptr_val_def]) >>
  `sba = ba /\ gas_shadow_state sm ssm` by
    (mp_tac (Q.INST [`nbytes` |-> `type_memory_bytes cenv (ArrayT et n)`]
      gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`cap` |-> `type_memory_bytes cenv (ArrayT et n)`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
    `ann` |-> `ArrayT et n`, `elem_opt` |-> `SOME et`, `bnd` |-> `n`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  `u = Var q /\ su = Var q` by metis_tac[compiler_make_array_result] >> gvs[] >>
  suspend "split_header"
QED

Resume make_array_vv_sim_full_conditional[split_header]:
  qmatch_asmsub_abbrev_tac `compile_make_array compile_expr cenv args et _ header _ _` >>
  `?sh. (if header then emit_void MSTORE [Var q; Lit (n2w (LENGTH args))]
         else return ()) sm = ((),sh) /\
     compile_make_array_elems compile_expr cenv args et (type_memory_size tv)
       header (Var q) 0 sh = (Var q,sb)` by
    (qpat_x_assum `compile_make_array _ _ args _ _ _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_make_array_def,compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_bind_def] >>
     pairarg_tac >>
     rename1 `(if header then _ else _) sm = (uh,hcs)` >>
     Cases_on `uh` >> gvs[] >> metis_tac[]) >>
  `?ssh. (if header then emit_void MSTORE [Var q; Lit (n2w (LENGTH args))]
         else return ()) ssm = ((),ssh) /\ gas_shadow_state sh ssh` by
    (reverse (Cases_on `header`)
     >- gvs[compileEnvTheory.comp_return_def] >>
     mp_tac (Q.INST [`opc` |-> `MSTORE`,
       `ops` |-> `[Var q; Lit (n2w (LENGTH (args:expr list)))]`] gas_shadow_compiles_emit_void) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`ssm`] mp_tac) >> simp[] >>
     Cases_on `emit_void MSTORE [Var q; Lit (n2w (LENGTH args))] ssm` >>
     Cases_on `q'` >> gvs[]) >>
  `compile_make_array_elems compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) et
     (type_memory_size tv) header (Var q) 0 ssh = (Var q,shadow_sb)` by
    (qpat_x_assum `compile_make_array _ _ (MAP _ args) _ _ _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_make_array_def,compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_bind_def]) >>
  suspend "header"
QED

Resume make_array_vv_sim_full_conditional[header]:
  `ci_mono sm sh` by
    (Cases_on `header` >> gvs[compileEnvTheory.comp_return_def] >-
      metis_tac[ci_mono_emit_void, pairTheory.SND] >>
     simp[ci_mono_refl]) >>
  `ci_mono sh sb` by
    (qpat_assum `compile_make_array_elems _ _ args _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `type_memory_bytes cenv et = _`
       (fn th => pure_rewrite_tac[GSYM th,compile_make_array_elems_as_tuple]) >> strip_tac >>
     qpat_x_assum `compile_make_tuple _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> strip_tac >>
     metis_tac[ci_mono_compile_make_tuple_cfn,compile_expr_ci_mono,pairTheory.SND]) >>
  `fn_has_code sm sh func /\ fn_has_code sh sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `0 < type_slot_size tv` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  `0 < type_memory_size tv` by metis_tac[valueEncodingPropsTheory.type_memory_size_pos] >>
  `LENGTH args < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `type_memory_bytes cenv (ArrayT et n)` >>
     conj_tac >- decide_tac >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH args * type_memory_size tv` >>
     conj_tac >- simp[] >>
     qpat_x_assum `_ + _ <= type_memory_bytes cenv (ArrayT et n)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qmatch_goalsub_abbrev_tac `sz + _ <= cap` >> decide_tac) >>
  `header ==> 32 <= type_memory_bytes cenv (ArrayT et n)` by
    (strip_tac >> gvs[]) >>
  mp_tac (Q.INST [`csbase` |-> `sa`, `ebase` |-> `es`, `sbase` |-> `s0`,
    `Gbase` |-> `G0`, `tnbase` |-> `tn0`, `aid` |-> `sa.cs_next_id`,
    `base` |-> `w2n (w:256 word)`, `cap` |-> `type_memory_bytes cenv (ArrayT et n)`,
    `s` |-> `si`, `G` |-> `Gi`, `tn` |-> `tni`, `len` |-> `LENGTH (args:expr list)`,
    `ai` |-> `mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (ArrayT et n)))]
      [STRING #"%" (toString sa.cs_next_var)]`]
    make_array_header_full) >>
  (impl_tac >- suspend "header_pre") >>
  disch_then (qx_choosel_then [`sj`,`Gj`,`tnj`,`ps`] strip_assume_tac) >>
  suspend "elements"
QED

Resume make_array_vv_sim_full_conditional[header_pre]:
  simp[venomInstTheory.mk_inst_def] >>
  conj_tac >-
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >> simp[]
QED

Resume make_array_vv_sim_full_conditional[elements]:
  `ci_mono shadow_sa ssm` by
    (qpat_x_assum `compile_alloc_buffer _ shadow_sa = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND]) >>
  `ci_mono ssm ssh` by
    (Cases_on `header` >> gvs[compileEnvTheory.comp_return_def] >-
      metis_tac[ci_mono_emit_void,pairTheory.SND] >> simp[ci_mono_refl]) >>
  `ci_mono shadow_sa ssh` by
    (irule ci_mono_trans >> qexists_tac `ssm` >> simp[]) >>
  `type_memory_bytes (gas_shadow_env T cenv) et = type_memory_size tv` by
    simp[gasShadowCompileBaseTheory.type_memory_bytes_gas_shadow_env] >>
  `ci_mono ssh shadow_sb` by
    (qpat_assum `compile_make_array_elems _ _ (MAP _ args) _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `type_memory_bytes (gas_shadow_env T _) _ = _`
       (fn th => pure_rewrite_tac[GSYM th,compile_make_array_elems_as_tuple]) >> strip_tac >>
     qpat_x_assum `compile_make_tuple _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> strip_tac >>
     metis_tac[ci_mono_compile_make_tuple_cfn,compile_expr_ci_mono,pairTheory.SND]) >>
  `fn_has_code ssh shadow_sb shadow_func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     conj_tac >- fs[ci_mono_def] >> qexists_tac `shadow_sa` >> fs[ci_mono_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn i z. frag_reachable ctx func si fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  `!fn i z. frag_reachable ctx func sj fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (si,Gi,tni) [] (OK sj,Gj,tnj)`
       (qspecl_then [`DF (storage_trace_horizon es.storage_trace)`,
                     `gas_explicit_sites ctx shadow_ctx`] assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (si,Gi,tni) [] (OK sj,Gj,tnj)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func si fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  mp_tac (Q.INST [`csbase` |-> `sa`, `ebase` |-> `es`, `sbase` |-> `s0`,
    `Gbase` |-> `G0`, `tnbase` |-> `tn0`, `aid` |-> `sa.cs_next_id`,
    `base` |-> `w2n (w:256 word)`, `cap` |-> `type_memory_bytes cenv (ArrayT et n)`]
    make_array_elements_full) >>
  disch_then (qspecl_then [`args`,`et`,`tv`,`header`,`if header then 32 else 0`,
    `ps`,`sh`,`sb`,`ssh`,`shadow_sb`,`es`,`sj`,`Gj`,`tnj`] mp_tac) >>
  (impl_tac >- suspend "elements_pre") >>
  strip_tac >> suspend "outcome"
QED

Resume make_array_vv_sim_full_conditional[elements_pre]:
  fs[ci_mono_def] >> simp[arithmeticTheory.ADD_SYM] >> rpt conj_tac
  >~ [`!fn inst z. frag_reachable ctx func sj fn inst z ==> dalloca_fmp_headroom inst z`]
  >- first_assum ACCEPT_TAC
  >~ [`regions_disjoint _ _ _ _`]
  >-
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >> simp[]) >>
  qpat_x_assum `EVERY _ ps` mp_tac >> simp[arithmeticTheory.ADD_SYM]
QED

Resume make_array_vv_sim_full_conditional[outcome]:
  drule_at Any (Q.INST [
    `f` |-> `\rr. case rr of INL vs => INL (Value (ArrayV (make_array_value tv n vs))) | INR ex => INR ex`]
    (INST_TYPE [beta |-> ``:value list``, alpha |-> ``:eval_result``]
      gas_outcome_full_source_map)) >>
  disch_then (qspecl_then [`tv`,
    `eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)`,`n`] mp_tac) >>
  (impl_tac >-
    (simp[] >> gen_tac >> Cases_on `eval_exprs cx args es'` >>
     drule aggregate_eval_make_array >> simp[])) >>
  strip_tac >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Gi`,`si`,`tni`] >> simp[] >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Gj`,`sj`,`tnj`] >> simp[] >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "package" >>
  POP_ASSUM_LIST (K all_tac) >> BETA_TAC >> rpt strip_tac >>
  gvs[oneline exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def,
      AllCaseEqs()]
QED

Resume make_array_vv_sim_full_conditional[package]:
  BETA_TAC >> rpt strip_tac >> gvs[] >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  `eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)
     (es with gas_obs := xs) =
     (INL (Value (ArrayV (make_array_value tv n vs))),ee)` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes cenv (ArrayT et n)))] [q]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_tac o MATCH_MP abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
     strip_tac >> drule emitted_insts_emit_op >> simp[] >> strip_tac >> gvs[]) >>
  `!name b len. local_region cenv es.scopes si name b len <=>
     local_region cenv es.scopes s0 name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
     val_in_memory (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) (w2n w) m` by
    (rpt strip_tac >> irule array_from_dense_memory >>
     Cases_on `n` >> gvs[Abbr `header`] >> suspend "memory") >>
  `ci_mono sa sh` by (irule ci_mono_trans >> qexists_tac `sm` >> simp[]) >>
  `make_array_completed H (DF H) lo d ctx func cenv cx env
    (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) es sa sh sb s0 si
    G0 tn0 ee (ArrayV (make_array_value tv n vs)) (ArrayTV tv n) (w2n (w:256 word))
    (type_memory_bytes cenv (ArrayT et n)) q G' tn' t xs` by
    (simp[make_array_completed_def,vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
          compileEnvTheory.is_word_type_def] >> suspend "certificate") >>
  qpat_x_assum `make_array_packaging_ok` mp_tac >>
  rewrite_tac[make_array_packaging_ok_def] >> disch_then drule >>
  simp[loweringPostsTheory.post_value_type_def,vyperASTTheory.expr_type_def]
QED

Resume make_array_vv_sim_full_conditional[memory]:
  qpat_x_assum `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory _ _ _ m`
    (qspec_then `m` mp_tac) >>
  simp[valueEncodingDefsTheory.val_in_memory_def,
       valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_pos]
QED

Resume make_array_vv_sim_full_conditional[certificate]:
  conj_tac >- metis_tac[expr_sim_inv_memory_size] >>
  conj_tac >-
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >> simp[]) >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
       drule >> strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!name b sz. local_region cenv es.scopes sj name b sz <=>
     local_region cenv es.scopes s0 name b sz` by
    (rpt gen_tac >> irule exprSimSubscriptArrayFrameTheory.local_region_wb_frame >>
     conj_tac >- (qexists_tac `func` >> simp[]) >>
     qexistsl_tac [`es`,`sa`] >> simp[]) >>
  qpat_x_assum `EVERY _ args ==> _` drule >> strip_tac >>
  conj_tac >- metis_tac[] >>
  map_every qx_gen_tac [`p`,`len`] >> disch_tac >>
  `mem_bytes_at p len t.vs_memory = mem_bytes_at p len sj.vs_memory` by
    (qpat_x_assum `!p sz. (_ \/ _) /\ _ ==> mem_bytes_at p sz t.vs_memory = _` irule >>
     metis_tac[]) >>
  `mem_bytes_at p len sj.vs_memory = mem_bytes_at p len s0.vs_memory` by
    (qpat_x_assum `!p sz. _ \/ _ ==> mem_bytes_at p sz sj.vs_memory = _` irule >>
     Cases_on `header` >> gvs[] >> decide_tac) >>
  simp[]
QED

Finalise make_array_vv_sim_full_conditional
