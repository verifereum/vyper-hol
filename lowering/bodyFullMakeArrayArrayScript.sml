(* Joint array-literal execution, conditional only on completed-buffer packaging. *)
Theory bodyFullMakeArrayArray
Ancestors
  bodyFullMakeArrayResultDefs bodyFullMakeArrayInit bodyFullMakeArrayLoop
  bodyFullMakeArrayHeader bodyFullMakeArrayElements exprOperandVar gasShadowState
  gasShadow exprSimCopy exprSimAggregateLoops
  exprSimDefs[qualified,ignore_grammar]
  bodyInvNoDalloca bodyMemArrayLayout
  exprSimAggregateEncoding exprSimAggregateSource exprSimAggregateLayout
  gasOutcomeFullGuarded gasOutcomeFullStmts gasOutcomeFullCompose
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompileContext
  calldataOverwritePtr bodyFullHashCleanFrame bodyPtrMakeArrayCopyStep
  bodyPtrMakeArrayWordStore exprSimSource exprLoweringProps emitHelperProps
  exprSimHyps exprSimHypsDefs bodySimFull vyperTypeSystem bodyFullPreds

val _ = Parse.hide "base";

Theorem make_array_vv_sim_full_conditional:
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,well_typed_expr_def,well_typed_builtin_app_def] >>
  `body_exprs_full_ok cx args` by
    (first_x_assum irule >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ann`,`args`,`MakeArray (SOME et) n`,`es`] >> simp[]) >>
  rw[expr_vv_sim_full_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_bad_intro >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`G0`,
                    `PG`,`tn0`,`[]`,`s0`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil] >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  drule_all array_body_allocation_layout >> strip_tac >> gvs[] >>
  `?sba ssm su.
    compile_alloc_buffer (type_memory_bytes cenv (ArrayT et n)) shadow_sa = (sba,ssm) /\
    compile_make_array compile_expr cenv (MAP gas_shadow_expr args) et
      (type_memory_bytes cenv et) (case n of Dynamic _ => T | _ => F)
      sba.buf_operand ssm = (su,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_array_literal] >>
     Cases_on `compile_alloc_buffer (type_memory_bytes cenv (ArrayT et n)) shadow_sa` >>
     simp[] >>
     Cases_on `compile_make_array compile_expr cenv (MAP gas_shadow_expr args) et
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
  `compile_make_array_elems compile_expr cenv (MAP gas_shadow_expr args) et
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
     simp[ci_mono_def,compileEnvTheory.cs_extends_refl]) >>
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
  cheat
QED

Resume make_array_vv_sim_full_conditional[header_pre]:
  simp[] >> FAIL_TAC "header pre"
QED

Finalise make_array_vv_sim_full_conditional
