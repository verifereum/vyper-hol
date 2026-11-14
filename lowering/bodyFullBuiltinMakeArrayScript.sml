(*
 * The joint (full) judgments of an array or tuple literal, laid out in a
 * fresh memory buffer, at every horizon (DF H, lo): source GAS origins,
 * memory posts and pointer ghosts share one witness.  bodyFullCases'
 * make_array_expr_full_ok is this, with body_expr_full_ok unfolded.
 *
 * TOP-LEVEL:
 *   make_array_sim_full
 *)
Theory bodyFullBuiltinMakeArray
Ancestors
  bodyFullPreds bodySimFull exprSimHypsDefs exprLowering vyperAST list
  bodyFullMakeArrayLoop bodyFullMakeArrayInit bodyFullOfVV
  exprSimAggregateLayout exprSimAggregateSource exprSimBuffer
  gasOutcomeFullStmts gasOutcomeFullCompose exprSimHyps exprSimSource
  gasShadowCompileContext rawCallBufferPtr entryAggregateValuePackaging

val _ = Parse.hide "body";
val _ = Parse.hide "base";

(* The checked MakeArray slot continuation preserves the parent allocation,
   initialized prefix, baseline trace prefix and conditional pure frame at one
   endpoint. A dynamic array's length word is an initialized prefix cell. *)
Theorem make_array_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (?t n. bt = MakeArray t n) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `expr_body_pre cenv cx env
    (Builtin a (MakeArray elem_opt bnd) args) es` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `post_value_type cenv (Builtin a (MakeArray elem_opt bnd) args) = a /\
   lowered_value_type cenv (Builtin a (MakeArray elem_opt bnd) args) = a /\
   expr_type (Builtin a (MakeArray elem_opt bnd) args) = a` by
    simp[loweringPostsTheory.post_value_type_def,
         exprLoweringTheory.lowered_value_type_def,vyperASTTheory.expr_type_def] >>
  `?rt. evaluate_type (get_tenv cx) a = SOME rt` by
    (drule expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `~is_word_type a` by
    (Cases_on `elem_opt`
     >- (drule make_tuple_evaluated_layout >> strip_tac >>
         gvs[compileEnvTheory.is_word_type_def]) >>
     drule make_array_evaluated_layout >> strip_tac >>
     gvs[compileEnvTheory.is_word_type_def]) >>
  `type_memory_bytes cenv a = type_memory_size rt` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size rt < 2 ** 64` by
    fs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def] >>
  `compatible_bound bnd (LENGTH args)` by
    (Q.UNDISCH_TAC `expr_body_pre cenv cx env
       (Builtin a (MakeArray elem_opt bnd) args) es` >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `elem_opt` >>
     simp[expr_body_pre_def,vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def] >>
     rpt strip_tac >> gvs[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `builtin_args_length_ok (MakeArray elem_opt bnd) (LENGTH args) ==> _`
       irule >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`a`,`MakeArray elem_opt bnd`,
        `args`,`e`,`es`,`ee`] expr_body_pre_builtin_arg) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a (MakeArray elem_opt bnd) args) es` by
    suspend "vv" >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (Q.INST
    [`e` |-> `Builtin a (MakeArray elem_opt bnd) args`, `rty` |-> `rt`]
    expr_sim_full_of_vv) >> simp[] >> rpt conj_tac
  >~ [`type_memory_size _ < _`]
  >- (Q.UNDISCH_TAC `type_memory_size rt < 2 ** 64` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin a (MakeArray elem_opt bnd) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[]
QED

Resume make_array_sim_full[vv]:
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> disch_tac >>
  Cases_on `elem_opt`
  >- suspend "tuple" >> suspend "array"
QED

Resume make_array_sim_full[tuple]:
  Q.UNDISCH_THEN `expr_body_pre cenv cx env
    (Builtin a (MakeArray NONE bnd) args) es`
    (fn th => assume_tac th >>
      qx_choosel_then [`tys`,`dtvs`] strip_assume_tac
        (MATCH_MP make_tuple_evaluated_layout th)) >> gvs[] >>
  Q.UNDISCH_THEN `compile_expr cenv ty
    (Builtin (TupleT tys) (MakeArray NONE bnd) args) sa = (vv,sb)`
    (fn th => assume_tac th >>
      qx_choosel_then [`ba`,`sm`,`out`] strip_assume_tac
        (SIMP_RULE (srw_ss()) [exprLoweringTheory.tuple_literal_types_def]
          (MATCH_MP compile_tuple_literal_inv th))) >>
  Q.UNDISCH_THEN `compile_expr cenv ty
    (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE bnd) args))
    shadow_sa = (vv,shadow_sb)`
    (fn th => assume_tac th >>
      qx_choosel_then [`shadow_ba`,`shadow_sm`,`shadow_out`] strip_assume_tac
        (SIMP_RULE (srw_ss()) [exprLoweringTheory.tuple_literal_types_def]
          (MATCH_MP compile_tuple_literal_inv
            (SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
               gasShadowTheory.gas_shadow_builtin_def] th)))) >>
  `ba = shadow_ba /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`nbytes` |-> `SUM (MAP (type_memory_bytes cenv) tys)`]
      gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_compile_make_tuple_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  suspend "tuple_alloc"
QED

Resume make_array_sim_full[tuple_alloc]:
  `SUM (MAP (type_memory_bytes cenv) tys) < dimword (:256)` by
    (fs[valueEncodingTheory.type_memory_size_def,wordsTheory.dimword_def] >>
     decide_tac) >>
  mp_tac (Q.INST [
    `DF` |-> `DF`,`lo` |-> `lo`,`d` |-> `d`,
    `ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,
    `cx` |-> `cx`,`env` |-> `env`,`es` |-> `es`,`st0` |-> `st0`,
    `ann` |-> `TupleT tys`,`elem_opt` |-> `NONE`,
    `bnd` |-> `bnd`,`args` |-> `args`,
    `cap` |-> `SUM (MAP (type_memory_bytes cenv) tys)`,
    `sa` |-> `sa`,`sm` |-> `sm`,`ba` |-> `ba`,
    `s0` |-> `s0`,`G0` |-> `G0`,`tn0` |-> `tn0`,`PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    make_array_init_full) >>
  (impl_tac >- simp[compileEnvTheory.type_memory_bytes_def,
    valueEncodingTheory.type_memory_size_def]) >>
  disch_then (qx_choosel_then [`q`,`w`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `out = Var q /\ shadow_out = Var q` by
    metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by
    (`ci_mono shadow_sa shadow_sm` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,pairTheory.SND] >>
     `ci_mono shadow_sm shadow_sb` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_make_tuple_cfn,
         exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  suspend "tuple_loop"
QED

Resume make_array_sim_full[tuple_loop]:
  `LIST_REL (\mt tv. type_memory_bytes cenv mt = type_memory_size tv)
      tys dtvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     rewrite_tac[listTheory.LIST_REL_EL_EQN] >> strip_tac >> simp[] >>
     rpt strip_tac >> irule expr_sim_inv_memory_size >>
     qexistsl_tac [`cx`,`env`,`es`] >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,`d` |-> `d`,
    `ctx` |-> `ctx`,`shadow_ctx` |-> `shadow_ctx`,`PG` |-> `PG`,
    `tops` |-> `tops`,`func` |-> `func`,`shadow_func` |-> `shadow_func`,
    `cenv` |-> `cenv`,`cx` |-> `cx`,`env` |-> `env`,`st0` |-> `st0`,
    `ebase` |-> `es`,`csbase` |-> `sa`,`sbase` |-> `s0`,
    `Gbase` |-> `G0`,`tnbase` |-> `tn0`,
    `aid` |-> `sa.cs_next_id`,`base` |-> `w2n (w:256 word)`,
    `cap` |-> `SUM (MAP (type_memory_bytes cenv) tys)`,`q` |-> `q`]
    (Q.SPECL [`args`,`tys`,`dtvs`,`0`,`[]`,`sm`,`sb`,
      `shadow_sm`,`shadow_sb`,`es`,`s1`,`G1`,`tn1`] make_array_loop_full)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> metis_tac[])) >>
  disch_tac >> suspend "tuple_wrap"
QED

Resume make_array_sim_full[tuple_wrap]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _
    (eval_exprs cx args) (es,s1,G1,tn1) loopQ loopR` >>
  qabbrev_tac `wrap = (\rr : value list + exception.
    case rr of INL vs => INL (Value (ArrayV (TupleV vs)))
      | INR ex => INR ex)` >>
  `!ee0. eval_expr cx (Builtin (TupleT tys) (MakeArray NONE bnd) args) ee0 =
     (wrap (FST (eval_exprs cx args ee0)),SND (eval_exprs cx args ee0))` by
    (gen_tac >> Cases_on `eval_exprs cx args ee0` >>
     rename1 `eval_exprs cx args ee0 = (rr,ee1)` >>
     simp[Abbr `wrap`] >> irule aggregate_eval_make_tuple >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (eval_expr cx (Builtin (TupleT tys) (MakeArray NONE bnd) args))
     (es,s1,G1,tn1)
     (\H raw ee G tn t. ?res. raw = wrap res /\ loopQ H res ee G tn t)
     (\H raw ee gt r. ?res. raw = wrap res /\ loopR H res ee gt r)` by
    (ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
     qexists_tac `eval_exprs cx args` >> simp[Abbr `wrap`]) >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`G1`,`s1`,`tn1`] >>
  conj_tac >- simp[] >>
  irule gas_outcome_full_post_source >>
  first_assum (irule_at Any) >>
  conj_tac >- suspend "tuple_post" >> suspend "tuple_exit"
QED

Resume make_array_sim_full[tuple_post]:
  qx_genl_tac [`hh`,`raw`,`ee`,`Gf`,`tnf`,`t`] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopQ`,Abbr `wrap`] >>
  suspend "tuple_value"
QED

Resume make_array_sim_full[tuple_value]:
  rename1 `LIST_REL value_has_type dtvs vs` >>
  `stmt_state_rel hh ctx func cenv cx ee t /\
   storage_well_formed_on cx ee (FST hh) /\
   ghost_inv_at (DF hh) lo d cenv cx ee Gf tnf t` by metis_tac[] >>
  `LENGTH vs = LENGTH dtvs` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  `val_wf (TupleTV dtvs) (ArrayV (TupleV vs))` by
    simp[valueEncodingDefsTheory.val_wf_def,
      typedCopyOriginPtrFieldsTheory.tuple_val_wf_LIST_REL] >>
  `val_footprint (TupleTV dtvs) (ArrayV (TupleV vs)) <=
     type_memory_size_list dtvs /\
   val_store_size (TupleTV dtvs) (ArrayV (TupleV vs)) <=
     type_memory_size_list dtvs` by
    metis_tac[exprSimPropsTheory.val_footprint_le,
      exprSimPropsTheory.val_store_size_le,valueEncodingTheory.type_memory_size_def] >>
  `!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
       val_in_memory (TupleTV dtvs) (ArrayV (TupleV vs)) (w2n w) m` by
    simp[valueEncodingPropsTheory.val_in_memory_tuple] >>
  `val_in_memory (TupleTV dtvs) (ArrayV (TupleV vs)) (w2n w) t.vs_memory` by
    (first_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `!name b n. local_region cenv es.scopes s1 name b n <=>
             local_region cenv es.scopes s0 name b n` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size_list dtvs))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  `~expr_has_effect (Builtin (TupleT tys) (MakeArray NONE bnd) args) ==>
     pure_frame cenv func es sa s0 t` by
    (strip_tac >>
     qpat_assum `EVERY ($~ o expr_has_effect) args ==> _` mp_tac >>
     (impl_tac >-
       (Q.UNDISCH_TAC `~expr_has_effect
          (Builtin (TupleT tys) (MakeArray NONE bnd) args)` >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [loweringPostsTheory.expr_has_effect_thm,
          listTheory.EVERY_MEM,listTheory.EXISTS_MEM,combinTheory.o_DEF] >>
        metis_tac[])) >> strip_tac >>
     mp_tac (Q.SPECL [`cenv`,`func`,`es`,`sa`,`sm`,`s0`,`s1`,`t`,
       `[Lit (n2w (type_memory_size_list dtvs))]`,
       `[STRING #"%" (toString sa.cs_next_var)]`,`w2n (w:256 word)`,
       `type_memory_size_list dtvs`]
       exprSimAggregateChildrenTheory.aggregate_pure_frame_buffer) >>
     (impl_tac >-
       (simp[] >> conj_tac
        >- (Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s1 name b n ==>
              mem_bytes_at b n t.vs_memory = mem_bytes_at b n s0.vs_memory` >>
            Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s1 name b n <=>
              local_region cenv es.scopes s0 name b n` >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
        qpat_assum `!p n. _ /\ _ ==> mem_bytes_at p n t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  suspend "tuple_vv_post"
QED

Resume make_array_sim_full[tuple_vv_post]:
  `!name b n. local_region cenv ee.scopes t name b n ==>
     w2n w + type_memory_size_list dtvs <= b \/ b+n <= w2n w` by
    metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  Q.UNDISCH_THEN `wb_frame cenv es ee sa s0 t`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `vv_post hh ctx func cenv cx
     (Builtin (TupleT tys) (MakeArray NONE bnd) args) es sa sb s0 ee
     (Value (ArrayV (TupleV vs)))
     (LocatedValue (TupleT tys) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [`H` |->
       `(hh : (bool # 256 word # type_value) list # num list)`]
       (Q.SPECL [`func`,`cenv`,`cx`,
         `Builtin (TupleT tys) (MakeArray NONE bnd) args`,
         `es`,`sa`,`sb`,`s0`,`ee`,`t`,`ArrayV (TupleV vs)`,
         `TupleTV dtvs`,`mk_ptr (Var q) LocMemory`,`w:256 word`,
         `type_memory_size_list dtvs`,`ctx`]
         (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           buffer_memory_vv_post_general))) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def] >>
        conj_tac
        >- (Q.UNDISCH_TAC `!name b n. local_region cenv ee.scopes t name b n ==>
              w2n w + type_memory_size_list dtvs <= b \/ b+n <= w2n w` >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
        qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa.cs_next_id /\ _ ==> mem_bytes_at off sz t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  `vv_store_bound cx (TupleT tys) (TupleT tys) ee
     (Value (ArrayV (TupleV vs)))
     (LocatedValue (TupleT tys) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [
       `H` |-> `(hh : (bool # 256 word # type_value) list # num list)`,
       `ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,`cx` |-> `cx`,
       `e` |-> `Builtin (TupleT tys) (MakeArray NONE bnd) args`,
       `es` |-> `es`,`sa` |-> `sa`,`sb` |-> `sb`,`s0` |-> `s0`,
       `es'` |-> `ee`,`tv` |-> `Value (ArrayV (TupleV vs))`,
       `vt` |-> `TupleT tys`,`p` |-> `mk_ptr (Var q) LocMemory`,
       `t` |-> `t`,`ftv` |-> `TupleTV dtvs`,`fw` |-> `w:256 word`]
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
         exprSimMemDefsTheory.vv_store_bound_capacity)) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def,
         valueEncodingTheory.type_memory_size_def] >> decide_tac)) >>
     simp[vyperASTTheory.expr_type_def]) >>
  suspend "tuple_pointers"
QED

Resume make_array_sim_full[tuple_pointers]:
  `ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) (Var q) Gf tnf t` by
    (irule ptr_val_ok_from_covers >>
     simp[] >> qexists_tac `type_memory_size_list dtvs` >>
     simp[]) >>
  `ptr_buf_ok cenv (Builtin (TupleT tys) (MakeArray NONE bnd) args)
     (Var q) Gf t` by
    (irule ptr_buf_ok_from_covers >>
     qexistsl_tac [`type_memory_size_list dtvs`,`tnf`] >>
     simp[exprLoweringTheory.lowered_value_type_def,
       valueEncodingTheory.type_memory_size_def]) >>
  fs[bodyPtrDefsTheory.ptr_vv_ok_def,bodyPtrDefsTheory.ptr_val_ok_def,
    contextTheory.mk_ptr_def,contextTheory.vv_location_def,
    vyperStateTheory.read_result_def,
    vyperStateTheory.return_def]
QED

Resume make_array_sim_full[tuple_exit]:
  rpt gen_tac >> BETA_TAC >>
  disch_then (qx_choose_then `oldres` strip_assume_tac) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopR`,Abbr `wrap`,exprSimDefsTheory.expr_exit_success_map]
QED

Resume make_array_sim_full[array]:
  rename1 `expr_body_pre cenv cx env
    (Builtin a (MakeArray (SOME et) bnd) args) es` >>
  Q.UNDISCH_THEN `expr_body_pre cenv cx env
    (Builtin a (MakeArray (SOME et) bnd) args) es`
    (fn th => assume_tac th >>
      qx_choose_then `tv` strip_assume_tac
        (MATCH_MP make_array_evaluated_layout th)) >> gvs[] >>
  Q.UNDISCH_THEN `compile_expr cenv ty
    (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) sa = (vv,sb)`
    (fn th => assume_tac th >>
      qx_choosel_then [`ba`,`sm`,`out`] strip_assume_tac
        (MATCH_MP compile_array_literal_inv th)) >>
  Q.UNDISCH_THEN `compile_expr cenv ty
    (gas_shadow_expr (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args))
    shadow_sa = (vv,shadow_sb)`
    (fn th => assume_tac th >>
      qx_choosel_then [`shadow_ba`,`shadow_sm`,`shadow_out`] strip_assume_tac
        (MATCH_MP compile_array_literal_inv
          (SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
             gasShadowTheory.gas_shadow_builtin_def] th))) >>
  `ba = shadow_ba /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`nbytes` |-> `type_memory_bytes cenv (ArrayT et bnd)`]
      gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_compile_make_array_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `type_memory_bytes cenv (ArrayT et bnd) < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  mp_tac (Q.INST [
    `DF` |-> `DF`,`lo` |-> `lo`,`d` |-> `d`,
    `ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,
    `cx` |-> `cx`,`env` |-> `env`,`es` |-> `es`,`st0` |-> `st0`,
    `ann` |-> `ArrayT et bnd`,`elem_opt` |-> `SOME et`,
    `bnd` |-> `bnd`,`args` |-> `args`,
    `cap` |-> `type_memory_bytes cenv (ArrayT et bnd)`,
    `sa` |-> `sa`,`sm` |-> `sm`,`ba` |-> `ba`,
    `s0` |-> `s0`,`G0` |-> `G0`,`tn0` |-> `tn0`,`PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `out = Var q /\ shadow_out = Var q` by
    metis_tac[exprOperandVarTheory.compiler_make_array_result] >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by
    (`ci_mono shadow_sa shadow_sm` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,pairTheory.SND] >>
     `ci_mono shadow_sm shadow_sb` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_make_array_cfn,
         exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  suspend "array_header"
QED

Resume make_array_sim_full[array_header]:
  Cases_on `bnd`
  >- suspend "fixed" >> suspend "dynamic"
QED

Resume make_array_sim_full[fixed]:
  rename1 `compatible_bound (Fixed n) (LENGTH (args:expr list))` >>
  `n = LENGTH (args:expr list)` by fs[vyperValueTheory.compatible_bound_def] >>
  gvs[exprLoweringTheory.compile_make_array_def,
    compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def,
    compileEnvTheory.comp_ignore_bind_def,
    exprSimAggregateLoopsTheory.compile_make_array_elems_as_tuple] >>
  `OPT_MMAP (evaluate_type (get_tenv cx))
      (REPLICATE (LENGTH (args:expr list)) et) = SOME (REPLICATE (LENGTH (args:expr list)) tv)` by
    (Q.SPEC_TAC (`LENGTH (args:expr list)`,`n`) >> Induct >>
     simp[rich_listTheory.REPLICATE]) >>
  `LIST_REL (\mt e. arg_type_fits (expr_type e) mt)
      (REPLICATE (LENGTH (args:expr list)) et) args` by
    fs[listTheory.LIST_REL_EL_EQN,rich_listTheory.EL_REPLICATE,
      listTheory.EVERY_EL] >>
  `LIST_REL (\mt dtv. type_memory_bytes cenv mt = type_memory_size dtv)
      (REPLICATE (LENGTH (args:expr list)) et) (REPLICATE (LENGTH (args:expr list)) tv)` by
    simp[listTheory.LIST_REL_EL_EQN,rich_listTheory.EL_REPLICATE] >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,`d` |-> `d`,
    `ctx` |-> `ctx`,`shadow_ctx` |-> `shadow_ctx`,`PG` |-> `PG`,
    `tops` |-> `tops`,`func` |-> `func`,`shadow_func` |-> `shadow_func`,
    `cenv` |-> `cenv`,`cx` |-> `cx`,`env` |-> `env`,`st0` |-> `st0`,
    `ebase` |-> `es`,`csbase` |-> `sa`,`sbase` |-> `s0`,
    `Gbase` |-> `G0`,`tnbase` |-> `tn0`,
    `aid` |-> `sa.cs_next_id`,`base` |-> `w2n (w:256 word)`,
    `cap` |-> `type_memory_size (ArrayTV tv (Fixed (LENGTH (args:expr list))))`,
    `q` |-> `q`]
    (Q.SPECL [`args`,`REPLICATE (LENGTH (args:expr list)) et`,
      `REPLICATE (LENGTH (args:expr list)) tv`,`0`,`[]`,`sm`,`sb`,
      `shadow_sm`,`shadow_sb`,`es`,`s1`,`G1`,`tn1`] make_array_loop_full)) >>
  (impl_tac >-
    (fs[exprSimAggregateEncodingTheory.type_memory_size_list_replicate,
       valueEncodingTheory.type_memory_size_def] >>
     rpt conj_tac >> metis_tac[])) >>
  disch_tac >> suspend "fixed_wrap"
QED

Resume make_array_sim_full[fixed_wrap]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _
    (eval_exprs cx args) (es,s1,G1,tn1) loopQ loopR` >>
  qabbrev_tac `wrap = (\rr : value list + exception.
    case rr of INL vs =>
      INL (Value (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs)))
      | INR ex => INR ex)` >>
  `!ee0. eval_expr cx
     (Builtin (ArrayT et (Fixed (LENGTH (args:expr list))))
       (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args) ee0 =
     (wrap (FST (eval_exprs cx args ee0)),SND (eval_exprs cx args ee0))` by
    (gen_tac >> Cases_on `eval_exprs cx args ee0` >>
     rename1 `eval_exprs cx args ee0 = (rr,ee1)` >>
     simp[Abbr `wrap`] >> irule aggregate_eval_make_array >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (eval_expr cx (Builtin (ArrayT et (Fixed (LENGTH (args:expr list))))
       (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args))
     (es,s1,G1,tn1)
     (\H raw ee G tn t. ?res. raw = wrap res /\ loopQ H res ee G tn t)
     (\H raw ee gt r. ?res. raw = wrap res /\ loopR H res ee gt r)` by
    (ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
     qexists_tac `eval_exprs cx args` >> simp[Abbr `wrap`]) >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`G1`,`s1`,`tn1`] >>
  conj_tac >- simp[] >>
  irule gas_outcome_full_post_source >>
  first_assum (irule_at Any) >>
  conj_tac >- suspend "fixed_post" >> suspend "fixed_exit"
QED

Resume make_array_sim_full[fixed_post]:
  qx_genl_tac [`hh`,`raw`,`ee`,`Gf`,`tnf`,`t`] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopQ`,Abbr `wrap`] >>
  suspend "fixed_value"
QED

Resume make_array_sim_full[fixed_value]:
  rename1 `LIST_REL value_has_type (REPLICATE (LENGTH (args:expr list)) tv) vs` >>
  `LENGTH vs = LENGTH (args:expr list)` by metis_tac[listTheory.LIST_REL_LENGTH,
    rich_listTheory.LENGTH_REPLICATE] >>
  `stmt_state_rel hh ctx func cenv cx ee t /\
   storage_well_formed_on cx ee (FST hh) /\
   ghost_inv_at (DF hh) lo d cenv cx ee Gf tnf t` by metis_tac[] >>
  `val_wf (ArrayTV tv (Fixed (LENGTH (args:expr list))))
      (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs))` by
    (rewrite_tac[vyperValueTheory.make_array_value_def] >>
     irule entryAggregateValuePackagingTheory.entry_fixed_array_wf >>
     simp[typedCopyOriginPtrFieldsTheory.tuple_val_wf_LIST_REL]) >>
  `val_footprint (ArrayTV tv (Fixed (LENGTH (args:expr list))))
       (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs)) <=
       LENGTH (args:expr list) * type_memory_size tv /\
   val_store_size (ArrayTV tv (Fixed (LENGTH (args:expr list))))
       (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs)) <=
       LENGTH (args:expr list) * type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le,
      exprSimPropsTheory.val_store_size_le,valueEncodingTheory.type_memory_size_def] >>
  `!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
       val_in_memory (ArrayTV tv (Fixed (LENGTH (args:expr list))))
         (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs)) (w2n w) m` by
    (rpt strip_tac >> irule exprSimAggregateEncodingTheory.fixed_array_from_dense >>
     simp[] >>
     rewrite_tac[GSYM exprSimAggregateEncodingTheory.tuple_in_memory_replicate_elems] >>
     metis_tac[]) >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH (args:expr list))))
     (ArrayV (make_array_value tv (Fixed (LENGTH (args:expr list))) vs)) (w2n w) t.vs_memory` by
    (first_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  suspend "fixed_frame"
QED

Resume make_array_sim_full[fixed_frame]:
  `!name b n. local_region cenv es.scopes s1 name b n <=>
             local_region cenv es.scopes s0 name b n` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size (ArrayTV tv (Fixed (LENGTH (args:expr list))))))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  `~expr_has_effect (Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args) ==>
     pure_frame cenv func es sa s0 t` by
    (strip_tac >>
     qpat_assum `EVERY ($~ o expr_has_effect) args ==> _` mp_tac >>
     (impl_tac >-
       (Q.UNDISCH_TAC `~expr_has_effect
          (Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args)` >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [loweringPostsTheory.expr_has_effect_thm,
          listTheory.EVERY_MEM,listTheory.EXISTS_MEM,combinTheory.o_DEF] >>
        metis_tac[])) >> strip_tac >>
     mp_tac (Q.SPECL [`cenv`,`func`,`es`,`sa`,`sm`,`s0`,`s1`,`t`,
       `[Lit (n2w (type_memory_size (ArrayTV tv (Fixed (LENGTH (args:expr list))))))]`,
       `[STRING #"%" (toString sa.cs_next_var)]`,`w2n (w:256 word)`,
       `type_memory_size (ArrayTV tv (Fixed (LENGTH (args:expr list))))`]
       exprSimAggregateChildrenTheory.aggregate_pure_frame_buffer) >>
     (impl_tac >-
       (simp[] >> conj_tac
        >- (Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s1 name b n ==>
              mem_bytes_at b n t.vs_memory = mem_bytes_at b n s0.vs_memory` >>
            Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s1 name b n <=>
              local_region cenv es.scopes s0 name b n` >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
        qpat_assum `!p n. _ /\ _ ==> mem_bytes_at p n t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  suspend "fixed_vv_post"
QED

Resume make_array_sim_full[fixed_vv_post]:
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  `!name b n. local_region cenv ee.scopes t name b n ==>
     w2n w + type_memory_size (ArrayTV etv (Fixed (LENGTH (args:expr list)))) <= b \/ b+n <= w2n w` by
    metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  Q.UNDISCH_THEN `wb_frame cenv es ee sa s0 t`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `vv_post hh ctx func cenv cx
     (Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args) es sa sb s0 ee
     (Value (ArrayV (make_array_value etv (Fixed (LENGTH (args:expr list))) vs)))
     (LocatedValue (ArrayT et (Fixed (LENGTH (args:expr list)))) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [`H` |->
       `(hh : (bool # 256 word # type_value) list # num list)`]
       (Q.SPECL [`func`,`cenv`,`cx`,
         `Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args`,
         `es`,`sa`,`sb`,`s0`,`ee`,`t`,`ArrayV (make_array_value etv (Fixed (LENGTH (args:expr list))) vs)`,
         `ArrayTV etv (Fixed (LENGTH (args:expr list)))`,`mk_ptr (Var q) LocMemory`,`w:256 word`,
         `type_memory_size (ArrayTV etv (Fixed (LENGTH (args:expr list))))`,`ctx`]
         (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           buffer_memory_vv_post_general))) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def] >>
        conj_tac
        >- (Q.UNDISCH_TAC `!name b n. local_region cenv ee.scopes t name b n ==>
              w2n w + type_memory_size (ArrayTV etv (Fixed (LENGTH (args:expr list)))) <= b \/ b+n <= w2n w` >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
        qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa.cs_next_id /\ _ ==> mem_bytes_at off sz t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  `vv_store_bound cx (ArrayT et (Fixed (LENGTH (args:expr list)))) (ArrayT et (Fixed (LENGTH (args:expr list)))) ee
     (Value (ArrayV (make_array_value etv (Fixed (LENGTH (args:expr list))) vs)))
     (LocatedValue (ArrayT et (Fixed (LENGTH (args:expr list)))) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [
       `H` |-> `(hh : (bool # 256 word # type_value) list # num list)`,
       `ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,`cx` |-> `cx`,
       `e` |-> `Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args`,
       `es` |-> `es`,`sa` |-> `sa`,`sb` |-> `sb`,`s0` |-> `s0`,
       `es'` |-> `ee`,`tv` |-> `Value (ArrayV (make_array_value etv (Fixed (LENGTH (args:expr list))) vs))`,
       `vt` |-> `ArrayT et (Fixed (LENGTH (args:expr list)))`,`p` |-> `mk_ptr (Var q) LocMemory`,
       `t` |-> `t`,`ftv` |-> `ArrayTV etv (Fixed (LENGTH (args:expr list)))`,`fw` |-> `w:256 word`]
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
         exprSimMemDefsTheory.vv_store_bound_capacity)) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def,
         valueEncodingTheory.type_memory_size_def] >> decide_tac)) >>
     simp[vyperASTTheory.expr_type_def]) >>
  suspend "fixed_pointers"
QED

Resume make_array_sim_full[fixed_pointers]:
  `ptr_val_ok cx (ArrayT et (Fixed (LENGTH (args:expr list)))) (ArrayV (make_array_value etv (Fixed (LENGTH (args:expr list))) vs)) (Var q) Gf tnf t` by
    (irule ptr_val_ok_from_covers >>
     simp[] >> qexists_tac `type_memory_size (ArrayTV etv (Fixed (LENGTH (args:expr list))))` >>
     simp[]) >>
  `ptr_buf_ok cenv (Builtin (ArrayT et (Fixed (LENGTH (args:expr list)))) (MakeArray (SOME et) (Fixed (LENGTH (args:expr list)))) args)
     (Var q) Gf t` by
    (irule ptr_buf_ok_from_covers >>
     qexistsl_tac [`type_memory_size (ArrayTV etv (Fixed (LENGTH (args:expr list))))`,`tnf`] >>
     simp[exprLoweringTheory.lowered_value_type_def,
       valueEncodingTheory.type_memory_size_def]) >>
  fs[bodyPtrDefsTheory.ptr_vv_ok_def,bodyPtrDefsTheory.ptr_val_ok_def,
    contextTheory.mk_ptr_def,contextTheory.vv_location_def,
    vyperStateTheory.read_result_def,
    vyperStateTheory.return_def]
QED

Resume make_array_sim_full[fixed_exit]:
  rpt gen_tac >> BETA_TAC >>
  disch_then (qx_choose_then `oldres` strip_assume_tac) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopR`,Abbr `wrap`,exprSimDefsTheory.expr_exit_success_map]
QED

Resume make_array_sim_full[dynamic]:
  rename1 `compatible_bound (Dynamic n) (LENGTH args)` >>
  gvs[exprLoweringTheory.compile_make_array_def,
    compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.comp_bind_def,
    AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var q; Lit (n2w (LENGTH args))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u,cm)` >> Cases_on `u` >> gvs[] >>
  Cases_on `emit_void MSTORE [Var q; Lit (n2w (LENGTH args))] shadow_sm` >>
  rename1 `emit_void MSTORE _ shadow_sm = (u,shadow_cm)` >>
  Cases_on `u` >> gvs[] >>
  `gas_shadow_state cm shadow_cm` by
    (mp_tac (Q.INST [`opc` |-> `MSTORE`,
       `ops` |-> `[Var q; Lit (n2w (LENGTH (args:expr list)))]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_void) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`args`,`0`] (Q.INST [
    `cfn` |-> `compile_expr`,`ce` |-> `cenv`,`elem_ty` |-> `et`,
    `header` |-> `T`,`buf` |-> `Var q`]
    exprSimAggregateLoopsTheory.compile_make_array_elems_as_tuple)) >>
  simp[] >> disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  mp_tac (Q.SPECL [`MAP gas_shadow_expr args`,`0`] (Q.INST [
    `cfn` |-> `compile_expr`,`ce` |-> `cenv`,`elem_ty` |-> `et`,
    `header` |-> `T`,`buf` |-> `Var q`]
    exprSimAggregateLoopsTheory.compile_make_array_elems_as_tuple)) >>
  simp[] >> disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `ci_mono sm cm /\ ci_mono cm sb /\
   ci_mono shadow_sm shadow_cm /\ ci_mono shadow_cm shadow_sb` by
    (rpt conj_tac >> metis_tac[exprLoweringPropsTheory.ci_mono_emit_void,
      exprLoweringPropsTheory.ci_mono_compile_make_tuple_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND]) >>
  `fn_has_code sm cm func /\ fn_has_code cm sb func /\
   fn_has_code shadow_sm shadow_cm shadow_func /\
   fn_has_code shadow_cm shadow_sb shadow_func` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  suspend "dynamic_store"
QED

Resume make_array_sim_full[dynamic_store]:
  `32 <= type_memory_size (ArrayTV tv (Dynamic n))` by
    simp[valueEncodingTheory.type_memory_size_def] >>
  `w2n w + 32 < dimword (:256) /\
   w2n w + 32 <= s1.vs_alloca_next` by decide_tac >>
  `ptr_covers G1 tn1 q s1 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size (ArrayTV tv (Dynamic n))` >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `ghost_inv_at (DF (storage_trace_horizon es.storage_trace)) lo d
     cenv cx es G1 tn1 s1` by metis_tac[] >>
  `lo <= s1.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ G1 tn1 s1`
       (strip_assume_tac o REWRITE_RULE[bodyPtrDefsTheory.ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  `compile_store_memory cenv (Lit (n2w (LENGTH args))) (Var q)
     (BaseT (UintT 256)) (BaseT (UintT 256)) sm = ((),cm)` by
    simp[contextTheory.compile_store_memory_def,compileEnvTheory.is_word_type_def] >>
  qabbrev_tac `hv = IntV (&(w2n (n2w (LENGTH args):256 word)))` >>
  `value_has_type (BaseTV (UintT 256)) hv` by
    simp[Abbr `hv`,vyperTypingTheory.value_has_type_def,
      wordsTheory.dimword_def] >>
  `typed_val_to_w256 (BaseTV (UintT 256)) hv =
      (n2w (LENGTH args):256 word)` by
    simp[Abbr `hv`,valueEncodingTheory.typed_val_to_w256_def,
      valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_def] >>
  mp_tac (Q.INST [
    `sa` |-> `sm`,`sb` |-> `cm`,`s` |-> `s1`,`G` |-> `G1`,`tn` |-> `tn1`,
    `lo` |-> `lo`,`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`,`cenv` |-> `cenv`,
    `src` |-> `Lit (n2w (LENGTH (args:expr list)))`,`xd` |-> `q`,
    `dw` |-> `w:256 word`,`tenv` |-> `get_tenv cx`,
    `dty` |-> `BaseT (UintT 256)`,`sty` |-> `BaseT (UintT 256)`,
    `dtv` |-> `BaseTV (UintT 256)`,`v` |-> `hv`]
    logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path) >>
  (impl_tac >-
    simp[compileEnvTheory.is_word_type_def,vyperValueTheory.evaluate_type_def,
      venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def]) >>
  disch_then (qx_choosel_then [`s2`,`G2`,`tn2`] strip_assume_tac) >>
  suspend "dynamic_packet"
QED

Resume make_array_sim_full[dynamic_packet]:
  qpat_assum `typed_copy_state_frame sm (w2n w) 32 s1 s2`
    (strip_assume_tac o REWRITE_RULE
      [typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def]) >>
  `s2.vs_allocas = s1.vs_allocas /\
   s2.vs_alloca_next = s1.vs_alloca_next /\
   s2.vs_accounts = s1.vs_accounts /\
   s2.vs_transient = s1.vs_transient /\
   s2.vs_requests = s1.vs_requests /\
   s2.vs_call_ctx = s1.vs_call_ctx /\
   s2.vs_immutables = s1.vs_immutables` by
    (qpat_assum `(s2 with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory;
       vs_prev_bb := s1.vs_prev_bb; vs_current_bb := s1.vs_current_bb;
       vs_inst_idx := s1.vs_inst_idx|>) = s1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomStateTheory.venom_state_component_equality] >>
     strip_tac >> simp[]) >>
  `lookup_var q s2 = SOME w` by metis_tac[] >>
  `ptr_covers G2 tn2 q s2 (type_memory_size (ArrayTV tv (Dynamic n)))` by
    (qpat_assum `ptr_covers G1 tn1 q s1
       (type_memory_size (ArrayTV tv (Dynamic n)))` mp_tac >>
     qpat_assum `!p. FLOOKUP G2 p = FLOOKUP G1 p /\ _` mp_tac >>
     qpat_assum `lookup_var q s1 = SOME w` mp_tac >>
     qpat_assum `lookup_var q s2 = SOME w` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo s1` mp_tac >>
     qpat_assum `FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (w2n w,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `allocas_from lo s2 /\ lo <= s2.vs_alloca_next` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es s1` by metis_tac[] >>
  `alloca_inv s1` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `gas_path_mem ctx func s1 0 (OK s2)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s1,G1,tn1) [] (OK s2,G2,tn2)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_history func s2` by
    (irule fragGasPathFrameMemTheory.gas_path_mem_zero_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ctx`,`s1`] >> simp[] >>
     rpt strip_tac >> irule bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >>
     goal_assum (drule_at Any) >> simp[]) >>
  suspend "dynamic_frames"
QED

Resume make_array_sim_full[dynamic_frames]:
  `sm.cs_next_var <= cm.cs_next_var /\ sm.cs_next_id <= cm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv cm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `not_fresh_at cm q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name b len. local_region cenv es.scopes s1 name b len ==>
     b+len <= w2n w \/ w2n w+32 <= b` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
       regions_disjoint _ _ b len` (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `32 <= type_memory_size (ArrayTV tv (Dynamic n))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `cenv.ce_module = NONE /\ cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY)` by
    (qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodySimTheory.body_inv_def,bodySimTheory.cenv_module_pins_def]) >>
  `env_consistent env cx es` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n w) 32` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace)
       ctx func cenv cx es s1` mp_tac >>
     qpat_assum `FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (w2n w,_)` mp_tac >>
     qpat_assum `32 <= type_memory_size (ArrayTV tv (Dynamic n))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.immutable_decl_sep_alt,
       loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> !name ty tv off.
       FLOOKUP _ _ = _ /\ cenv.ce_module_var_type _ = _ /\ _ ==> _`
       (mp_tac o Q.SPECL [`nm`,`ity`,`itv`,`io`] o UNDISCH) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!aid b sz. FLOOKUP s1.vs_allocas aid = SOME (b,sz) ==> _`
       (mp_tac o Q.SPECL [`sa.cs_next_id`,`w2n (w:256 word)`,
         `type_memory_size (ArrayTV tv (Dynamic n))`]) >>
     simp[] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (w2n w) 32` by
    (strip_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !nm io ity itv.
       FLOOKUP _ _ = _ /\ cenv.ce_module_var_type _ = _ /\ _ ==> _`
       (assume_tac o UNDISCH) >>
     mp_tac (Q.INST [`tops` |-> `tops`,`ctx` |-> `ctx`,`cenv` |-> `cenv`,
       `cx` |-> `cx`,`env` |-> `env`,`es` |-> `es`,`ee` |-> `es`,
       `b` |-> `w2n (w:256 word)`,`cap` |-> `32`]
       internalReturnImmutableTypesTheory.internal_return_immutable_separation) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s2` by
    (qx_gen_tac `hh` >> strip_tac >>
     `stmt_state_rel hh ctx func cenv cx es s1` by metis_tac[] >>
     mp_tac (Q.INST [
       `H` |-> `(hh : (bool # 256 word # type_value) list # num list)`,
       `s` |-> `s1`,`q` |-> `s2`,`ce` |-> `cenv`,`es` |-> `es`,
       `sa` |-> `sm`,`dst` |-> `w2n (w:256 word)`,`n` |-> `32`]
       (INST_TYPE [alpha |-> ``:256``]
         exprSimAggregateChildrenTheory.aggregate_store_control_frame)) >>
     (impl_tac >-
       (qpat_assum `stmt_state_rel hh ctx func cenv cx es s1` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sm` mp_tac >>
        qpat_assum `(s2 with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory;
          vs_prev_bb := s1.vs_prev_bb; vs_current_bb := s1.vs_current_bb;
          vs_inst_idx := s1.vs_inst_idx|>) = s1` mp_tac >>
        qpat_assum `!x. not_fresh_at sm x ==> lookup_var x s2 = lookup_var x s1` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
          mem_bytes_at a k s1.vs_memory` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
          b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
        qpat_assum `LENGTH s1.vs_memory <= LENGTH s2.vs_memory` mp_tac >>
        qpat_assum `cenv.ce_is_ctor ==> !name itv iv io.
          FLOOKUP _ _ = _ /\ FLOOKUP _ _ = _ ==>
          regions_disjoint io (type_memory_size itv) (w2n w) 32` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        rpt disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  suspend "dynamic_ghost"
QED

Resume make_array_sim_full[dynamic_ghost]:
  `local_ptrs_rel func cenv es.scopes s1` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace)
       ctx func cenv cx es s1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at sm x)` by
    (conj_tac >> rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[] >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x. not_fresh_at sm x ==> lookup_var x s2 = lookup_var x s1 /\
    FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x s2 = lookup_var x s1` mp_tac >>
     qpat_assum `!p. FLOOKUP G2 p = FLOOKUP G1 p /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!j. j < w2n w \/ w2n w+32 <= j ==>
    (j IN tn2.t_mem <=> j IN tn1.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!i. ~(w2n w <= i /\ i < w2n w+32) ==> _` irule >>
     decide_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stor_taint_ok_at (DF H) tn2 s2` by
    (qx_gen_tac `hh` >> strip_tac >>
     `ghost_inv_at (DF hh) lo d cenv cx es G1 tn1 s1` by metis_tac[] >>
     qpat_assum `ghost_inv_at (DF hh) lo d cenv cx es G1 tn1 s1` mp_tac >>
     qpat_assum `s2.vs_accounts = s1.vs_accounts` mp_tac >>
     qpat_assum `s2.vs_transient = s1.vs_transient` mp_tac >>
     qpat_assum `s2.vs_call_ctx = s1.vs_call_ctx` mp_tac >>
     qpat_assum `s2.vs_immutables = s1.vs_immutables` mp_tac >>
     qpat_assum `tn2.t_stor = tn1.t_stor` mp_tac >>
     qpat_assum `tn2.t_trans = tn1.t_trans` mp_tac >>
     qpat_assum `tn2.t_imm = tn1.t_imm` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def,bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G2 tn2 s2` by
    (qx_gen_tac `hh` >> strip_tac >>
     `ghost_inv_at (DF hh) lo d cenv cx es G1 tn1 s1` by metis_tac[] >>
     `stor_taint_ok_at (DF hh) tn2 s2` by metis_tac[] >>
     mp_tac (Q.INST [
       `D` |-> `DF (hh : (bool # bytes32 # type_value) list # num list)`,
       `G` |-> `G1`,`tn` |-> `tn1`,`s` |-> `s1`,`H` |-> `G2`,
       `tf` |-> `tn2`,`z` |-> `s2`,`es` |-> `es`,`sa` |-> `sm`,
       `start` |-> `w2n (w:256 word)`,`nb` |-> `32`]
       (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at)) >>
     (impl_tac >-
       (qpat_assum `ghost_inv_at (DF hh) lo d cenv cx es G1 tn1 s1` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sm` mp_tac >>
        qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x` mp_tac >>
        qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x` mp_tac >>
        qpat_assum `local_ptrs_rel func cenv es.scopes s1` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
          b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
        qpat_assum `!x. not_fresh_at sm x ==> lookup_var x s2 = lookup_var x s1 /\ _` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
          mem_bytes_at a k s1.vs_memory` mp_tac >>
        qpat_assum `!j. j < w2n w \/ w2n w+32 <= j ==> _` mp_tac >>
        qpat_assum `lo <= w2n w` mp_tac >>
        qpat_assum `stor_taint_ok_at (DF hh) tn2 s2` mp_tac >>
        qpat_assum `allocas_from lo s2` mp_tac >>
        qpat_assum `lo <= s2.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >> simp[]) >>
  suspend "dynamic_baseline"
QED

Resume make_array_sim_full[dynamic_baseline]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!name b len. local_region cenv es.scopes s1 name b len <=>
    local_region cenv es.scopes s0 name b len` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at sa p` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
    b+len <= w2n w \/ w2n w+32 <= b` by
    (qpat_assum `!name b len. local_region cenv es.scopes s1 name b len <=> _` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
       b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!aid b len. aid < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
    b+len <= w2n w \/ w2n w+32 <= b` by
    (rpt strip_tac >>
     qpat_assum `!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s0.vs_allocas aid = SOME (b,len) ==> regions_disjoint _ _ b len`
       (qspecl_then [`aid`,`b`,`len`] mp_tac) >>
     (impl_tac >- simp[]) >>
     qpat_assum `32 <= type_memory_size (ArrayTV tv (Dynamic n))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s0 /\
    FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `!a k. a+k <= w2n w \/ w2n w+32 <= a ==>
    mem_bytes_at a k s2.vs_memory = mem_bytes_at a k s0.vs_memory` by
    (qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
       mem_bytes_at a k s1.vs_memory` mp_tac >>
     qpat_assum `s1.vs_memory = s0.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP s2.vs_allocas aid = SOME entry` by
    (qpat_assum `!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==> _` mp_tac >>
     qpat_assum `s2.vs_allocas = s1.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `wb_frame cenv es es sa s0 s2` by
    (mp_tac (Q.INST [`s` |-> `s0`,`z` |-> `s2`,`sa` |-> `sa`,
       `es` |-> `es`,`start` |-> `w2n (w:256 word)`,`nb` |-> `32`]
       bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_wb_frame) >>
     (impl_tac >-
       (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s0 /\ _` mp_tac >>
        qpat_assum `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> _` mp_tac >>
        qpat_assum `!aid b len. aid < sa.cs_next_id /\
          FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
          b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==>
          b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
          mem_bytes_at a k s0.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >> simp[]) >>
  `return_buf_frame d cenv cm s2` by
    (mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sm`,`cm`,`s1`,`s2`]
       bodyMemoryDefsTheory.return_buf_frame_frame) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
  suspend "dynamic_kept"
QED

Resume make_array_sim_full[dynamic_kept]:
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (mp_tac (Q.INST [`Gi` |-> `G0`,`ti` |-> `tn0`,`s0` |-> `s0`,
       `G` |-> `G1`,`tn` |-> `tn1`,`H` |-> `G2`,`tf` |-> `tn2`,
       `es` |-> `es`,`sa` |-> `sa`]
       (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at)) >>
     (impl_tac >-
       (rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s0 /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[])
        >- (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
            `off+sz <= w2n w \/ w2n w+32 <= off` by
              (qpat_assum `!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
                 b+len <= w2n w \/ w2n w+32 <= b`
                 (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
            qpat_assum `!j. j < w2n w \/ w2n w+32 <= j ==> _`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- decide_tac) >> simp[])
        >- (qx_genl_tac [`name`,`off`,`sz`,`i`] >> strip_tac >>
            `off+sz <= w2n w \/ w2n w+32 <= off` by
              (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==>
                 b+len <= w2n w \/ w2n w+32 <= b`
                 (qspecl_then [`name`,`off`,`sz`] mp_tac) >> simp[]) >>
            qpat_assum `!j. j < w2n w \/ w2n w+32 <= j ==> _`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- decide_tac) >> simp[])
        >- (qx_gen_tac `i` >> strip_tac >>
            qpat_assum `!j. j < w2n w \/ w2n w+32 <= j ==> _`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- decide_tac) >> simp[]))) >> simp[]) >>
  `!name b len. local_region cenv es.scopes s2 name b len <=>
    local_region cenv es.scopes s1 name b len` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at sm p` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s2 name b len ==>
    regions_disjoint (w2n w) (type_memory_size (ArrayTV tv (Dynamic n))) b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s1 name b len` by metis_tac[] >>
     qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
       regions_disjoint _ _ b len`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >> simp[]) >>
  `val_wf (BaseTV (UintT 256)) hv` by
    metis_tac[exprSimAggregateChildrenTheory.typed_value_wf] >>
  `val_footprint (BaseTV (UintT 256)) hv <= 32` by
    metis_tac[exprSimPropsTheory.val_footprint_le,
      valueEncodingTheory.type_memory_size_def] >>
  `OPT_MMAP (evaluate_type (get_tenv cx))
      (REPLICATE (LENGTH (args:expr list)) et) = SOME (REPLICATE (LENGTH (args:expr list)) tv)` by
    (Q.SPEC_TAC (`LENGTH (args:expr list)`,`k`) >> Induct >>
     simp[rich_listTheory.REPLICATE]) >>
  `LIST_REL (\mt e. arg_type_fits (expr_type e) mt)
      (REPLICATE (LENGTH (args:expr list)) et) args` by
    fs[listTheory.LIST_REL_EL_EQN,rich_listTheory.EL_REPLICATE,
      listTheory.EVERY_EL] >>
  `LIST_REL (\mt dtv. type_memory_bytes cenv mt = type_memory_size dtv)
      (REPLICATE (LENGTH (args:expr list)) et) (REPLICATE (LENGTH (args:expr list)) tv)` by
    simp[listTheory.LIST_REL_EL_EQN,rich_listTheory.EL_REPLICATE] >>
  suspend "dynamic_loop"
QED

Resume make_array_sim_full[dynamic_loop]:
  `ptr_covers G2 tn2 q s2 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size (ArrayTV tv (Dynamic n))` >> simp[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
    regions_disjoint (w2n w) 32 b len` by
    (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==>
       b+len <= w2n w \/ w2n w+32 <= b` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
    regions_disjoint (w2n w) (type_memory_size (ArrayTV tv (Dynamic n))) b len` by
    (qpat_assum `!name b len. local_region cenv es.scopes s1 name b len <=> _` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==>
       regions_disjoint _ _ b len` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,`d` |-> `d`,
    `ctx` |-> `ctx`,`shadow_ctx` |-> `shadow_ctx`,`PG` |-> `PG`,
    `tops` |-> `tops`,`func` |-> `func`,`shadow_func` |-> `shadow_func`,
    `cenv` |-> `cenv`,`cx` |-> `cx`,`env` |-> `env`,`st0` |-> `st0`,
    `ebase` |-> `es`,`csbase` |-> `sa`,`sbase` |-> `s0`,
    `Gbase` |-> `G0`,`tnbase` |-> `tn0`,
    `aid` |-> `sa.cs_next_id`,`base` |-> `w2n (w:256 word)`,
    `cap` |-> `type_memory_size (ArrayTV tv (Dynamic n))`,`q` |-> `q`]
    (Q.SPECL [`args`,`REPLICATE (LENGTH (args:expr list)) et`,
      `REPLICATE (LENGTH (args:expr list)) tv`,`32`,
      `[(BaseTV (UintT 256),hv,w2n (w:256 word),32)]`,
      `cm`,`sb`,`shadow_cm`,`shadow_sb`,`es`,`s2`,`G2`,`tn2`]
      make_array_loop_full)) >>
  (impl_tac >-
    (fs[exprSimAggregateEncodingTheory.type_memory_size_list_replicate,
       valueEncodingTheory.type_memory_size_def] >>
     rpt conj_tac >> metis_tac[])) >>
  disch_tac >> suspend "dynamic_wrap"
QED

Resume make_array_sim_full[dynamic_wrap]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _
    (eval_exprs cx args) (es,s2,G2,tn2) loopQ loopR` >>
  qabbrev_tac `wrap = (\rr : value list + exception.
    case rr of INL vs =>
      INL (Value (ArrayV (make_array_value tv (Dynamic n) vs)))
      | INR ex => INR ex)` >>
  `!ee0. eval_expr cx
     (Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args) ee0 =
     (wrap (FST (eval_exprs cx args ee0)),SND (eval_exprs cx args ee0))` by
    (gen_tac >> Cases_on `eval_exprs cx args ee0` >>
     rename1 `eval_exprs cx args ee0 = (rr,ee1)` >>
     simp[Abbr `wrap`] >> irule aggregate_eval_make_array >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (eval_expr cx (Builtin (ArrayT et (Dynamic n))
       (MakeArray (SOME et) (Dynamic n)) args))
     (es,s2,G2,tn2)
     (\H raw ee G tn t. ?res. raw = wrap res /\ loopQ H res ee G tn t)
     (\H raw ee gt r. ?res. raw = wrap res /\ loopR H res ee gt r)` by
    (ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
     qexists_tac `eval_exprs cx args` >> simp[Abbr `wrap`]) >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`G1`,`s1`,`tn1`] >>
  conj_tac >- simp[] >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`G2`,`s2`,`tn2`] >>
  conj_tac >- simp[] >>
  irule gas_outcome_full_post_source >>
  first_assum (irule_at Any) >>
  conj_tac >- suspend "dynamic_post" >> suspend "dynamic_exit"
QED

Resume make_array_sim_full[dynamic_post]:
  qx_genl_tac [`hh`,`raw`,`ee`,`Gf`,`tnf`,`t`] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopQ`,Abbr `wrap`] >>
  suspend "dynamic_value"
QED

Resume make_array_sim_full[dynamic_value]:
  rename1 `LIST_REL value_has_type (REPLICATE (LENGTH (args:expr list)) tv) vs` >>
  `LENGTH vs = LENGTH (args:expr list)` by
    metis_tac[listTheory.LIST_REL_LENGTH,rich_listTheory.LENGTH_REPLICATE] >>
  `stmt_state_rel hh ctx func cenv cx ee t /\
   storage_well_formed_on cx ee (FST hh) /\
   ghost_inv_at (DF hh) lo d cenv cx ee Gf tnf t` by metis_tac[] >>
  `value_has_type (ArrayTV tv (Dynamic n))
    (ArrayV (make_array_value tv (Dynamic n) vs))` by
    (qpat_assum `LIST_REL value_has_type (REPLICATE (LENGTH (args:expr list)) tv) vs` mp_tac >>
     qpat_assum `compatible_bound (Dynamic n) (LENGTH args)` mp_tac >>
     qpat_assum `LENGTH vs = LENGTH args` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperValueTheory.make_array_value_def,
       vyperTypingTheory.value_has_type_def,vyperTypingTheory.all_have_type_EVERY,
       vyperValueTheory.compatible_bound_def,listTheory.LIST_REL_EL_EQN,
       rich_listTheory.EL_REPLICATE,listTheory.EVERY_EL]) >>
  `val_wf (ArrayTV tv (Dynamic n))
    (ArrayV (make_array_value tv (Dynamic n) vs))` by
    metis_tac[exprSimAggregateChildrenTheory.typed_value_wf] >>
  `val_footprint (ArrayTV tv (Dynamic n))
       (ArrayV (make_array_value tv (Dynamic n) vs)) <=
       type_memory_size (ArrayTV tv (Dynamic n)) /\
   val_store_size (ArrayTV tv (Dynamic n))
       (ArrayV (make_array_value tv (Dynamic n) vs)) <=
       type_memory_size (ArrayTV tv (Dynamic n))` by
    metis_tac[exprSimPropsTheory.val_footprint_le,exprSimPropsTheory.val_store_size_le] >>
  `!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic n))
      (ArrayV (make_array_value tv (Dynamic n) vs)) (w2n w) m` by
    (rpt strip_tac >>
     `val_in_memory (BaseTV (UintT 256)) hv (w2n w) m` by metis_tac[] >>
     `mem_word_at (w2n w) m = n2w (LENGTH vs)` by
       (qpat_assum `val_in_memory (BaseTV (UintT 256)) hv (w2n w) m` mp_tac >>
        qpat_assum `LENGTH vs = LENGTH args` mp_tac >>
        qpat_assum `Abbrev (hv = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[markerTheory.Abbrev_def,valueEncodingDefsTheory.val_in_memory_def,
          valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_def]) >>
     simp[vyperValueTheory.make_array_value_def,valueEncodingDefsTheory.val_in_memory_def] >>
     rewrite_tac[GSYM exprSimAggregateEncodingTheory.tuple_in_memory_replicate_elems] >>
     metis_tac[]) >>
  `val_in_memory (ArrayTV tv (Dynamic n))
    (ArrayV (make_array_value tv (Dynamic n) vs)) (w2n w) t.vs_memory` by
    (first_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  suspend "dynamic_frame"
QED

Resume make_array_sim_full[dynamic_frame]:
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size (ArrayTV tv (Dynamic n))))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  `sa.cs_next_id <= cm.cs_next_id` by decide_tac >>
  `~expr_has_effect
      (Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args) ==>
    pure_frame cenv func es sa s0 t` by
    (strip_tac >>
     qpat_assum `EVERY ($~ o expr_has_effect) args ==> _` mp_tac >>
     (impl_tac >-
       (Q.UNDISCH_TAC `~expr_has_effect
          (Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args)` >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [loweringPostsTheory.expr_has_effect_thm,
          listTheory.EVERY_MEM,listTheory.EXISTS_MEM,combinTheory.o_DEF] >>
        metis_tac[])) >> strip_tac >>
     `!name b len. local_region cenv es.scopes s0 name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory` by
       (qpat_assum `!name b len. local_region cenv es.scopes _ name b len ==>
          mem_bytes_at b len t.vs_memory = mem_bytes_at b len s2.vs_memory` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
          mem_bytes_at a k s0.vs_memory` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==>
          regions_disjoint (w2n w) 32 b len` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s2 name b len <=> _` mp_tac >>
        qpat_assum `!name b len. local_region cenv es.scopes s1 name b len <=> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
     `!p k. (p+k <= w2n w \/ w2n w+type_memory_size (ArrayTV tv (Dynamic n)) <= p) /\
       (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         cm.cs_next_id <= inst.inst_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
         regions_disjoint p k b sz) ==>
       mem_bytes_at p k t.vs_memory = mem_bytes_at p k s0.vs_memory` by
       (qx_genl_tac [`p`,`k`] >> disch_then (CONJUNCTS_THEN assume_tac) >>
        SUBGOAL_THEN ``p+k <= w2n (w:256 word) \/ w2n w+32 <= p`` ASSUME_TAC >- decide_tac >>
        qpat_assum `!p n'. _ /\ _ ==> mem_bytes_at p n' t.vs_memory =
          mem_bytes_at p n' s2.vs_memory` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k s2.vs_memory =
          mem_bytes_at a k s0.vs_memory` mp_tac >>
        qpat_assum `p+k <= w2n w \/ w2n w+32 <= p` mp_tac >>
        qpat_assum `p+k <= w2n w \/ w2n w+type_memory_size (ArrayTV tv (Dynamic n)) <= p` mp_tac >>
        qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          cm.cs_next_id <= inst.inst_id /\ _ ==> regions_disjoint p k b sz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     mp_tac (Q.SPECL [`cenv`,`func`,`es`,`sa`,`cm`,`s0`,`s0`,`t`,
       `[Lit (n2w (type_memory_size (ArrayTV tv (Dynamic n))))]`,
       `[STRING #"%" (toString sa.cs_next_var)]`,`w2n (w:256 word)`,
       `type_memory_size (ArrayTV tv (Dynamic n))`]
       exprSimAggregateChildrenTheory.aggregate_pure_frame_buffer) >>
     (impl_tac >-
       (simp[] >>
        qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==>
          mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory` mp_tac >>
        qpat_assum `!p k. _ /\ _ ==> mem_bytes_at p k t.vs_memory =
          mem_bytes_at p k s0.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  suspend "dynamic_vv_post"
QED

Resume make_array_sim_full[dynamic_vv_post]:
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  `!name b len. local_region cenv ee.scopes t name b len ==>
     w2n w + type_memory_size (ArrayTV etv (Dynamic n)) <= b \/ b+len <= w2n w` by
    (qpat_assum `!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) (type_memory_size (ArrayTV etv (Dynamic n))) b len` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  Q.UNDISCH_THEN `wb_frame cenv es ee sa s0 t`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `vv_post hh ctx func cenv cx
     (Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args) es sa sb s0 ee
     (Value (ArrayV (make_array_value etv (Dynamic n) vs)))
     (LocatedValue (ArrayT et (Dynamic n)) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [`H` |->
       `(hh : (bool # 256 word # type_value) list # num list)`]
       (Q.SPECL [`func`,`cenv`,`cx`,
         `Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args`,
         `es`,`sa`,`sb`,`s0`,`ee`,`t`,`ArrayV (make_array_value etv (Dynamic n) vs)`,
         `ArrayTV etv (Dynamic n)`,`mk_ptr (Var q) LocMemory`,`w:256 word`,
         `type_memory_size (ArrayTV etv (Dynamic n))`,`ctx`]
         (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           buffer_memory_vv_post_general))) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def] >>
        conj_tac
        >- (Q.UNDISCH_TAC `!name b len. local_region cenv ee.scopes t name b len ==>
              w2n w + type_memory_size (ArrayTV etv (Dynamic n)) <= b \/ b+len <= w2n w` >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
        qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa.cs_next_id /\ _ ==> mem_bytes_at off sz t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  `vv_store_bound cx (ArrayT et (Dynamic n)) (ArrayT et (Dynamic n)) ee
     (Value (ArrayV (make_array_value etv (Dynamic n) vs)))
     (LocatedValue (ArrayT et (Dynamic n)) (mk_ptr (Var q) LocMemory)) t` by
    (mp_tac (Q.INST [
       `H` |-> `(hh : (bool # 256 word # type_value) list # num list)`,
       `ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,`cx` |-> `cx`,
       `e` |-> `Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args`,
       `es` |-> `es`,`sa` |-> `sa`,`sb` |-> `sb`,`s0` |-> `s0`,
       `es'` |-> `ee`,`tv` |-> `Value (ArrayV (make_array_value etv (Dynamic n) vs))`,
       `vt` |-> `ArrayT et (Dynamic n)`,`p` |-> `mk_ptr (Var q) LocMemory`,
       `t` |-> `t`,`ftv` |-> `ArrayTV etv (Dynamic n)`,`fw` |-> `w:256 word`]
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
         exprSimMemDefsTheory.vv_store_bound_capacity)) >>
     (impl_tac >-
       (simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
         contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def,
         valueEncodingTheory.type_memory_size_def] >>
        fs[valueEncodingTheory.type_memory_size_def] >> decide_tac)) >>
     simp[vyperASTTheory.expr_type_def]) >>
  suspend "dynamic_pointers"
QED

Resume make_array_sim_full[dynamic_pointers]:
  `ptr_val_ok cx (ArrayT et (Dynamic n)) (ArrayV (make_array_value etv (Dynamic n) vs)) (Var q) Gf tnf t` by
    (irule ptr_val_ok_from_covers >>
     simp[] >> qexists_tac `type_memory_size (ArrayTV etv (Dynamic n))` >>
     simp[]) >>
  `ptr_buf_ok cenv (Builtin (ArrayT et (Dynamic n)) (MakeArray (SOME et) (Dynamic n)) args)
     (Var q) Gf t` by
    (irule ptr_buf_ok_from_covers >>
     qexistsl_tac [`type_memory_size (ArrayTV etv (Dynamic n))`,`tnf`] >>
     simp[exprLoweringTheory.lowered_value_type_def,
       valueEncodingTheory.type_memory_size_def]) >>
  fs[bodyPtrDefsTheory.ptr_vv_ok_def,bodyPtrDefsTheory.ptr_val_ok_def,
    contextTheory.mk_ptr_def,contextTheory.vv_location_def,
    vyperStateTheory.read_result_def,
    vyperStateTheory.return_def]
QED

Resume make_array_sim_full[dynamic_exit]:
  rpt gen_tac >> BETA_TAC >>
  disch_then (qx_choose_then `oldres` strip_assume_tac) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  gvs[Abbr `loopR`,Abbr `wrap`,exprSimDefsTheory.expr_exit_success_map]
QED

Finalise make_array_sim_full
