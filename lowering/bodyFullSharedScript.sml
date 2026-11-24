(* Facts shared by the scoped and branching cases of the full body
   induction: pointer ghosts across jumps and scope push/pop, the shadow
   compile's step and termination agreement, and a scoped body's post once
   its scope is popped. *)
Theory bodyFullShared
Ancestors
  bodySimFull gasOutcomeFull fragGasOriginPtr
  ptrSafetyTransport ptrDiscipline loweringStateRelDefs
  fragGasEmitCtrl gasShadowState gasShadowUnit gasShadow bodyDeclMemoryCompose
  bodyPtrDefs bodyMemoryDefs stmtSimIfProps stmtSimProps stmtSimDefs
  exprSimDefs loweringPosts emitHelper emitHelperProps exprLoweringProps
  stmtLowering exprLowering compileEnv allocaHistory
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend
  vyperInterpreter vyperState vyperTypeEnvPreservation
  venomInst venomState list rich_list finite_map pred_set

(* fragGasEmitCtrl's ghost_inv_at_jump_to at the state's own observations. *)
Theorem ghost_inv_at_jump:
  ghost_inv_at D lo d cenv cx es G tn (jump_to l s) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  `es with gas_obs := es.gas_obs = es` by
    simp[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`gs` |-> `es.gas_obs`] ghost_inv_at_jump_to) >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem ghost_inv_at_push:
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ghost_inv_at D lo d cenv cx (es with scopes := FEMPTY :: es.scopes) G tn s
Proof
  simp[ghost_inv_at_def, lookup_scopes_def] >> metis_tac[]
QED

Theorem ghost_inv_at_pop:
  !D lo d cenv cenv' cx ee G tn s sc rest.
  ghost_inv_at D lo d cenv' cx ee G tn s /\
  cenv_top_ext cenv cenv' ee.scopes /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  ghost_inv_at D lo d cenv cx (ee with scopes := rest) G tn s
Proof
  rpt gen_tac >>
  simp[ghost_inv_at_def, cenv_top_ext_def, compile_env_component_equality] >>
  strip_tac >> gvs[] >> conj_tac
  >- (rpt strip_tac >>
      `name NOTIN FDOM sc` by metis_tac[optionTheory.NOT_NONE_SOME] >>
      `FLOOKUP sc name = NONE` by simp[FLOOKUP_DEF] >>
      `lookup_scopes name (sc :: rest) = SOME entry` by
        simp[lookup_scopes_def] >>
      `FLOOKUP cenv'.ce_vars name = SOME (PtrVar (Var p) sz)` by
        metis_tac[optionTheory.NOT_NONE_SOME] >> metis_tac[]) >>
  gvs[] >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `SOME ds` >> PairCases_on `ds` >>
  gvs[return_buf_ptr_def]
QED

(* local_ptrs_reserved reads only ce_vars, which the shadow env keeps, and
   the variable counter, which a shadow state keeps. *)
Theorem local_ptrs_reserved_gas_shadow:
  !sa shadow_sa cenv sd.
    gas_shadow_state sa shadow_sa /\ local_ptrs_reserved cenv sa ==>
    local_ptrs_reserved (gas_shadow_env sd cenv) shadow_sa
Proof
  rpt strip_tac >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[gas_shadow_state_def]) >>
  pop_assum mp_tac >>
  pure_rewrite_tac[local_ptrs_reserved_def,
    gasShadowCompileBaseTheory.gas_shadow_env_fields] >>
  disch_then ACCEPT_TAC
QED

Theorem gas_shadow_step:
  gas_shadow_compiles f g /\ gas_shadow_state s t /\
  f s = (x, s') /\ g t = (y, t') ==>
  y = x /\ gas_shadow_state s' t'
Proof
  rw[gas_shadow_compiles_def] >> first_x_assum drule >> simp[]
QED

Theorem list_rel_last:
  !xs ys. LIST_REL R xs ys /\ xs <> [] ==> ys <> [] /\ R (LAST xs) (LAST ys)
Proof
  rpt gen_tac >> strip_tac >> fs[LIST_REL_EL_EQN] >>
  `ys <> []` by (strip_tac >> gvs[]) >> simp[LAST_EL] >>
  first_x_assum irule >> Cases_on `ys` >> fs[]
QED

(* Temporary: the restored shadow-compile spine states this as
   gas_shadow_state_terminated. *)
Theorem gas_shadow_terminated:
  gas_shadow_state s t ==> block_is_terminated s = block_is_terminated t
Proof
  rw[gas_shadow_state_def, block_is_terminated_def] >>
  Cases_on `s.cs_current_insts = []`
  >- (gvs[] >> Cases_on `t.cs_current_insts` >> fs[]) >>
  drule_all list_rel_last >> strip_tac >>
  Cases_on `s.cs_current_insts` >> Cases_on `t.cs_current_insts` >> fs[] >>
  gvs[gas_shadow_inst_def, is_terminator_def]
QED

Theorem return_buf_sep_gas_obs:
  return_buf_sep d cenv (es with gas_obs := gs) s <=>
  return_buf_sep d cenv es s
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def]
QED

Theorem return_buf_sep_jump:
  return_buf_sep d cenv es (jump_to l s) <=> return_buf_sep d cenv es s
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def, allocas_from_def, local_region_def,
       jump_to_def, lookup_var_def]
QED

Theorem return_buf_sep_push:
  return_buf_sep d cenv (es with scopes := FEMPTY :: es.scopes) s <=>
  return_buf_sep d cenv es s
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def, local_region_def, lookup_scopes_def]
QED

Theorem return_buf_sep_pop:
  return_buf_sep d cenv' (ee with scopes := sc :: ee.scopes) s /\
  cenv_top_ext cenv cenv' (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  return_buf_sep d cenv ee s
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def] >> rpt strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_region_def]) >>
  rename1 `lookup_scopes n ee.scopes = SOME entry` >>
  `FLOOKUP sc n = NONE` by
    (simp[FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n` by
    (CCONTR_TAC >> fs[cenv_top_ext_def] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _`
    irule >> simp[local_region_def, lookup_scopes_def] >>
  qexistsl_tac [`n`, `entry`, `p`] >> simp[]
QED

Theorem return_buf_allocas_path:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (OK t, G', tn') /\
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
  !bw capacity. d = SOME (bw, capacity) ==>
    allocas_from (w2n bw + capacity) t
Proof
  Cases_on `d` >- simp[] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  rw[return_buf_sep_def, return_buf_frame_def] >>
  drule_then (strip_assume_tac o cj 2) gas_origin_ptr_path_projections >>
  drule_then (qspecl_then [`w2n buf0 + buf1`, `t`] mp_tac)
    gas_path_ptr_allocas_from >> simp[]
QED

Theorem return_buf_allocas_suffix:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (OK t, G', tn') /\
  return_buf_frame d cenv sa s /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) s) ==>
  !bw capacity. d = SOME (bw, capacity) ==>
    allocas_from (w2n bw + capacity) t
Proof
  Cases_on `d` >- simp[] >>
  rename1 `return_buf_frame (SOME buf) _ _ _` >> PairCases_on `buf` >>
  rw[return_buf_frame_def] >>
  drule_then (strip_assume_tac o cj 2) gas_origin_ptr_path_projections >>
  drule_then (qspecl_then [`w2n buf0 + buf1`, `t`] mp_tac)
    gas_path_ptr_allocas_from >> simp[]
QED

(* Attach the allocation half of return_buf_sep to an existing outcome,
   using its own successful path. *)
Theorem gas_outcome_full_return_buf_allocas_from:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R /\
  return_buf_frame d cenv sa s /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) s) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn)
    (\H res ee G' tn' t.
      Q H res ee G' tn' t /\
      (!bw capacity. d = SOME (bw, capacity) ==>
         allocas_from (w2n bw + capacity) t)) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >>
      qpat_assum `gas_origin_ptr_path _ _ _ (OK t,G',tn')`
        (mp_then Any mp_tac return_buf_allocas_suffix) >>
      simp[] >>
      disch_then (qspecl_then [`sa`,`cenv`] mp_tac) >>
      Cases_on `d` >- simp[] >>
      rename1 `return_buf_frame (SOME buf) _ _ _` >> PairCases_on `buf` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem gas_outcome_full_return_buf_allocas:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R /\
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn)
    (\H res ee G' tn' t.
      Q H res ee G' tn' t /\
      (!bw capacity. d = SOME (bw, capacity) ==>
         allocas_from (w2n bw + capacity) t)) R
Proof
  strip_tac >> match_mp_tac gas_outcome_full_return_buf_allocas_from >> simp[] >>
  Cases_on `d` >- simp[] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  fs[return_buf_sep_def]
QED

(* A consumer may use the final allocation floor in its regular post. *)
Theorem gas_outcome_full_use_return_buf_allocas:
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn)
    (\H res ee G' tn' t.
      (!bw capacity. d = SOME (bw,capacity) ==>
         allocas_from (w2n bw + capacity) t) ==> Q H res ee G' tn' t) R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R
Proof
  rpt strip_tac >>
  irule gas_outcome_full_post_mono >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s` (fn sep =>
        irule_at Any (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  simp[]
QED

Theorem return_buf_sep_transport:
  return_buf_sep d cenv es s /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) t) /\
  (!n b sz. local_region cenv' ee.scopes t n b sz ==>
             local_region cenv es.scopes s n b sz) ==>
  return_buf_sep d cenv' ee t
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def] >> metis_tac[]
QED

Theorem return_buf_sep_locals_kept:
  return_buf_sep d cenv es s /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) t) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) ==>
  return_buf_sep d cenv ee t
Proof
  strip_tac >> irule return_buf_sep_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`cenv`, `es`, `s`] >> simp[] >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC local_region_kept
QED

Theorem return_buf_sep_allocated_local:
  return_buf_sep d cenv es s /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) t) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
  (!n. n <> id ==> FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n) /\
  (!n entry. n <> id /\ lookup_scopes n ee.scopes = SOME entry ==>
              IS_SOME (lookup_scopes n es.scopes)) /\
  FLOOKUP cenv'.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) ==>
  return_buf_sep d cenv' ee t
Proof
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[return_buf_sep_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_region_def]) >>
  Cases_on `n = id`
  >- (gvs[] >>
      qpat_assum `allocas_from _ t` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
      disch_then (drule_then mp_tac) >> simp[regions_disjoint_def]) >>
  qpat_x_assum `b = w2n w'` SUBST_ALL_TAC >>
  `local_region cenv es.scopes t n (w2n w') sz'` by
    (simp[local_region_def] >>
     `IS_SOME (lookup_scopes n es.scopes)` by
       (qpat_assum `!n entry. _ ==> IS_SOME _`
          (qspecl_then [`n`,`entry`] mp_tac) >> simp[]) >>
     pop_assum (mp_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
     disch_then (qx_choose_then `old_entry` assume_tac) >>
     qexistsl_tac [`old_entry`,`p'`] >> simp[] >>
     qpat_assum `!n. n <> id ==> FLOOKUP _ _ = _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `local_region cenv es.scopes s n (w2n w') sz'` by
    (irule local_region_kept >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`t`,`sa`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  qpat_assum `!n b sz. local_region cenv es.scopes s n b sz ==> _`
    (drule_then ACCEPT_TAC)
QED

Theorem lookup_scopes_declared_other:
  MAP FDOM (sc :: rest) = MAP FDOM scopes /\ n <> id /\
  lookup_scopes n ((sc |+ (id, entry)) :: rest) = SOME found ==>
  IS_SOME (lookup_scopes n scopes)
Proof
  strip_tac >>
  `id <> n` by metis_tac[] >>
  `FLOOKUP (sc |+ (id,entry)) n = FLOOKUP sc n` by
    simp[FLOOKUP_UPDATE] >>
  `lookup_scopes n (sc :: rest) = SOME found` by
    (qpat_assum `lookup_scopes _ ((sc |+ _) :: rest) = _` mp_tac >>
     pure_rewrite_tac[lookup_scopes_def] >> asm_rewrite_tac[]) >>
  drule_all_then ACCEPT_TAC lookup_scopes_same_fdoms_some
QED

(* A scoped body's post after its scope is popped, at one horizon. *)
Theorem full_post_scope_pop:
  (?cenv''.
     stmt_lands lctx last res u /\ ~u.vs_halted /\
     (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenvb) /\
     cenv_top_ext cenv cenv'' (sc :: ee.scopes) /\
     stmt_state_rel H ctx func cenv'' cx (ee with scopes := sc :: ee.scopes) u /\
     storage_well_formed_on cx (ee with scopes := sc :: ee.scopes) (FST H) /\
     return_buf_frame d cenv'' last u /\ alloca_history func u /\
     s0.vs_alloca_next <= u.vs_alloca_next /\
     ghost_inv_at D lo d cenv'' cx (ee with scopes := sc :: ee.scopes) G tn u /\
     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
            lookup_var x u = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP u.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  ?cenv''.
    stmt_lands lctx last res u /\ ~u.vs_halted /\
    (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel H ctx func cenv'' cx ee u /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv'' last u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at D lo d cenv'' cx ee G tn u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `(ee with scopes := sc :: ee.scopes) with scopes := ee.scopes = ee` by
    simp[evaluation_state_component_equality] >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (qspecl_then [`H`, `func`, `cenv`, `cenv''`, `cx`,
       `ee with scopes := sc :: ee.scopes`, `u`, `sc`, `ee.scopes`, `ctx`]
       mp_tac stmt_state_rel_pop_top_ext >>
     asm_rewrite_tac[] >> simp[]) >>
  `storage_well_formed_on cx ee (FST H)` by
    fs[storage_well_formed_on_def, get_storage_scopes] >>
  `ghost_inv_at D lo d cenv cx ee G tn u` by
    (qspecl_then [`D`, `lo`, `d`, `cenv`, `cenv''`, `cx`,
       `ee with scopes := sc :: ee.scopes`, `G`, `tn`, `u`, `sc`, `ee.scopes`]
       mp_tac ghost_inv_at_pop >>
     asm_rewrite_tac[] >> simp[]) >>
  `return_buf_frame d cenv last u` by
    (`cenv''.ce_return_buf = cenv.ce_return_buf` by
       fs[cenv_top_ext_def, compile_env_component_equality] >>
     qpat_x_assum `return_buf_frame _ _ _ _` mp_tac >>
     Cases_on `d` >> simp[return_buf_frame_def] >>
     rename1 `SOME dd` >> PairCases_on `dd` >> simp[return_buf_frame_def]) >>
  qexists_tac `cenv` >> simp[cenv_top_ext_refl]
QED
