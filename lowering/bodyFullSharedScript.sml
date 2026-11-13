(* Facts shared by the scoped and branching cases of the full body
   induction: pointer ghosts across jumps and scope push/pop, the shadow
   compile's step and termination agreement, and a scoped body's post once
   its scope is popped. *)
Theory bodyFullShared
Ancestors
  fragGasEmitCtrl gasShadowState gasShadowUnit gasShadow bodyDeclMemoryCompose
  bodyPtrDefs bodyMemoryDefs stmtSimIfProps stmtSimProps stmtSimDefs
  exprSimDefs loweringPosts emitHelper emitHelperProps exprLoweringProps
  stmtLowering exprLowering compileEnv allocaHistory
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend
  vyperInterpreter vyperState venomInst venomState list rich_list finite_map pred_set

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
