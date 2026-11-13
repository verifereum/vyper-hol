Theory ifGhostPtr
Ancestors
  bodyPtrDefs loweringPosts compileEnv vyperState venomState finite_map

Theorem if_ghost_inv_jump:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx es G tn (jump_to lbl s)
Proof
  Cases_on `d`
  >- (simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, jump_to_def, lookup_var_def] >> metis_tac[]) >>
  rename1 `SOME ds` >> PairCases_on `ds` >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, jump_to_def, lookup_var_def] >> metis_tac[]
QED

Theorem if_ghost_inv_gas:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx (es with gas_obs := gs) G tn s
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED

Theorem if_ghost_inv_push:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx (es with scopes := FEMPTY :: es.scopes) G tn s
Proof
  simp[ghost_inv_def, lookup_scopes_def] >> metis_tac[]
QED

Theorem if_ghost_inv_pop:
  ghost_inv d cenv' cx ee G tn s /\
  cenv_top_ext cenv cenv' ee.scopes /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  ghost_inv d cenv cx (ee with scopes := rest) G tn s
Proof
  simp[ghost_inv_def, cenv_top_ext_def, compile_env_component_equality] >>
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

Theorem if_stmt_exit_ptr_scopes:
  stmt_exit_ptr RetQ (es with scopes := scopes) res gt r <=>
  stmt_exit_ptr RetQ es res gt r
Proof
  simp[stmt_exit_ptr_def]
QED
