(* The constructor body's shadow placement: the deploy unit's GAS shadow
   (gas_shadow_run_deploy_lowering) holds the shadow body's code at the
   compile states paired with the actual body's.  The deploy analogue of
   runtimeBodyShadow's runtime_selected_body_shadow.
   TOP-LEVEL: deploy_ctor_body_shadow. *)
Theory ctorDeployBodyShadow
Ancestors
  bodyFullShadowBodyInvLowering
  ctorDeployLoweringCode ctorDeployLoweringCodeShape ctorDeployLoweringDefs
  ctorDeployDefs ctorDeployEntryLabels
  gasShadowDeployRegisterEnv
  gasShadowDeployRunner gasShadowShape gasShadowCompileStmt gasShadowStmtEnv
  gasShadowInternal gasShadowUnitExtract gasShadowUnitGuards
  gasShadowModuleDefs gasShadowState gasShadowUnit gasShadow
  loweringShapeProps loweringShapeDefs fragExec immSectionDead
  vyperCompiler compileVyper moduleLowering compileEnv venomInst list

val _ = Parse.hide "body";

(* A constructor deploy run with a non-view lock flag, for any body and
   internal packages, is compile_generate_deploy's constructor branch laid
   out step by step. *)
Theorem run_deploy_lowering_ctor_trace:
  !rpolicy bc cap args ifns cenv0 body pay nr nkey ut u lnr lkey lut.
    cenv0.ce_nonreentrant = (lnr,lkey,lut,F) /\
    run_deploy_lowering T rpolicy bc cap args 0 ifns cenv0 body pay nr nkey
      ut "__deploy" = SOME u ==>
    ?st_pay imm st1 cenv1 st2 st3 exit_lbl sa sb sj old_bb st_exit
     st_epilogue st_final post ctx data.
      (if pay then comp_return () else
         comp_bind (emit_op CALLVALUE []) (\cv.
           comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))
        (initial_compile_state "__deploy") = ((),st_pay) /\
      (if cap > 0 then
         comp_bind (compile_fixed_region_with_id cap)
           (\r. comp_return (SND r).buf_operand)
       else comp_return (Lit 0w)) st_pay = (imm,st1) /\
      compile_register_constructor_args
        (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
        args 0 0 st1 = (cenv1,st2) /\
      (if nr then compile_nonreentrant_lock nkey ut F else comp_return ())
        st2 = ((),st3) /\
      fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
      compile_stmts (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
        NoLoop NoneT body sa = ((),sb) /\
      (if block_is_terminated sb then comp_return ()
       else emit_inst JMP [Label exit_lbl] []) sb = ((),sj) /\
      new_block exit_lbl sj = (old_bb,st_exit) /\
      (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
        st_exit = ((),st_epilogue) /\
      compile_constructor_epilogue (LENGTH bc) cap imm st_epilogue =
        ((),st_final) /\
      compile_internal_fn_bodies ifns st_final = ((),post) /\
      extract_context_with_internals "__deploy" ifns post = SOME (ctx,data) /\
      lowering_context_ok (install_immutable_reservation cap ctx) /\
      u.cu_context = install_immutable_reservation cap ctx
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `_.ce_nonreentrant = _` (fn th =>
    rewrite_tac [th, compile_generate_deploy_def, comp_ignore_bind_def,
      comp_bind_def, comp_get_def, LET_THM]) >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_get_def, LET_THM]) >>
  strip_tac >>
  Cases_on `pay` >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* The deploy unit, with a constructor, is run_deploy_lowering's. *)
Theorem lower_vyper_deploy_unit_ctor_run[local]:
  lower_vyper_deploy_unit tops rpolicy bc = SOME dunit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  set_constructor_package_target rpolicy.rpol_target
    (package_constructor tops T (K global_nonreentrant_slot) cf) =
    (cenv0,args,pay,nr,nkey,ut,body,ret) ==>
  run_deploy_lowering T rpolicy bc (imm_len tops) args 0
    (MAP (set_internal_package_target rpolicy.rpol_target o
          package_internal_fn tops T (K global_nonreentrant_slot) T
            (imm_len tops))
      (order_internals (deploy_internal_order (SOME cf) ints) ints))
    cenv0 body pay nr nkey ut "__deploy" = SOME dunit
Proof
  simp[lower_vyper_deploy_unit_def, GSYM imm_len_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Two members of a list with distinct names and the same name are one. *)
Theorem deploy_body_shadow_name_unique[local]:
  !fs f g. ALL_DISTINCT (MAP (\h. h.fn_name) fs) /\ MEM f fs /\ MEM g fs /\
    f.fn_name = g.fn_name ==> f = g
Proof
  Induct >> rw[] >> gvs[MEM_MAP] >> metis_tac[]
QED

(* The shadow unit's __deploy function is the raw function over the shadow
   compile's blocks; the shadow of func has the same name, so it is that
   function.

   Intuition:
   - The prefix up to the body start sa reads neither the body nor the
     internal packages, so the shadow run reaches the same sa.
   - gas_shadow_compile_stmt pairs the actual body end sb with the shadow
     one; compile_stmt_cs_mono and the tail extensions give cs_extends on
     the shadow side unconditionally.
   - Entry blocks and internal delimiters have distinct labels, so
     packaging preserves the shadow constructor's emitted blocks. *)
Theorem deploy_ctor_body_shadow:
  !tops am tx rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_source_ok tops am tx /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) ==>
    ?shadow_ctx shadow_func shadow_sa shadow_sb.
      shadow_body_inv tops dunit.cu_context shadow_ctx /\
      gas_shadow_context dunit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      compile_stmts (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body) shadow_sa =
        ((),shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  simp[deploy_ctor_code_def] >> strip_tac >>
  rename1 `set_constructor_package_target _ _ =
    (cenv0,pos_args,pay,nr,nkey,ut,body,ret)` >>
  drule_all deploy_constructor_package_not_view >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  qabbrev_tac `ifns = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) T
        (imm_len tops))
      (order_internals (deploy_internal_order (SOME cf) ints) ints)` >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns))` by
    (qspecl_then [`tops`, `rpolicy.rpol_target`, `T`,
       `K global_nonreentrant_slot`, `T`, `imm_len tops`,
       `order_internals (deploy_internal_order (SOME cf) ints) ints`, `ifns`]
       mp_tac deploy_internal_package_labels >>
     simp[Abbr `ifns`, PERM_order_deploy_internals]) >>
  `run_deploy_lowering T rpolicy runtime_bc (imm_len tops) pos_args 0 ifns
     cenv0 body pay nr nkey ut "__deploy" = SOME dunit` by
    (simp[Abbr `ifns`] >> irule lower_vyper_deploy_unit_ctor_run >>
     metis_tac[]) >>
  (* the shadow unit *)
  qspecl_then [`T`, `rpolicy`, `runtime_bc`, `imm_len tops`, `pos_args`,
    `0`, `ifns`, `cenv0`, `body`, `pay`, `nr`, `nkey`, `ut`, `"__deploy"`]
    mp_tac gas_shadow_run_deploy_lowering >>
  asm_rewrite_tac[] >>
  Cases_on `run_deploy_lowering T rpolicy runtime_bc (imm_len tops) pos_args
    0 (MAP gas_shadow_internal_package ifns) (gas_shadow_env T cenv0)
      (MAP gas_shadow_stmt body) pay nr nkey ut "__deploy"` >> simp[] >>
  rename1 `_ = SOME su` >> strip_tac >>
  `shadow_body_inv tops dunit.cu_context su.cu_context` by
    (qspecl_then [`tops`, `am`, `tx`, `rpolicy`, `runtime_bc`, `dunit`, `su`,
       `exts`, `ints`, `fb`, `cf`, `cenv0`, `pos_args`, `pay`,
       `nr`, `nkey`, `ut`, `body`, `ret`] mp_tac deploy_shadow_body_inv >>
     fs[Abbr `ifns`]) >>
  `gas_shadow_context dunit.cu_context su.cu_context` by
    fs[gas_shadow_unit_def] >>
  qspecl_then [`rpolicy`, `runtime_bc`, `imm_len tops`, `pos_args`,
    `MAP gas_shadow_internal_package ifns`, `gas_shadow_env T cenv0`,
    `MAP gas_shadow_stmt body`, `pay`, `nr`, `nkey`, `ut`, `su`, `nr`,
    `nkey`, `ut`] mp_tac run_deploy_lowering_ctor_trace >>
  simp[] >> strip_tac >>
  `compile_register_constructor_args
      (gas_shadow_env T cenv0 with
         ce_imm_alloca := if imm_len tops > 0 then SOME imm else NONE)
      pos_args 0 0 st1 = (gas_shadow_env T cenv1,st2)` by
    (qpat_assum `compile_register_constructor_args _ _ _ _ _ = (cenv1,st2)` mp_tac >>
     mp_tac (Q.SPECL [`pos_args`,
       `cenv0 with ce_imm_alloca := if imm_len tops > 0 then SOME imm else NONE`,
       `0`, `0`, `st1`]
       (Q.INST [`sd` |-> `T`] compile_register_constructor_args_gas_shadow_env)) >>
     simp[gasShadowCompileBaseTheory.gas_shadow_env_def] >>
     strip_tac >>
     qpat_x_assum `compile_register_constructor_args _ _ _ _ _ = (cenv1',st2')`
       (fn th => map_every assume_tac
         [Q.AP_TERM `FST` th, Q.AP_TERM `SND` th]) >>
     simp[] >> gvs[gasShadowCompileBaseTheory.gas_shadow_env_def]) >>
  `cenv1' = gas_shadow_env T cenv1 /\ st2' = st2` by
    (qpat_assum `compile_register_constructor_args _ _ _ _ _ = (cenv1',st2')` mp_tac >>
     disch_then (fn th => qpat_assum
       `compile_register_constructor_args _ _ _ _ _ = (gas_shadow_env T cenv1,st2)`
       (mp_tac o REWRITE_RULE [th])) >>
     simp[] >> strip_tac >> gvs[]) >>
  gvs[] >>
  (* the shadow body run from the shared sa *)
  rename1 `compile_stmts _ NoLoop NoneT (MAP gas_shadow_stmt body) sa =
    ((),tb)` >>
  rename1 `(if block_is_terminated tb then _ else _) tb = ((),tj)` >>
  rename1 `new_block exit_lbl tj = (_,t_exit)` >>
  `gas_shadow_state sb tb` by
    (rewrite_tac[stmtSimPropsTheory.compile_stmts_env] >>
     qspecl_then [`body`, `cenv1 with ce_ctor_exit_label := SOME exit_lbl`,
       `NoLoop`, `NoneT`] mp_tac
       (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
     simp[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `sa`] mp_tac) >>
     Cases_on `stmts_env (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
       NoLoop NoneT body sa` >>
     Cases_on `stmts_env (gas_shadow_env T
       (cenv1 with ce_ctor_exit_label := SOME exit_lbl)) NoLoop NoneT
       (MAP gas_shadow_stmt body) sa` >>
     `gas_shadow_env T cenv1 with ce_ctor_exit_label := SOME exit_lbl =
        gas_shadow_env T (cenv1 with ce_ctor_exit_label := SOME exit_lbl)` by
       rw[gasShadowCompileBaseTheory.gas_shadow_env_def,
          compile_env_component_equality] >>
     strip_tac >> gvs[gas_shadow_state_refl,
       stmtSimPropsTheory.compile_stmts_env]) >>
  `gas_shadow_env T cenv1 with ce_ctor_exit_label := SOME exit_lbl =
     gas_shadow_env T (cenv1 with ce_ctor_exit_label := SOME exit_lbl)` by
    rw[gasShadowCompileBaseTheory.gas_shadow_env_def,
       compile_env_component_equality] >>
  rename1 `compile_constructor_epilogue _ _ _ _ = ((),t_final)` >>
  `compile_generate_deploy T (LENGTH runtime_bc) (imm_len tops) pos_args 0 []
    (gas_shadow_env T cenv0) (MAP gas_shadow_stmt body) pay nr nkey ut
      (initial_compile_state "__deploy") = ((),t_final)` by
    (PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
       ctor_code_cond_not, ctor_lock_flag_select] >>
     simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_get_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >>
     gvs[compile_internal_fn_bodies_def, comp_return_def]) >>
  drule deploy_entry_blocks_not_internal >> strip_tac >>
  drule_at (Pos last) deploy_ctor_packaged_entry_by_labels >> simp[] >>
  disch_then (qspec_then `t_final` mp_tac) >> simp[] >> strip_tac >>
  drule_all deploy_ctor_member_certificates >> strip_tac >>
  (* the shadow code extends through the constructor tail *)
  drule_all ctor_code_setup_extension >> strip_tac >>
  drule_all ctor_code_tail_extensions >> strip_tac >>
  `fn_has_code sa tb
     (mk_raw_function "__deploy" (all_blocks t_final))` by
    (qspecl_then [`initial_compile_state "__deploy"`, `sa`, `tb`, `tj`,
       `t_exit`, `t_final`, `"__deploy"`] mp_tac ctor_code_intervals_contained >>
     simp[]) >>
  (* func's shadow partner is that function *)
  `?g. MEM g su.cu_context.ctx_functions /\ gas_shadow_function func g` by
    (fs[gas_shadow_context_def] >> metis_tac[LIST_REL_MEM_IMP]) >>
  `g.fn_name = "__deploy"` by
    (fs[gas_shadow_function_def] >>
     qpat_x_assum `_ with fn_blocks := _ = func` (mp_tac o
       Q.AP_TERM `ir_function_fn_name`) >> simp[]) >>
  `g = mk_raw_function "__deploy" (all_blocks t_final)` by
    (irule deploy_body_shadow_name_unique >> simp[mk_raw_function_def] >>
     qexists_tac `su.cu_context.ctx_functions` >>
     fs[lowering_context_ok_def, ctx_fn_names_def, mk_raw_function_def]) >>
  qexistsl_tac [`su.cu_context`, `g`, `sa`, `tb`] >>
  gvs[] >>
  simp[gas_shadow_state_refl]
QED
