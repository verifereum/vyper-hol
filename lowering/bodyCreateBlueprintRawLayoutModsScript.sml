(* Paired compiler cuts for the raw blueprint argument. *)
Theory bodyCreateBlueprintRawLayoutMods
Ancestors
  exprLoweringProps gasShadowCompile gasShadowCompileHelpers
  bodyFullForArrayRound fragExec compileEnv exprLowering
  vyperAST venomInst venomState pair
Libs pairLib

Triviality raw_parts_local:
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((dp,len),sb) ==>
  ?vv sm sv ss ptr su sn.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
    unwrap_value cenv sv ss = (ptr,su) /\
    emit_op MLOAD [ptr] su = (len,sn) /\
    emit_op ADD [ptr; Lit 32w] sn = (dp,sb)
Proof
  simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Triviality shadow_parts_local:
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T
      (MAP gas_shadow_expr later) [gas_shadow_expr e] sh = ((dp,len),shb) ==>
  ?shv shm shsv shss shptr shsu shn.
    compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sh = (shv,shm) /\
    compile_snapshot_vv (gas_shadow_env T cenv)
      (exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later))
      shv shm = (shsv,shss) /\
    unwrap_value (gas_shadow_env T cenv) shsv shss = (shptr,shsu) /\
    emit_op MLOAD [shptr] shsu = (len,shn) /\
    emit_op ADD [shptr; Lit 32w] shn = (dp,shb)
Proof
  simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Triviality shadow_expr_local:
  gas_shadow_state sa sh /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  gas_shadow_compiles (compile_expr cenv (expr_type e) e)
    (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)) ==>
  ?shv shm. compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sh = (shv,shm) /\ gas_shadow_state sm shm
Proof
  strip_tac >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sh` >>
  rename1 `compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sh = (shv,shm)` >>
  drule_then (drule_all_then strip_assume_tac)
    bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  qexistsl_tac [`shv`,`shm`] >> simp[] >> first_assum ACCEPT_TAC
QED
Theorem blueprint_raw_paired_cuts_mods:
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((dp,len),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T
    (MAP gas_shadow_expr later) [gas_shadow_expr e] sh = ((dp,len),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_function func shadow_func /\ fn_has_code sa sb func /\
  fn_has_code sh shb shadow_func /\ fn_inst_ids_distinct func ==>
  ?vv sm sv ss ptr su sn shv shm shsv shss shptr shsu shn.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
    unwrap_value cenv sv ss = (ptr,su) /\
    emit_op MLOAD [ptr] su = (len,sn) /\
    emit_op ADD [ptr; Lit 32w] sn = (dp,sb) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sh = (shv,shm) /\
    compile_snapshot_vv (gas_shadow_env T cenv)
      (exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later))
      shv shm = (shsv,shss) /\
    unwrap_value (gas_shadow_env T cenv) shsv shss = (shptr,shsu) /\
    emit_op MLOAD [shptr] shsu = (len,shn) /\
    emit_op ADD [shptr; Lit 32w] shn = (dp,shb) /\
    ci_mono sa sm /\ ci_mono sm ss /\ ci_mono ss su /\
    ci_mono su sn /\ ci_mono sn sb /\
    ci_mono sh shm /\ ci_mono shm shss /\ ci_mono shss shsu /\
    ci_mono shsu shn /\ ci_mono shn shb /\
    fn_has_code sa sm func /\ fn_has_code sm ss func /\
    fn_has_code ss su func /\ fn_has_code su sn func /\
    fn_has_code sh shm shadow_func /\ fn_has_code shm shss shadow_func /\
    fn_has_code shss shsu shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?vv sm sv ss ptr su sn.
      compile_expr cenv (expr_type e) e sa = (vv,sm) /\
      compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
      unwrap_value cenv sv ss = (ptr,su) /\
      emit_op MLOAD [ptr] su = (len,sn) /\
      emit_op ADD [ptr; Lit 32w] sn = (dp,sb)` by
    (irule raw_parts_local >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `unwrap_value cenv sv ss = (p,su)` >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
      (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
      Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  `?shv shm shsv shss shptr shsu shn.
      compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) sh = (shv,shm) /\
      compile_snapshot_vv (gas_shadow_env T cenv)
        (exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later))
        shv shm = (shsv,shss) /\
      unwrap_value (gas_shadow_env T cenv) shsv shss = (shptr,shsu) /\
      emit_op MLOAD [shptr] shsu = (len,shn) /\
      emit_op ADD [shptr; Lit 32w] shn = (dp,shb)` by
    (irule shadow_parts_local >> first_assum ACCEPT_TAC) >>
  drule_then (drule_all_then strip_assume_tac)
    bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  `ci_mono sa sm /\ ci_mono sm ss /\ ci_mono ss su /\ ci_mono su sn /\ ci_mono sn sb` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`cenv`,`exprs_can_mutate cenv later`,`vv`,`sm`]
       ci_mono_compile_snapshot_vv) >>
     mp_tac (Q.SPECL [`cenv`,`sv`,`ss`] ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`MLOAD`,`[p]`,`su`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[p;Lit 32w]`,`sn`] ci_mono_emit_op) >>
     asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono sh shm /\ ci_mono shm shss /\ ci_mono shss shsu /\
   ci_mono shsu shn /\ ci_mono shn shb` by
    (mp_tac (Q.SPECL [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`sh`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`gas_shadow_env T cenv`,
       `exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later)`,
       `shv`,`shm`] ci_mono_compile_snapshot_vv) >>
     mp_tac (Q.SPECL [`gas_shadow_env T cenv`,`shsv`,`shss`] ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`MLOAD`,`[shptr]`,`shsu`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[shptr;Lit 32w]`,`shn`] ci_mono_emit_op) >>
     asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code sa sm func /\ fn_has_code sm ss func /\ fn_has_code ss su func /\
   fn_has_code su sn func` by
    (map_every (fn (a,b) =>
        qspecl_then [a,b,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
        (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> strip_tac)
       [(`sa`,`sm`),(`sm`,`ss`),(`ss`,`su`),(`su`,`sn`)] >> simp[]) >>
  `fn_has_code sh shm shadow_func /\ fn_has_code shm shss shadow_func /\
   fn_has_code shss shsu shadow_func` by
    (map_every (fn (a,b) =>
        qspecl_then [a,b,`shb`,`shadow_func`] mp_tac fragExecTheory.fn_has_code_split >>
        (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> strip_tac)
       [(`sh`,`shm`),(`shm`,`shss`),(`shss`,`shsu`)] >> simp[]) >>
  qexistsl_tac [`vv`,`sm`,`sv`,`ss`,`p`,`su`,`sn`,`shv`,`shm`,`shsv`,`shss`,`shptr`,`shsu`,`shn`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
