(* Structural compiler correspondence; classification of reached explicit
   GAS events is a separate consumer of this result. *)
Theory gasShadowCompile
Ancestors
  gasShadow gasShadowState gasShadowCompileBodies gasShadowCompileBase
  gasShadowCompileHelpers gasShadowCenv exprLowering compileEnv list

val _ = augment_srw_ss [rewrites [gsc_shift_thms]]

Theorem compile_expr_body_call[local]:
  compile_expr_body f bf tf cenv ty (Call a target args dr) =
  compile_call f cenv (expr_type (Call a target args dr)) ty target args dr
Proof
  simp[FUN_EQ_THM, compile_expr_body_def]
QED

Theorem gas_shadow_compile_bounded[local]:
  !n.
  (!cenv ty e shadow. 2 * (expr_size e + cenv_defaults_size cenv) + 2 <= n ==>
    gas_shadow_compiles (compile_expr cenv ty e)
      (compile_expr (gas_shadow_cenv cenv) ty (if shadow then gas_shadow_expr e else e))) /\
  (!cenv ret_ty ty bi args shadow. 2 * (list_size expr_size args + cenv_defaults_size cenv) + 1 <= n ==>
    gas_shadow_compiles (compile_builtin_dispatch cenv ret_ty ty bi args)
      (compile_builtin_dispatch (gas_shadow_cenv cenv) ret_ty ty
        (if shadow then gas_shadow_builtin bi else bi)
        (if shadow then MAP gas_shadow_expr args else args))) /\
  (!cenv vv_ty ty tb ret_ty args shadow. 2 * (list_size expr_size args + cenv_defaults_size cenv) + 1 <= n ==>
    gas_shadow_compiles (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args)
      (compile_type_builtin_dispatch (gas_shadow_cenv cenv) vv_ty ty tb ret_ty
        (if shadow then MAP gas_shadow_expr args else args)))
Proof
  completeInduct_on `n` >>
  `!bound. 2 * bound + 1 <= n ==>
    !cenv ty e shadow.
      gas_shadow_compiles (expr_child_callback bound compile_expr cenv ty e)
        (expr_child_callback bound (\c. compile_expr (gas_shadow_cenv c)) cenv ty
          (if shadow then gas_shadow_expr e else e))`
    by (rpt strip_tac >> irule gas_shadow_compiles_expr_child >>
        map_every qx_gen_tac [`child_env`, `child_ty`, `child_e`, `mode`] >> strip_tac >>
        `2 * (expr_size child_e + cenv_defaults_size child_env) + 2 < n` by decide_tac >>
        qpat_x_assum `!m. m < n ==> _` (qspec_then `2 * (expr_size child_e + cenv_defaults_size child_env) + 2` mp_tac) >>
        simp[] >> metis_tac[]) >>
  `!bound. 2 * bound + 1 <= n ==>
    !cenv ret_ty ty bi args shadow.
      gas_shadow_compiles (builtin_child_callback bound compile_builtin_dispatch cenv ret_ty ty bi args)
        (builtin_child_callback bound
          (\c. compile_builtin_dispatch (gas_shadow_cenv c)) cenv ret_ty ty
          (if shadow then gas_shadow_builtin bi else bi)
          (if shadow then MAP gas_shadow_expr args else args))`
    by (rpt strip_tac >> irule gas_shadow_compiles_builtin_child >>
        map_every qx_gen_tac [`ce`, `rt`, `ct`, `cb`, `es`, `mode`] >> strip_tac >>
        `2 * (list_size expr_size es + cenv_defaults_size ce) + 1 < n` by decide_tac >>
        qpat_x_assum `!m. m < n ==> _` (qspec_then `2 * (list_size expr_size es + cenv_defaults_size ce) + 1` mp_tac) >>
        simp[] >> metis_tac[]) >>
  `!bound. 2 * bound + 1 <= n ==>
    !cenv vv_ty ty tb ret_ty args shadow.
      gas_shadow_compiles (type_child_callback bound compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args)
        (type_child_callback bound
          (\c. compile_type_builtin_dispatch (gas_shadow_cenv c)) cenv vv_ty ty tb ret_ty
          (if shadow then MAP gas_shadow_expr args else args))`
    by (rpt strip_tac >> irule gas_shadow_compiles_type_child >>
        map_every qx_gen_tac [`ce`, `vt`, `ct`, `cb`, `rt`, `es`, `mode`] >> strip_tac >>
        `2 * (list_size expr_size es + cenv_defaults_size ce) + 1 < n` by decide_tac >>
        qpat_x_assum `!m. m < n ==> _` (qspec_then `2 * (list_size expr_size es + cenv_defaults_size ce) + 1` mp_tac) >>
        simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      once_rewrite_tac[compile_expr_raw_def] >>
      `expr_size (if shadow then gas_shadow_expr e else e) = expr_size e`
        by (Cases_on `shadow` >> simp[gas_shadow_expr_size]) >>
      simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      `2 * (cenv_defaults_size cenv + expr_size e) + 1 <= n` by decide_tac >>
      Cases_on `?a fid args dr. e = Call a (IntCall fid) args dr`
      >- (gvs[] >>
          `(if shadow then gas_shadow_expr (Call a (IntCall fid) args dr)
            else Call a (IntCall fid) args dr) =
           Call a (IntCall fid) (if shadow then MAP gas_shadow_expr args else args)
             (if shadow then OPTION_MAP gas_shadow_expr dr else dr)`
            by (Cases_on `shadow` >> simp[gas_shadow_expr_def]) >>
          pop_assum SUBST1_TAC >> simp[compile_expr_body_call, vyperASTTheory.expr_type_def] >>
          qmatch_goalsub_abbrev_tac `compile_call (expr_child_callback B compile_expr)` >>
          `2 * B + 1 <= n` by (unabbrev_all_tac >> decide_tac) >>
          irule gas_shadow_compiles_call_int_gsc >> simp[] >> metis_tac[]) >>
      `!a fid args dr. (if shadow then gas_shadow_expr e else e) <>
                       Call a (IntCall fid) args dr`
        by (Cases_on `shadow` >> rw[gas_shadow_expr_intcall] >> metis_tac[]) >>
      simp[compile_expr_body_gsc, SF ETA_ss] >>
      irule gas_shadow_compiles_expr_body >>
      metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      once_rewrite_tac[compile_expr_raw_def] >>
      `list_size expr_size (if shadow then MAP gas_shadow_expr args else args) =
       list_size expr_size args`
        by (Cases_on `shadow` >> simp[gas_shadow_args_size]) >>
      simp[compile_builtin_dispatch_body_gsc, SF ETA_ss] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule gas_shadow_compiles_builtin_body >>
      `2 * (cenv_defaults_size cenv + list_size expr_size args) + 1 <= n`
        by decide_tac >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  once_rewrite_tac[compile_expr_raw_def] >>
  `list_size expr_size (if shadow then MAP gas_shadow_expr args else args) =
   list_size expr_size args`
    by (Cases_on `shadow` >> simp[gas_shadow_args_size]) >>
  simp[compile_type_builtin_dispatch_body_gsc, SF ETA_ss] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gas_shadow_compiles_type_body >>
  `2 * (cenv_defaults_size cenv + list_size expr_size args) + 1 <= n`
    by decide_tac >>
  metis_tac[]
QED

(* The shadow side compiles in the shadowed-defaults env: an internal call
   that omits arguments compiles the callee's defaults shadowed.
   The identity alternative also covers arbitrary expressions returned by
   total HD/EL selectors on malformed argument lists. Both executions then
   compile the same arbitrary expression under the same size guard. *)
Theorem gas_shadow_compile_expr:
  (!cenv ty e shadow.
     gas_shadow_compiles (compile_expr cenv ty e)
       (compile_expr (gas_shadow_cenv cenv) ty (if shadow then gas_shadow_expr e else e))) /\
  (!cenv ret_ty ty bi args shadow.
     gas_shadow_compiles (compile_builtin_dispatch cenv ret_ty ty bi args)
       (compile_builtin_dispatch (gas_shadow_cenv cenv) ret_ty ty
         (if shadow then gas_shadow_builtin bi else bi)
         (if shadow then MAP gas_shadow_expr args else args))) /\
  (!cenv vv_ty ty tb ret_ty args shadow.
     gas_shadow_compiles
       (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args)
       (compile_type_builtin_dispatch (gas_shadow_cenv cenv) vv_ty ty tb ret_ty
         (if shadow then MAP gas_shadow_expr args else args)))
Proof
  conj_tac
  >- (rpt gen_tac >>
      qspec_then `2 * (expr_size e + cenv_defaults_size cenv) + 2` mp_tac gas_shadow_compile_bounded >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >>
      qspec_then `2 * (list_size expr_size args + cenv_defaults_size cenv) + 1` mp_tac gas_shadow_compile_bounded >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >>
  qspec_then `2 * (list_size expr_size args + cenv_defaults_size cenv) + 1` mp_tac gas_shadow_compile_bounded >>
  simp[] >> metis_tac[]
QED
