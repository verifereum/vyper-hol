(* Relational interfaces for structurally guarded compiler callbacks. *)
Theory gasShadowCompileBase
Ancestors
  gasShadow gasShadowState exprCallBounds compileEnv emitHelper vyperAST list pair

Theorem gas_shadow_compiles_pair:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) ==>
  gas_shadow_compiles
    (\s. let (x,s1) = f s in h x s1)
    (\t. let (x,t1) = g t in k x t1)
Proof
  pure_rewrite_tac[GSYM comp_bind_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  MATCH_ACCEPT_TAC gas_shadow_compiles_bind
QED

Theorem gas_shadow_compiles_ignore_bind:
  gas_shadow_compiles f g /\ gas_shadow_compiles h k ==>
  gas_shadow_compiles (comp_ignore_bind f h) (comp_ignore_bind g k)
Proof
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_map_result:
  gas_shadow_compiles f g ==>
  gas_shadow_compiles
    (\s. let (x,s1) = f s in (h x,s1))
    (\t. let (x,t1) = g t in (h x,t1))
Proof
  strip_tac >> ho_match_mp_tac gas_shadow_compiles_pair >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_invalid_expr_call:
  gas_shadow_compiles (invalid_expr_call ty) (invalid_expr_call ty)
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  pure_rewrite_tac[invalid_expr_call_def] >>
  ho_match_mp_tac gas_shadow_compiles_map_result >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  MATCH_ACCEPT_TAC gas_shadow_compiles_emit_inst
QED

Theorem gas_shadow_args_size[simp]:
  list_size expr_size (MAP gas_shadow_expr args) = list_size expr_size args
Proof
  Induct_on `args` >> simp[list_size_def, gas_shadow_expr_size] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem gas_shadow_compiles_expr_child:
  (!cenv ty e shadow. expr_size e + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv ty e)
       (g cenv ty (if shadow then gas_shadow_expr e else e))) ==>
  !cenv ty e shadow.
    gas_shadow_compiles (expr_child_callback bound f cenv ty e)
      (expr_child_callback bound g cenv ty
        (if shadow then gas_shadow_expr e else e))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `expr_size e + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[expr_child_callback_def, gas_shadow_expr_size] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspec_then `cenv` mp_tac) >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

Theorem gas_shadow_compiles_builtin_child:
  (!cenv ret_ty ty bi args shadow. list_size expr_size args + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv ret_ty ty bi args)
       (g cenv ret_ty ty (if shadow then gas_shadow_builtin bi else bi)
         (if shadow then MAP gas_shadow_expr args else args))) ==>
  !cenv ret_ty ty bi args shadow.
    gas_shadow_compiles (builtin_child_callback bound f cenv ret_ty ty bi args)
      (builtin_child_callback bound g cenv ret_ty ty
        (if shadow then gas_shadow_builtin bi else bi)
        (if shadow then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `list_size expr_size args + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[builtin_child_callback_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspecl_then [`cenv`, `ret_ty`, `ty`, `bi`, `args`] mp_tac) >>
  simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

Theorem gas_shadow_compiles_type_child:
  (!cenv vv_ty ty tb ret_ty args shadow. list_size expr_size args + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv vv_ty ty tb ret_ty args)
       (g cenv vv_ty ty tb ret_ty
         (if shadow then MAP gas_shadow_expr args else args))) ==>
  !cenv vv_ty ty tb ret_ty args shadow.
    gas_shadow_compiles (type_child_callback bound f cenv vv_ty ty tb ret_ty args)
      (type_child_callback bound g cenv vv_ty ty tb ret_ty
        (if shadow then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `list_size expr_size args + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[type_child_callback_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspec_then `cenv` mp_tac) >>
  disch_then (qspec_then `vv_ty` mp_tac) >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspec_then `tb` mp_tac) >>
  disch_then (qspec_then `ret_ty` mp_tac) >>
  disch_then (qspec_then `args` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

(* Eta-insensitive state-threading boundary. *)
Theorem comp_bind_uncurry:
  (\s. UNCURRY h (f s)) = comp_bind f h
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
  Cases_on `f s` >> simp[]
QED

Theorem gas_shadow_compiles_uncurry:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) ==>
  gas_shadow_compiles (\s. UNCURRY h (f s)) (\t. UNCURRY k (g t))
Proof
  simp[comp_bind_uncurry, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_uncurry_nested[local]:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) /\
  (!x y. gas_shadow_compiles (p x y) (q x y)) ==>
  gas_shadow_compiles
    (\s. UNCURRY (\x t. UNCURRY (p x) (h x t)) (f s))
    (\s. UNCURRY (\x t. UNCURRY (q x) (k x t)) (g s))
Proof
  strip_tac >> simp[comp_bind_uncurry, SF ETA_ss] >>
  match_mp_tac gas_shadow_compiles_bind >> simp[] >>
  gen_tac >> match_mp_tac gas_shadow_compiles_bind >> simp[]
QED
