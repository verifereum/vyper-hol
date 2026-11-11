Theory gasShadowCompileBodies
Ancestors
  gasShadowCompileBase gasShadowCompilePure gasShadowCompileHelpers
  gasShadowCompileOps gasShadowCompileConvert gasShadowCompileNames
  gasShadowCompileBuiltinBytes exprLowering gasShadow gasShadowState compileEnv
  list pair

Theorem as_ptr_val_action[local]:
  (\s. as_ptr_val ty loc (f s)) =
  (\s. let (x,s1) = f s in (LocatedValue ty (mk_ptr x loc),s1))
Proof
  simp[FUN_EQ_THM] >> gen_tac >> Cases_on `f s` >> simp[as_ptr_val_def]
QED

Theorem gas_shadow_compiles_as_ptr_val[local]:
  gas_shadow_compiles f g ==>
  gas_shadow_compiles (\s. as_ptr_val ty loc (f s)) (\s. as_ptr_val ty loc (g s))
Proof
  rewrite_tac[as_ptr_val_action] >>
  strip_tac >> ho_match_mp_tac gas_shadow_compiles_map_result >> simp[]
QED

Theorem gas_shadow_compiles_type_body_convert[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_type_builtin_dispatch_body f cenv vv_ty ty Convert ret_ty args)
    (compile_type_builtin_dispatch_body g cenv vv_ty ty Convert ret_ty
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def,
       GSYM comp_return_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   simp[gas_shadow_lowered_value_type] >>
   qmatch_goalsub_abbrev_tac `if zero_case then _ else _` >>
   Cases_on `zero_case` >> simp[]
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
       irule gas_shadow_compiles_return) >>
   qmatch_goalsub_abbrev_tac `if widen_case then _ else _` >>
   Cases_on `widen_case` >> simp[]
   >- (irule gas_shadow_compiles_as_stack_val >>
       irule gas_shadow_compiles_bytestring_widen_copy) >>
   Cases_on `ret_ty` >> simp[] >>
   irule gas_shadow_compiles_as_stack_val >>
   irule gas_shadow_compiles_type_convert)
QED

Theorem gas_shadow_compiles_type_body_extract32[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_type_builtin_dispatch_body f cenv vv_ty ty Extract32 ret_ty args)
    (compile_type_builtin_dispatch_body g cenv vv_ty ty Extract32 ret_ty
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `head_mode` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `offset_mode` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `head_mode` >> Cases_on `offset_mode` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def,
       comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[COND_CLAUSES] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- irule gas_shadow_compiles_bytestring_src >>
  qx_gen_tac `src` >> PairCases_on `src` >> simp[] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[COND_CLAUSES] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- irule gas_shadow_compiles_extract32_load >>
  gen_tac >> BETA_TAC >>
  irule gas_shadow_compiles_as_stack_val >>
  irule gasShadowCompileArithTheory.gas_shadow_compiles_clamp_basetype)
QED

Theorem gas_shadow_compiles_type_body_decode[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_type_builtin_dispatch_body f cenv vv_ty ty (AbiDecode unwrap) ret_ty args)
    (compile_type_builtin_dispatch_body g cenv vv_ty ty (AbiDecode unwrap) ret_ty
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def,
       comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gas_shadow_compiles_unwrap_value >>
   gen_tac >> BETA_TAC >>
   irule gas_shadow_compiles_as_ptr_val >>
   irule gasShadowCompileBuiltinAbiTheory.gas_shadow_compiles_lower_abi_decode)
QED

Theorem gas_shadow_compiles_type_body_encode[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_type_builtin_dispatch_body f cenv vv_ty ty (AbiEncode ensure method_id) ret_ty args)
    (compile_type_builtin_dispatch_body g cenv vv_ty ty (AbiEncode ensure method_id) ret_ty
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `MAP expr_type (if sh then MAP gas_shadow_expr args else args) = MAP expr_type args`
    by (Cases_on `sh` >> simp[MAP_MAP_o, combinTheory.o_DEF, ETA_THM]) >>
  `LENGTH (if sh then MAP gas_shadow_expr args else args) = LENGTH args`
    by (Cases_on `sh` >> simp[]) >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def] >>
  Cases_on `LENGTH args = 1 /\ ~ensure` >> simp[]
  >- (Cases_on `selected` >> gvs[] >>
      (Cases_on `is_word_type (expr_type (HD args))` >> simp[]
       >- (simp[GSYM comp_bind_def, comp_bind_uncurry] >>
           CONV_TAC (DEPTH_CONV ETA_CONV) >>
           match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- metis_tac[COND_CLAUSES] >>
           gen_tac >> BETA_TAC >>
           match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- irule gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer >>
           gen_tac >> BETA_TAC >>
           match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- irule gas_shadow_compiles_emit_void >>
           gen_tac >> BETA_TAC >>
           irule gas_shadow_compiles_as_ptr_val >>
           irule gasShadowCompileBuiltinAbiTheory.gas_shadow_compiles_lower_abi_encode) >>
       simp[GSYM comp_bind_def, comp_bind_uncurry] >>
       CONV_TAC (DEPTH_CONV ETA_CONV) >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- metis_tac[COND_CLAUSES] >>
       gen_tac >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- irule gas_shadow_compiles_unwrap_value >>
       gen_tac >> BETA_TAC >>
       irule gas_shadow_compiles_as_ptr_val >>
       irule gasShadowCompileBuiltinAbiTheory.gas_shadow_compiles_lower_abi_encode)) >>
  simp[GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (irule gas_shadow_compiles_abi_encode_args >> simp[]) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- irule gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- irule gasShadowCompileBuiltinAbiTheory.gas_shadow_compiles_store_abi_tuple >>
  gen_tac >> BETA_TAC >>
  irule gas_shadow_compiles_as_ptr_val >>
  irule gasShadowCompileBuiltinAbiTheory.gas_shadow_compiles_lower_abi_encode
QED

Theorem gas_shadow_compiles_type_body:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args)
    (compile_type_builtin_dispatch_body g cenv vv_ty ty tb ret_ty
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> Cases_on `tb`
  >- (CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_type_builtin_dispatch_body_def] >>
      Cases_on `is_word_type ret_ty` >> simp[]
      >- (simp[GSYM comp_return_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >>
          irule gas_shadow_compiles_return) >>
      simp[GSYM comp_bind_def, GSYM comp_return_def, comp_bind_uncurry] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      match_mp_tac gas_shadow_compiles_bind >> conj_tac
      >- irule gasShadowCompileArithTheory.gas_shadow_compiles_builtin_empty_complex >>
      gen_tac >> BETA_TAC >> simp[gas_shadow_compiles_return])
  >- (Cases_on `type_bounds ret_ty` >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_type_builtin_dispatch_body_def, GSYM comp_return_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return)
  >- (Cases_on `type_bounds ret_ty` >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_type_builtin_dispatch_body_def, GSYM comp_return_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return)
  >- (Cases_on `type_bounds ret_ty` >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_type_builtin_dispatch_body_def, GSYM comp_return_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return)
  >- (irule gas_shadow_compiles_type_body_convert >> simp[])
  >- (irule gas_shadow_compiles_type_body_extract32 >> simp[])
  >- (irule gas_shadow_compiles_type_body_decode >> simp[])
  >> irule gas_shadow_compiles_type_body_encode >> simp[]
QED

Theorem gas_shadow_compiles_expr_body_if[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_expr_body f bf tf cenv ty (IfExp et cond_e then_e else_e))
    (compile_expr_body g bg tg cenv ty
      (if sh then gas_shadow_expr (IfExp et cond_e then_e else_e)
       else IfExp et cond_e then_e else_e))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, GSYM comp_bind_def, GSYM comp_return_def,
       comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (gvs[COND_CLAUSES] >>
   simp[vyperASTTheory.expr_type_def, gas_shadow_lowered_value_type] >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_fresh_var, gas_shadow_compiles_fresh_label,
                gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
                gas_shadow_compiles_ifexp_arm] >>
        gen_tac >> BETA_TAC) >>
   qmatch_goalsub_abbrev_tac `if word_result then _ else _` >>
   Cases_on `word_result` >> simp[] >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- (simp[gas_shadow_compiles_ifexp_arm, gas_shadow_compiles_emit_inst,
                 gas_shadow_compiles_new_block] >> metis_tac[COND_CLAUSES]) >>
        gen_tac >> BETA_TAC) >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return)
QED

Theorem gas_shadow_compiles_expr_body_struct[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_expr_body f bf tf cenv ty (StructLit et name fields))
    (compile_expr_body g bg tg cenv ty
      (if sh then gas_shadow_expr (StructLit et name fields)
       else StructLit et name fields))
Proof
  strip_tac >>
  drule gas_shadow_compiles_struct_lit >> strip_tac >>
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def,
       GSYM comp_bind_def, GSYM comp_return_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >> simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_expr_body_pop[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_expr_body f bf tf cenv ty (Pop et target))
    (compile_expr_body g bg tg cenv ty
      (if sh then gas_shadow_expr (Pop et target) else Pop et target))
Proof
  strip_tac >>
  drule gas_shadow_compiles_get_target_ptr >> strip_tac >>
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def,
       GSYM comp_bind_def, GSYM comp_return_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   qx_gen_tac `place` >> PairCases_on `place` >> simp[] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gasShadowCompileCallSupportTheory.gas_shadow_compiles_dynarray_pop >>
   gen_tac >> BETA_TAC >> simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_expr_body_toplevel[local]:
  gas_shadow_compiles
    (compile_expr_body f bf tf cenv ty (TopLevelName et nsid))
    (compile_expr_body g bg tg cenv ty (TopLevelName et nsid))
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[]
  >- (simp[GSYM comp_bind_def, GSYM comp_return_def, comp_bind_uncurry] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      match_mp_tac gas_shadow_compiles_bind >>
      simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_return]) >>
  rename1 `SOME location` >> Cases_on `location` >> simp[] >>
  simp[GSYM comp_bind_def, GSYM comp_return_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_inst]
QED


Theorem expr_body_addmod_names[local]:
  compile_expr_body f bf tf cenv ty
    (Builtin et AddMod [Name at a; Name bt b; Name mt m]) =
  compile_addmod_names cenv et at a bt b mt m
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def]
QED

Theorem expr_body_mulmod_names[local]:
  compile_expr_body f bf tf cenv ty
    (Builtin et MulMod [Name at a; Name bt b; Name mt m]) =
  compile_mulmod_names cenv et at a bt b mt m
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def]
QED

Theorem expr_body_powmod_names[local]:
  compile_expr_body f bf tf cenv ty
    (Builtin et PowMod256 [Name at a; Name bt b]) =
  compile_powmod256_names cenv et at a bt b
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def]
QED


Theorem expr_body_builtin_default[local]:
  ~(bi = AddMod /\ ?at a bt b mt m.
      args = [Name at a; Name bt b; Name mt m]) /\
  ~(bi = MulMod /\ ?at a bt b mt m.
      args = [Name at a; Name bt b; Name mt m]) /\
  ~(bi = PowMod256 /\ ?at a bt b.
      args = [Name at a; Name bt b]) ==>
  compile_expr_body f bf tf cenv ty (Builtin et bi args) =
    bf cenv et ty bi args
Proof
  strip_tac >>
  Cases_on `bi = AddMod` >- (gvs[] >> suspend "add") >>
  Cases_on `bi = MulMod` >- (gvs[] >> suspend "mul") >>
  Cases_on `bi = PowMod256` >- (gvs[] >> suspend "pow") >>
  suspend "other"
QED

Resume expr_body_builtin_default[other]:
  Cases_on `args` >- (Cases_on `bi` >> gvs[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[]
  >- (Cases_on `bi` >> gvs[]) >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  Cases_on `bi` >> gvs[]
QED

Resume expr_body_builtin_default[add]:
  Cases_on `args` >- simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> gvs[]
QED

Resume expr_body_builtin_default[mul]:
  Cases_on `args` >- simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> gvs[]
QED

Resume expr_body_builtin_default[pow]:
  Cases_on `args` >- simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> gvs[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> simp[]
QED

Finalise expr_body_builtin_default

Theorem shadow_expr_eq_name[local,simp]:
  (gas_shadow_expr e = Name t n) <=> (e = Name t n)
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def]
QED

Theorem name_eq_shadow_expr[local,simp]:
  (Name t n = gas_shadow_expr e) <=> (Name t n = e)
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def]
QED

Theorem shadow_args_eq_names3[local,simp]:
  (MAP gas_shadow_expr args = [Name at a; Name bt b; Name mt m]) <=>
  (args = [Name at a; Name bt b; Name mt m])
Proof
  simp[MAP_EQ_CONS]
QED

Theorem shadow_args_eq_names2[local,simp]:
  (MAP gas_shadow_expr args = [Name at a; Name bt b]) <=>
  (args = [Name at a; Name bt b])
Proof
  simp[MAP_EQ_CONS]
QED

Theorem shadow_builtin_fast_tags[local,simp]:
  ((gas_shadow_builtin bi = AddMod) <=> (bi = AddMod)) /\
  ((gas_shadow_builtin bi = MulMod) <=> (bi = MulMod)) /\
  ((gas_shadow_builtin bi = PowMod256) <=> (bi = PowMod256))
Proof
  Cases_on `bi` >> simp[gas_shadow_builtin_def] >>
  Cases_on `e = MsgGas` >> simp[]
QED

Theorem gas_shadow_compiles_expr_body_builtin[local]:
  (!cenv et ty bi args sh.
    gas_shadow_compiles (bf cenv et ty bi args)
      (bg cenv et ty (if sh then gas_shadow_builtin bi else bi)
        (if sh then MAP gas_shadow_expr args else args))) ==>
  gas_shadow_compiles
    (compile_expr_body f bf tf cenv ty (Builtin et bi args))
    (compile_expr_body g bg tg cenv ty
      (if sh then gas_shadow_expr (Builtin et bi args)
       else Builtin et bi args))
Proof
  strip_tac >>
  Cases_on `bi = AddMod /\ ?at a bt b mt m.
    args = [Name at a; Name bt b; Name mt m]`
  >- (gvs[] >> Cases_on `sh` >>
      simp[gas_shadow_expr_def, gas_shadow_builtin_def,
           expr_body_addmod_names, gas_shadow_compiles_addmod_names]) >>
  Cases_on `bi = MulMod /\ ?at a bt b mt m.
    args = [Name at a; Name bt b; Name mt m]`
  >- (gvs[] >> Cases_on `sh` >>
      simp[gas_shadow_expr_def, gas_shadow_builtin_def,
           expr_body_mulmod_names, gas_shadow_compiles_mulmod_names]) >>
  Cases_on `bi = PowMod256 /\ ?at a bt b.
    args = [Name at a; Name bt b]`
  >- (gvs[] >> Cases_on `sh` >>
      simp[gas_shadow_expr_def, gas_shadow_builtin_def,
           expr_body_powmod_names, gas_shadow_compiles_powmod256_names]) >>
  `compile_expr_body f bf tf cenv ty (Builtin et bi args) =
    bf cenv et ty bi args` by (irule expr_body_builtin_default >> metis_tac[]) >>
  Cases_on `sh` >> gvs[gas_shadow_expr_def] >>
  simp[expr_body_builtin_default] >> metis_tac[COND_CLAUSES]
QED

Theorem gas_shadow_compiles_expr_body:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) /\
  (!cenv et ty bi args sh. gas_shadow_compiles (bf cenv et ty bi args)
    (bg cenv et ty (if sh then gas_shadow_builtin bi else bi)
      (if sh then MAP gas_shadow_expr args else args))) /\
  (!cenv vv_ty ty tb ret_ty args sh.
    gas_shadow_compiles (tf cenv vv_ty ty tb ret_ty args)
      (tg cenv vv_ty ty tb ret_ty (if sh then MAP gas_shadow_expr args else args))) ==>
  gas_shadow_compiles (compile_expr_body f bf tf cenv ty e)
    (compile_expr_body g bg tg cenv ty (if sh then gas_shadow_expr e else e))
Proof
  strip_tac >> Cases_on `e`
  >- suspend "name"
  >- suspend "top"
  >- suspend "flag"
  >- (irule gas_shadow_compiles_expr_body_if >> simp[])
  >- suspend "literal"
  >- (irule gas_shadow_compiles_expr_body_struct >> simp[])
  >- suspend "subscript"
  >- suspend "attribute"
  >- (irule gas_shadow_compiles_expr_body_builtin >> simp[])
  >- suspend "type"
  >- (irule gas_shadow_compiles_expr_body_pop >> simp[])
  >> suspend "call"
QED

Resume gas_shadow_compiles_expr_body[name]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gasShadowCompileLiteralTheory.gas_shadow_compiles_name_vv
QED

Resume gas_shadow_compiles_expr_body[top]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  irule gas_shadow_compiles_expr_body_toplevel
QED

Resume gas_shadow_compiles_expr_body[flag]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def, GSYM comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return
QED

Resume gas_shadow_compiles_expr_body[literal]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gasShadowCompileLiteralTheory.gas_shadow_compiles_literal_vv
QED

Resume gas_shadow_compiles_expr_body[subscript]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  metis_tac[gas_shadow_compiles_subscript, COND_CLAUSES]
QED

Resume gas_shadow_compiles_expr_body[attribute]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  metis_tac[gas_shadow_compiles_attribute, COND_CLAUSES]
QED

Resume gas_shadow_compiles_expr_body[type]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> metis_tac[COND_CLAUSES]
QED

Resume gas_shadow_compiles_expr_body[call]:
  Cases_on `sh` >> simp[gas_shadow_expr_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  metis_tac[gas_shadow_compiles_call, COND_CLAUSES]
QED

Finalise gas_shadow_compiles_expr_body

Theorem gas_shadow_compiles_builtin_body_simple[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) /\
  (bi = Len \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/
   bi = BlobHash \/ bi = Ceil \/ bi = Floor) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
    (compile_builtin_dispatch_body g cenv ret_ty ty bi
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >> irule gas_shadow_compiles_as_stack_val >>
   simp[gasShadowCompileArithTheory.gas_shadow_compiles_builtin_len,
        gas_shadow_compiles_neg, gasShadowCompileArithTheory.gas_shadow_compiles_builtin_abs,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_blockhash,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_blobhash,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_ceil,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_floor])
QED

Theorem gas_shadow_compiles_builtin_body_modular[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) /\
  (bi = AddMod \/ bi = MulMod) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
    (compile_builtin_dispatch_body g cenv ret_ty ty bi
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_a` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_b` assume_tac)
    gas_shadow_EL_alternative >>
  qspecl_then [`2`, `args`, `sh`] (qx_choose_then `sel_m` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >>
  Cases_on `sel_a` >> Cases_on `sel_b` >> Cases_on `sel_m` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (ntac 3 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_stack_val >>
   simp[gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_addmod,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_mulmod])
QED

Theorem gas_shadow_compiles_builtin_body_ptr_unary[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) /\
  (bi = CalldataSlice n \/ bi = Uint2Str n) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
    (compile_builtin_dispatch_body g cenv ret_ty ty bi
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   irule gas_shadow_compiles_as_ptr_val >>
   simp[gas_shadow_compiles_slice_calldata,
        gasShadowCompileBuiltinStringsTheory.gas_shadow_compiles_uint2str])
QED

Theorem gas_shadow_compiles_builtin_body_env[local]:
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (Env item) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty
      (if sh then gas_shadow_builtin (Env item) else Env item)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  Cases_on `sh` >> simp[gas_shadow_builtin_def] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >- (Cases_on `item = MsgGas` >> simp[] >>
      irule gas_shadow_compiles_as_stack_val >>
      simp[gasShadowCompileLiteralTheory.gas_shadow_compiles_env_var,
           gasShadowCompileLiteralTheory.gas_shadow_compiles_env_msggas]) >>
  irule gas_shadow_compiles_as_stack_val >>
  irule gasShadowCompileLiteralTheory.gas_shadow_compiles_env_var
QED

Theorem gas_shadow_compiles_builtin_body_not[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty Not args)
    (compile_builtin_dispatch_body g cenv ret_ty ty Not
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
   irule gas_shadow_compiles_as_stack_val >>
   simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_invert])
QED

Theorem gas_shadow_compiles_builtin_body_acc[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (Acc item) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (Acc item)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gas_shadow_compiles_as_stack_val >>
  metis_tac[gas_shadow_compiles_acc, COND_CLAUSES]
QED

Theorem gas_shadow_compiles_builtin_body_calldatalen[local]:
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty CalldataLen args)
    (compile_builtin_dispatch_body g cenv ret_ty ty CalldataLen args')
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gas_shadow_compiles_as_stack_val >>
  irule gasShadowCompileArithTheory.gas_shadow_compiles_builtin_calldatasize
QED

Theorem gas_shadow_compiles_builtin_body_powmod[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty PowMod256 args)
    (compile_builtin_dispatch_body g cenv ret_ty ty PowMod256
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_a` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_b` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sel_a` >> Cases_on `sel_b` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_stack_val >>
   irule gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_pow_mod256)
QED

Theorem gas_shadow_compiles_builtin_body_ecrecover[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty ECRecover args)
    (compile_builtin_dispatch_body g cenv ret_ty ty ECRecover
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_h` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_v` assume_tac)
    gas_shadow_EL_alternative >>
  qspecl_then [`2`, `args`, `sh`] (qx_choose_then `sel_r` assume_tac)
    gas_shadow_EL_alternative >>
  qspecl_then [`3`, `args`, `sh`] (qx_choose_then `sel_s` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sel_h` >> Cases_on `sel_v` >>
  Cases_on `sel_r` >> Cases_on `sel_s` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (ntac 4 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_stack_val >>
   irule gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_ecrecover)
QED

Theorem gas_shadow_compiles_builtin_body_ecadd[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty ECAdd args)
    (compile_builtin_dispatch_body g cenv ret_ty ty ECAdd
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_a` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_b` assume_tac)
    gas_shadow_EL_alternative >>
  Cases_on `sel_a` >> Cases_on `sel_b` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
    match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- irule gas_shadow_compiles_unwrap_value >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_ptr_val >>
   irule gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_ecadd_points)
QED

Theorem gas_shadow_compiles_builtin_body_ecmul[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty ECMul args)
    (compile_builtin_dispatch_body g cenv ret_ty ty ECMul
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_a` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_b` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sel_a` >> Cases_on `sel_b` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gas_shadow_compiles_unwrap_value >> gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   irule gas_shadow_compiles_as_ptr_val >>
   irule gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_ecmul_point)
QED

Theorem gas_shadow_compiles_builtin_body_wei[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (AsWeiValue denom) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (AsWeiValue denom)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   Cases_on `is_decimal_type (expr_type (HD args))` >> simp[] >>
   irule gas_shadow_compiles_as_stack_val >>
   simp[gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_as_wei_value_int,
        gasShadowCompileBuiltinScalarTheory.gas_shadow_compiles_as_wei_value_decimal])
QED

Theorem gas_shadow_compiles_builtin_body_methodid[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty MethodId args)
    (compile_builtin_dispatch_body g cenv ret_ty ty MethodId
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (Cases_on `method_id_literal (HD args)` >> simp[] >>
   CONV_TAC (DEPTH_CONV ETA_CONV)
   >- (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
       Cases_on `ret_ty = BaseT (BytesT (Fixed 4))` >> simp[] >>
       FIRST [irule gas_shadow_compiles_as_stack_val,
              irule gas_shadow_compiles_as_ptr_val] >>
       irule gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_method_id_runtime) >>
   irule gasShadowCompileLiteralTheory.gas_shadow_compiles_literal_vv)
QED

Theorem gas_shadow_compiles_builtin_body_makearray[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (MakeArray elem_ty_opt bnd) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (MakeArray elem_ty_opt bnd)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> Cases_on `elem_ty_opt` >> Cases_on `sh` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, MAP_MAP_o, combinTheory.o_DEF,
       GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer >> gen_tac >> BETA_TAC >>
   irule gas_shadow_compiles_as_ptr_val >>
   metis_tac[gas_shadow_compiles_make_tuple, gas_shadow_compiles_make_array,
             COND_CLAUSES])
QED

Theorem gas_shadow_compiles_builtin_body_concat[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (Concat max_len) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (Concat max_len)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> Cases_on `sh` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, MAP_MAP_o, combinTheory.o_DEF,
       GSYM comp_bind_def, comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (ntac 4 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
            gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void] >>
    gen_tac >> BETA_TAC) >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[gas_shadow_compiles_concat, COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void] >>
    gen_tac >> BETA_TAC) >>
   CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
   rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >> irule gas_shadow_compiles_return)
QED

Theorem gas_shadow_compiles_builtin_body_hash[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) /\
  (bi = Keccak256 \/ bi = Sha256) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
    (compile_builtin_dispatch_body g cenv ret_ty ty bi
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `selected` assume_tac)
    gas_shadow_HD_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `selected` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  Cases_on `expr_type (HD args)` >> simp[] >>
  TRY (rename1 `BaseT base_ty` >> Cases_on `base_ty` >> simp[]) >>
  TRY (rename1 `BytesT bound` >> Cases_on `bound` >> simp[]) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   irule gas_shadow_compiles_as_stack_val >>
   simp[gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_keccak256_bytes,
        gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_keccak256_bytesm,
        gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_keccak256_word,
        gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_sha256_bytes,
        gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_sha256_bytesm,
        gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_sha256_word])
QED

Theorem gas_shadow_compiles_builtin_body_slice[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (Slice max_len) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (Slice max_len)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_src` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`1`, `args`, `sh`] (qx_choose_then `sel_start` assume_tac)
    gas_shadow_EL_alternative >>
  qspecl_then [`2`, `args`, `sh`] (qx_choose_then `sel_len` assume_tac)
    gas_shadow_EL_alternative >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sel_src` >> Cases_on `sel_start` >> Cases_on `sel_len` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  Cases_on `is_msg_data (HD args)` >> simp[] >>
  Cases_on `is_self_code (HD args)` >> simp[] >>
  Cases_on `is_extcode (HD args)` >> simp[] >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- simp[gas_shadow_compiles_slice_out_buf,
            gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
            gas_shadow_compiles_emit_void, gas_shadow_compiles_bytestring_src] >>
    gen_tac >> BETA_TAC >>
    rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
      >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC)) >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >>~- ([`gas_shadow_compiles (\s. as_ptr_val _ _ (_ s)) _`],
    irule gas_shadow_compiles_as_ptr_val >>
    simp[gas_shadow_compiles_slice_calldata, gas_shadow_compiles_slice_code,
         gas_shadow_compiles_slice_extcode, gas_shadow_compiles_slice_data]) >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >>~- ([`gas_shadow_compiles (\s. as_ptr_val _ _ (_ s)) _`],
    irule gas_shadow_compiles_as_ptr_val >>
    simp[gas_shadow_compiles_slice_extcode, gas_shadow_compiles_slice_data]) >>
  rewrite_tac[comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- irule gas_shadow_compiles_bytestring_src >>
   gen_tac >> CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
   ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
     >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_ptr_val >>
   irule gas_shadow_compiles_slice_data)
QED

Theorem gas_shadow_compiles_builtin_body_bop[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty (Bop op) args)
    (compile_builtin_dispatch_body g cenv ret_ty ty (Bop op)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  qspecl_then [`args`, `sh`] (qx_choose_then `sel_a` assume_tac)
    gas_shadow_HD_alternative >>
  qspecl_then [`TL args`, `sh`] (qx_choose_then `sel_b` assume_tac)
    gas_shadow_HD_alternative >>
  `TL (if sh then MAP gas_shadow_expr args else args) =
   (if sh then MAP gas_shadow_expr (TL args) else TL args)`
    by (Cases_on `sh` >> simp[]) >>
  `!t e mode. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g cenv t (if mode then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value >> simp[]) >>
  Cases_on `sel_a` >> Cases_on `sel_b` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def, comp_bind_uncurry] >>
  (Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))` >> simp[]
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
       (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
       `!mode. gas_shadow_compiles
          (f cenv (expr_type (HD (TL args))) (HD (TL args)))
          (g cenv (expr_type (HD (TL args)))
            (if mode then gas_shadow_expr (HD (TL args)) else HD (TL args)))`
         by metis_tac[] >>
       `!es mode. gas_shadow_compiles (compile_multi_exprs f cenv es)
         (compile_multi_exprs g cenv (if mode then MAP gas_shadow_expr es else es))`
         by metis_tac[gas_shadow_compiles_multi_exprs] >>
       qpat_x_assum `!cenv ty e sh. _` kall_tac >>
       qpat_x_assum `!t e mode. _` kall_tac >>
       Cases_on `HD (TL args)` >> gvs[gas_shadow_expr_def] >>
       TRY (rename1 `Builtin ety tag es` >> Cases_on `tag` >> gvs[gas_shadow_builtin_def]) >>
       TRY (rename1 `Builtin _ (Env item) _` >> Cases_on `item = MsgGas` >> gvs[]) >>
       simp[GSYM comp_bind_def, comp_bind_uncurry] >>
       CONV_TAC (DEPTH_CONV ETA_CONV) >>
       (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- metis_tac[gas_shadow_compiles_multi_exprs, COND_CLAUSES] >>
        gen_tac >> BETA_TAC >> irule gas_shadow_compiles_as_stack_val >>
        Cases_on `op = In` >>
        simp[gasShadowCompileMembershipTheory.gas_shadow_compiles_list_membership_in,
             gasShadowCompileMembershipTheory.gas_shadow_compiles_list_membership_notin,
             gasShadowCompileMembershipTheory.gas_shadow_compiles_var_array_membership])) >>
   Cases_on `is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)` >> simp[]
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
       ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
         >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
       ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
         >- irule gasShadowCompileMembershipTheory.gas_shadow_compiles_bytestring_hash >>
         gen_tac >> BETA_TAC) >>
       (Cases_on `op = Eq` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
        >- (irule gas_shadow_compiles_as_stack_val >> simp[gas_shadow_compiles_emit_op]) >>
        match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC >>
        irule gas_shadow_compiles_as_stack_val >> simp[gas_shadow_compiles_emit_op])) >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >>
   ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
     >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC) >>
   irule gas_shadow_compiles_as_stack_val >>
   irule gasShadowCompileArithTheory.gas_shadow_compiles_binop)
QED

Theorem gas_shadow_compiles_builtin_body:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g cenv ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
    (compile_builtin_dispatch_body g cenv ret_ty ty
      (if sh then gas_shadow_builtin bi else bi)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> Cases_on `bi`
  >~ [`Env item`] >- irule gas_shadow_compiles_builtin_body_env >>
  simp[gas_shadow_builtin_def] >>
  FIRST (map (fn tac => tac >> NO_TAC)
    [irule gas_shadow_compiles_builtin_body_simple >> simp[],
     irule gas_shadow_compiles_builtin_body_modular >> simp[],
     irule gas_shadow_compiles_builtin_body_ptr_unary >> simp[],
     irule gas_shadow_compiles_builtin_body_hash >> simp[],
     irule gas_shadow_compiles_builtin_body_bop >> simp[],
     irule gas_shadow_compiles_builtin_body_not >> simp[],
     irule gas_shadow_compiles_builtin_body_acc >> simp[],
     irule gas_shadow_compiles_builtin_body_calldatalen,
     irule gas_shadow_compiles_builtin_body_powmod >> simp[],
     irule gas_shadow_compiles_builtin_body_ecrecover >> simp[],
     irule gas_shadow_compiles_builtin_body_ecadd >> simp[],
     irule gas_shadow_compiles_builtin_body_ecmul >> simp[],
     irule gas_shadow_compiles_builtin_body_wei >> simp[],
     irule gas_shadow_compiles_builtin_body_methodid >> simp[],
     irule gas_shadow_compiles_builtin_body_makearray >> simp[],
     irule gas_shadow_compiles_builtin_body_concat >> simp[],
     irule gas_shadow_compiles_builtin_body_slice >> simp[]])
QED
