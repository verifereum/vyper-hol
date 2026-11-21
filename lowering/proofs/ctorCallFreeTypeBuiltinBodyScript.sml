(* Open type-builtin dispatcher: only traversed children need be safe. *)
Theory ctorCallFreeTypeBuiltinBody
Ancestors
  list pair vyperAST compileEnv venomInst loweringShapeDefs loweringShapeProps
  emitHelper context exprLowering exprCallBounds exprCallbackContracts ctorCallFreeRules
  loweringCallArgsOpcodes ctorCallFreeCallbacks supportedExprTraverse e2eDeployDefs
  abiBuiltinDispatchCorrect exprBopLowering builtinAbi

Theorem type_builtin_member_callback[local]:
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\
      ~supported_expr_exists root2 e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ety e st)))) /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists root2 args ==>
  !e ety st. MEM e args ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ety e st)))
Proof
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[expr_list_member_bound, supported_exprs_exists_every, EXISTS_MEM]
QED

val member_callback_tac =
  drule_then (drule_then (drule_then
    (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO])))
  type_builtin_member_callback;

local
  val finish_ptr =
    qmatch_goalsub_abbrev_tac `as_ptr_val vv_ty LocMemory action` >>
    `EVERY (\i. P i.inst_opcode) (state_insts (SND action))` by
      (simp[Abbr `action`] >> first_assum irule >> simp[]) >>
    Cases_on `as_ptr_val vv_ty LocMemory action` >>
    drule as_ptr_val_result >> strip_tac >> gvs[];

  val extract_case =
    Cases_on `args` >- gvs[type_builtin_arity_def] >> rename1 `a::rest` >>
    Cases_on `rest` >- gvs[type_builtin_arity_def] >> rename1 `a::b::tail` >>
    simp[compile_type_builtin_dispatch_body_def, as_stack_val_pair] >> rpt strip_tac >>
    ntac 4 (pairarg_tac >> simp[]) >>
    rename1 `lower_value cfn cenv (expr_type a) a st = (_,st1)` >>
    rename1 `compile_bytestring_src _ st1 = (_,st2)` >>
    rename1 `lower_value cfn cenv ty b st2 = (_,st3)` >>
    rename1 `compile_extract32_load _ _ _ st3 = (_,st4)` >>
    `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
      (qpat_assum `!e ety. MEM e _ ==> !st. _ ==> EVERY _ (state_insts (SND (lower_value _ _ _ _ st)))` (qspecl_then [`a`, `expr_type a`] mp_tac) >>
       simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >>
       qpat_assum `lower_value _ _ (expr_type a) a st = _` (fn th => simp[NoAsms, th]) >> simp[]) >>
    `EVERY (\i. P i.inst_opcode) (state_insts st2)` by
      metis_tac[pairTheory.SND] >>
    `EVERY (\i. P i.inst_opcode) (state_insts st3)` by
      (qpat_assum `!e ety. MEM e _ ==> !st. _ ==> EVERY _ (state_insts (SND (lower_value _ _ _ _ st)))` (qspecl_then [`b`, `ty`] mp_tac) >>
       simp[NoAsms, MEM] >> disch_then (qspec_then `st2` mp_tac) >>
       qpat_assum `lower_value _ _ ty b st2 = _` (fn th => simp[NoAsms, th]) >> simp[]) >>
    `EVERY (\i. P i.inst_opcode) (state_insts st4)` by
      metis_tac[pairTheory.SND] >> simp[];

  val decode_case =
    Cases_on `args` >- gvs[type_builtin_arity_def] >> rename1 `arg::rest` >>
    simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
    ntac 2 (pairarg_tac >> simp[]) >>
    rename1 `cfn cenv (expr_type arg) arg st = (data_vv,st1)` >>
    rename1 `unwrap_value cenv data_vv st1 = (data_op,st2)` >>
    `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
      (qpat_assum `!e ety st. MEM e _ ==> _` (qspecl_then [`arg`, `expr_type arg`, `st`] mp_tac) >>
       qpat_assum `cfn _ _ _ st = _` (fn th => simp[NoAsms, th, MEM]) >> simp[]) >>
    `EVERY (\i. P i.inst_opcode) (state_insts st2)` by
      metis_tac[pairTheory.SND] >> finish_ptr;

  val encode_case =
    simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
    pairarg_tac >> simp[] >>
    rename1 `compile_abi_encode_args cfn cenv args st = (vs,st1)` >>
    `EVERY (\i. P i.inst_opcode) (state_insts st1)` by metis_tac[pairTheory.SND] >>
    finish_ptr;
in
Theorem outcomes_free_type_builtin_dispatch_body:
  P MSTORE ==>
  (
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) /\
  (!sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer sz st)))) /\
  (!v cop st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_convert v cop st)))) /\
  (!sz v srcsz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_bytestring_widen_copy sz v srcsz st)))) /\
  (!sz z st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_builtin_empty_complex sz z st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_bytestring_src v st)))) /\
  (!len data off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_extract32_load len data off st)))) /\
  (!v t st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_clamp_basetype v t st)))) /\
  (!mid n ce single vs tys st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_abi_encode mid n (compile_abi_encode_payload ce single vs tys) st)))) /\
  (!data info minsz maxsz outsz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_abi_decode data info minsz maxsz outsz st)))) /\
  (!ce t vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_materialize_vv ce t vv st)))) ==>
  !args cfn cenv vv_ty ty tb ret_ty.
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\
      ~supported_expr_exists root2 e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ety e st)))) /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_args cfn cenv args st)))) /\
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists root2 args ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  member_callback_tac >>
  `!e ety. MEM e args ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv ety e st)))` by
    (rpt strip_tac >> irule every_state_insts_lower_value >> simp[]) >>
  Cases_on `tb`
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Empty _ _`]
  >- (simp[compile_type_builtin_dispatch_body_def] >>
      Cases_on `is_word_type ret_ty` >> simp[] >> rpt strip_tac >>
      pairarg_tac >> simp[] >> metis_tac[pairTheory.SND])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ MaxValue _ _`]
  >- (simp[compile_type_builtin_dispatch_body_def] >> pairarg_tac >> simp[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ MinValue _ _`]
  >- (simp[compile_type_builtin_dispatch_body_def] >> pairarg_tac >> simp[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Epsilon _ _`]
  >- simp[compile_type_builtin_dispatch_body_def]
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Convert _ _`]
  >- suspend "convert"
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Extract32 _ _`]
  >- extract_case
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiDecode unwrap) _ _`]
  >- decode_case
  >> encode_case
QED

Resume outcomes_free_type_builtin_dispatch_body[convert]:
  Cases_on `args` >- gvs[type_builtin_arity_def] >> rename1 `arg::rest` >>
  simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
    (qpat_x_assum `!e ety. MEM e _ ==> !st. _ ==> EVERY _ (state_insts (SND (lower_value _ _ _ _ st)))`
       (qspecl_then [`arg`, `ety`] mp_tac) >>
     simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  rpt (IF_CASES_TAC >> simp[]) >> Cases_on `ret_ty` >>
  simp[as_stack_val_pair, as_ptr_val_pair] >> first_assum irule >> simp[]
QED

Finalise outcomes_free_type_builtin_dispatch_body

end

Theorem opcode_every_type_builtin_dispatch_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) /\
  (!sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer sz st)))) /\
  (!v cop st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_convert v cop st)))) /\
  (!sz v srcsz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_bytestring_widen_copy sz v srcsz st)))) /\
  (!sz z st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_builtin_empty_complex sz z st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_bytestring_src v st)))) /\
  (!len data off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_extract32_load len data off st)))) /\
  (!v t st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_clamp_basetype v t st)))) /\
  (!mid n ce single vs tys st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_abi_encode mid n (compile_abi_encode_payload ce single vs tys) st)))) /\
  (!data info minsz maxsz outsz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_abi_decode data info minsz maxsz outsz st)))) /\
  (!ce t vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_materialize_vv ce t vv st)))) ==>
  !args cfn cenv vv_ty ty tb ret_ty.
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\
      ~supported_expr_exists root2 e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ety e st)))) /\
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists root2 args ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args st)))
  )
Proof
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `P MSTORE` by simp[] >>
  member_callback_tac >>
  rpt strip_tac >> irule outcomes_free_type_builtin_dispatch_body >>
  simp[outcomes_free_abi_encode_args] >>
  qexistsl_tac [`R`, `root2`] >> simp[]
QED
