(* Builtin dispatcher: callbacks are restricted to traversed, smaller children. *)
Theory ctorCallFreeBuiltinBody
Ancestors
  list pair vyperAST compileEnv venomInst loweringShapeDefs loweringShapeProps
  emitHelper context exprLowering exprCallBounds exprCallbackContracts
  ctorCallFreeRules ctorCallFreeCallbacks supportedExprTraverse e2eDeployDefs
  exprBopLowering abiBuiltinDispatchCorrect ctorCallFreeValues builtinHashing builtinMisc

Theorem builtin_lower_value_child[local]:
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\ ~supported_expr_exists Q e ==>
    EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ety e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  ~supported_exprs_exists R args /\ ~supported_exprs_exists Q args ==>
  !e ety. MEM e args ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety e st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac every_state_insts_lower_value >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[expr_list_member_bound, supported_exprs_exists_every, EXISTS_MEM]
QED

Theorem builtin_lower_value_extcode[local]:
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\ ~supported_expr_exists Q e ==>
    EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ety e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  ~supported_exprs_exists R args /\ ~supported_exprs_exists Q args ==>
  !e ety. MEM e args /\ is_extcode e ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety (extcode_addr_expr e) st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac every_state_insts_lower_value >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[extcode_child_bound, expr_shape_extcode_addr, supported_exprs_exists_every, EXISTS_MEM]
QED

Theorem opcode_every_precompiles[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_sha256_word v st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_sha256_bytes v st)))) /\
  (!v m st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_sha256_bytesm v m st)))) /\
  (!h v r s st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ecrecover h v r s st)))) /\
  (!p1 p2 st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ecadd_points p1 p2 st)))) /\
  (!p s st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ecmul_point p s st))))
  )
Proof
  strip_tac >>
  rpt conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[builtinHashingTheory.compile_sha256_word_def,
    builtinHashingTheory.compile_sha256_bytes_def,
    builtinHashingTheory.compile_sha256_bytesm_def,
    builtinMiscTheory.compile_ecrecover_def,
    builtinMiscTheory.compile_ecadd_points_def,
    builtinMiscTheory.compile_ecmul_point_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_alloc_buffer), every_state_insts_return])])
QED

Theorem opcode_every_ec_ptr[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!t l p1 p2 st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (as_ptr_val t l (compile_ecadd_points p1 p2 st))))) /\
  (!t l p s st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (as_ptr_val t l (compile_ecmul_point p s st)))))
  )
Proof
  strip_tac >>
  rpt strip_tac >> qmatch_goalsub_abbrev_tac `as_ptr_val t l r` >>
  Cases_on `r` >> simp[as_ptr_val_def] >>
  fs[markerTheory.Abbrev_def] >> metis_tac[pairTheory.SND, (UNDISCH opcode_every_precompiles)]
QED

local
  fun branch "unary" g = (
  (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
  rpt strip_tac >> pairarg_tac >> simp[] >>
  first_assum irule >>
  rename1 `lower_value cfn cenv ety arg st = _` >>
  qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[])
) g

  | branch "uint2str" g = (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
    qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  qpat_x_assum `!v n sz st. _ ==> EVERY _ (state_insts (SND (compile_uint2str v n sz st)))`
    (qspecl_then [`v`, `n`, `type_memory_bytes cenv ret_ty`, `st1`] mp_tac) >> simp[] >>
  Cases_on `as_ptr_val ret_ty LocMemory (compile_uint2str v n (type_memory_bytes cenv ret_ty) st1)` >>
  drule as_ptr_val_result >> strip_tac >> gvs[]
) g

  | branch "calldataslice" g = (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
    qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  qpat_x_assum `!a b sz st. _ ==> EVERY _ (state_insts (SND (compile_slice_calldata a b sz st)))`
    (qspecl_then [`v`, `Lit (n2w n)`, `type_memory_bytes cenv ret_ty`, `st1`] mp_tac) >> simp[] >>
  Cases_on `as_ptr_val ret_ty LocMemory (compile_slice_calldata v (Lit (n2w n)) (type_memory_bytes cenv ret_ty) st1)` >>
  drule as_ptr_val_result >> strip_tac >> gvs[]
) g


  | branch "mod3" g = (
  (
  Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
  Cases_on `rest` >- gvs[] >> rename1 `a::b::tail` >>
  Cases_on `tail` >- gvs[] >> rename1 `a::b::c::rest` >>
  simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >> rpt strip_tac >>
  ntac 3 (pairarg_tac >> simp[]) >>
  first_assum irule >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`c`, `ty`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st2` mp_tac) >>
  qpat_assum `lower_value cfn cenv ty c st2 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`b`, `ty`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st1` mp_tac) >>
  qpat_assum `lower_value cfn cenv ty b st1 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`a`, `ty`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >>
  qpat_assum `lower_value cfn cenv ty a st = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >> simp[])
) g

  | branch "mod2" g = (
  Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
  Cases_on `rest` >- gvs[] >> rename1 `a::b::tail` >>
  simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >> rpt strip_tac >>
  ntac 2 (pairarg_tac >> simp[]) >>
  qpat_x_assum `!a b st. _ ==> EVERY _ (state_insts (SND (compile_pow_mod256 a b st)))` irule >>
  rename1 `lower_value cfn cenv ty b st1 = _` >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`b`, `ty`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st1` mp_tac) >>
  qpat_assum `lower_value cfn cenv ty b st1 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`a`, `ty`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >>
  qpat_assum `lower_value cfn cenv ty a st = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >> simp[]
) g

  | branch "wei" g = (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >> rpt strip_tac >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
    qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  Cases_on `is_decimal_type ety` >> simp[]
) g

  | branch "concat" g = (
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  ntac 7 (pairarg_tac >> simp[]) >>
  rename1 `compile_alloc_buffer _ st = (buf,st1)` >>
  rename1 `emit_op ADD _ st1 = (dp,st2)` >>
  rename1 `compile_alloc_buffer 64 st2 = (off,st3)` >>
  rename1 `emit_void MSTORE _ st3 = (_,s4)` >>
  rename1 `compile_concat cfn cenv args dp _ _ s4 = (_,s5)` >>
  rename1 `emit_op MLOAD _ s5 = (len,s6)` >>
  rename1 `emit_void MSTORE _ s6 = (_,s7)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts st2)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[SRULE [] (Q.INST [`opc` |-> `ADD`] opcode_every_emit_op),
      SRULE [] (Q.INST [`opc` |-> `MLOAD`] opcode_every_emit_op), pairTheory.SND]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts st3)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts s4)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[SRULE [] (Q.INST [`opc` |-> `MSTORE`] opcode_every_emit_void), pairTheory.SND]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts s5)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts s6)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[SRULE [] (Q.INST [`opc` |-> `ADD`] opcode_every_emit_op),
      SRULE [] (Q.INST [`opc` |-> `MLOAD`] opcode_every_emit_op), pairTheory.SND]) >>
  (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[SRULE [] (Q.INST [`opc` |-> `MSTORE`] opcode_every_emit_void), pairTheory.SND])
) g

  | branch "methodid" g = (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `method_id_literal arg` >> simp[] >>
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
    qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  Cases_on `ret_ty = BaseT (BytesT (Fixed 4))` >> simp[as_stack_val_pair] >>
  Cases_on `as_ptr_val ret_ty LocMemory (compile_method_id_runtime ety v F st1)` >>
  drule as_ptr_val_result >> strip_tac >>
  qpat_x_assum `!t v b st. _ ==> EVERY _ (state_insts (SND (compile_method_id_runtime t v b st)))`
    (qspecl_then [`ety`, `v`, `F`, `st1`] mp_tac) >> gvs[]
) g

  | branch "keccak" g = (
  Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
  rpt strip_tac >>
  Cases_on `lower_value cfn cenv (expr_type arg) arg st` >>
  rename1 `lower_value cfn cenv (expr_type arg) arg st = (v,st1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
    qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `expr_type arg`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `is_bytestring_type (expr_type arg)` >> simp[as_stack_val_pair] >>
  Cases_on `expr_type arg` >> simp[as_stack_val_pair] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[as_stack_val_pair] >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >> simp[as_stack_val_pair]
) g

  | branch "array" g = (
  Cases_on `ety`
  >- (simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
    pairarg_tac >> simp[] >>
    rename1 `compile_alloc_buffer sz st = (buf,st1)` >>
    `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
      (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]) >>
    qmatch_goalsub_abbrev_tac `compile_make_tuple cfn cenv args mtys buf.buf_operand 0 st1` >>
    Cases_on `as_ptr_val ret_ty LocMemory (compile_make_tuple cfn cenv args mtys buf.buf_operand 0 st1)` >>
    drule as_ptr_val_result >> strip_tac >>
    qpat_x_assum `!tys buf st. _ ==> EVERY _ (state_insts (SND (compile_make_tuple cfn cenv args tys buf 0 st)))`
      (qspecl_then [`mtys`, `buf.buf_operand`, `st1`] mp_tac) >> gvs[]) >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> simp[] >>
  rename1 `compile_alloc_buffer sz st = (buf,st1)` >>
  qmatch_goalsub_abbrev_tac `compile_make_array cfn cenv args elem_ty esz lw buf.buf_operand st1` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
    (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]) >>
  Cases_on `as_ptr_val ret_ty LocMemory (compile_make_array cfn cenv args elem_ty esz lw buf.buf_operand st1)` >>
  drule as_ptr_val_result >> strip_tac >>
  qpat_x_assum `!ety sz lw buf st. _ ==> EVERY _ (state_insts (SND (compile_make_array cfn cenv args ety sz lw buf st)))`
    (qspecl_then [`elem_ty`, `esz`, `lw`, `buf.buf_operand`, `st1`] mp_tac) >> gvs[]
) g

  | branch "bop" g = (
  Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
  Cases_on `rest` >- gvs[] >> rename1 `a::b::tail` >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `(bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type b)` >> simp[]
  >- branch "membership" >>
  Cases_on `is_bytestring_type (expr_type a) /\ (bop = Eq \/ bop = NotEq)` >> simp[]
  >- branch "compare" >>
  simp[as_stack_val_pair] >> ntac 2 (pairarg_tac >> simp[]) >>
  qpat_x_assum `!op a b t x y st. _ ==> EVERY _ (state_insts (SND (compile_binop op a b t x y st)))` irule >>
  rename1 `lower_value cfn cenv ety b st1 = _` >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`b`, `ety`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st1` mp_tac) >>
  qpat_assum `lower_value cfn cenv ety b st1 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >>
  qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`a`, `ety`] mp_tac) >>
  simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >>
  qpat_assum `lower_value cfn cenv ety a st = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >> simp[]
) g

  | branch "membership" g = (
  pairarg_tac >> simp[] >>
  rename1 `lower_value cfn cenv (expr_type a) a st = (needle,s1)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts s1)` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`a`, `expr_type a`] mp_tac) >>
    simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >>
    qpat_assum `lower_value cfn cenv (expr_type a) a st = _` (fn th => simp[NoAsms, th]) >>
    disch_then irule >> simp[]) >>
  Cases_on `b` >> simp[as_stack_val_pair] >>
  TRY (rename1 `Builtin ann builtin es` >> Cases_on `builtin` >> simp[as_stack_val_pair]) >>
  pairarg_tac >> simp[] >>
  TRY (rename1 `compile_multi_exprs cfn cenv es s1 = _` >> branch "member_literal") >>
  qpat_assum `!v vv t isin st. _ ==> EVERY _ (state_insts (SND (compile_var_array_membership cenv v vv t isin st)))` irule >>
  rename1 `cfn cenv ety rhs s1 = _` >>
  qpat_assum `!e ety st. MEM e _ ==> _` (qspecl_then [`rhs`, `ety`, `s1`] mp_tac) >>
  simp[NoAsms, MEM] >>
  qpat_assum `cfn cenv ety rhs s1 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >> simp[]
) g

  | branch "member_literal" g = (
  (
  rename1 `~supported_exprs_exists root2 (a::Builtin ann (MakeArray elem_ty bound) es::tail)` >>
  Cases_on `bop = In` >> simp[] >> first_assum irule >>
  qpat_assum `!ann ety bnd es st. MEM (Builtin ann (MakeArray ety bnd) es) _ ==> _`
    (qspecl_then [`ann`, `elem_ty`, `bound`, `es`, `s1`] mp_tac) >>
  simp[NoAsms, MEM] >>
  qpat_assum `compile_multi_exprs cfn cenv es s1 = _` (fn th => simp[NoAsms, th]) >>
  disch_then irule >> simp[])
) g

  | branch "compare" g = (
  `!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv (expr_type a) a s)))` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`a`, `expr_type a`] mp_tac) >> simp[NoAsms, MEM]) >>
  `!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv (expr_type a) b s)))` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspecl_then [`b`, `expr_type a`] mp_tac) >> simp[NoAsms, MEM]) >>
  Cases_on `bytestring_literal_hash a` >> simp[] >>
  Cases_on `bytestring_literal_hash b` >> simp[] >>
  ntac 2 (TRY (pairarg_tac >> simp[])) >>
  Cases_on `bop = Eq` >> simp[as_stack_val_pair] >>
  TRY (pairarg_tac >> simp[]) >>
  rpt (qpat_x_assum `(\(x,y). z) arg = rhs` mp_tac >> pairarg_tac >> simp[] >> strip_tac) >>
  (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND,
    SRULE [] (Q.INST [`opc` |-> `EQ`] opcode_every_emit_op),
    SRULE [] (Q.INST [`opc` |-> `ISZERO`] opcode_every_emit_op)])
) g

  | branch "slice" g = (
  Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
  Cases_on `rest` >- gvs[] >> rename1 `a::b::tail` >>
  Cases_on `tail` >- gvs[] >> rename1 `a::b::c::rest` >>
  `!ety s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv ety a s)))` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspec_then `a` mp_tac) >> simp[NoAsms, MEM]) >>
  `!ety s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv ety b s)))` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspec_then `b` mp_tac) >> simp[NoAsms, MEM]) >>
  `!ety s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv ety c s)))` by (
    qpat_assum `!e ety. MEM e _ ==> _` (qspec_then `c` mp_tac) >> simp[NoAsms, MEM]) >>
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `is_self_code a` >> simp[] >- branch "slice_short" >>
  Cases_on `is_extcode a` >> simp[] >- branch "slice_ext" >>
  pairarg_tac >> simp[] >>
  Cases_on `is_bytestring_type (expr_type a)` >> simp[] >> branch "slice_data"
) g

  | branch "slice_short" g = (
  (
  ntac 2 (pairarg_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val ret_ty LocMemory result` >>
  Cases_on `as_ptr_val ret_ty LocMemory result` >>
  drule as_ptr_val_result >> strip_tac >> gvs[] >>
  unabbrev_all_tac >> (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND]))
) g

  | branch "slice_ext" g = (
  `!ety s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv ety (extcode_addr_expr a) s)))` by (
    qpat_assum `!e ety. MEM e _ /\ is_extcode e ==> _` (qspec_then `a` mp_tac) >> simp[NoAsms, MEM] >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val ret_ty LocMemory result` >>
  Cases_on `as_ptr_val ret_ty LocMemory result` >>
  drule as_ptr_val_result >> strip_tac >> gvs[] >>
  unabbrev_all_tac >> (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND])
) g

  | branch "slice_data" g = (
  (
  ntac 3 (pairarg_tac >> simp[]) >>
  TRY (pairarg_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `as_ptr_val ret_ty LocMemory result` >>
  Cases_on `as_ptr_val ret_ty LocMemory result` >>
  drule as_ptr_val_result >> strip_tac >> gvs[] >>
  unabbrev_all_tac >> (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[pairTheory.SND,
    SRULE [] (Q.INST [`opc` |-> `MSTORE`] opcode_every_emit_void)]))
) g


  | branch "precompile" g = (
  simp[compile_builtin_dispatch_body_def, as_stack_val_pair, LET_THM,
    pairTheory.UNCURRY] >> rpt strip_tac >>
  rpt (FIRST [IF_CASES_TAC, CASE_TAC]) >> simp[as_stack_val_pair] >>
  rpt (FIRST [MAP_FIRST irule
    (CONJUNCTS (UNDISCH opcode_every_precompiles) @ CONJUNCTS (UNDISCH opcode_every_ec_ptr)),
    first_assum irule])
) g

  | branch label _ = raise Fail ("unknown builtin proof branch: " ^ label)
  fun child_facts qs =
    MAP_EVERY (fn q =>
      qpat_assum `!e ety. MEM e _ ==> _`
        (qspec_then q (assume_tac o SIMP_RULE (srw_ss()) [MEM])) >>
      qpat_assum `!e ety st. MEM e _ ==> _`
        (qspec_then q (assume_tac o SIMP_RULE (srw_ss()) [MEM]))) qs
  val prepare =
    strip_tac >> rpt gen_tac >> strip_tac >>
    `!e ety. MEM e args ==> !st.
      EVERY (\i. P i.inst_opcode) (state_insts st) ==>
      EVERY (\i. P i.inst_opcode)
        (state_insts (SND (lower_value cfn cenv ety e st)))`
      by (ho_match_mp_tac (Q.INST [`R` |-> `R`, `Q` |-> `root2`] builtin_lower_value_child) >> simp[]) >>
    `!e ety. MEM e args /\ is_extcode e ==> !st.
      EVERY (\i. P i.inst_opcode) (state_insts st) ==>
      EVERY (\i. P i.inst_opcode)
        (state_insts (SND (lower_value cfn cenv ety (extcode_addr_expr e) st)))`
      by (ho_match_mp_tac (Q.INST [`R` |-> `R`, `Q` |-> `root2`] builtin_lower_value_extcode) >> simp[]) >>
    `!e ety st. MEM e args ==>
      EVERY (\i. P i.inst_opcode) (state_insts st) ==>
      EVERY (\i. P i.inst_opcode)
        (state_insts (SND (cfn cenv ety e st)))`
      by (rpt strip_tac >> first_x_assum irule >>
          (`P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >> metis_tac[expr_list_member_bound, supported_exprs_exists_every, EXISTS_MEM])) >>
    qpat_x_assum `builtin_arity bi <= LENGTH args` mp_tac >>
    Cases_on `bi` >> simp[builtin_arity_def] >> ntac 2 strip_tac
in
Theorem opcode_every_builtin_dispatch_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer sz st)))) /\
  (!t lit st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_literal_vv t lit st)))) /\
  (!op a b t x y st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_binop op a b t x y st)))) /\
  (!v t st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_invert v t cenv st)))) /\
  (!v t st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_neg v t st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_abs v st)))) /\
  (!item st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_env_var item st)))) /\
  (!v ops st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_in v ops st)))) /\
  (!v ops st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_notin v ops st)))) /\
  (!v vv t isin st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_var_array_membership cenv v vv t isin st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_hash v st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytes v st)))) /\
  (!v m st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytesm v m st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_word v st)))) /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_calldatasize st)))) /\
  (!v loc st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca v loc st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blockhash v st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blobhash v st)))) /\
  (!a b c st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_addmod a b c st)))) /\
  (!a b c st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_mulmod a b c st)))) /\
  (!a b st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_pow_mod256 a b st)))) /\
  (!v d st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ceil v d st)))) /\
  (!v d st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_floor v d st)))) /\
  (!a b sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_calldata a b sz st)))) /\
  (!a b sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_code a b sz st)))) /\
  (!a b c d st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_extcode a b c d st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_src v st)))) /\
  (!sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_out_buf sz st)))) /\
  (!a b c d sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_data a b c d sz st)))) /\
  (!v n sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_uint2str v n sz st)))) /\
  (!v m d st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_decimal v m d st)))) /\
  (!v m s st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_int v m s st)))) /\
  (!t v b st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_method_id_runtime t v b st)))) ==>
  !bi args.
  builtin_arity bi <= LENGTH args /\
  ~supported_exprs_exists R args /\ ~supported_exprs_exists root2 args /\
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists R e /\ ~supported_expr_exists root2 e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn cenv ety e st)))) /\
  (!ann ety bnd es st. MEM (Builtin ann (MakeArray ety bnd) es) args ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_multi_exprs cfn cenv es st)))) /\
  (!e item st. MEM e args ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_acc cfn cenv e item st)))) /\
  (!dp infos off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_concat cfn cenv args dp infos off st)))) /\
  (!tys buf st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_make_tuple cfn cenv args tys buf 0 st)))) /\
  (!ety sz lw buf st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_make_array cfn cenv args ety sz lw buf st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args st)))
  )
Proof
  strip_tac >>
  `P ADD /\ P MLOAD /\ P MSTORE /\ P EQ /\ P ISZERO` by simp[] >>
    prepare >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop bop) args`] >- branch "bop" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (Slice maxlen) args`] >- branch "slice" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Keccak256 args`] >- branch "keccak" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray ety bnd) args`] >- branch "array" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ MethodId args`] >- branch "methodid" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Len args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
      `MEM arg (arg::rest)` by simp[] >>
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
      rpt strip_tac >> pairarg_tac >> simp[] >> first_assum irule >>
      qpat_x_assum `!e ety st. MEM e _ ==> _` (qspec_then `arg` mp_tac) >>
      simp[] >> disch_then (qspec_then `ty` mp_tac) >>
      disch_then (qspec_then `st` mp_tac) >> simp[]) >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (Env item) args`] >-
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ CalldataLen args`] >-
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Neg args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
      rpt strip_tac >> pairarg_tac >> simp[] >> first_assum irule >>
      qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `expr_type arg`] mp_tac) >>
      simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Abs args`] >- branch "unary" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ BlockHash args`] >- branch "unary" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ BlobHash args`] >- branch "unary" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Ceil args`] >- branch "unary" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Floor args`] >- branch "unary" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (Uint2Str n) args`] >- branch "uint2str" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (CalldataSlice n) args`] >- branch "calldataslice" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Not args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >>
      rpt strip_tac >> pairarg_tac >> simp[] >>
      rename1 `lower_value cfn cenv ety arg st = (v,st1)` >>
      `EVERY (\i. P i.inst_opcode) (state_insts st1)` by (
        qpat_x_assum `!e ety. MEM e _ ==> _` (qspecl_then [`arg`, `ety`] mp_tac) >>
        simp[NoAsms, MEM] >> disch_then (qspec_then `st` mp_tac) >> simp[]) >>
      Cases_on `ety = BaseT BoolT` >> simp[]
      >- (irule opcode_every_emit_op >> simp[]) >>
      qpat_x_assum `!v t st. _ ==> EVERY _ (state_insts (SND (compile_invert v t cenv st)))` irule >> simp[]) >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ AddMod args`] >- branch "mod3" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ MulMod args`] >- branch "mod3" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ PowMod256 args`] >- branch "mod2" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc item) args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `arg::rest` >>
      simp[compile_builtin_dispatch_body_def, as_stack_val_pair] >> rpt strip_tac >>
      qpat_x_assum `!e item st. MEM e _ ==> _` irule >> simp[]) >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue denom) args`] >- branch "wei" >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ Sha256 args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
      child_facts [`a`] >> branch "precompile") >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ ECRecover args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
      Cases_on `rest` >- gvs[] >> rename1 `a::b::rest` >>
      Cases_on `rest` >- gvs[] >> rename1 `a::b::c::rest` >>
      Cases_on `rest` >- gvs[] >> rename1 `a::b::c::d::rest` >>
      child_facts [`a`, `b`, `c`, `d`] >> branch "precompile") >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ ECAdd args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
      Cases_on `rest` >- gvs[] >> rename1 `a::b::rest` >>
      child_facts [`a`, `b`] >> branch "precompile") >>
    all_tac >~ [`compile_builtin_dispatch_body _ _ _ _ ECMul args`] >- (
      Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
      Cases_on `rest` >- gvs[] >> rename1 `a::b::rest` >>
      child_facts [`a`, `b`] >> branch "precompile") >>
    branch "concat"
QED

Theorem call_free_builtin_dispatch_body:
  (!vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_alloc_buffer sz st)))) /\
  (!t lit st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_literal_vv t lit st)))) /\
  (!op a b t x y st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_binop op a b t x y st)))) /\
  (!v t st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_invert v t cenv st)))) /\
  (!v t st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_neg v t st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_builtin_abs v st)))) /\
  (!item st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_env_var item st)))) /\
  (!v ops st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_list_membership_in v ops st)))) /\
  (!v ops st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_list_membership_notin v ops st)))) /\
  (!v vv t isin st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_var_array_membership cenv v vv t isin st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_bytestring_hash v st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_keccak256_bytes v st)))) /\
  (!v m st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_keccak256_bytesm v m st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_keccak256_word v st)))) /\
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_builtin_calldatasize st)))) /\
  (!v loc st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca v loc st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_blockhash v st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_blobhash v st)))) /\
  (!a b c st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_addmod a b c st)))) /\
  (!a b c st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_mulmod a b c st)))) /\
  (!a b st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_pow_mod256 a b st)))) /\
  (!v d st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_ceil v d st)))) /\
  (!v d st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_floor v d st)))) /\
  (!a b sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_slice_calldata a b sz st)))) /\
  (!a b sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_slice_code a b sz st)))) /\
  (!a b c d st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_slice_extcode a b c d st)))) /\
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_bytestring_src v st)))) /\
  (!sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_slice_out_buf sz st)))) /\
  (!a b c d sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_slice_data a b c d sz st)))) /\
  (!v n sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_uint2str v n sz st)))) /\
  (!v m d st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_as_wei_value_decimal v m d st)))) /\
  (!v m s st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_as_wei_value_int v m s st)))) /\
  (!t v b st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_method_id_runtime t v b st)))) ==>
  !bi args.
  builtin_arity bi <= LENGTH args /\
  ~supported_exprs_exists expr_call_root args /\ ~supported_exprs_exists root2 args /\
  (!e ety st. expr_size e < list_size expr_size args /\
      ~supported_expr_exists expr_call_root e /\ ~supported_expr_exists root2 e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (cfn cenv ety e st)))) /\
  (!ann ety bnd es st. MEM (Builtin ann (MakeArray ety bnd) es) args ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_multi_exprs cfn cenv es st)))) /\
  (!e item st. MEM e args ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_acc cfn cenv e item st)))) /\
  (!dp infos off st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_concat cfn cenv args dp infos off st)))) /\
  (!tys buf st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_make_tuple cfn cenv args tys buf 0 st)))) /\
  (!ety sz lw buf st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts (SND (compile_make_array cfn cenv args ety sz lw buf st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_builtin_dispatch_body) >> simp[]
QED
end
