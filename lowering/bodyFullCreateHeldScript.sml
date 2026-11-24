(*
 * The create body cases over the finite-horizon joint judgment, one per
 * create kind.
 *
 * TOP-LEVEL: create_minimal_proxy_expr_full_ok, create_copy_expr_full_ok,
 *   create_blueprint_expr_full_ok, raw_create_expr_full_ok
 *
 * These discharge case 47 of body_sim_full_mutual (the CreateTarget call),
 * whose hypothesis covers operands in interpreter evaluation order.
 *)
Theory bodyFullCreateHeld
Ancestors
  bodySingletonCallSupport
  blueprintLiteralOffsetProps[qualified,ignore_grammar]
  bodyFullForArrayRound[qualified,ignore_grammar]
  abiDecodeValidFiniteLoop[qualified,ignore_grammar]
  bodyFullExtCallPosAggregate[qualified,ignore_grammar]
  bodyFullAssign[qualified,ignore_grammar]
  bodyAugPlaceTarget[qualified,ignore_grammar]
  bodyFullDynamicBuffer[qualified,ignore_grammar]
  ptrDisciplineTaintProps[qualified,ignore_grammar]
  bodyFullPreds exprBodyPreProps bodyInvCodeProps[qualified,ignore_grammar]
  exprSimSend vyperLocalAccessFrame
  exprLowering builtinCreate vyperInterpreter vyperCreate vyperTypeSystem
  vyperState vyperAST compileEnv
  exprSimSource exprSimHypsDefs allocLimits vyperTypeCallGraph
  memoryReadProps venomMemProps list
  extCallOracleStep vyperFiniteStoragePreservation gasOutcomeFull
  extCallOracle venomCallOracleDefs venomExecSemantics vyperCallOutcome
  exprLoweringProps loweringStateRelDefs accountsRelProps vyperStorageFootprint
  venomState venomMemDefs
  venomInst fragGasSeqPtr ptrSafeRun ptrDiscipline unitTransformDefs memSafeRun
  memLocDefs codegenRel contextCodegenRel bodyPtrDefs
  lowerDloadPtrCreateInterfaces[qualified,ignore_grammar]
  bodyFullUnwrapRun[qualified,ignore_grammar] context emitHelper
  bodyPtrMakeArrayEmission[qualified] bodyPtrEnvBuiltinsEdges[qualified]
  ptrDisciplineEmptyTaint[qualified]
  fragGasOriginPtrLoop[qualified] fragGasOriginPtr[qualified] fragExec[qualified]
  fragGasOrigin[qualified] fragGasPathPtr[qualified]
  bodyFullAbiEncodeSetupTail[qualified] bodyFullAllocaFresh[qualified]
  bodyMemEcArithTransfers[qualified] bodyFullBuiltinECArithTransfers[qualified]
  stmtReasonLitFragMemory[qualified] bodyFullHashKeccakFixed[qualified]
  stmtFragPtr[qualified] exprPtrUnwrapFrames[qualified] exprSimStorageCopy[qualified]
  exprSimCalldataSlice[qualified] exprSimHash[qualified]
  exprSimCopy[qualified] bodyFullHashShaFrame[qualified]
  bodyFullPathHistory[qualified] bodyPtrIfExpAllocCompiler[qualified]
  valueEncodingProps[qualified] bodyFullUnwrapSlotPost[qualified]
  bodyFullExtCallDispatch[qualified] emitHelperProps[qualified] loweringHalt[qualified]
  gasShadow gasShadowState gasShadowCompileStmtHelpers[qualified]
  gasShadowCompileBuiltinCreate[qualified] gasShadowCompileHelpers[qualified]
  externalEntryShape[qualified] bodyFullExprGeneric[qualified]
  bodyFullExtCallDirectLayout[qualified] bodyFullExtCallDirectEncode[qualified]
  bodyFullExtCallDirectRow[qualified] bodyFullExtCallDirectState[qualified]
  abiEncodeValuesMetadata[qualified] abiEncodeValuesRun[qualified]
  abiDecoderMembers[qualified] vyperABIRoundtrip[qualified]
  vyperABI[qualified] vyperTypeArgFits[qualified] exprSimHyps[qualified]
  contractABI[qualified] bodySimLogArgs[qualified] allocaSiteResource[qualified]
  exprReasonOperand[qualified] bodyMemSnapshotSourceLocation[qualified]
  bodyStorageMetadata[qualified] entryStateRel[qualified]
  vyperTypeContractStaticMaps[qualified] vyperPlaceMutationSoundness[qualified]
  vyperPlaceResultTyping[qualified] vyperStoragePlaceProvenance[qualified]
  exprSimPopNestedBase[qualified] targetPlaceSim[qualified] bodySim[qualified]
  exprPtrUnwrapStorageShape[qualified] bodyFullExtCallPosTransport[qualified]
  abiEncodeArgsCase[qualified] abiEncodeMaterialize[qualified]
  abiEncodeArgsSim[qualified] valueCopyBytes[qualified]
  exprSimProps[qualified] exprSimUnwrapProps[qualified]
  vyperTypeExprSoundness vyperTypeInvariants vyperStoragePlaceObserved
  bodyFullExtCallDefaultKeyword[qualified] bodyFullExtCallPosWord[qualified]
  gasOriginPtrLabels[qualified]
  bodyPtrMakeArrayPrimitiveInstall[qualified] bodyPtrBytestringBuiltinsExternalSlice[qualified]
  wordLoadStorePtr[qualified] exprSimSliceExtcode[qualified] bodyFullAttributeAdd[qualified]
  bodyFullExtCallPrecheck[qualified] bodyPtrBopScalarSeq[qualified]
  bodyFullBopWordSuccess[qualified] bodyFullBopWordAbort[qualified] bodyPtrBopScalarOutcome[qualified]
  constSubstStmtsPreserve[qualified] vyperPinFoldProps[qualified]
Libs
  pairLib blastLib

Triviality create_compile_stack:
  compile_expr cenv ty (Call ann (CreateTarget kind salted rof ks) args dflt) sa =
    (StackValue ann (FST (compile_create_call compile_expr cenv kind salted rof args sa)),
     SND (compile_create_call compile_expr cenv kind salted rof args sa))
Proof
  simp[compile_expr_call, compile_call_def, as_stack_val_def] >>
  Cases_on `compile_create_call compile_expr cenv kind salted rof args sa` >>
  simp[as_stack_val_def]
QED

Theorem blueprint_compile_parts[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) sa = (result,sb) ==>
  ?x y sop p n off sz a b c d f k.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    compile_create_blueprint_args compile_expr cenv raw
      (amount::(salts ++ [offset])) ctor a = ((p,n),b) /\
    lower_value compile_expr cenv (expr_type amount) amount b = (y,c) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) c = (sop,d) /\
    (case origin_fold_value offset of
       Literal _ (IntL i) => comp_return (Lit (i2w i))
     | _ => lower_value compile_expr cenv (expr_type offset) offset) d = (off,f) /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value offset)) x off f = (sz,k) /\
    compile_create_blueprint_append x y sop off sz p n rof k = (result,sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lower_value compile_expr cenv ty
     (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
       (target::amount::(salts ++ offset::ctor)) dflt) =
   compile_create_call compile_expr cenv (CreateFromBlueprint raw) salted rof
     (target::amount::(salts ++ offset::ctor))` by
    (simp[FUN_EQ_THM, lower_value_def, create_compile_stack, unwrap_value_def,
          comp_bind_def, comp_return_def] >>
     gen_tac >> Cases_on
       `compile_create_call compile_expr cenv (CreateFromBlueprint raw) salted rof
          (target::amount::(salts ++ offset::ctor)) x` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `compile_create_call _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute,compile_create_call_def, comp_bind_def] >>
  pairarg_tac >> gvs[comp_bind_def] >>
  pairarg_tac >> gvs[comp_bind_def] >>
  pairarg_tac >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def]) >>
  strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem blueprint_compile_cuts[local]:
  gas_shadow_state sa sh /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt)) sh = (result,shb) /\
  LENGTH salts = (if salted then 1 else 0) ==>
  ?x y sop p n off sz a b c d f k a' b' c' d' f' k'.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    compile_create_blueprint_args compile_expr cenv raw
      (amount::(salts ++ [offset])) ctor a = ((p,n),b) /\
    lower_value compile_expr cenv (expr_type amount) amount b = (y,c) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) c = (sop,d) /\
    (case expr_int_literal (origin_fold_value offset) of
      SOME i => comp_return (Lit (i2w i))
    | NONE => lower_value compile_expr cenv (expr_type offset) offset) d = (off,f) /\
    compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset))) x off f = (sz,k) /\
    compile_create_blueprint_append x y sop off sz p n rof k = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target) (gas_shadow_expr target) sh = (x,a') /\
    compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) raw
      (MAP gas_shadow_expr (amount::(salts ++ [offset]))) (MAP gas_shadow_expr ctor) a' = ((p,n),b') /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount) (gas_shadow_expr amount) b' = (y,c') /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) c' = (sop,d') /\
    (case expr_int_literal (origin_fold_value offset) of
      SOME i => comp_return (Lit (i2w i))
    | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type offset) (gas_shadow_expr offset)) d' = (off,f') /\
    compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset))) x off f' = (sz,k') /\
    compile_create_blueprint_append x y sop off sz p n rof k' = (result,shb) /\
    gas_shadow_state a a' /\ gas_shadow_state b b' /\ gas_shadow_state c c' /\
    gas_shadow_state d d' /\ gas_shadow_state f f' /\ gas_shadow_state k k'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_compile_parts >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def,MAP_APPEND] >> strip_tac >>
  `LENGTH (MAP gas_shadow_expr salts) = (if salted then 1 else 0)` by simp[] >>
  drule_all blueprint_compile_parts >> strip_tac >>
  `(if salted then SOME (HD (MAP gas_shadow_expr salts)) else NONE) =
     OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)` by
    (Cases_on `salted` >> Cases_on `salts` >> gvs[]) >>
  gvs[gas_shadow_expr_type,blueprintLiteralOffsetPropsTheory.blueprint_offset_form,
      gasShadowCompileHelpersTheory.gas_shadow_origin_fold_value,
      gasShadowCompilePureTheory.gas_shadow_expr_int_literal] >>
  drule_all_then strip_assume_tac
    (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
      gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >> gvs[] >>
  `gas_shadow_compiles
     (compile_create_blueprint_args compile_expr cenv raw (amount::(salts ++ [offset])) ctor)
     (compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) raw
       (MAP gas_shadow_expr (amount::(salts ++ [offset]))) (MAP gas_shadow_expr ctor))` by
    (irule (SRULE [] (Q.INST [`sh` |-> `T`]
       gasShadowCompileHelpersTheory.gas_shadow_compiles_create_blueprint_args)) >>
     simp[cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env]) >>
  pop_assum (drule_all_then strip_assume_tac o
    MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut o SRULE [MAP_APPEND]) >> gvs[] >>
  drule_all_then strip_assume_tac
    (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
      gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >> gvs[] >>
  drule_all_then strip_assume_tac
    (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
      (SRULE [] (Q.INST [`sh` |-> `T`]
        (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_salt
          (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env))))) >> gvs[] >>
  `gas_shadow_compiles
    (case expr_int_literal (origin_fold_value offset) of
       SOME i => comp_return (Lit (i2w i))
     | NONE => lower_value compile_expr cenv (expr_type offset) offset)
    (case expr_int_literal (origin_fold_value offset) of
       SOME i => comp_return (Lit (i2w i))
     | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type offset) (gas_shadow_expr offset))` by
    (Cases_on `expr_int_literal (origin_fold_value offset)` >>
     simp[gas_shadow_compiles_return,gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env]) >>
  pop_assum (drule_all_then strip_assume_tac o
    MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut) >> gvs[] >>
  drule_all_then strip_assume_tac
    (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
      gasShadowCompileBuiltinCreateTheory.gas_shadow_compiles_create_blueprint_check) >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_create_compile_parts[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr ce ty
    (Call ann (CreateTarget RawCreate salted rof ks) (code::amount::(ctor ++ salts)) dflt)
    sa = (result,sb) ==>
  ?vv root len data ptr total v sp a b c d e f g.
    compile_expr ce (expr_type code) code sa = (vv,a) /\
    compile_create_snapshot ce vv (lowered_value_type ce code) a = (root,b) /\
    emit_op MLOAD [root] b = (len,c) /\
    emit_op ADD [root;Lit 32w] c = (data,d) /\
    lower_value compile_expr ce (expr_type amount) amount e = (v,f) /\
    compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE) f = (sp,g) /\
    compile_create_dispatch ptr total v sp rof g = (result,sb) /\
    (if ctor = [] then e = d /\ ptr = data /\ total = len else
      ?vals buf dst args_len r i j k m.
        compile_create_ctor_args compile_expr ce ctor d = (vals,r) /\
        compile_alloc_buffer (bytelike_type_bound (lowered_value_type ce code) +
          abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctor))) r = (buf,i) /\
        compile_copy_memory_dynamic buf.buf_operand data len i = ((),j) /\
        emit_op ADD [buf.buf_operand;len] j = (dst,k) /\
        compile_abi_encode_values_to_buf ce dst (ZIP (vals,MAP (lowered_value_type ce) ctor)) k = (args_len,m) /\
        emit_op ADD [len;args_len] m = (total,e) /\ ptr = buf.buf_operand)
Proof
  strip_tac >>
  `lower_value compile_expr ce ty
      (Call ann (CreateTarget RawCreate salted rof ks) (code::amount::(ctor ++ salts)) dflt) =
   compile_create_call compile_expr ce RawCreate salted rof (code::amount::(ctor ++ salts))` by
    (simp[FUN_EQ_THM,lower_value_def,create_compile_stack,unwrap_value_def,comp_bind_def,comp_return_def] >>
     gen_tac >> Cases_on `compile_create_call compile_expr ce RawCreate salted rof (code::amount::(ctor ++ salts)) x` >>
     simp[]) >>
  `compile_create_call compile_expr ce RawCreate salted rof (code::amount::(ctor ++ salts)) =
   compile_raw_create compile_expr ce code amount ctor (if salted then SOME (HD salts) else NONE) rof` by
    (Cases_on `salted` >> fs[LENGTH_EQ_NUM_compute] >>
     simp[compile_create_call_def,rich_listTheory.FRONT_APPEND]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = (result,sb)` mp_tac >>
  simp[] >>
  Cases_on `ctor = []` >>
  simp[compile_raw_create_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def]) >> strip_tac >> gvs[]
QED

Theorem raw_create_compile_cuts:
  gas_shadow_state sa sh /\ LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr ce ty
    (Call ann (CreateTarget RawCreate salted rof ks) (code::amount::(ctor ++ salts)) dflt)
    sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Call ann (CreateTarget RawCreate salted rof ks)
      (code::amount::(ctor ++ salts)) dflt)) sh = (result,shb) /\
  fn_has_code sa sb func /\ fn_has_code sh shb shfunc ==>
  ?vv root len data ptr total v sp a b c d e f g a' b' c' d' e' f' g'.
    compile_expr ce (expr_type code) code sa = (vv,a) /\
    compile_create_snapshot ce vv (lowered_value_type ce code) a = (root,b) /\
    emit_op MLOAD [root] b = (len,c) /\
    emit_op ADD [root;Lit 32w] c = (data,d) /\
    lower_value compile_expr ce (expr_type amount) amount e = (v,f) /\
    compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE) f = (sp,g) /\
    compile_create_dispatch ptr total v sp rof g = (result,sb) /\
    compile_expr (gas_shadow_env T ce) (expr_type code) (gas_shadow_expr code) sh = (vv,a') /\
    compile_create_snapshot ce vv (lowered_value_type ce code) a' = (root,b') /\
    emit_op MLOAD [root] b' = (len,c') /\
    emit_op ADD [root;Lit 32w] c' = (data,d') /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) e' = (v,f') /\
    compile_create_salt compile_expr (gas_shadow_env T ce)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) f' = (sp,g') /\
    compile_create_dispatch ptr total v sp rof g' = (result,shb) /\
    gas_shadow_state a a' /\ gas_shadow_state b b' /\ gas_shadow_state c c' /\ gas_shadow_state d d' /\
    gas_shadow_state e e' /\ gas_shadow_state f f' /\ gas_shadow_state g g' /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func /\
    fn_has_code d e func /\ fn_has_code e f func /\ fn_has_code f g func /\ fn_has_code g sb func /\
    fn_has_code sh a' shfunc /\ fn_has_code a' b' shfunc /\ fn_has_code b' c' shfunc /\ fn_has_code c' d' shfunc /\
    fn_has_code d' e' shfunc /\ fn_has_code e' f' shfunc /\ fn_has_code f' g' shfunc /\ fn_has_code g' shb shfunc /\
    (if ctor = [] then e = d /\ e' = d' /\ ptr = data /\ total = len else
      ?vals buf dst args_len r i j k m r' i' j' k' m' tys cap.
        tys = MAP (lowered_value_type ce) ctor /\
        cap = bytelike_type_bound (lowered_value_type ce code) +
              abi_size_bound ce.ce_struct_fields (TupleT tys) /\
        compile_create_ctor_args compile_expr ce ctor d = (vals,r) /\
        compile_alloc_buffer cap r = (buf,i) /\
        compile_copy_memory_dynamic buf.buf_operand data len i = ((),j) /\
        emit_op ADD [buf.buf_operand;len] j = (dst,k) /\
        compile_abi_encode_values_to_buf ce dst (ZIP (vals,tys)) k = (args_len,m) /\
        emit_op ADD [len;args_len] m = (total,e) /\ ptr = buf.buf_operand /\
        compile_create_ctor_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr ctor) d' = (vals,r') /\
        compile_alloc_buffer cap r' = (buf,i') /\
        compile_copy_memory_dynamic buf.buf_operand data len i' = ((),j') /\
        emit_op ADD [buf.buf_operand;len] j' = (dst,k') /\
        compile_abi_encode_values_to_buf ce dst (ZIP (vals,tys)) k' = (args_len,m') /\
        emit_op ADD [len;args_len] m' = (total,e') /\
        gas_shadow_state r r' /\ gas_shadow_state i i' /\ gas_shadow_state j j' /\
        gas_shadow_state k k' /\ gas_shadow_state m m' /\
        fn_has_code d r func /\ fn_has_code r i func /\ fn_has_code i j func /\
        fn_has_code j k func /\ fn_has_code k m func /\ fn_has_code m e func /\
        fn_has_code d' r' shfunc /\ fn_has_code r' i' shfunc /\ fn_has_code i' j' shfunc /\
        fn_has_code j' k' shfunc /\ fn_has_code k' m' shfunc /\ fn_has_code m' e' shfunc)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_create_compile_parts >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (Call _ (CreateTarget RawCreate _ _ _) _ _) _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Call _ _ _ _)) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def,MAP_APPEND] >> strip_tac >>
  `LENGTH (MAP gas_shadow_expr salts) = (if salted then 1 else 0)` by simp[] >>
  drule_all raw_create_compile_parts >> strip_tac >>
  `(if salted then SOME (HD (MAP gas_shadow_expr salts)) else NONE) =
   OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)` by
    (Cases_on `salted` >> Cases_on `salts` >> gvs[]) >>
  gvs[gas_shadow_expr_type,gasShadowCompilePureTheory.gas_shadow_lowered_value_type,
      MAP_MAP_o,combinTheory.o_DEF] >>
  `gas_shadow_compiles (compile_expr ce (expr_type code) code)
      (compile_expr (gas_shadow_env T ce) (expr_type code) (gas_shadow_expr code))` by
    irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_all_then strip_assume_tac bodyFullForArrayRoundTheory.nonslot_shadow_cut >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileCallSupportTheory.gas_shadow_compiles_create_snapshot) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >> gvs[] >>
  `gas_shadow_compiles (compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE))
    (compile_create_salt compile_expr (gas_shadow_env T ce)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)))` by
    irule (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_salt
             (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env) |>
           Q.INST [`sh` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ETA_AX]) >>
  Cases_on `ctor = []` >> gvs[]
  >- suspend "empty" >>
  `MAP (\x. lowered_value_type ce x) ctor = MAP (lowered_value_type ce) ctor` by
    simp[listTheory.MAP_EQ_f] >>
  pop_assum (rule_assum_tac o PURE_REWRITE_RULE o single) >>
  `gas_shadow_compiles (compile_create_ctor_args compile_expr ce ctor)
     (compile_create_ctor_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr ctor))` by
    irule (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_ctor_args
             (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env) |>
           Q.INST [`sh` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_all_then strip_assume_tac bodyFullForArrayRoundTheory.nonslot_shadow_cut >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_copy_memory_dynamic) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileExternalTheory.gas_shadow_compiles_abi_encode_values_to_buf) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >> gvs[] >>
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >> gvs[] >>
  qpat_x_assum `gas_shadow_compiles (compile_create_salt _ _ _) _`
    (drule_all_then strip_assume_tac o MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut) >> gvs[] >>
  `(ci_mono sa a /\ ci_mono sh a') /\ (ci_mono a b /\ ci_mono a' b') /\
   (ci_mono b c /\ ci_mono b' c') /\ (ci_mono c d /\ ci_mono c' d') /\
   (ci_mono d r /\ ci_mono d' r') /\ (ci_mono r i /\ ci_mono r' i') /\
   (ci_mono i j /\ ci_mono i' j') /\ (ci_mono j k /\ ci_mono j' k') /\
   (ci_mono k m /\ ci_mono k' m') /\ (ci_mono m e /\ ci_mono m' e') /\
   (ci_mono e f /\ ci_mono e' f') /\ (ci_mono f g /\ ci_mono f' g')` by
    (conj_tac >- metis_tac[compile_expr_ci_mono,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_create_snapshot,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_copy_memory_dynamic,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
     metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends g sb /\ cs_extends g' shb` by
    metis_tac[externalEntryShapeTheory.compile_create_dispatch_labels,pairTheory.SND] >>
  fs[ci_mono_def] >> ntac 4 (imp_res_tac cs_extends_trans) >>
  rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
  qpat_assum `fn_has_code _ _ _` (irule_at Any) >> simp[cs_extends_refl]
QED
Resume raw_create_compile_cuts[empty]:
  drule_all_then strip_assume_tac (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut
    gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >> gvs[] >>
  qpat_x_assum `gas_shadow_compiles (compile_create_salt _ _ _) _`
    (drule_all_then strip_assume_tac o MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut) >> gvs[] >>
  `(ci_mono sa a /\ ci_mono sh a') /\ (ci_mono a b /\ ci_mono a' b') /\
   (ci_mono b c /\ ci_mono b' c') /\ (ci_mono c d /\ ci_mono c' d') /\
   (ci_mono d f /\ ci_mono d' f') /\ (ci_mono f g /\ ci_mono f' g')` by
    (conj_tac >- metis_tac[compile_expr_ci_mono,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_create_snapshot,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
     metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends g sb /\ cs_extends g' shb` by
    metis_tac[externalEntryShapeTheory.compile_create_dispatch_labels,pairTheory.SND] >>
  fs[ci_mono_def] >> ntac 3 (imp_res_tac cs_extends_trans) >>
  rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
  qpat_assum `fn_has_code _ _ _` (irule_at Any) >> simp[cs_extends_refl]
QED
Finalise raw_create_compile_cuts

Triviality create_eval_value:
  eval_expr cx (Call ann (CreateTarget kind salted rof ks) args dflt) es =
    (INL tv, ee) ==> ?v. tv = Value v
Proof
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx (create_operand_order kind salted args) es` >>
  rename1 `eval_exprs _ _ _ = (res, mid)` >>
  Cases_on `res` >> simp[] >>
  metis_tac[eval_create_operands_success_value]
QED

Theorem proxy_pre_args:
  expr_body_pre cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts.
    args = target :: amount :: salts /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = [])
Proof
  strip_tac >> drule expr_body_pre_static_facts >>
  Cases_on `salted` >>
  simp[well_typed_expr_def, create_arg_types_ok_def, listTheory.MAP_EQ_CONS] >>
  metis_tac[]
QED

Triviality compile_proxy_parts:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) ==>
  ?target_op amount_op buf salt_op s1 s2 s3 s4.
    lower_value compile_expr cenv (expr_type target) target sa = (target_op,s1) /\
    lower_value compile_expr cenv (expr_type amount) amount s1 = (amount_op,s2) /\
    compile_create_proxy_buf target_op s2 = (buf,s3) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) s3 = (salt_op,s4) /\
    compile_create_dispatch buf (Lit 54w) amount_op salt_op rof s4 = (result,sb)
Proof
  strip_tac >>
  `lower_value compile_expr cenv ty
     (Call ann (CreateTarget CreateMinimalProxy salted rof ks)
       (target::amount::salts) dflt) =
   compile_create_call compile_expr cenv CreateMinimalProxy salted rof
     (target::amount::salts)` by
    (simp[FUN_EQ_THM, lower_value_def, create_compile_stack, unwrap_value_def,
          comp_bind_def, comp_return_def] >>
     gen_tac >> Cases_on
       `compile_create_call compile_expr cenv CreateMinimalProxy salted rof
          (target::amount::salts) x` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `compile_create_call _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_call_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem create_eval_read:
  bind (eval_expr cx (Call ann (CreateTarget kind salted rof ks) args dflt))
    (read_result cx) =
  bind (eval_exprs cx (create_operand_order kind salted args))
    (\values. bind (eval_create_operands cx kind salted rof (MAP expr_type args)
      (blueprint_literal_offset cx salted args) values) (read_result cx))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem create_operand_pre:
  expr_body_pre cenv cx env (Call ann (CreateTarget kind salted rof ks) args dflt) es /\
  MEM e args /\ expr_sim_inv cenv cx env ee ==>
  expr_body_pre cenv cx env e ee
Proof
  rw[expr_body_pre_split_def, expr_body_pre_mods_def, expr_sim_inv_split_def,
     well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every,
     listTheory.EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Triviality proxy_aligned_target_bytes:
  TAKE 20 (word_to_bytes ((word:bytes32) << 96) T) =
  word_to_bytes (w2w word:address) T
Proof
  simp[byteTheory.word_to_bytes_def, byteTheory.word_to_bytes_aux_compute,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  BBLAST_TAC
QED

Triviality proxy_initcode_stores:
  read_memory pbase 54
    (mstore (pbase + 39)
      0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w
      (mstore (pbase + 19) (word << 96)
        (mstore pbase
          0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w
          s))) =
  minimal_proxy_initcode (w2w word)
Proof
  mp_tac (Q.SPECL [`pbase`,`19`,`35`] read_memory_split) >>
  mp_tac (Q.SPECL [`pbase+19`,`20`,`15`] read_memory_split) >>
  simp[arithmeticTheory.ADD_ASSOC] >> rpt strip_tac >>
  asm_rewrite_tac [] >>
  simp[read_memory_mstore_disjoint] >>
  `!a n v s. n <= 32 ==> read_memory a n (mstore a v s) =
    TAKE n (word_to_bytes v T)` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`a`,`32`,`0`,`n`,`mstore a v s`] read_memory_subwindow) >>
     simp[read_memory_word, mload_mstore_same]) >>
  simp[proxy_aligned_target_bytes] >>
  `TAKE 19 (word_to_bytes
     (0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w:bytes32) T) =
   minimal_proxy_loader ++ minimal_proxy_forwarder_pre` by EVAL_TAC >>
  `TAKE 15 (word_to_bytes
     (0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w:bytes32) T) =
   minimal_proxy_forwarder_post` by EVAL_TAC >>
  ASM_REWRITE_TAC [minimal_proxy_initcode_def, minimal_proxy_runtime_def,
                   APPEND_ASSOC]
QED

(* CREATE adopts the backend on both success and failure. Only its logs
   and deletion queue are conditional on the success bit. *)
Theorem create_paired_adoption:
  ee.outcomes = SOME (oc::rest) /\ s.vs_outcomes = oc::rest /\
  outcomes_accounts_typed ee.outcomes /\
  read_memory (w2n off) (w2n sz) s = code /\ w2n w = value /\
  w2n sz <= 2 * max_code_size /\ inst.inst_outputs = [out] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\
       storage_well_formed_on cx ee (FST H)) ==>
  ?ee' t a rq rq'.
    rq = create_outcome_request
      (case salt of NONE => CreateCall | SOME sl => Create2Call sl) value code ee /\
    rq' = venom_create_request s w off sz salt /\
    consume_create_outcome rq' s = (w2w a,t) /\
    exec_create inst s w off sz salt = OK (update_var out (w2w a) t) /\
    a = (if oc.co_success then oc.co_created else 0w) /\
    (!tail. create_oracle_result salt value code rof (ee with gas_obs := tail) =
      (if a = 0w /\ rof then INR (Error (RevertData oc.co_returnData))
       else INL (Value (AddressV a)), ee' with gas_obs := tail)) /\
    ee'.scopes = ee.scopes /\ ee'.immutables = ee.immutables /\
    ee'.outcomes = SOME rest /\ ee'.requests = ee.requests ++ [rq] /\
    ee'.storage_trace = ee.storage_trace ++
      [StorageOutcome rq oc; StorageBackend oc.co_accounts oc.co_tStorage] /\
    t.vs_outcomes = rest /\ t.vs_requests = s.vs_requests ++ [rq'] /\
    t.vs_returndata = oc.co_returnData /\
    LENGTH oc.co_returnData < dimword (:256) /\
    t = s with <|vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := oc.co_accounts; vs_transient := oc.co_tStorage;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := oc.co_returnData|> /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      request_agree H cx.txn.target rq rq' /\ stmt_state_rel H ctx func cenv cx ee' t) /\
    (!H. valid_horizon cx st0 H ee'.storage_trace ==>
      valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx ee' (FST H))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `accounts_runtime_well_typed oc.co_accounts /\
   LENGTH oc.co_returnData < dimword (:256)` by gvs[outcomes_accounts_typed_def] >>
  qabbrev_tac `k = case salt of NONE => CreateCall | SOME sl => Create2Call sl` >>
  `k <> MessageCall /\ k <> DelegateMessageCall` by
    (Cases_on `salt` >> simp[Abbr `k`]) >>
  qabbrev_tac `rq = create_outcome_request k value code ee` >>
  qabbrev_tac `rq' = venom_create_request s w off sz salt` >>
  qabbrev_tac `taken = ee with <|outcomes := SOME rest;
    requests := ee.requests ++ [rq];
    storage_trace := ee.storage_trace ++ [StorageOutcome rq oc]|>` >>
  qabbrev_tac `ee' = taken with <|accounts := oc.co_accounts;
    tStorage := oc.co_tStorage; logs := if oc.co_success then ee.logs ++ oc.co_logs else ee.logs;
    pending_deletions := if oc.co_success then oc.co_toDelete ++ ee.pending_deletions
      else ee.pending_deletions;
    storage_trace := ee.storage_trace ++
      [StorageOutcome rq oc; StorageBackend oc.co_accounts oc.co_tStorage]|>` >>
  qabbrev_tac `t = s with <|vs_outcomes := rest; vs_requests := s.vs_requests ++ [rq'];
    vs_accounts := oc.co_accounts; vs_transient := oc.co_tStorage;
    vs_logs := if oc.co_success then s.vs_logs ++ oc.co_logs else s.vs_logs;
    vs_pending_deletions := if oc.co_success then oc.co_toDelete ++ s.vs_pending_deletions
      else s.vs_pending_deletions; vs_returndata := oc.co_returnData|>` >>
  qabbrev_tac `a = if oc.co_success then oc.co_created else 0w` >>
  `rq'.cr_kind = k /\ ~rq'.cr_static /\ ~computed_precompile rq'` by
    simp[Abbr `rq'`, venom_create_request_def, computed_precompile_def, Abbr `k`] >>
  `consume_create_outcome rq' s = (w2w a,t)` by
    (Cases_on `oc.co_success` >>
     simp[take_outcome_ordinary, adopt_outcome_def, adopt_outcome_deletions_def,
          Abbr `a`, Abbr `t`, wordsTheory.w2w_0]) >>
  `adopt_call_outcome rq oc taken = (INL (),ee')` by
    simp[Abbr `rq`, adopt_create_outcome_equation, Abbr `ee'`, Abbr `taken`,
         evaluation_state_component_equality] >>
  `!tail. create_oracle_result salt value code rof (ee with gas_obs := tail) =
      (if a = 0w /\ rof then INR (Error (RevertData oc.co_returnData))
       else INL (Value (AddressV a)), ee' with gas_obs := tail)` by
    (gen_tac >>
     `create_outcome_request k value code (ee with gas_obs := tail) = rq` by
       simp[Abbr `rq`, create_outcome_request_def] >>
     `take_create_outcome k value code (ee with gas_obs := tail) =
       (INL (rq,oc),taken with gas_obs := tail)` by
       (mp_tac (Q.INST [`st` |-> `ee with gas_obs := tail`,
           `kind` |-> `k`, `initcode` |-> `code`, `rq` |-> `rq`,
           `outcome` |-> `oc`, `rest` |-> `rest`]
          vyperCallOutcomeTheory.take_create_outcome_ordinary) >>
        simp[Abbr `taken`, evaluation_state_component_equality]) >>
     `adopt_call_outcome rq oc (taken with gas_obs := tail) =
       (INL (),ee' with gas_obs := tail)` by
       simp[Abbr `rq`, adopt_create_outcome_equation, Abbr `ee'`, Abbr `taken`,
            evaluation_state_component_equality] >>
     simp[create_oracle_result_def] >>
     qpat_assum `Abbrev (k = _)` (fn th =>
       simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     Cases_on `oc.co_success` >> Cases_on `oc.co_created = 0w` >>
     Cases_on `rof` >> simp[Abbr `a`]) >>
  `ee'.storage_trace = ee.storage_trace ++
      [StorageOutcome rq oc; StorageBackend oc.co_accounts oc.co_tStorage]` by
    simp[Abbr `ee'`, Abbr `taken`] >>
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx ee' (FST H)` by
    (rpt gen_tac >> disch_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by metis_tac[valid_horizon_append] >>
     simp[] >>
     `storage_well_formed_on cx taken (FST H)` by
       (`taken.accounts = ee.accounts /\ taken.tStorage = ee.tStorage` by
          simp[Abbr `taken`] >> metis_tac[storage_well_formed_on_backends]) >>
     irule adopt_call_outcome_preserves_finite_storage >>
     conj_tac >- fs[valid_horizon_def] >>
     goal_assum drule >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       request_agree H cx.txn.target rq rq' /\ stmt_state_rel H ctx func cenv cx ee' t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >> strip_tac >>
     `state_rel H func cenv cx ee s` by fs[stmt_state_rel_def] >>
     `request_agree H cx.txn.target rq rq'` by
       (`LENGTH code = w2n sz` by
          (qpat_assum `read_memory _ _ _ = code` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
           simp[]) >>
        drule state_rel_accounts >>
        simp[request_agree_def, Abbr `rq`, Abbr `rq'`, Abbr `k`,
             create_outcome_request_def, venom_create_request_def,
             call_request_component_equality]) >>
     simp[] >>
     `!p. eval_operand p t = eval_operand p s` by
       (Cases >> simp[eval_operand_def, lookup_var_def, Abbr `t`]) >>
     `s.vs_call_ctx.cc_address = cx.txn.target` by fs[state_rel_def, call_ctx_rel_def] >>
     `immutable_base_zero cenv t <=> immutable_base_zero cenv s` by
       (simp[immutable_base_zero_def] >> simp[Abbr `t`]) >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ ee s`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`consume_create_outcome rq' s = _`, `adopt_call_outcome rq oc taken = _`,
        `!tail. create_oracle_result salt value code rof (ee with gas_obs := tail) = _`,
        `ee'.storage_trace = _`,
        `!H. valid_horizon cx st0 H ee'.storage_trace ==> _`,
        `!H. valid_horizon cx st0 H ee.storage_trace ==> _`,
        `state_rel H func cenv cx ee s`] >>
     Cases_on `oc.co_success` >>
     fs[stmt_state_rel_def, state_rel_def, Abbr `ee'`, Abbr `taken`, Abbr `t`,
        local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def,
        alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
        alloca_room_def, fmp_room_def, pending_alloca_size_def,
        immutable_alloca_sep_def, immutable_base_zero_def,
        storage_rel_def, transient_rel_def, contract_storage_def, contract_transient_def,
        accounts_rel_def, immutables_rel_def, extCallOracleStepTheory.logs_rel_eq,
        listTheory.LIST_REL_APPEND] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ee'`,`t`,`a`,`rq`,`rq'`] >>
  simp[exec_create_def] >>
  simp[Abbr `t`, Abbr `ee'`, Abbr `taken`, Abbr `rq`, Abbr `rq'`, Abbr `k`, Abbr `a`]
QED

(* CREATE reads its input window but has no caller-memory output window. *)
Theorem create_origin_edge[local]:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  eval_operand amount s = SOME value /\
  eval_operand bufop s = SOME off /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. bufop = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n off + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n off /\
     w2n off + w2n sz <= w2n s.vs_fmp)) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n off <= j /\ j < w2n off + w2n sz ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  stor_taint_ok_at D tn s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = OK u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
   source_memory_write_ranges inst s = [] /\
   mem_read_ops inst = SOME <|iao_ofst := bufop; iao_size := SOME len;
                              iao_max_size := SOME len|>` by
    simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
         memory_range_of_operands_def, mem_read_ops_def] >>
  `access_ok lo G func inst s` by
    (simp[access_ok_def] >> rpt strip_tac >>
     `sz <> 0w` by fs[] >>
     qpat_assum `sz <> 0w ==> ?p. _` drule >> strip_tac >>
     gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (irule ptrDisciplineTaintPropsTheory.taint_ok_clean_step >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (gvs[ptr_inst_ok_def, stor_taint_ok_at_def, step_inst_non_invoke] >>
     metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   ~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `mem_safe_step 0 ctx inst s` by
    (Cases_on `sz = 0w` >>
     simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
          inst_mem_below_frontiers_def, wordsTheory.w2n_eq_0] >> metis_tac[]) >>
  irule bodyFullRawCallCallOriginTheory.non_gas_mem_safe_origin_ptr_edge >> simp[]
QED

(* World fields may change; the local and return pointers use only the
   unchanged memory and the pre-existing registers. *)
Theorem create_ghost_frame[local]:
  ghost_inv_at D lo d cenv cx es G tn s /\ es'.scopes = es.scopes /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
  z.vs_alloca_next = s.vs_alloca_next /\ tf.t_mem = tn.t_mem /\
  stor_taint_ok_at D tf z ==>
  ghost_inv_at D lo d cenv cx es' Gf tf z
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p z sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[local_ptrs_reserved_def]
QED

(* The origin edge and the post share the actual ghosts of the same
   consumed CREATE/CREATE2 instruction. In particular, a failed head
   still clears storage and transient taint. *)
Theorem create_consumed_origin_ghost:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  inst.inst_outputs = [out] /\
  eval_operand amount s = SOME value /\
  eval_operand bufop s = SOME off /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. bufop = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n off + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n off /\
     w2n off + w2n sz <= w2n s.vs_fmp)) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n off <= j /\ j < w2n off + w2n sz ==> j NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = OK u /\
  consume_create_outcome rq s = (result,t) /\ u = update_var out result t /\
  ghost_inv_at D lo d cenv cx es G tn s /\ es'.scopes = es.scopes /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK (u with vs_inst_idx := SUC s.vs_inst_idx),(step_prov PG G inst u),(step_taint inst s u tn)) /\
  ghost_inv_at D lo d cenv cx es' (step_prov PG G inst u) (step_taint inst s u tn) (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 (step_prov PG G inst u) (step_taint inst s u tn) /\
  lookup_var out (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME result /\ FLOOKUP (step_prov PG G inst u) out = NONE /\
  op_taint (step_taint inst s u tn) (Var out) = {} /\ (step_taint inst s u tn).t_stor = {} /\ (step_taint inst s u tn).t_trans = {} /\
  (step_taint inst s u tn).t_mem = tn.t_mem /\ (step_taint inst s u tn).t_imm = tn.t_imm /\
  (!x. x <> out ==> lookup_var x (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var x s /\
        FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\ op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `allocas_from lo s /\ stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  conj_tac >- (drule_all create_origin_edge >> simp[]) >>
  qabbrev_tac `z = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G inst u` >>
  qabbrev_tac `tf = step_taint inst s u tn` >>
  `MEM inst.inst_opcode [CREATE;CREATE2] /\ inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `out_taint tn inst s = {}` by gvs[out_taint_def] >>
  `tf = tn with <|t_var := tn.t_var |+ (out,{}); t_stor := {}; t_trans := {}|>` by
    (drule_all lowerDloadPtrCreateInterfacesTheory.dload_create_step_taint >>
     simp[Abbr `tf`, set_var_taint_def]) >>
  `Gf = DRESTRICT G (COMPL {out})` by
    gvs[Abbr `Gf`, step_prov_def, out_prov_def, set_prov_def] >>
  `t.vs_memory = s.vs_memory /\ t.vs_vars = s.vs_vars /\
   t.vs_immutables = s.vs_immutables /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (drule lowerDloadPtrCreateInterfacesTheory.dload_consume_create_state >>
     disch_then SUBST1_TAC >> simp[]) >>
  `z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next /\ z.vs_immutables = s.vs_immutables` by
    simp[Abbr `z`, update_var_def] >>
  `stor_taint_ok_at D tf z` by
    fs[stor_taint_ok_at_def, pred_setTheory.EMPTY_SUBSET] >>
  `!x. x <> out ==> lookup_var x z = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[Abbr `z`, update_var_def, lookup_var_def, op_taint_def,
         finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `tf.t_mem = tn.t_mem` by simp[] >>
  conj_tac >- (drule_all create_ghost_frame >> simp[]) >>
  conj_tac
  >- (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`,`tn`] >> simp[]) >>
  simp[Abbr `z`, update_var_def, lookup_var_def, op_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The allocation is a separate prefix. The two offset stores each
   compile as the existing ADD/MSTORE scalar-write fragment. *)
Theorem proxy_buf_parts[local]:
  compile_create_proxy_buf target sa = (buf,sb) ==>
  ?allocation m1 m2 aligned m3 m4.
    compile_alloc_buffer 96 sa = (allocation,m1) /\
    buf = allocation.buf_operand /\
    emit_void MSTORE [buf;
      Lit 0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w]
      m1 = ((),m2) /\
    emit_op SHL [Lit 96w;target] m2 = (aligned,m3) /\
    (do dst <- emit_op ADD [buf;Lit 19w];
        emit_void MSTORE [dst;aligned] od) m3 = ((),m4) /\
    (do dst <- emit_op ADD [buf;Lit 39w];
        emit_void MSTORE [dst;
          Lit 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w]
     od) m4 = ((),sb) /\
    cs_extends sa m1 /\ cs_extends m1 m2 /\ cs_extends m2 m3 /\
    cs_extends m3 m4 /\ cs_extends m4 sb /\
    m1.cs_next_id = SUC sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sa.cs_next_var <= m1.cs_next_var /\ m1.cs_next_var <= m2.cs_next_var /\
    m2.cs_next_var <= m3.cs_next_var /\ m3.cs_next_var <= m4.cs_next_var /\
    m4.cs_next_var <= sb.cs_next_var
Proof
  simp[compile_create_proxy_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, cs_extends_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM, pairTheory.UNCURRY]) >>
  gvs[] >>
  simp[GSYM APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem proxy_shift_origin[local]:
  emit_op SHL [Lit 96w;target] sa = (aligned,sb) /\ fn_has_code sa sb func /\
  eval_operand target s = SOME w /\ op_taint tn target = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x t G' tn'. aligned = Var x /\ not_fresh_at sb x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t = (update_var x (w << 96) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    lookup_var x t = SOME (w << 96) /\ op_taint tn' aligned = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME (mk_inst _ _ _ [x])` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id SHL [Lit 96w;target] [x]` >>
  qabbrev_tac `u = update_var x (w << 96) s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, exec_pure2_def,
         bind_outputs_def, eval_operand_def] >>
  `step_taint i s u tn = tn with t_var := tn.t_var |+ (x,{})` by
    (`new_site_bytes s u = {}` by
       (irule ptrDisciplineEmptyTaintTheory.new_site_bytes_unchanged >>
        simp[Abbr `u`, update_var_def]) >>
     simp[Abbr `i`, mk_inst_def, step_taint_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, written_taint_def, range_bytes_def,
          store_taint_def, adopt_reset_def, imm_taint_def, out_taint_def,
          eval_operand_def, set_var_taint_def, taint_component_equality,
          ptrDisciplineEmptyTaintTheory.shift_taint_empty]) >>
  qexistsl_tac [`x`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G i u`, `step_taint i s u tn`] >> simp[] >>
  conj_tac
  >- (simp[not_fresh_at_def] >>
      gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def]) >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
          step_prov PG G i u, step_taint i s u tn)` by
        (`ptr_inst_ok D lo 0 ctx func G tn i s` by
           (simp[Abbr `i`] >> irule bodyPtrEnvBuiltinsEdgesTheory.ptr_inst_ok_scalar_builtin_at >>
            simp[DISJ_IMP_THM, FORALL_AND_THM] >>
            simp[op_taint_def]) >>
         drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
         simp[Abbr `i`, mk_inst_def, is_terminator_def,
              inst_mem_below_frontier_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, inst_dload_in_section_def,
              IgnAsm `step_taint _ _ _ _ = _`] >>
         disch_then irule >> gvs[mk_inst_def]) >>
      drule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> disch_then irule >>
      irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      simp[Abbr `u`, update_var_def]) >>
  simp[Abbr `u`, Abbr `i`, update_var_def, lookup_var_def, op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE, step_prov_def, out_prov_def, set_prov_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, mk_inst_def] >>
  qx_gen_tac `y` >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> y` by metis_tac[] >> simp[]
QED

Theorem proxy_offset_store_origin[local]:
  (do dst <- emit_op ADD [Var p;Lit (n2w off)];
      emit_void MSTORE [dst;value] od) sa = ((),sb) /\
  fn_has_code sa sb func /\ lookup_var p s = SOME w /\
  eval_operand value s = SOME x /\ op_taint tn value = {} /\
  not_fresh_at sa p /\ (!y. value = Var y ==> not_fresh_at sa y) /\
  ptr_covers G tn p s 96 /\ off + 32 <= 96 /\
  w2n w + 96 < dimword (:256) /\ w2n w + 96 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96 /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_memory = (mstore (w2n w + off) x s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n w + off <= i /\ i < w2n w + off + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> drule bodyMemEcArithTransfersTheory.ec_scalar_store_shape >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all bodyFullBuiltinECArithTransfersTheory.ec_scalar_store_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
   t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
   t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96` by
    (qpat_assum `!y. not_fresh_at sa y ==> _` drule >> strip_tac >>
     gvs[ptr_covers_def]) >>
  simp[allocas_from_def, allocas_below_fmp_def] >>
  fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[LENGTH_APPEND]
QED

(* The writes and the alignment operation leave one shared, clean
   read window; nothing outside the allocation is touched. *)
Theorem proxy_buf_written[local]:
  emit_void MSTORE [Var p;Lit pre] m1 = ((),m2) /\
  emit_op SHL [Lit 96w;target] m2 = (aligned,m3) /\
  (do dst <- emit_op ADD [Var p;Lit 19w];
      emit_void MSTORE [dst;aligned] od) m3 = ((),m4) /\
  (do dst <- emit_op ADD [Var p;Lit 39w];
      emit_void MSTORE [dst;Lit post] od) m4 = ((),sb) /\
  fn_has_code m1 m2 func /\ fn_has_code m2 m3 func /\
  fn_has_code m3 m4 func /\ fn_has_code m4 sb func /\
  m1.cs_next_var <= m2.cs_next_var /\ m2.cs_next_var <= m3.cs_next_var /\
  m3.cs_next_var <= m4.cs_next_var /\ m4.cs_next_var <= sb.cs_next_var /\
  not_fresh_at m1 p /\ (!y. target = Var y ==> not_fresh_at m1 y) /\
  eval_operand target s = SOME x /\ op_taint tn target = {} /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 96 /\
  w2n w + 96 < dimword (:256) /\ w2n w + 96 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = m1.cs_current_bb /\ s.vs_inst_idx = LENGTH m1.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96 /\
    t.vs_memory = (mstore (w2n w + 39) post
      (mstore (w2n w + 19) (x << 96) (mstore (w2n w) pre s))).vs_memory /\
    exprSimStorageCopy$copy_static t = exprSimStorageCopy$copy_static s /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 71} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at m1 y ==> lookup_var y t = lookup_var y s /\
         FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `b = w2n w` >>
  `n2w b = w /\ b < dimword (:256) /\ b + 32 <= s.vs_alloca_next` by
     (simp[Abbr `b`] >> fs[] >> decide_tac) >>
  `lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s 32` by
     (simp[] >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Lit pre) s = SOME pre /\ op_taint tn (Lit pre) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all bodyFullAbiEncodeSetupTailTheory.abi_encode_payload_word_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s1` (qx_choose_then `t1` strip_assume_tac))) >>
  suspend "shift"
QED

Resume proxy_buf_written[shift]:
  `allocas_from lo s1 /\ lo <= s1.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
   eval_operand target s1 = SOME x /\ op_taint t1 target = {}` by
    (simp[mstore_def, allocas_from_def,allocas_below_fmp_def] >>
     Cases_on `target` >> gvs[eval_operand_def, lookup_var_def, op_taint_def,
       allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all proxy_shift_origin >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `al` (qx_choose_then `s2` (qx_choose_then `G2`
       (qx_choose_then `t2` strip_assume_tac))))) >>
  suspend "middle"
QED

Resume proxy_buf_written[middle]:
  `lookup_var p s2 = SOME w /\ ptr_covers G2 t2 p s2 96` by
    (`not_fresh_at m2 p` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!y. not_fresh_at m2 y ==> _` drule >> strip_tac >>
     gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]) >>
  `allocas_from lo s2 /\ lo <= s2.vs_alloca_next /\ ~s2.vs_halted /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\
   w2n w + 96 <= s2.vs_alloca_next` by
    (`s2.vs_allocas = s.vs_allocas /\ s2.vs_alloca_next = s.vs_alloca_next /\
      s2.vs_initial_fmp = s.vs_initial_fmp /\ s2.vs_fmp = s.vs_fmp /\
      s2.vs_halted = s.vs_halted` by
       (qpat_assum `s2 = _` (fn shift =>
          qpat_assum `s1 = _` (fn store => simp[NoAsms,shift,store,mstore_def,update_var_def]))) >>
     qpat_assum `Abbrev (b = w2n w)` (fn base =>
       asm_simp_tac bool_ss [SYM (REWRITE_RULE [markerTheory.Abbrev_def] base),
         allocas_from_def,allocas_below_fmp_def]) >>
     qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (assume_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s2.vs_inst_idx = LENGTH m3.cs_current_insts /\ not_fresh_at m3 p /\
   eval_operand aligned s2 = SOME (x << 96) /\
   (!y. aligned = Var y ==> not_fresh_at m3 y)` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `m1` >>
     simp[] >> decide_tac) >>
  `19 + 32 <= 96` by decide_tac >>
  `w2n w + 96 < dimword (:256)` by fs[Abbr `b`] >>
  drule_all (Q.INST [`off` |-> `19`] proxy_offset_store_origin) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s3` (qx_choose_then `G3` (qx_choose_then `t3` strip_assume_tac)))) >>
  suspend "last"
QED

Resume proxy_buf_written[last]:
  `not_fresh_at m4 p /\ lo <= s3.vs_alloca_next /\ w2n w + 96 <= s3.vs_alloca_next` by
    (simp[IgnAsm `s2 = _`] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand (Lit post) s3 = SOME post /\ op_taint t3 (Lit post) = {} /\
   (!y. Lit post = Var y ==> not_fresh_at m4 y) /\ 39 + 32 <= 96` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (Q.INST [`off` |-> `39`] proxy_offset_store_origin) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  suspend "pack"
QED

Resume proxy_buf_written[pack]:
  conj_tac
  >- (gen_tac >>
      metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `s2.vs_memory = (mstore b pre s).vs_memory /\
   s2.vs_allocas = s.vs_allocas /\ s2.vs_alloca_next = s.vs_alloca_next` by
    simp[update_var_def,mstore_def] >>
  `s3.vs_memory = (mstore (b+19) (x << 96) (mstore b pre s)).vs_memory` by
    (qpat_assum `s3.vs_memory = _` SUBST1_TAC >>
     qpat_assum `s2.vs_memory = _` (mp_tac o MATCH_MP exprSimCalldataSliceTheory.mstore_equal_memory) >>
     disch_then (qspecl_then [`w2n w + 19`,`x << 96`] (pure_rewrite_tac o single)) >>
     simp[Abbr `b`]) >>
  `t.vs_memory = (mstore (b+39) post
        (mstore (b+19) (x << 96) (mstore b pre s))).vs_memory` by
    (qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     qpat_assum `s3.vs_memory = (mstore (b+19) _ _).vs_memory`
       (mp_tac o MATCH_MP exprSimCalldataSliceTheory.mstore_equal_memory) >>
     disch_then (qspecl_then [`w2n w + 39`,`post`] (pure_rewrite_tac o single)) >>
     simp[Abbr `b`]) >>
  `copy_static t = copy_static s3` by
    (qpat_assum `t with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s3`
       (SUBST1_TAC o SYM) >> simp[exprSimStorageCopyTheory.copy_static_def]) >>
  `copy_static s3 = copy_static s2` by
    (qpat_assum `s3 with <|vs_vars := _;vs_memory := _;vs_inst_idx := _|> = s2`
       (SUBST1_TAC o SYM) >> simp[exprSimStorageCopyTheory.copy_static_def]) >>
  `copy_static s2 = copy_static s` by
    simp[exprSimStorageCopyTheory.copy_static_def,update_var_def,mstore_def] >>
  `tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b + 71}` by
    (simp[pred_setTheory.EXTENSION,pred_setTheory.IN_DIFF,Abbr `b`] >>
     qx_gen_tac `i` >> Cases_on `i IN tn.t_mem` >> simp[] >> decide_tac) >>
  simp[IgnAsm `s2 = _`] >>
  qx_gen_tac `y` >> strip_tac >>
  `not_fresh_at m2 y /\ not_fresh_at m3 y /\ not_fresh_at m4 y` by
    (rpt conj_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `m1` >> simp[] >> decide_tac) >>
  qpat_assum `!y. not_fresh_at m4 y ==> _` drule >> strip_tac >>
  qpat_assum `!y. not_fresh_at m3 y ==> _` drule >> strip_tac >>
  qpat_assum `!y. not_fresh_at m2 y ==> _` drule >> strip_tac >>
  simp[lookup_var_def,op_taint_def,mstore_def]
QED
Finalise proxy_buf_written

(* The proxy window is an ordinary registered 96-byte allocation, but
   CREATE reads only its first 54 bytes. The full registration and the
   saved-variable frame are available to a subsequent salt evaluation. *)
Theorem proxy_buf_origin_window:
  compile_create_proxy_buf target sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME word /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) ==>
  ?p w t G' tn'.
    buf = Var p /\ not_fresh_at sb p /\ sa.cs_next_id < sb.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_history func t /\
    w2n w + 96 < dimword (:256) /\ w2n w + 96 <= t.vs_alloca_next /\
    lookup_var p t = SOME w /\ ptr_covers G' tn' p t 96 /\
    FLOOKUP G' p = SOME (w2n w,96) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,96) /\
    (!name b n. local_region cenv es.scopes t name b n ==> regions_disjoint (w2n w) 96 b n) /\
    read_memory (w2n w) 54 t = minimal_proxy_initcode (w2w word) /\
    (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tn'.t_mem) /\
    (!H':(bool # bytes32 # type_value) list # num list.
       stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t) /\
    wb_frame cenv es es sa s t /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' t) /\
    (!sk es0 G0 tn0 s0. sk.cs_next_var <= sa.cs_next_var /\
      (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sk.cs_next_id ==>
                   b + n <= s.vs_alloca_next) /\
      (!name b n. local_region cenv es0.scopes s0 name b n ==> b + n <= s.vs_alloca_next) /\
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G' tn') /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule proxy_buf_parts >> strip_tac >>
  `fn_has_code sa m1 func /\ fn_has_code m1 m2 func /\
   fn_has_code m2 m3 func /\ fn_has_code m3 m4 func /\ fn_has_code m4 sb func` by
    (`cs_extends m3 sb` by
       (irule cs_extends_trans >> qexists_tac `m4` >> asm_rewrite_tac[]) >>
     `cs_extends m2 sb` by
       (irule cs_extends_trans >> qexists_tac `m3` >> asm_rewrite_tac[]) >>
     `cs_extends m1 sb` by
       (irule cs_extends_trans >> qexists_tac `m2` >> asm_rewrite_tac[]) >>
     `fn_has_code sa m1 func /\ fn_has_code m1 sb func` by
       (match_mp_tac (Q.SPECL [`sa`,`m1`,`sb`,`func`] fragExecTheory.fn_has_code_split) >>
        asm_rewrite_tac[]) >>
     `fn_has_code m1 m2 func /\ fn_has_code m2 sb func` by
       (match_mp_tac (Q.SPECL [`m1`,`m2`,`sb`,`func`] fragExecTheory.fn_has_code_split) >>
        asm_rewrite_tac[]) >>
     `fn_has_code m2 m3 func /\ fn_has_code m3 sb func` by
       (match_mp_tac (Q.SPECL [`m2`,`m3`,`sb`,`func`] fragExecTheory.fn_has_code_split) >>
        asm_rewrite_tac[]) >>
     `fn_has_code m3 m4 func /\ fn_has_code m4 sb func` by
       (match_mp_tac (Q.SPECL [`m3`,`m4`,`sb`,`func`] fragExecTheory.fn_has_code_split) >>
        asm_rewrite_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `96 < dimword (:256)` by EVAL_TAC >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  mp_tac (Q.INST [`n` |-> `96`, `buf` |-> `allocation`, `sb` |-> `m1`,
    `sa` |-> `sa`, `func` |-> `func`, `cenv` |-> `cenv`, `H` |-> `H`,
    `ctx` |-> `ctx`, `cx` |-> `cx`, `es` |-> `es`, `s` |-> `s`,
    `lo` |-> `lo`, `explicit` |-> `explicit`, `PG` |-> `PG`, `G` |-> `G`, `tn` |-> `tn`]
    (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
      bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`p`,`w`,`u`,`Ga`,`ta`] strip_assume_tac) >>
  suspend "writes"
QED

Resume proxy_buf_origin_window[writes]:
  `stmt_state_rel H ctx func cenv cx es u` by
    (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ _ ==> stmt_state_rel h _ _ _ _ _ _`
       (qspec_then `H:(bool # bytes32 # type_value) list # num list` mp_tac) >> simp[]) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es u`
    (assume_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `u.vs_halted = s.vs_halted /\ u.vs_memory = s.vs_memory /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `~u.vs_halted /\ lo <= u.vs_alloca_next` by (simp[] >> decide_tac) >>
  `!y. target = Var y ==> not_fresh_at sa y /\ not_fresh_at m1 y` by
    (rpt strip_tac >> simp[] >>
     irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand target u = SOME word /\ op_taint ta target = {} /\
   (!y. target = Var y ==> not_fresh_at m1 y)` by
    (Cases_on `target` >> fs[eval_operand_def,op_taint_def] >>
     qpat_assum `!z. not_fresh_at sa z ==> _` drule >> simp[]) >>
  `buf = Var p` by simp[] >>
  qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  drule_all proxy_buf_written >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`p`,`w`,`t`,`G'`,`tn'`] >>
  suspend "frame"
QED

Resume proxy_buf_origin_window[frame]:
  `!x. not_fresh_at sa x ==> not_fresh_at m1 x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >> fs[]) >>
  `local_ptrs_reserved cenv m1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at m1 x ==> lookup_var x t = lookup_var x u` by simp[] >>
  `!name b n. local_region cenv es.scopes t name b n <=>
             local_region cenv es.scopes u name b n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `m1` >> simp[]) >>
  `!name b n. local_region cenv es.scopes u name b n <=>
             local_region cenv es.scopes s name b n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `pb = w2n w` >>
  `!off n. off+n <= pb \/ pb+71 <= off ==>
          mem_bytes_at off n t.vs_memory = mem_bytes_at off n u.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     `off+n <= pb \/ pb+32 <= off` by decide_tac >>
     `off+n <= pb+19 \/ pb+19+32 <= off` by decide_tac >>
     `off+n <= pb+39 \/ pb+39+32 <= off` by decide_tac >>
     qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `t.vs_memory = _` SUBST1_TAC >>
     simp[] >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `LENGTH (mstore (pb+19) (word << 96) (mstore pb
       0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w u)).vs_memory` >>
     simp[mstore_memory_nondecreasing] >>
     metis_tac[mstore_memory_nondecreasing, arithmeticTheory.LESS_EQ_TRANS]) >>
  `lo <= pb` by (qpat_assum `allocas_from lo u`
    (mp_tac o REWRITE_RULE [allocas_from_def]) >>
    disch_then (qspecl_then [`sa.cs_next_id`,`pb`,`96`] mp_tac) >> simp[]) >>
  suspend "pack"
QED

Resume proxy_buf_origin_window[pack]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Ga`,`u`,`ta`] >> simp[]) >>
  `alloca_inv s` by
    qpat_assum `stmt_state_rel H ctx func cenv cx es s`
      (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (s,G,tn) [] (OK t,G',tn')`
       (qspec_then `ARB` assume_tac) >>
     drule_all bodyFullPathHistoryTheory.body_full_path_alloca_history >> simp[]) >>
  `not_fresh_at sb p` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `m1` >> simp[] >> decide_tac) >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     qpat_assum `t.vs_allocas = u.vs_allocas`
       (fn th => simp[NoAsms,allocas_from_def,th])) >>
  `FLOOKUP G' p = SOME (pb,96)` by
    (qpat_assum `!y. not_fresh_at m1 y ==> _ /\ FLOOKUP G' y = _ /\ _`
       (qspec_then `p` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> asm_rewrite_tac[]) >>
  `read_memory pb 54 t = minimal_proxy_initcode (w2w word)` by
    (mp_tac (Q.INST [`pbase` |-> `pb`, `s` |-> `u`] proxy_initcode_stores) >>
     simp[read_memory_def]) >>
  `!i. pb <= i /\ i < pb + 54 ==> i NOTIN tn'.t_mem` by
    (simp[pred_setTheory.IN_DIFF] >> decide_tac) >>
  simp[IgnAsm `t.vs_memory = _`,IgnAsm `u.vs_memory = _`] >>
  suspend "state_rel"
QED

Resume proxy_buf_origin_window[state_rel]:
  `(∀name b n. local_region cenv es.scopes s name b n ⇒
       regions_disjoint pb 96 b n)` by
    (qpat_assum `!name b n. local_region cenv es.scopes u name b n ==> _`
       mp_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `stmt_state_rel H' ctx func cenv cx es u` by simp[] >>
      drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
      disch_then (qx_choose_then `out` strip_assume_tac) >>
      irule exprSimCopyTheory.copy_buffer_state_rel_frame >>
      qexistsl_tac [`pb`,`mk_inst sa.cs_next_id ALLOCA [Lit 96w] [out]`,`u`,`m1`,`96:num`] >>
      simp[IgnAsm `t.vs_memory = _`, IgnAsm `u.vs_memory = _`] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` drule >>
          simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
      >- (rpt strip_tac >>
          qpat_assum `!off n. _ ==> mem_bytes_at off n t.vs_memory = _` irule >> decide_tac)
      >> simp[mk_inst_def]) >>
  suspend "wb_frame"
QED

Resume proxy_buf_origin_window[wb_frame]:
  conj_tac
  >- (irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_wb_frame >>
      conj_tac >- simp[] >>
      conj_tac
      >- (qexistsl_tac [`96:num`,`pb`] >> rpt conj_tac
          >- (rpt strip_tac >>
              qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` drule >>
              simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
          >- (rpt gen_tac >> strip_tac >>
              `aid < sa.cs_next_id ∧ FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
              qpat_assum `!aid b n. _ ==> regions_disjoint pb 96 b n` drule >>
              simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
          >> rpt gen_tac >> disch_tac >>
          qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
          qpat_assum `!off n. _ ==> mem_bytes_at off n t.vs_memory = _` irule >> decide_tac)
      >> simp[]) >>
  conj_tac >- suspend "ghost_inv" >>
  suspend "ghost_kept"
QED

Resume proxy_buf_origin_window[ghost_inv]:
  rpt strip_tac >>
  `ghost_inv_at D lo d cenv cx es Ga ta u` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G`,`H`,`ctx`,`pb + 96`,`func`,`s`,`sa`,`tn`] >> simp[]) >>
  `stor_taint_ok_at D ta u` by
    (qpat_assum `ghost_inv_at D lo d cenv cx es Ga ta u` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at D ta t` by
    (qpat_assum `copy_static t = copy_static u`
      (mp_tac o AP_TERM ``\z:venom_state.
         (z.vs_accounts,z.vs_call_ctx,z.vs_transient,z.vs_immutables)``) >>
     simp[NoAsms, exprSimStorageCopyTheory.copy_static_def] >> strip_tac >>
     qpat_assum `stor_taint_ok_at D ta u`
       (mp_tac o REWRITE_RULE [stor_taint_ok_at_def]) >>
     simp[stor_taint_ok_at_def]) >>
  irule (cj 1 (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullHashShaFrameTheory.sha_shrinking_ghost_frame_at)) >>
  conj_tac
  >- (qpat_assum `stor_taint_ok_at D ta t`
        (mp_tac o REWRITE_RULE [stor_taint_ok_at_def]) >> simp[stor_taint_ok_at_def]) >>
  qexistsl_tac [`Ga`,`H`,`ctx`,`func`,`u`,`m1`,`ta`,`{i | pb <= i /\ i < pb + 71}`] >>
  simp[IgnAsm `t.vs_memory = _`, IgnAsm `u.vs_memory = _`] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!off n. _ ==> mem_bytes_at off n t.vs_memory = _` irule >> decide_tac
QED

Resume proxy_buf_origin_window[ghost_kept]:
  rpt strip_tac >>
  `!x. not_fresh_at sk x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sk` >> simp[]) >>
  `ghost_kept_at lo cenv es0 sk G0 tn0 s0 Ga ta` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`,`pb + 96`,`s`,`tn`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qexistsl_tac [`Ga`,`ta`] >>
  simp[IgnAsm `!x. not_fresh_at sa x ==> lookup_var x t = _`, pred_setTheory.DIFF_SUBSET]
QED

Finalise proxy_buf_origin_window

(* Run the compiler's result check after either creation opcode. The
   non-reverting case returns the original word, even when it is zero. *)
Theorem create_check_result_path:
  compile_check_create_result result rof sa = (out,sb) /\
  fn_has_code sa sb func /\
  u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~u.vs_halted /\ eval_operand result u = SOME addr /\ op_taint tn result = {} /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (rof /\ addr = 0w ==>
    lo <= u.vs_alloca_next /\ LENGTH u.vs_returndata < dimword (:256) /\
    (ctx_has_dalloca ctx ==>
      u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)) ==>
  out = result /\
  if rof /\ addr = 0w then
    ?t Gf tf. t.vs_returndata = u.vs_returndata /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) []
        (Abort Revert_abort t,Gf,tf)
  else
    (if rof then jump_to sb.cs_current_bb u else u).vs_current_bb = sb.cs_current_bb /\
    (if rof then jump_to sb.cs_current_bb u else u).vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~(if rof then jump_to sb.cs_current_bb u else u).vs_halted /\ eval_operand out (if rof then jump_to sb.cs_current_bb u else u) = SOME addr /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) []
      (OK (if rof then jump_to sb.cs_current_bb u else u),G,tn)
Proof
  Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def]
  >- (rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      rename1 `emit_inst JNZ [out;Label ok_lbl;Label fail_lbl] [] sj = ((),se)` >>
      rename1 `new_block fail_lbl se = (old,sf)` >>
      rename1 `emit_inst REVERT [rbuf.buf_operand;rds] [] sc = ((),sr)` >>
      rename1 `new_block ok_lbl sr = (old_ok,sb)` >>
      `sj.cs_current_bb = sa.cs_current_bb /\
       sj.cs_current_insts = sa.cs_current_insts` by
        metis_tac[emitHelperPropsTheory.fresh_label_props] >>
      `sb.cs_current_bb = ok_lbl /\ sb.cs_current_insts = [] /\ cs_extends sr sb` by
        metis_tac[emitHelperPropsTheory.new_block_props,cs_extends_new_block] >>
      `cs_extends sa sj` by
        metis_tac[cs_extends_fresh_label,cs_extends_trans] >>
      `cs_extends sf sr` by
        (drule (REWRITE_RULE [fragExecTheory.cs_appends_def]
                  (cj 2 fragExecTheory.cs_appends_emit_helpers)) >>
         drule loweringHaltTheory.compile_alloc_buffer_extends >>
         drule (REWRITE_RULE [fragExecTheory.cs_appends_def]
                  (cj 3 fragExecTheory.cs_appends_emit_helpers)) >>
         qpat_assum `emit_inst REVERT _ _ _ = _`
           (mp_then Any mp_tac fragExecTheory.cs_extends_emit_inst) >>
         metis_tac[cs_extends_trans]) >>
      `cs_extends sf sb` by metis_tac[cs_extends_trans] >>
      `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
            get_instruction bb u.vs_inst_idx =
              SOME (mk_inst sj.cs_next_id JNZ [out;Label ok_lbl;Label fail_lbl] [])` by
        (simp[] >> drule_all fragExecTheory.fn_has_code_emit_new_block >> simp[]) >>
      `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) []
             (OK (jump_to (if addr <> 0w then ok_lbl else fail_lbl) u),G,tn)` by
        (gen_tac >> irule fragGasOriginPtrLoopTheory.jnz_origin_ptr_path >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl [`out`,`sj.cs_next_id`] >> simp[] >> metis_tac[]) >>
      Cases_on `addr = 0w` >> gvs[]
      >- (`cs_extends sa sf` by
            metis_tac[fragExecTheory.cs_extends_emit_inst,cs_extends_new_block,
                      cs_extends_trans] >>
          `fn_has_code sf sr func` by metis_tac[fragExecTheory.fn_has_code_mid] >>
          `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
             u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by simp[] >>
          `LENGTH u.vs_returndata < dimword (:256)` by simp[] >>
          drule_all bodyFullExtCallDispatchTheory.extcall_dispatch_failure_path >>
          disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
          `jump_to fail_lbl (next_inst u) = jump_to fail_lbl u` by
            simp[jump_to_def,next_inst_def] >>
          qexistsl [`t`,`Gf`,`tnf`] >> simp[] >>
          gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
          qexistsl [`G`,`jump_to fail_lbl u`,`tn`] >> fs[]) >>
      simp[jump_to_def]) >>
  strip_tac >> gvs[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]
QED

Theorem create_dispatch_code[local]:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?mid out bb.
    compile_check_create_result (Var out) rof mid = (result,sb) /\
    fn_has_code mid sb func /\ ~not_fresh_at sm out /\
    s.vs_current_bb = mid.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH mid.cs_current_insts /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
        ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out])
Proof
  `(case sop of NONE => emit_op CREATE [amount;codep;len]
      | SOME p => emit_op CREATE2 [amount;codep;len;p]) =
    emit_op (if IS_SOME sop then CREATE2 else CREATE)
       ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p]))` by
    (Cases_on `sop` >> simp[]) >>
  simp[compile_create_dispatch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_check_create_result optmp rof mid = (result,sb)` >>
  `cs_extends sm mid` by
    (irule (REWRITE_RULE [fragExecTheory.cs_appends_def]
       (cj 2 fragExecTheory.cs_appends_emit_helpers)) >>
     goal_assum (drule_at Any)) >>
  `cs_extends mid sb` by
    (qspecl_then [`optmp`,`rof`,`mid`] mp_tac
       externalEntryShapeTheory.compile_check_create_result_labels >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
  strip_tac >> qexistsl [`mid`,`tmp`,`bb`] >> simp[] >> metis_tac[]
QED

(* A pre-consumption exit still checks the same instruction's input window. *)
Theorem create_preconsume_abort_edge[local]:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  eval_operand amount s = SOME value /\
  eval_operand bufop s = SOME off /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. bufop = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n off + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n off /\
     w2n off + w2n sz <= w2n s.vs_fmp)) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n off <= j /\ j < w2n off + w2n sz ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  stor_taint_ok_at D tn s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = Abort ab u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (Abort ab u,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
   source_memory_write_ranges inst s = [] /\
   mem_read_ops inst = SOME <|iao_ofst := bufop; iao_size := SOME len;
                              iao_max_size := SOME len|> /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
          memory_range_of_operands_def, mem_read_ops_def]) >>
  `access_ok lo G func inst s` by
    (simp[access_ok_def] >> rpt strip_tac >>
     `sz <> 0w` by fs[] >>
     qpat_assum `sz <> 0w ==> ?p. _` drule >> strip_tac >>
     gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (irule ptrDisciplineTaintPropsTheory.taint_ok_clean_step >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     gvs[ptr_inst_ok_def, stor_taint_ok_at_def, step_inst_non_invoke] >> metis_tac[]) >>
  `mem_safe_step 0 ctx inst s` by
    (qpat_assum `_ \/ _` strip_assume_tac >> Cases_on `sz = 0w` >>
     simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
          inst_mem_below_frontiers_def, wordsTheory.w2n_eq_0] >> metis_tac[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn inst s` by simp[ptr_safe_step_def] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_edge_def,
       fragGasOriginTheory.gas_origin_edge_def, fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gasEventsTheory.gas_events_step_def,
       gasCountTheory.gas_count_step_def,fragExecTheory.exit_result_def] >>
  metis_tac[]
QED

(* Keep the branch's exact path witness while it is still available.  P
   certifies the endpoint of that witness, independently of the horizon. *)
Definition create_dispatch_prepared_outcome_def:
  create_dispatch_prepared_outcome (DF,lo,explicit,ctx,func,PG) cx st0
    source (es,s,G,tn) Q R P <=>
    ?res ee r G' tn'. P r /\
      (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
        ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
         (exit_result r /\ R H res (ee with gas_obs := []) (G',tn') r))
End

Theorem create_dispatch_witness_exit[local]:
  P r /\ (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  exit_result r /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
    R H res (ee with gas_obs := []) (G',tn') r) ==>
  create_dispatch_prepared_outcome (DF,lo,explicit,ctx,func,PG) cx st0
    source (es,s,G,tn) Q R P
Proof
  rw[create_dispatch_prepared_outcome_def] >>
  qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[]
QED

Theorem create_dispatch_witness_normal[local]:
  P (OK t) /\ (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    Q H res (ee with gas_obs := []) G' tn' t) ==>
  create_dispatch_prepared_outcome (DF,lo,explicit,ctx,func,PG) cx st0
    source (es,s,G,tn) Q R P
Proof
  rw[create_dispatch_prepared_outcome_def] >>
  qexistsl_tac [`res`,`ee`,`OK t`,`G'`,`tn'`] >> simp[]
QED

(* The post-validation dispatch depends only on the prepared initcode
   window, not on the builtin that produced it. *)
Theorem create_dispatch_outcome_witness:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  outcomes_accounts_typed ee.outcomes /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  read_memory (w2n pv) (w2n sz) s = initcode /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) /\
  (!r. exit_result r /\ gas_origin_edge T explicit ctx func s [] r ==> P r) /\
  (!mid out u w r.
     compile_check_create_result (Var out) rof mid = (result,sb) /\
     fn_has_code mid sb func /\
     u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
     u.vs_inst_idx = SUC s.vs_inst_idx /\
     ~u.vs_halted /\ eval_operand (Var out) u = SOME w /\
     gas_origin_edge T explicit ctx func s [] (OK u) /\
     (if rof /\ w = 0w then exit_result r /\ gas_origin_path T explicit ctx func u [] r
      else r = OK (if rof then jump_to sb.cs_current_bb u else u)) ==> P r) ==>
  create_dispatch_prepared_outcome (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)) P
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_dispatch_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
    ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out]` >>
  suspend "dispatch_shape"
QED

Resume create_dispatch_outcome_witness[dispatch_shape]:
  `inst.inst_outputs = [out] /\ EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  Q.SUBGOAL_THEN
   `((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;codep;len]) \/
    (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;codep;len;THE sop] /\
       ?w. eval_operand (THE sop) s = SOME w))` ASSUME_TAC
  >- (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  `step_inst_base inst s =
    if s.vs_call_ctx.cc_static then Abort ExHalt_abort (halt_state (set_returndata [] s))
    else exec_create inst s aw pv sz sw` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def,step_inst_base_opcode_eqs,eval_operands_def]) >>
  `ee.outcomes = SOME s.vs_outcomes /\ s.vs_call_ctx.cc_static = cx.txn.is_static` by
    (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
       by fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def]) >>
  Cases_on `w2n sz > 2 * max_code_size \/ cx.txn.is_static \/ s.vs_outcomes = []`
  >- suspend "preconsume" >>
  `w2n sz <= 2 * max_code_size /\ ~cx.txn.is_static /\ s.vs_outcomes <> []` by
    (gvs[] >> decide_tac) >>
  Cases_on `s.vs_outcomes` >> gns[] >>
  suspend "consume"
QED

Resume create_dispatch_outcome_witness[preconsume]:
  `step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (Cases_on `cx.txn.is_static` >> gvs[exec_create_abort_iff]) >>
  qabbrev_tac `msg = if w2n sz > 2 * max_code_size then "create initcode too large"
    else if cx.txn.is_static then "write in static context" else "take_create_outcome"` >>
  `!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError msg)),ee with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => rewrite_tac[th]) >>
     Cases_on `w2n sz > 2 * max_code_size` >> simp[Abbr `msg`] >>
     Cases_on `cx.txn.is_static` >> fs[bind_def,ignore_bind_def,
       create_oracle_result_def,take_create_outcome_exhausted]) >>
  qabbrev_tac `r = Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G,tn)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
     `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_def] >>
     simp[Abbr `r`] >> drule_all create_preconsume_abort_edge >> simp[]) >>
  `exit_result r` by simp[Abbr `r`,fragExecTheory.exit_result_def] >>
  `P r` by
    (qpat_assum `!r. exit_result r /\ gas_origin_edge _ _ _ _ _ _ r ==> P r` irule >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def,fragGasOriginPtrTheory.gas_origin_ptr_edge_def]) >>
  irule create_dispatch_witness_exit >>
  qexistsl [`G`,`ee`,`r`,`INR (Error (RuntimeError msg))`,`tn`] >> simp[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  simp[Abbr `r`,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED

Resume create_dispatch_outcome_witness[consume]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `outcomes_accounts_typed ee.outcomes` by simp[] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`value` |-> `w2n w`, `salt` |-> `sw`] create_paired_adoption)) >>
  disch_then (qspecl_then [`aw`,`sw`,`rof`]
    (qx_choose_then `ef` (qx_choose_then `adopted` (map_every assume_tac o CONJUNCTS)))) >>
  rename1 `ee.outcomes = SOME (oc::rest)` >>
  qabbrev_tac `addr = if oc.co_success then oc.co_created else 0w` >>
  qabbrev_tac `raw = update_var out (w2w addr) adopted` >>
  `step_inst_base inst s = OK raw` by simp[Abbr `raw`] >>
  qabbrev_tac `u = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gu = step_prov PG G inst raw` >>
  qabbrev_tac `tu = step_taint inst s raw tn` >>
  `raw = update_var out (w2w addr) adopted` by simp[Abbr `raw`] >>
  `ghost_kept_at lo cenv ee sm G tn s G tn` by simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME inst` by simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
    ghost_inv_at (DF H) lo d cenv cx ef Gu tu u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    lookup_var out u = SOME (w2w addr) /\ FLOOKUP Gu out = NONE /\
    op_taint tu (Var out) = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all create_consumed_origin_ghost >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     simp_tac bool_ss [LET_THM] >>
     map_every (fn q => qpat_assum q (fn th =>
       once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
       [`Abbrev (u = _)`,`Abbrev (Gu = _)`,`Abbrev (tu = _)`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     `x <> out` by metis_tac[] >> simp[]) >>
  suspend "result_check"
QED

Resume create_dispatch_outcome_witness[result_check]:
  `adopted.vs_current_bb = s.vs_current_bb /\ adopted.vs_vars = s.vs_vars /\
   adopted.vs_alloca_next = s.vs_alloca_next /\ adopted.vs_allocas = s.vs_allocas /\
   adopted.vs_initial_fmp = s.vs_initial_fmp /\ adopted.vs_fmp = s.vs_fmp /\
   adopted.vs_memory = s.vs_memory /\ adopted.vs_halted = s.vs_halted` by
    (qpat_assum `adopted = _` (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
  qpat_x_assum `adopted = _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _` (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee s /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_fmp = s.vs_fmp /\
   u.vs_memory = s.vs_memory /\ u.vs_returndata = oc.co_returnData /\ ~u.vs_halted` by
    (map_every (fn q => qpat_assum q (fn th =>
       once_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
       [`Abbrev (u = _)`,`Abbrev (raw = _)`] >>
     simp[NoAsms,update_var_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `adopted.vs_halted = _` (fn th => once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ ef Gu tu u` mp_tac >>
     simp[NoAsms,ghost_inv_at_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
   (ctx_has_dalloca ctx ==> u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)` by
    (conj_tac
     >- (simp[allocas_below_fmp_def] >>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
           (ACCEPT_TAC o REWRITE_RULE[allocas_below_fmp_def])) >>
     `pending_alloca_size func u = pending_alloca_size func s` by simp[pending_alloca_size_def] >>
     simp[] >> strip_tac >>
     drule stateRelProjTheory.stmt_state_rel_fmp_room >>
     simp[fmp_room_def] >> decide_tac) >>
  `eval_operand (Var out) u = SOME (w2w addr)` by simp[eval_operand_def] >>
  `u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts` by simp[] >>
  `(rof /\ (w2w addr:bytes32) = 0w ==>
     lo <= u.vs_alloca_next /\ LENGTH u.vs_returndata < dimword (:256) /\
     (ctx_has_dalloca ctx ==> u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp))`
    by (strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum `u.vs_returndata = _` (fn th => once_rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
  `((w2w addr:bytes32) = 0w) = (addr = 0w)` by
    simp[wordsTheory.w2w_eq_n2w] >>
  `gas_origin_edge T explicit ctx func s [] (OK u)` by
    (qpat_assum `gas_origin_ptr_edge _ (s,G,tn) [] _` mp_tac >>
     simp[NoAsms,fragGasOriginPtrTheory.gas_origin_ptr_edge_def]) >>
  drule_all create_check_result_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gu`] mp_tac) >>
  Cases_on `rof /\ addr = 0w` >> simp_tac bool_ss [] >> simp[]
  >- suspend "forward" >>
  suspend "land"
QED

Resume create_dispatch_outcome_witness[forward]:
  strip_tac >>
  `!tail. source (ee with gas_obs := tail) =
    (INR (Error (RevertData oc.co_returnData)),ef with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => once_rewrite_tac[th]) >>
     simp[bind_def,ignore_bind_def,check_not_static_def,check_def,assert_def,return_def] >>
     qpat_x_assum `rof /\ addr = 0w` strip_assume_tac >>
     qpat_assum `!tail. create_oracle_result _ _ _ _ _ = _`
       (qspec_then `tail` (fn th =>
          qpat_assum `rof:bool` (fn hr => qpat_assum `addr = 0w` (fn hz =>
            once_rewrite_tac [REWRITE_RULE [hr,hz] th])))) >>
     simp[NoAsms]) >>
  `gas_origin_path T explicit ctx func u [] (Abort Revert_abort t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] _`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` mp_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections]) >>
  `P (Abort Revert_abort t)` by
    (qpat_assum `!mid out u w r. _ ==> P r`
       (qspecl_then [`mid`,`out`,`u`,`w2w addr`,`Abort Revert_abort t`] mp_tac) >>
     simp[fragExecTheory.exit_result_def]) >>
  irule create_dispatch_witness_exit >>
  qexistsl [`Gf`,`ef`,`Abort Revert_abort t`,`INR (Error (RevertData oc.co_returnData))`,`tf`] >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def,
       IgnAsm `ef.storage_trace = _`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ef.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  irule (REWRITE_RULE [listTheory.APPEND]
    (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
      (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >> first_assum MATCH_ACCEPT_TAC
QED

Resume create_dispatch_outcome_witness[land]:
  qmatch_goalsub_abbrev_tac `eval_operand result z = _` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. source (ee with gas_obs := tail) = (INL (AddressV addr),ef with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => once_rewrite_tac[th]) >>
     simp[bind_def,ignore_bind_def,check_not_static_def,check_def,assert_def,return_def] >>
     `~(addr = 0w /\ rof)` by metis_tac[] >>
     qpat_assum `!tail. create_oracle_result _ _ _ _ _ = _`
       (qspec_then `tail` (fn th => qpat_assum `~(addr = 0w /\ rof)` (fn h =>
          once_rewrite_tac [REWRITE_RULE [h] th]))) >> simp[read_result_def,return_def]) >>
  `P (OK z)` by
    (qpat_assum `!mid out u w r. _ ==> P r`
       (qspecl_then [`mid`,`out`,`u`,`w2w addr`,`OK z`] mp_tac) >>
     simp[Abbr `z`]) >>
  irule create_dispatch_witness_normal >>
  qexistsl [`Gu`,`ef`,`INL (AddressV addr)`,`z`,`tu`] >>
  simp[IgnAsm `ef.storage_trace = _`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ef.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule (REWRITE_RULE [listTheory.APPEND]
        (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
          (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
      goal_assum (drule_at Any) >> first_assum MATCH_ACCEPT_TAC) >>
  `alloca_history func u` by
    (`alloca_inv s` by
       (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s` mp_tac >>
        simp[NoAsms,stmt_state_rel_def]) >>
     `~is_terminator inst.inst_opcode` by
       (qpat_assum `_ \/ _` strip_assume_tac >> simp[is_terminator_def]) >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     qpat_assum `Abbrev (u = _)` (fn th =>
       once_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `~is_terminator inst.inst_opcode` (fn th => rewrite_tac [th])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "expr_post"
  >- simp[exprSimMemDefsTheory.expr_store_bound_word,is_word_type_def]
  >- (Cases_on `rof` >> simp[Abbr `z`] >>
      irule allocaHistoryTheory.alloca_history_jump >>
      simp[jump_to_def] >> qexists `u` >> simp[])
  >- (Cases_on `rof` >> simp[Abbr `z`,allocas_below_fmp_def,jump_to_def] >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
        (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def]))
  >- simp[Abbr `z`,jump_to_def,COND_RAND,COND_RATOR]
  >- (Cases_on `rof` >> simp[Abbr `z`,fragGasEmitCtrlTheory.ghost_inv_at_jump_to] >>
      qpat_assum `ghost_inv_at (DF H) lo d cenv cx ef Gu tu u` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_inv_at_def] >> metis_tac[]) >>
  irule ptr_val_ok_word >> simp[is_word_type_def,op_prov_def]
QED

Resume create_dispatch_outcome_witness[expr_post]:
  (* The optional jump changes only control; restore the expression frame
     using the same adopted state and the fresh address output. *)
  `stmt_state_rel H ctx func cenv cx ef adopted` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> request_agree _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `not_local_ptr cenv ef.scopes out` by (irule exprSimOperandsTheory.fresh_not_local_ptr >>
    goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ef raw` by
    (qpat_assum `raw = _` (fn th => once_rewrite_tac [th]) >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx (ef with gas_obs := []) z` by
    (map_every (fn q => qpat_assum q (fn th =>
       once_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
       [`Abbrev (z = _)`,`Abbrev (u = _)`] >>
     Cases_on `rof` >>
     rewrite_tac[stmt_state_rel_jump_to,stmt_state_rel_inst_idx,
                 stmt_state_rel_start_gas_obs] >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `ef` >> simp[]) >>
  `z.vs_allocas = s.vs_allocas /\ z.vs_memory = s.vs_memory` by
    (Cases_on `rof` >> simp[Abbr `z`,jump_to_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     `x <> out` by metis_tac[] >>
     map_every (fn q => qpat_assum q (fn th =>
       once_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
       [`Abbrev (z = _)`,`Abbrev (u = _)`,`Abbrev (raw = _)`] >>
     map_every (fn q => qpat_assum q mp_tac) [`x <> out`,`adopted.vs_vars = s.vs_vars`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `rof` >>
     simp[lookup_var_def,update_var_def,jump_to_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  `eval_operand (Var out) z = SOME (w2w addr)` by
    (qpat_assum `result = Var out` (fn th => once_rewrite_tac [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `wb_frame cenv es ee sa s0 s` mp_tac >>
  simp[loweringPostsTheory.expr_post_def,loweringPostsTheory.wb_frame_def,
       loweringPostsTheory.expr_val_rel_def,loweringPostsTheory.expr_val_at_def,
       loweringPostsTheory.expr_val_own_def,is_word_type_def,
       vyperValueTheory.evaluate_type_def,convertScalarBytesTheory.scalar_typed_address_word,
       loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_dispatch_outcome_witness

Theorem create_dispatch_outcome_full:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  outcomes_accounts_typed ee.outcomes /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  read_memory (w2n pv) (w2n sz) s = initcode /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`P` |-> `\r. T`] create_dispatch_outcome_witness)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  simp[NoAsms,create_dispatch_prepared_outcome_def] >> strip_tac >>
  rename1 `!tail. source (ee with gas_obs := tail) = (res,ef with gas_obs := tail)` >>
  Cases_on `storage_trace_domain cx st0 ef.storage_trace`
  >- (simp[gas_outcome_full_def] >> qexists_tac `[]` >> simp[] >>
      disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bad_nil >> simp[]
QED

(* In oracle mode, a well-decoded proxy has no source-code or size
   validation branch between its operands and the shared create action. *)
Theorem create_proxy_read_prepared:
  IS_SOME es.outcomes /\ dest_AddressV target = SOME addr /\
  dest_NumV amount = SOME value /\
  dest_optional_salt salt = SOME salt_word /\
  LENGTH ts = (if IS_SOME salt then 3 else 2) ==>
  bind (eval_create_operands cx CreateMinimalProxy (IS_SOME salt) rof ts off
        (target::amount::(case salt of NONE => [] | SOME v => [v])))
    (read_result cx) es =
  bind (ignore_bind (check_not_static cx)
        (create_oracle_result salt_word value (minimal_proxy_initcode addr) rof))
    (read_result cx) es
Proof
  Cases_on `salt` >>
  simp[NoAsms,eval_create_operands_def,create_operand_layout_def,dest_optional_salt_def] >>
  rpt strip_tac >>
  qpat_x_assum `LENGTH ts = _` mp_tac >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [eval_create_def] >>
  simp[dest_create_args_def,make_create_operands_def,dest_optional_num_def,
       dest_optional_salt_def,create_arg_ctor_types_def,build_create_code_def] >>
  simp[bind_def,ignore_bind_def,lift_option_type_def,lift_option_def,
       get_accounts_def,check_def,check_not_static_def,assert_def,return_def,raise_def] >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

(* A child exit is already a proxy exit. On a continuing child, expose
   both the replay and its joint path at the same endpoint. *)
Theorem create_bind_operand[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ C H v ee G1 tn1 t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v ee G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v, ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       C H v ee G1 tn1 t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (next v) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >> irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  simp[] >> qexists `\H res ee G1 tn1 t. ?v. res = INL v /\ C H v ee G1 tn1 t` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  Cases_on `res` >> fs[] >> metis_tac[]
QED

(* Pair the same operand cuts in the real and shadow compiler runs. *)
Theorem proxy_shadow_salt[local]:
  gas_shadow_compiles (compile_create_salt compile_expr cenv salt)
    (compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt))
Proof
  mp_tac (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_salt
    (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env) |>
    Q.INST [`sd` |-> `T`, `sh` |-> `T`, `salt_e` |-> `salt`]) >>
  simp[]
QED

Theorem proxy_compile_cuts:
  gas_shadow_state sa sh /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateMinimalProxy salted rof ks)
      (target::amount::salts) dflt)) sh = (result,shb) /\
  LENGTH salts = (if salted then 1 else 0) ==>
  ?x y buf sop a b c d a' b' c' d'.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_proxy_buf x b = (buf,c) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) c = (sop,d) /\
    compile_create_dispatch buf (Lit 54w) y sop rof d = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target) (gas_shadow_expr target) sh = (x,a') /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount) (gas_shadow_expr amount) a' = (y,b') /\
    compile_create_proxy_buf x b' = (buf,c') /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) c' = (sop,d') /\
    compile_create_dispatch buf (Lit 54w) y sop rof d' = (result,shb) /\
    gas_shadow_state a a' /\ gas_shadow_state b b' /\
    gas_shadow_state c c' /\ gas_shadow_state d d'
Proof
  strip_tac >> drule_all compile_proxy_parts >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def] >> strip_tac >>
  `LENGTH (MAP gas_shadow_expr salts) = (if salted then 1 else 0)` by simp[] >>
  drule_all compile_proxy_parts >> strip_tac >>
  gvs[gas_shadow_expr_type] >>
  `(if salted then SOME (HD (MAP gas_shadow_expr salts)) else NONE) =
       OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)` by
    (Cases_on `salted` >> Cases_on `salts` >> gvs[]) >>
  gs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileBuiltinCreateTheory.gas_shadow_compiles_create_proxy_buf) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut proxy_shadow_salt) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem copy_compile_parts[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) ==>
  ?x y sop a b c.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) b = (sop,c) /\
    compile_create_copy x y sop rof c = (result,sb)
Proof
  strip_tac >>
  `lower_value compile_expr cenv ty
     (Call ann (CreateTarget CreateCopyOf salted rof ks)
       (target::amount::salts) dflt) =
   compile_create_call compile_expr cenv CreateCopyOf salted rof
     (target::amount::salts)` by
    (simp[FUN_EQ_THM, lower_value_def, create_compile_stack, unwrap_value_def,
          comp_bind_def, comp_return_def] >>
     gen_tac >> Cases_on
       `compile_create_call compile_expr cenv CreateCopyOf salted rof
          (target::amount::salts) x` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `compile_create_call _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_call_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem copy_compile_cuts[local]:
  gas_shadow_state sa sh /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt)) sh = (result,shb) /\
  LENGTH salts = (if salted then 1 else 0) ==>
  ?x y sop a b c a' b' c'.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) b = (sop,c) /\
    compile_create_copy x y sop rof c = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target) (gas_shadow_expr target) sh = (x,a') /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount) (gas_shadow_expr amount) a' = (y,b') /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) b' = (sop,c') /\
    compile_create_copy x y sop rof c' = (result,shb) /\
    gas_shadow_state a a' /\ gas_shadow_state b b' /\ gas_shadow_state c c'
Proof
  strip_tac >> drule_all copy_compile_parts >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def] >> strip_tac >>
  `LENGTH (MAP gas_shadow_expr salts) = (if salted then 1 else 0)` by simp[] >>
  drule_all copy_compile_parts >> strip_tac >> gvs[gas_shadow_expr_type] >>
  `(if salted then SOME (HD (MAP gas_shadow_expr salts)) else NONE) =
       OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)` by
    (Cases_on `salted` >> Cases_on `salts` >> gvs[]) >>
  gs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut proxy_shadow_salt) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* Replay at an arbitrary gas tail gives the type and state invariant.
   The guard of the list IH only asks for existence of a successful read. *)
Theorem create_operand_read_post[local]:
  expr_body_pre cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee with gas_obs := tail) ==>
  expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
  (?s tv t s1 v1 t1. eval_expr cx e s = (INL tv,t) /\
                      read_result cx tv s1 = (INL v1,t1)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
  simp[] >> strip_tac >> simp[] >> conj_tac
  >- (drule (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
      metis_tac[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >>
  simp[] >> metis_tac[valid_horizon_append]
QED

Theorem create_operand_const_cells_replay[local]:
  body_const_cells_agree mods cx env es /\
  expr_body_pre cenv cx env e es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (res,ee with gas_obs := tail)) ==>
  body_const_cells_agree mods cx env ee
Proof
  strip_tac >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `expr_body_pre _ _ _ _ _`
    (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
  `body_const_cells_agree mods cx env (ee with gas_obs := [])` suffices_by simp[] >>
  irule body_const_cells_agree_expr_read >>
  qexistsl [`e`, `res`, `es with gas_obs := prefix`] >> fs[]
QED

(* A cut evaluates exactly one operand. The continuation receives the
   typing and IH guard from replay, and all horizon facts from that run. *)
Theorem create_body_operand_cut_replay:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sh = (op,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sb s ee v op t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
    (?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    (?marks.
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) marks (OK t,G1,tn1))) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next v) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_def] >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
          `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodySimFullTheory.expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
           drule_then ACCEPT_TAC exprSimSourceTheory.expr_body_pre_gas_admissible])) >>
  strip_tac >> irule create_bind_operand >> simp[] >>
  qexists `\H v ee G1 tn1 t.
    expr_post H ctx func cenv cx e es sa sb s ee v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> qexists `v` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
  drule_all create_operand_read_post >> simp[] >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  rule_assum_tac BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `return_buf_frame d cenv sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     fs[loweringPostsTheory.expr_post_def] >>
     metis_tac[ci_mono_lower_value_compile_expr,ci_mono_def,pairTheory.SND]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee`
    by (irule create_operand_const_cells_replay >> rpt (goal_assum (drule_at Any))) >>
  qpat_assum `!v ee G1 tn1 t. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[] >> metis_tac[]
QED

Theorem create_body_operand_cut[local]:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sh = (op,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sb s ee v op t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
    (?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    (?marks. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next v) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `cenv` |-> `cenv`, `env` |-> `env`,
    `shadow_ctx` |-> `shadow_ctx`, `shadow_func` |-> `shadow_func`,
    `sa` |-> `sa`, `sb` |-> `sb`, `sh` |-> `sh`, `shb` |-> `shb`,
    `op` |-> `op`, `d` |-> `d`, `cx` |-> `cx`, `DF` |-> `DF`,
    `ctx` |-> `ctx`, `func` |-> `func`, `PG` |-> `PG`, `lo` |-> `lo`,
    `st0` |-> `st0`, `e` |-> `e`, `next` |-> `next`, `es` |-> `es`,
    `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`, `Q` |-> `Q`] create_body_operand_cut_replay) >>
  impl_tac
  >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!v ee G1 tn1 t. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `?marks. (!tail. monad_bind (eval_expr cx e) _ _ = _) /\ _`
        (qx_choose_then `marks` (fn th =>
          qexists_tac `marks` >> ACCEPT_TAC (CONJUNCT2 th)))) >>
  disch_then ACCEPT_TAC
QED

Theorem proxy_cut_code:
  lower_value compile_expr cenv ty e sa = (x,a) /\
  lower_value compile_expr cenv ty' e' a = (y,b) /\
  compile_create_proxy_buf x b = (buf,c) /\
  compile_create_salt compile_expr cenv salt c = (sop,d) /\
  compile_create_dispatch buf (Lit 54w) y sop rof d = (out,sb) /\
  fn_has_code sa sb fn ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\
  fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\
  fn_has_code c d fn /\ fn_has_code d sb fn
Proof
  strip_tac >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    (rpt conj_tac >> FIRST
       [metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND],
        metis_tac[ci_mono_compile_create_proxy_buf,pairTheory.SND],
        metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND]]) >>
  `cs_extends d sb` by
    metis_tac[externalEntryShapeTheory.compile_create_dispatch_labels,pairTheory.SND] >>
  fs[ci_mono_def] >>
  `cs_extends a sb /\ cs_extends b sb /\ cs_extends c sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a fn /\ fn_has_code a sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code a b fn /\ fn_has_code b sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code b c fn /\ fn_has_code c sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

(* The allocation frontier cannot move back along an operand path. *)
Theorem body_full_edge_alloca_next_mono[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule fragGasOriginPtrTheory.gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  TRY (qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
       gvs[fragExecTheory.exit_result_def] >> NO_TAC) >>
  drule lowerDloadFrontierTheory.ld_step_frontier_mono >> strip_tac >>
  TRY (drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> strip_tac) >>
  gvs[]
QED

Theorem body_full_path_alloca_next_mono_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lo,explicit,ctx,func,PG),(s,G,tn),(r,G',tn')) =>
        !u. r = OK u ==> s.vs_alloca_next <= u.vs_alloca_next
Proof
  ho_match_mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  metis_tac[body_full_edge_alloca_next_mono,arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem body_full_path_alloca_next_mono[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule body_full_path_alloca_next_mono_pair >> simp[]
QED

(* The private allocation and operand evaluation precede a prepared dispatch.
   The dispatch continuation is independent of how the byte window was built. *)
Theorem create_salt_word[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  dest_create_salt v = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v)
Proof
  Cases_on `v` >>
  simp[vyperTypingTheory.value_has_type_def,dest_create_salt_def,vyperValueTheory.dest_BytesV_def,
       valueEncodingTheory.typed_val_to_w256_def,listTheory.PAD_RIGHT]
QED

Theorem create_word_cut_facts[local]:
  expr_body_pre cenv cx env e es /\ expr_result_typed env e (Value v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  expr_post H ctx func cenv cx e es sa sb s ee v op t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t ==>
  value_has_type (BaseTV bt) v /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bt)` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[abiValueEncodingTheory.evaluate_type_base_result]) >>
  `is_word_type (expr_type e)` by simp[] >>
  qpat_assum `lower_value _ _ _ e _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  `value_has_type (BaseTV bt) v` by
    (qpat_x_assum `expr_result_typed _ e _` mp_tac >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def] >>
     metis_tac[abiValueEncodingTheory.evaluate_type_base_result]) >>
  drule_all exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
  fs[ptr_val_ok_def,loweringPostsTheory.post_value_type_def]
QED

Theorem create_operand_cut_frame[local]:
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G' tn' /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME w /\ op_taint tn op = {} ==>
  eval_operand op t = SOME w /\ op_taint tn' op = {}
Proof
  strip_tac >> drule_all abiEncodeArgsSimTheory.abi_args_operand_kept >>
  simp[] >> `op_taint tn' op = op_taint tn op` suffices_by simp[] >>
  irule emittedSeqComposePtrTheory.old_operand_taint_frame >>
  qexists `sa` >> fs[ghost_kept_at_def]
QED

Theorem create_eval_exprs_cons_replay[local]:
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v,em with gas_obs := tail)) /\
  (!tail. eval_exprs cx rest (em with gas_obs := ys ++ tail) = (INL vs,ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx (e::rest) (es with gas_obs := (xs ++ ys) ++ tail) =
    (INL (v::vs),ee with gas_obs := tail)
Proof
  strip_tac >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gasSummaryComposeTheory.gas_source_bind_normal >>
  goal_assum (drule_at Any) >> simp[] >> gen_tac >>
  pure_once_rewrite_tac[bind_def] >> simp[return_def]
QED

(* Compose the frames of two reached cuts using the scopes preserved by
   the first frame. *)
Theorem create_cut_frames_trans[local]:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ci_mono sa sm /\ wb_frame cenv es em sa s m /\ wb_frame cenv em ee sm m t /\
  ghost_kept_at lo cenv es sa G tn s Gm tm /\ ghost_kept_at lo cenv em sm Gm tm m G1 tn1 ==>
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  conj_asm1_tac
  >- (irule exprSimWordArgsTheory.wb_frame_trans >>
      qpat_assum `stmt_state_rel _ _ _ _ _ es s` (irule_at Any) >>
      qpat_assum `wb_frame cenv em ee sm m t` (irule_at Any) >> simp[]) >>
  metis_tac[wordArgsPtrTheory.ghost_kept_at_wb_trans]
QED

(* Project the typed word and the write-back and horizon frames from the
   same operand run. The scalar continuations use both views of the post. *)
Theorem create_word_cut_frame_facts[local]:
  expr_body_pre cenv cx env e es /\ expr_result_typed env e (Value v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sb s ee v op t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t) ==>
  value_has_type (BaseTV bt) v /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  wb_frame cenv es ee sa s t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ e _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all create_word_cut_facts >> strip_tac >>
  drule exprSimWordArgsTheory.expr_post_frame >> strip_tac >>
  asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ e _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[loweringPostsTheory.expr_post_def]
QED

Theorem create_cut_frames_keep_operand[local]:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ci_mono sa sm /\ wb_frame cenv es em sa s m /\ wb_frame cenv em ee sm m t /\
  ghost_kept_at lo cenv es sa G tn s Gm tm /\ ghost_kept_at lo cenv em sm Gm tm m G1 tn1 /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  eval_operand op m = SOME w /\ op_taint tm op = {} ==>
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  eval_operand op t = SOME w /\ op_taint tn1 op = {}
Proof
  strip_tac >>
  drule_all create_cut_frames_trans >> strip_tac >>
  drule_all create_operand_cut_frame >> simp[]
QED

(* The prepared initcode belongs to the continuation: the scalar cut
   evaluates only the amount and, when present, the one salt expression. *)
Theorem raw_create_scalar_suffix_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env amount es /\ body_exprs_full_ok cx (amount::salts) /\
  expr_type amount = BaseT (UintT 256) /\
  (if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  (!salt em. MEM salt salts /\ expr_sim_inv cenv cx env em ==>
     expr_body_pre cenv cx env salt em) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sb) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shb shadow_func /\ ci_mono sa sm /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!av sv. storage_trace_frame (next av sv)) /\
  (!av sv yw sw ee G1 tn1 t gs marks.
    dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\ IS_SOME sv = salted /\
    (!tail. eval_exprs cx (amount::salts) (es with gas_obs := gs ++ tail) =
      (INL (av::(case sv of NONE => [] | SOME v => [v])),ee with gas_obs := tail)) /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    (!x. y = Var x \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ expr_sim_inv cenv cx env ee /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    return_buf_frame d cenv sb t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next av sv) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_exprs cx (amount::salts))
      (\vs. next (HD vs) (if salted then SOME (EL 1 vs) else NONE)))
    (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `body_exprs_full_ok _ (amount::_)` mp_tac >>
  rewrite_tac[Once body_exprs_full_ok_def] >> strip_tac >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac >-
    simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexistsl [`cenv`,`d`,`env`,`y`,`sa`,`sm`,`sh`,`shadow_func`,`shm`,`tops`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `lower_value _ _ _ _ _` >>
       qpat_assum `expr_type amount = _` (fn th => once_rewrite_tac [GSYM th]) >>
       first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`av`,`em`,`Gm`,`tm`,`m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ma` strip_assume_tac) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ _` (drule_then assume_tac) >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  qabbrev_tac `yw = typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  `dest_NumV av = SOME (w2n yw)` by simp[Abbr `yw`,exprSimSendTheory.uint256_typed_dest] >>
  Cases_on `salted` >> gvs[compile_create_salt_def,comp_return_def]
  >- suspend "salt_some" >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  simp[bind_return] >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  qpat_assum `!av yw ee G1 tn1 t gs marks. _ ==> gas_outcome_full _ _ _ _ (next av NONE) _ _ _` irule >>
  simp[dest_optional_salt_def] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexists `gas_explicit ma s.vs_gas_readings` >>
      once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
      simp[GSYM bind_assoc,bind_def,return_def]) >>
  qexists `ma` >> simp[]
QED
Resume raw_create_scalar_suffix_cut[salt_some]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt sm` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) shm` >>
  gvs[comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt sm = (sop1,sb)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr salt) _ = (sop1,shb)` >>
  `expr_body_pre cenv cx env salt em` by (first_x_assum irule >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def,exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  fs[Once body_exprs_full_ok_def] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >>
  qpat_assum `!av sv. storage_trace_frame (next av sv)`
    (fn frame => simp[NoAsms,frame]) >>
  qexistsl [`cenv`,`d`,`env`,`sop1`,`sm`,`sb`,`shm`,`shadow_func`,`shb`,`tops`] >>
  qpat_assum `expr_type salt = _` (fn ty => simp[NoAsms,ty]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`sv`,`en`,`Gn`,`tnn`,`n`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ms` strip_assume_tac) >>
  `is_word_type (BaseT (BytesT (Fixed 32)))` by simp[is_word_type_def] >>
  `lower_value compile_expr cenv (expr_type salt) salt sm = (sop1,sb)` by simp[] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) es.storage_trace`
    by (fs[storage_trace_domain_def] >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `eval_operand y m = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  qabbrev_tac `sw = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `dest_create_salt sv = SOME sw` by
    (simp[Abbr `sw`] >> irule create_salt_word >> first_assum ACCEPT_TAC) >>
  `!tail. eval_exprs cx [salt]
      (em with gas_obs := gas_explicit ms m.vs_gas_readings ++ tail) =
      (INL [sv],en with gas_obs := tail)` by
    (once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     simp[GSYM bind_assoc,bind_def,return_def]) >>
  `!tail. eval_exprs cx [amount;salt]
      (es with gas_obs := (gas_explicit ma s.vs_gas_readings ++
                           gas_explicit ms m.vs_gas_readings) ++ tail) =
      (INL [av;sv],en with gas_obs := tail)` by
    (irule create_eval_exprs_cons_replay >> qexists `em` >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`cenv`,`expr_type salt`,`salt`,`sm`] mp_tac
       exprLoweringPropsTheory.ci_mono_lower_value_compile_expr >> simp[]) >>
  `!x. y = Var x ==> not_fresh_at sb x` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `MAP FDOM es.scopes = MAP FDOM en.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  `s.vs_alloca_next <= n.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  qpat_assum `!av sv yw sw ee G1 tn1 t gs marks. _ ==> gas_outcome_full _ _ _ _ (next av sv) _ _ _`
    irule >>
  simp[dest_optional_salt_def,optionTheory.OPTREL_def] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (qexists `gas_explicit ma s.vs_gas_readings ++ gas_explicit ms m.vs_gas_readings` >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> first_assum drule >> simp[]) >>
  qexists `ma ++ ms` >> gen_tac >> disch_tac >>
  simp[] >>
  irule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
  qexistsl [`Gm`,`m`,`(OK m,Gm,tm)`,`tm`] >> simp[]
QED
Finalise raw_create_scalar_suffix_cut

Theorem proxy_expr_sim_from_parts:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es /\
  body_exprs_full_ok cx (create_operand_order CreateMinimalProxy salted args) /\
  (!st0 sa sb sm s0 G0 tn0 result ee s G tn ptr pv amount aw sop sw addr source.
    compile_create_dispatch ptr (Lit 54w) amount sop rof sm = (result,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    return_buf_frame d cenv sm s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\ storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    outcomes_accounts_typed ee.outcomes /\
    eval_operand ptr s = SOME pv /\
    (?p. ptr = Var p /\ ptr_covers G tn p s 54 /\ not_fresh_at sm p) /\
    w2n pv + 54 <= s.vs_alloca_next /\ w2n pv + 54 < dimword (:256) /\
    read_memory (w2n pv) 54 s = minimal_proxy_initcode addr /\
    (!i. w2n pv <= i /\ i < w2n pv + 54 ==> i NOTIN tn.t_mem) /\
    eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
    (!x. amount = Var x ==> not_fresh_at sm x) /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {} /\
           (!x. op = Var x ==> not_fresh_at sm x)) /\
    (!tail. source (ee with gas_obs := tail) =
       bind (ignore_bind (check_not_static cx)
          (create_oracle_result sw (w2n aw) (minimal_proxy_initcode addr) rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 source (ee,s,G,tn)
      (\H res ee' G' tn' t. ?v. res = INL v /\
        expr_post H ctx func cenv cx
          (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt)
          es sa sb s0 ee' v result t /\
        expr_store_bound cx (BaseT AddressT) v result t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
        ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
      (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es
Proof
  strip_tac >> drule proxy_pre_args >> strip_tac >> gvs[] >>
  `LENGTH salts = (if salted then 1 else 0)` by
    (Cases_on `salted` >> gvs[]) >>
  rewrite_tac[bodySimFullTheory.expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all proxy_compile_cuts >> strip_tac >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_cut_code) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_cut_code) >>
  simp[NoAsms,create_eval_read,create_operand_order_def,vyperASTTheory.expr_type_def,
       loweringPostsTheory.post_value_type_def,is_word_type_def] >>
  suspend "target"
QED

Resume proxy_expr_sim_from_parts[target]:
  `expr_body_pre cenv cx env target es` by
    (irule create_operand_pre >> simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_full_ok_def]) >>
  strip_tac >> rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  qexistsl [`tops`,`a'`,`shadow_func`,`shadow_sa`,`a`,`sa`,`x`,`env`,`d`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env amount et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_full_ok_def] >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  qexistsl [`tops`,`b'`,`shadow_func`,`a'`,`b`,`a`,`y`,`env`,`d`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> fs[loweringPostsTheory.expr_post_def])
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`av`,`ea`,`Gamt`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "buffer_inputs"
QED

Resume proxy_expr_sim_from_parts[buffer_inputs]:
  qpat_x_assum `_ ==> body_exprs_full_ok _ salts` (drule_then assume_tac) >>
  `is_word_type (expr_type target) /\ is_word_type (expr_type amount)` by
    simp[is_word_type_def] >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  qpat_assum `lower_value _ _ _ amount a = _`
    (mp_then Any (drule_all_then strip_assume_tac) exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  `value_has_type (BaseTV AddressT) tv /\ value_has_type (BaseTV (UintT 256)) av` by
    (qpat_x_assum `expr_result_typed _ target _` mp_tac >>
     qpat_x_assum `expr_result_typed _ amount _` mp_tac >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def,vyperValueTheory.evaluate_type_def] >>
     rpt strip_tac >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) et.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ea.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qabbrev_tac `tw = typed_val_to_w256 (BaseTV AddressT) tv` >>
  qabbrev_tac `aw = typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  `eval_operand x st = SOME tw /\ eval_operand y samt = SOME aw` by
    (`evaluate_type (get_tenv cx) (expr_type target) = SOME (BaseTV AddressT) /\
      evaluate_type (get_tenv cx) (expr_type amount) = SOME (BaseTV (UintT 256))` by
       simp[vyperValueTheory.evaluate_type_def] >>
     conj_tac
     >- (qpat_assum `expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _`
          (mp_then Any drule_all exprSimPrecompilesTheory.expr_post_typed_stack_operand) >>
         simp[Abbr `tw`]) >>
     qpat_assum `expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _`
       (mp_then Any drule_all exprSimPrecompilesTheory.expr_post_typed_stack_operand) >>
     simp[Abbr `aw`]) >>
  `eval_operand x samt = SOME tw` by
    (qpat_assum `expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     match_mp_tac (Q.SPECL [`x`, `a`, `st`, `samt`, `tw`]
       exprBopSimPropsTheory.eval_operand_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tnt x = {} /\ op_taint tna y = {}` by
    fs[ptr_val_ok_def,loweringPostsTheory.post_value_type_def] >>
  `op_taint tna x = {}` by
    (`op_taint tna x = op_taint tnt x` suffices_by simp[] >>
     irule emittedSeqComposePtrTheory.old_operand_taint_frame >> qexists `a` >>
     simp[] >> fs[ghost_kept_at_def]) >>
  suspend "buffer_run"
QED

Resume proxy_expr_sim_from_parts[buffer_run]:
  `sa.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= b.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv b` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z. x = Var z ==> not_fresh_at b z)` by
    (conj_tac
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
     rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `a` >> simp[]) >>
  `allocas_from lo samt /\ lo <= samt.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx ea samt`
    by metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  mp_tac (Q.INST [`target` |-> `x`, `sa` |-> `b`, `sb` |-> `c`,
    `s` |-> `samt`, `es` |-> `ea`, `tn` |-> `tna`,
    `H` |-> `storage_trace_horizon ea.storage_trace`, `word` |-> `tw`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `G` |-> `Gamt`]
    proxy_buf_origin_window) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`pbuf`, `pw`, `sbuf`, `Gbuf`, `tnb`] strip_assume_tac) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gbuf`,`sbuf`,`tnb`] >> conj_tac
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `samt.vs_alloca_next <= sbuf.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `DF (storage_trace_horizon ea.storage_trace)`
        (mp_then Any ACCEPT_TAC body_full_path_alloca_next_mono))) >>
  `b.cs_next_var <= c.cs_next_var /\ c.cs_next_var <= d'.cs_next_var /\
   b.cs_next_id <= c.cs_next_id /\ c.cs_next_id <= d'.cs_next_id` by fs[ci_mono_def] >>
  `return_buf_frame d cenv c sbuf` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv b samt` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at b x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ea sbuf /\
     storage_well_formed_on cx ea (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ea Gbuf tnb sbuf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     conj_tac
     >- (qpat_assum `!H'. stmt_state_rel _ ctx func cenv cx ea samt ==> _`
           (drule_then ACCEPT_TAC)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D d. ghost_inv_at D lo d cenv cx ea Gamt tna samt ==> _`
       (drule_then ACCEPT_TAC)) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) es.storage_trace` by
    first_assum (drule_then ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ea.storage_trace` mp_tac) >> simp[]) >>
  qpat_assum `expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  qpat_assum `expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  `wb_frame cenv es et sa s0 st /\ wb_frame cenv et ea a st samt` by
    (rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM et.scopes /\ MAP FDOM et.scopes = MAP FDOM ea.scopes` by
    (conj_tac
     >- (qpat_assum `locals_kept cenv es et s0 st`
           (ACCEPT_TAC o SYM o cj 2 o REWRITE_RULE [loweringPostsTheory.locals_kept_def])) >>
     qpat_assum `locals_kept cenv et ea st samt`
       (ACCEPT_TAC o SYM o cj 2 o REWRITE_RULE [loweringPostsTheory.locals_kept_def])) >>
  `wb_frame cenv es ea sa s0 samt` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`et`,`a`,`st`] >> simp[] >> metis_tac[]) >>
     qexistsl [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gamt tna` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv et a Gtar tnt st Gamt tna` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `wb_frame cenv es ea sa s0 sbuf` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`ea`,`b`,`samt`] >> simp[] >> metis_tac[]) >>
     qexistsl [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  suspend "buffer_ready"
QED

Resume proxy_expr_sim_from_parts[buffer_ready]:
  `s0.vs_alloca_next <= sbuf.vs_alloca_next` by decide_tac >>
  `alloca_inv s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gbuf tnb` by
    (qpat_assum `!sk es0 G0 tn0 s0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gbuf tnb`
       irule >> simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
           (mp_then Any (drule_then assume_tac) abiEncodeOwnershipTheory.abi_encode_local_region_frontier) >>
         decide_tac) >>
     rpt strip_tac >>
     qpat_assum `alloca_inv s0` (mp_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def,
                                       venomMemDefsTheory.alloca_next_valid_def]) >>
     disch_then (drule_then assume_tac o CONJUNCT2) >> decide_tac) >>
  `local_ptrs_reserved cenv c` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= c.cs_next_var /\ sa.cs_next_id <= c.cs_next_id` by decide_tac >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z. y = Var z ==> not_fresh_at c z)` by
    (conj_tac
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `b` >> asm_rewrite_tac[] >>
         qpat_assum `!z n. cenv.ce_return_buf = _ ==> not_fresh_at b z`
           (drule_then ACCEPT_TAC)) >>
     conj_tac
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `b` >> asm_rewrite_tac[] >>
         qpat_assum `!z n. cenv.ce_return_pc = _ ==> not_fresh_at b z`
           (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `b` >> asm_rewrite_tac[] >>
     qpat_assum `!z. y = Var z ==> not_fresh_at b z` (drule_then ACCEPT_TAC)) >>
  `sbuf.vs_labels = samt.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (samt,Gamt,tna) [] (OK sbuf,Gbuf,tnb)`
       (qspec_then `DF (storage_trace_horizon ea.storage_trace)`
         (mp_then Any ACCEPT_TAC gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `!op. (!z. op = Var z ==> not_fresh_at b z) ==>
     eval_operand op sbuf = eval_operand op samt /\
     op_prov Gbuf op = op_prov Gamt op /\ op_taint tnb op = op_taint tna op` by
    (match_mp_tac bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >>
     simp[]) >>
  `eval_operand y sbuf = SOME aw /\ op_taint tnb y = {}` by
    (qpat_assum `!op. _ ==> eval_operand op sbuf = eval_operand op samt /\ _`
       (qspec_then `y` mp_tac) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx ea sbuf`
    by first_assum (drule_then ACCEPT_TAC) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp sbuf)` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `IS_SOME ea.outcomes` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ea sbuf`
      (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def,
                                       loweringStateRelDefsTheory.state_rel_def]) >> simp[]) >>
  `dest_AddressV tv = SOME (w2w tw) /\ dest_NumV av = SOME (w2n aw)` by
    (simp[NoAsms,Abbr `tw`,Abbr `aw`] >> conj_tac
     >- (irule exprSimSendTheory.address_typed_dest >> first_assum ACCEPT_TAC) >>
     irule exprSimSendTheory.uint256_typed_dest >> first_assum ACCEPT_TAC) >>
  Cases_on `salted` >> PURE_REWRITE_TAC [COND_CLAUSES] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES])
  >- (qpat_x_assum `?salt. salts = [salt] /\ _`
        (qx_choose_then `salt` (fn shape =>
           assume_tac (cj 2 shape) >> SUBST_ALL_TAC (cj 1 shape))) >>
      qpat_assum `expr_type salt = _` (fn ty =>
        map_every (fn pat => qpat_x_assum pat
          (assume_tac o SIMP_RULE (srw_ss())
            [compile_create_salt_def,gas_shadow_expr_type,ty]))
          [`compile_create_salt compile_expr cenv _ c = _`,
           `compile_create_salt compile_expr (gas_shadow_env T cenv) _ c' = _`]) >>
      suspend "salt_cut") >>
  qpat_x_assum `salts = []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_salt compile_expr cenv NONE c = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
     PURE_REWRITE_RULE [compile_create_salt_def,comp_return_def,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `compile_create_salt compile_expr (gas_shadow_env T cenv) _ c' = _`
    (SUBST_ALL_TAC o SYM o cj 2 o
     PURE_REWRITE_RULE [optionTheory.OPTION_MAP_DEF,compile_create_salt_def,
                        comp_return_def,pairTheory.PAIR_EQ]) >>
  suspend "no_salt"
QED

Resume proxy_expr_sim_from_parts[no_salt]:
  simp[NoAsms,Once vyperInterpreterTheory.evaluate_def,bind_return] >>
  qpat_assum `!st0 sa sb sm s0 G0 tn0 result ee s G tn ptr pv amount aw sop sw addr source.
    _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  `outcomes_accounts_typed ea.outcomes` by
    (qpat_assum `expr_sim_inv _ _ _ ea`
       (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (gen_tac >> disch_tac >> simp[] >> NO_TAC) >>
  TRY decide_tac >>
  qexistsl [`w2w tw`,`y`,`aw`,`Var pbuf`,`pw`,`c`,`NONE`,`NONE`] >>
  simp[eval_operand_def] >> rpt conj_tac
  >- (gen_tac >>
      irule (SIMP_RULE (srw_ss()) [dest_optional_salt_def]
          (Q.INST [`salt` |-> `NONE`] create_proxy_read_prepared)) >> simp[]) >>
  TRY (qpat_assum `ptr_covers Gbuf tnb pbuf sbuf 96`
     (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def] >> qexistsl [`w2n pw`,`96`] >> simp[] >> NO_TAC)
  >- (qpat_assum `w2n pw + 96 < dimword (:256)` mp_tac >>
      simp[NoAsms,wordsTheory.dimword_def] >> numLib.ARITH_TAC) >>
  qpat_assum `buf = Var pbuf` (fn buffer =>
    qpat_assum `compile_create_dispatch buf (Lit 54w) y NONE rof c = (op,sb)`
      (ACCEPT_TAC o REWRITE_RULE [buffer]))
QED

Resume proxy_expr_sim_from_parts[salt_cut]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt c` >>
  rename1 `lower_value _ _ _ salt c = (salt_op,stage)` >>
  qpat_assum `lower_value _ _ _ salt c = (salt_op,stage)` (fn lower =>
    qpat_x_assum `comp_bind (lower_value _ _ _ salt) _ c = _`
      (fn compiled =>
         let val result = CONV_RULE (LHS_CONV (SIMP_CONV pure_ss
               [comp_bind_def,lower,LET_THM,pairTheory.UNCURRY,
                pairTheory.FST,pairTheory.SND,comp_return_def])) compiled
             val parts = PURE_REWRITE_RULE [pairTheory.PAIR_EQ] result
         in SUBST_ALL_TAC (SYM (cj 1 parts)) >> SUBST_ALL_TAC (cj 2 parts) end)) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) c'` >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr salt) c' = _` (fn lower =>
    qpat_x_assum `comp_bind (lower_value _ _ _ (gas_shadow_expr salt)) _ c' = _`
      (map_every SUBST_ALL_TAC o CONJUNCTS o
       PURE_REWRITE_RULE [pairTheory.PAIR_EQ,optionTheory.SOME_11] o
       CONV_RULE (LHS_CONV (SIMP_CONV pure_ss
         [comp_bind_def,lower,LET_THM,pairTheory.UNCURRY,
                pairTheory.FST,pairTheory.SND,comp_return_def])))) >>
  `expr_body_pre cenv cx env salt ea` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok cx [salt]`
    (strip_assume_tac o SIMP_RULE bool_ss [body_exprs_full_ok_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  `!fn i z. frag_reachable ctx func sbuf fn i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK sbuf,Gbuf,tnb)`
       (qspec_then `DF (storage_trace_horizon ea.storage_trace)`
         (mp_then Any drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom)) >> simp[]) >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,Once vyperInterpreterTheory.evaluate_def,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  qexistsl [`tops`,`d''`,`shadow_func`,`c'`,`d'`,`c`,`salt_op`,`env`,`d`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[] >- simp[]
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`sv`,`ew`,`Gsalt`,`tns`,`ssalt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ew.storage_trace`
    by qpat_assum `storage_trace_domain cx st0 ew.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `wb_frame cenv ea ew c sbuf ssalt` by
    (qpat_assum `expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[loweringPostsTheory.wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ew.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ew ssalt /\
     storage_well_formed_on cx ew (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ew Gsalt tns ssalt` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
  suspend "salt_window"
QED

Resume proxy_expr_sim_from_parts[salt_window]:
  `!name base len. local_region cenv ea.scopes sbuf name base len ==>
     w2n pw + 96 <= base \/ base + len <= w2n pw` by
    (qpat_assum `!name b n. local_region cenv ea.scopes sbuf name b n ==> regions_disjoint _ _ b n`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `read_memory (w2n pw) 96 ssalt = read_memory (w2n pw) 96 sbuf` by
    (simp[read_memory_eq_mem_bytes_at] >>
     qpat_assum `wb_frame cenv ea ew c sbuf ssalt`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  `!u. read_memory (w2n pw) 54 u = TAKE 54 (read_memory (w2n pw) 96 u)` by
    (gen_tac >>
     qspecl_then [`w2n pw`,`96`,`0`,`54`,`u`] mp_tac read_memory_subwindow >> simp[]) >>
  `read_memory (w2n pw) 54 ssalt = minimal_proxy_initcode (w2w tw)` by
    (qpat_assum `!u. read_memory _ 54 u = _` (qspec_then `sbuf` mp_tac) >> simp[]) >>
  `!i. w2n pw <= i /\ i < w2n pw + 54 ==> i NOTIN tns.t_mem` by
    (rpt strip_tac >> `i < w2n pw + 96` by decide_tac >>
     qpat_assum `ghost_kept_at lo cenv ea c Gbuf tnb sbuf Gsalt tns`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     `i IN tnb.t_mem` by first_assum (drule_all_then ACCEPT_TAC) >>
     metis_tac[]) >>
  `lookup_var pbuf ssalt = SOME pw` by
    (match_mp_tac (Q.SPECL [`cenv`, `ea`, `ew`, `c`, `sbuf`, `ssalt`, `pbuf`, `pw`]
       exprSimWordArgsTheory.wb_frame_vars) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers Gsalt tns pbuf ssalt 54` by
    (qpat_assum `ghost_kept_at lo cenv ea c Gbuf tnb sbuf Gsalt tns`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `ptr_covers Gbuf tnb pbuf sbuf 96`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  `eval_operand y ssalt = SOME aw /\ op_taint tns y = {}` by
    (conj_tac
     >- (match_mp_tac (Q.SPECL [`y`,`c`,`sbuf`,`ssalt`,`aw`]
           exprBopSimPropsTheory.eval_operand_frame) >>
         simp[] >> rpt strip_tac >>
         match_mp_tac (Q.SPECL [`cenv`,`ea`,`ew`,`c`,`sbuf`,`ssalt`]
           exprSimWordArgsTheory.wb_frame_vars) >> simp[]) >>
     `op_taint tns y = op_taint tnb y` suffices_by simp[] >>
     irule emittedSeqComposePtrTheory.old_operand_taint_frame >> qexists `c` >>
     simp[] >> gen_tac >> disch_tac >>
     qpat_assum `ghost_kept_at lo cenv ea c Gbuf tnb sbuf Gsalt tns`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> simp[]) >>
  suspend "salt_root_frames"
QED
Resume proxy_expr_sim_from_parts[salt_root_frames]:
  `MAP FDOM es.scopes = MAP FDOM ea.scopes` by metis_tac[] >>
  `wb_frame cenv es ew sa s0 ssalt` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`ea`,`c`,`sbuf`] >> simp[]) >>
     qexistsl [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gsalt tns` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv ea c Gbuf tnb sbuf Gsalt tns` (irule_at Any) >>
     simp[] >>
     qexistsl [`func`,`ea`,`cx`,`ctx`,`storage_trace_horizon ea.storage_trace`] >> simp[]) >>
  `local_ptrs_reserved cenv d'` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `c` >> asm_rewrite_tac[]) >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at d' z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at d' z) /\
   (!z. y = Var z ==> not_fresh_at d' z) /\ not_fresh_at d' pbuf` by
    (rpt conj_tac >> rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `c` >> simp[]) >>
  suspend "salt_dispatch"
QED

Resume proxy_expr_sim_from_parts[salt_dispatch]:
  `is_word_type (expr_type salt) /\
   evaluate_type (get_tenv cx) (expr_type salt) = SOME (BaseTV (BytesT (Fixed 32)))` by
    simp[is_word_type_def,vyperValueTheory.evaluate_type_def] >>
  qpat_assum `lower_value _ _ _ salt c = _`
    (mp_then Any (drule_all_then strip_assume_tac) exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  `value_has_type (BaseTV (BytesT (Fixed 32))) sv` by
    (qpat_x_assum `expr_result_typed _ salt _` mp_tac >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def,vyperValueTheory.evaluate_type_def] >>
     rpt strip_tac >> simp[]) >>
  qabbrev_tac `sw = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `eval_operand salt_op ssalt = SOME sw` by
    (qpat_assum `expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _`
       (mp_then Any drule_all exprSimPrecompilesTheory.expr_post_typed_stack_operand) >>
     simp[Abbr `sw`]) >>
  `op_taint tns salt_op = {}` by
    (qpat_x_assum `ptr_val_ok _ _ sv salt_op _ _ _` mp_tac >>
     simp[ptr_val_ok_def,loweringPostsTheory.post_value_type_def,is_word_type_def]) >>
  `dest_create_salt sv = SOME sw` by
    (simp[Abbr `sw`] >> irule create_salt_word >> first_assum ACCEPT_TAC) >>
  `outcomes_accounts_typed ew.outcomes` by
    (qpat_assum `expr_sim_inv _ _ _ ew`
       (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ew.storage_trace) ctx func cenv cx ew ssalt`
    by first_assum (drule_then strip_assume_tac) >>
  `IS_SOME ew.outcomes` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ew ssalt`
      (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def,
                                       loweringStateRelDefsTheory.state_rel_def]) >> simp[]) >>
  qpat_assum `!st0 sa sb sm s0 G0 tn0 result ee s G tn ptr pv amount aw sop sw addr source.
    _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (gen_tac >> disch_tac >> simp[] >> NO_TAC) >>
  TRY decide_tac >>
  qexistsl [`w2w tw`,`y`,`aw`,`Var pbuf`,`pw`,`d'`,`SOME salt_op`,`SOME sw`] >>
  qpat_x_assum `buf = Var pbuf` SUBST_ALL_TAC >>
  simp[eval_operand_def] >> rpt conj_tac
  >- (gen_tac >>
      irule (SIMP_RULE (srw_ss()) [dest_optional_salt_def]
        (Q.INST [`salt` |-> `SOME sv`] create_proxy_read_prepared)) >> simp[]) >>
  qpat_assum `w2n pw + 96 < dimword (:256)` mp_tac >>
  simp[NoAsms,wordsTheory.dimword_def] >> numLib.ARITH_TAC
QED
Finalise proxy_expr_sim_from_parts

Theorem create_minimal_proxy_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx (create_operand_order CreateMinimalProxy s es) ==>
    body_expr_full_ok cx (Call ty (CreateTarget CreateMinimalProxy s r ks) es d)
Proof
  rpt gen_tac >> disch_tac >> ONCE_REWRITE_TAC [body_expr_full_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule proxy_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (irule proxy_expr_sim_from_parts >>
      reverse conj_tac >- (simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `?p. _ = Var p /\ ptr_covers _ _ p _ 54 /\ _` strip_assume_tac >>
      gvs[] >>
      irule (Q.INST [`len` |-> `Lit 54w`,`sz` |-> `54w`]
               create_dispatch_outcome_full) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (simp[eval_operand_def, op_taint_def, vfmConstantsTheory.max_code_size_def,
          loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def,
          supportedExprTraverseTheory.expr_has_effect_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedExprTraverseTheory.expr_effect_root_def] >> NO_TAC) >>
      qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `eval_operand (Var _) _ = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand amount _ = SOME _` (irule_at Any) >>
      qexistsl [`sw`,`minimal_proxy_initcode addr`] >>
      simp[vfmConstantsTheory.max_code_size_def] >>
      conj_tac >- fs[ptr_covers_def] >>
      Cases_on `sop` >> fs[] >> metis_tac[]) >>
  irule bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[create_compile_stack,loweringPostsTheory.post_value_type_def,
       vyperASTTheory.expr_type_def,is_word_type_def] >>
  metis_tac[create_eval_value]
QED

(* The physical rows and the source annotations yield the same ABI bytes.
   The bound here is for the physical allocation. *)
Triviality create_encoded_rows_layout:
  EVERY (\e. expr_body_pre ce cx env e es) args /\
  LENGTH args = LENGTH vs /\ LENGTH args = LENGTH (vals:vyper_value list) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    value_has_type tv (EL i vs)) ==>
  ?ats avs bytes.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
    bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                         abi_member_head_size at) (ZIP (vals,MAP (lowered_value_type ce) args)) ats
Proof
  strip_tac >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `src = MAP expr_type args` >>
  `?avs ats bytes.
    vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) tys /\
    bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
    build_ext_calldata (get_tenv cx) "" src vs =
      SOME (function_selector "" (vyper_to_abi_types (get_tenv cx) src) ++ bytes) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                    abi_member_head_size at) (ZIP (vals,tys)) ats` by
    (irule bodyFullExtCallDirectLayoutTheory.extcall_direct_args_layout >>
     simp[Abbr `tys`, Abbr `src`] >> qx_gen_tac `i` >> strip_tac >> simp[EL_MAP] >>
     `expr_body_pre ce cx env (EL i args) es` by fs[EVERY_EL] >>
     drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     disch_then (qx_choose_then `ftv` assume_tac) >>
     `i < LENGTH args` by decide_tac >>
     qpat_assum `!i. i < LENGTH args ==> ?tv. _`
       (qspec_then `i` (drule_then (qx_choose_then `tv` strip_assume_tac))) >>
     qexistsl [`tv`,`ftv`] >> simp[] >>
     metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
               cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type]) >>
  qexistsl [`ats`,`avs`,`bytes`] >> fs[Abbr `tys`, Abbr `src`] >>
  `TAKE (LENGTH vs) (MAP expr_type args) = MAP expr_type args` by simp[TAKE_LENGTH_ID_rwt] >>
  qpat_x_assum `build_ext_calldata _ _ _ _ = SOME _` mp_tac >>
  simp[vyperABITheory.build_ext_calldata_def, TAKE_LENGTH_ID_rwt,
       encode_create_ctor_args_def] >>
  Cases_on `vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs` >> simp[]
QED

(* Execute the final value-row encoder. se and s are at the end of
   constructor evaluation; st and initial are after destination setup.
   Blueprint uses an empty prefix, and RawCreate uses its saved bytecode. *)
Theorem create_encoded_rows_window:
  LENGTH args = LENGTH vals /\ LENGTH args = LENGTH vs /\
  EVERY (\e. expr_body_pre ce cx env e ee) args /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!i. i < LENGTH args ==>
    ?e saved v raw si sm ss vv copy tv.
      e = EL i args /\ saved = EL i vals /\ v = EL i vs /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr ce (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,ss) /\
      ((?tag op0. saved = StackValue tag op0) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type ce e = expr_type e /\ saved = vv)) /\
      local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand saved <> Label l) /\ read_result cx raw ee = (INL v,ee) /\
      vv_holds ce cx (lowered_value_type ce e) raw saved ee s /\
      vv_at ce cx (lowered_value_type ce e) si ss ee raw saved s /\
      ptr_vv_ok cx (lowered_value_type ce e) raw saved ee G tn s /\
      vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved s /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx saved ee s) /\
      ((case saved of StackValue tag op0 => ~is_word_type (lowered_value_type ce e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce e (vv_operand saved) G s)) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  LENGTH prefix + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <= capacity /\
  compile_abi_encode_values_to_buf ce (Var payload_var) (ZIP (vals,MAP (lowered_value_type ce) args)) st =
    (alen,fin) /\ fn_has_code st fin func /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var (LENGTH prefix) prefix st initial Gi ti ==>
  ?bytes z Gz tz.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    pure_frame ce func ee se initial z /\ wb_frame ce ee ee se initial z /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var (LENGTH prefix) prefix fin z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at fin x) /\
    LENGTH prefix + LENGTH bytes <= capacity /\ pbase + capacity <= z.vs_alloca_next /\
    read_memory pbase (LENGTH (prefix ++ bytes)) z = prefix ++ bytes /\
    (!j. pbase <= j /\ j < pbase + LENGTH (prefix ++ bytes) ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (initial,Gi,ti) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (drule_all bodyCustomErrorWindowBoundsTheory.custom_error_invariant_layout >> simp[]) >>
  Q.SUBGOAL_THEN `?H. valid_horizon cx st0 H ee.storage_trace` assume_tac
  >- metis_tac[storage_trace_domain_def] >>
  `!i. i < LENGTH args ==> ?tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    value_has_type tv (EL i vs)` by
    (qx_gen_tac `i` >> disch_tac >>
     qpat_assum `!i. i < LENGTH args ==> ?e saved v raw si sm ss vv copy tv. _`
       (qspec_then `i` (drule_then (qx_choosel_then [`e`,`saved`,`v`,`raw`,`si`,`sm`,`ss`,`vv`,`copy`,`tv`]
         (MAP_EVERY assume_tac o CONJUNCTS)))) >>
     qexists `tv` >> gvs[]) >>
  drule_all create_encoded_rows_layout >>
  disch_then (qx_choosel_then [`ats`,`avs`,`bytes`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `rows = ZIP (vals,MAP (lowered_value_type ce) args)` >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  `hl = head_lengths ats 0` by simp[NoAsms, Abbr `hl`] >>
  `LENGTH rows = LENGTH args /\ LENGTH ats = LENGTH args /\ LENGTH avs = LENGTH args` by
    (qpat_assum `LIST_REL abi_encoder_layout_valid ats avs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     simp[Abbr `rows`, LENGTH_ZIP, abiDecoderMembersTheory.vyper_to_abi_types_MAP]) >>
  `LENGTH prefix + LENGTH bytes <= capacity` by decide_tac >>
  mp_tac (Q.INST [`dst_offset` |-> `LENGTH prefix`, `en` |-> `fin`,
    `u` |-> `initial`, `Gu` |-> `Gi`, `tu` |-> `ti`]
    bodyFullExtCallDirectEncodeTheory.abi_encode_saved_values_execute_pure) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "saved_row") >>
  disch_then (qx_choosel_then [`out`,`Go`,`to`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl [`bytes`,`out`,`Go`,`to`] >>
  drule_all bodyFullExtCallDirectStateTheory.abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var (LENGTH prefix) prefix fin out Go to`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE
      [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[allocaSiteResourceTheory.alloca_site_registered_below]
  >- (PURE_REWRITE_TAC [LENGTH_APPEND] >>
      PURE_ONCE_REWRITE_TAC [read_memory_split] >>
      BINOP_TAC
      >- (qpat_assum `read_memory (pbase + LENGTH prefix - LENGTH prefix) _ _ = _` mp_tac >>
          simp[NoAsms]) >>
      pure_rewrite_tac[read_memory_eq_mem_bytes_at] >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[LENGTH_APPEND] >> gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> Cases_on `j < pbase + LENGTH prefix`
  >- (qpat_assum `!i. pbase + LENGTH prefix - LENGTH prefix <= i /\ _ ==> _` irule >>
      asm_rewrite_tac[arithmeticTheory.ADD_SUB]) >>
  qpat_assum `!i. pbase + LENGTH prefix <= i /\ _ ==> _` irule >>
  qpat_assum `j < pbase + (LENGTH prefix + LENGTH bytes)` mp_tac >>
  asm_rewrite_tac[GSYM arithmeticTheory.NOT_LESS, GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[]
QED

Resume create_encoded_rows_window[saved_row]:
  map_every qx_gen_tac [`ci`,`cursor_var`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  map_every qx_gen_tac [`i`,`su`,`en`,`u`,`Gu`,`tu`,`cursor`,`slot`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i < LENGTH args /\ i < LENGTH ats /\ i < LENGTH avs /\ i < LENGTH vals /\ i < LENGTH vs` by decide_tac >>
  qpat_assum `!i. i < LENGTH args ==> ?e saved v raw si sm ss vv copy tv. _`
    (qspec_then `i` (drule_then (qx_choosel_then [`e`,`saved`,`v`,`raw`,`si`,`sm`,`ss`,`vv`,`copy`,`tv`]
      (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  qabbrev_tac `ty = lowered_value_type ce e` >>
  qabbrev_tac `at = EL i ats` >>
  qabbrev_tac `av = EL i avs` >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `EL i rows = (saved,ty) /\ at = vyper_to_abi_type (get_tenv cx) ty` by
    simp[Abbr `rows`, Abbr `ty`, Abbr `at`, abiDecoderMembersTheory.vyper_to_abi_types_MAP, EL_MAP, EL_ZIP] >>
  `vyper_to_abi (get_tenv cx) ty v = SOME av` by
    (qpat_assum `vyper_to_abi_list _ _ _ = SOME avs`
       (mp_tac o cj 3 o MATCH_MP vyperABIRoundtripTheory.vyper_to_abi_list_EL) >>
     disch_then (qspec_then `i` mp_tac) >> simp[Abbr `ty`, Abbr `av`, EL_MAP]) >>
  `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
   hl <= off /\ off <= LENGTH bytes /\ h + abi_member_head_size at <= hl /\
   (is_dynamic at ==> off + LENGTH (contractABI$enc at av) <= LENGTH bytes) /\
   (~is_dynamic at ==> LENGTH (contractABI$enc at av) = abi_member_head_size at) /\
   abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abiEncodeValuesMetadataTheory.abi_encode_values_index_bounds) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[NoAsms, Abbr `at`, Abbr `av`, Abbr `off`] >> NO_TAC) >>
     TRY (qpat_assum `bytes = contractABI$enc _ _` (fn th => PURE_REWRITE_TAC [th]) >> REFL_TAC >> NO_TAC) >>
     qexistsl [`rows`,`ce.ce_struct_fields`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms, Abbr `h`]) >>
  `LENGTH ats = LENGTH avs /\ off <= capacity - LENGTH prefix /\
   (is_dynamic at ==> off + LENGTH (contractABI$enc at av) <= capacity - LENGTH prefix)` by
    (rpt conj_tac >> TRY decide_tac >> disch_tac >>
     qpat_assum `is_dynamic at ==> off + LENGTH (contractABI$enc at av) <= LENGTH bytes`
       (drule_then assume_tac) >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s` by
    (gen_tac >> disch_tac >> conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `~is_word_type ty ==> ~is_word_type (expr_type e)` by
    (`expr_body_pre ce cx env e ee` by
       (qpat_assum `EVERY _ args` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
               aggregateEvaluatedLayoutTheory.arg_type_fits_word_type, Abbr `ty`]) >>
  `shared < st.cs_next_id` by
    (qpat_assum `abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
         shared pbase capacity root payload_var (LENGTH prefix) prefix st initial Gi ti`
       (mp_tac o REWRITE_RULE [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
     simp_tac bool_ss [GSYM AND_IMP_INTRO]) >>
  `compile_abi_encode_value_rows ce (Var payload_var) cursor h [(saved,ty)] su = ((),en)` by
    (qpat_assum `EL i rows = (saved,ty)` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`dst` |-> `payload_var`, `d` |-> `disp`, `dst_offset` |-> `LENGTH prefix`,
    `loc` |-> `st.cs_next_id`, `cursor_inst` |-> `ci`]
    bodyFullExtCallDirectRowTheory.abi_encode_saved_row_open_pure) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (disch_tac >> first_assum ACCEPT_TAC) >>
      simp[NoAsms, Abbr `ty`, Abbr `at`, Abbr `av`, Abbr `off`]) >>
  disch_then ACCEPT_TAC
QED

Finalise create_encoded_rows_window

(* The snapshot's physical tag decides whether it saves a word or copies
   bytes. Retagging a nonword leaves the materialization code unchanged. *)
Theorem create_ctor_snapshot_retag:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e /\
  (is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) <=>
   is_word_type (expr_type e)) /\
  (~is_word_type (expr_type e) ==>
   compile_materialize_vv cenv (lowered_value_type cenv e)
     (ext_call_arg_value (lowered_value_type cenv e) vv) =
   compile_materialize_vv cenv (lowered_value_type cenv e) vv)
Proof
  strip_tac >> conj_tac
  >- drule_all_then ACCEPT_TAC bodyFullExtCallPosAggregateTheory.extcall_operand_snapshot_type >>
  drule_all_then ACCEPT_TAC bodyFullExtCallPosAggregateTheory.extcall_operand_materialize_retag
QED

Theorem create_ctor_borrowed_row[local]:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\ compile_expr ce (expr_type e) e sa = (vv,sb) /\
  ty = lowered_value_type ce e /\ sv = ext_call_arg_value ty vv /\ ~is_word_type ty /\
  vv_holds ce cx (post_value_type ce e) raw vv ee s /\
  vv_at ce cx (post_value_type ce e) sa sb ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  vv_store_bound cx (post_value_type ce e) ty ee raw vv s ==>
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue ty p /\ p.ptr_location = LocMemory) \/
   (?p. sv = LocatedValue ty p /\ p.ptr_location <> LocMemory /\ ty = expr_type e /\ sv = vv)) /\
  (?r. read_result cx r ee = (INL v,ee) /\
    vv_holds ce cx ty r sv ee s /\ vv_at ce cx ty sa sb ee r sv s /\
    ptr_vv_ok cx ty r sv ee G tn s /\ vv_store_bound cx ty ty ee r sv s)
Proof
  strip_tac >> gvs[] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `(bind (eval_expr cx e) (read_result cx)) es = (INL v,ee)` by simp[bind_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) (cj 3 abiEncodeArgsCaseTheory.abi_args_success_ready)) >>
  simp[] >> strip_tac >>
  `~is_word_type (post_value_type ce e)` by
    (drule_all (Q.SPECL [`ce`,`e`] abiEncodeMaterializeTheory.materialize_post_lowered_classify) >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  qabbrev_tac `sv = ext_call_arg_value (lowered_value_type ce e) vv` >>
  Q.SUBGOAL_THEN
    `?r. read_result cx r ee = (INL v,ee) /\
         vv_holds ce cx (lowered_value_type ce e) r sv ee s /\
         vv_at ce cx (lowered_value_type ce e) sa sb ee r sv s /\
         ptr_vv_ok cx (lowered_value_type ce e) r sv ee G tn s /\
         vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee r sv s /\
         ((?tag op. sv = StackValue tag op) \/
          (?p. sv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocMemory) \/
          (?p. sv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location <> LocMemory /\
               lowered_value_type ce e = expr_type e /\ sv = vv))`
    (qx_choose_then `r` (map_every assume_tac o CONJUNCTS))
  >- suspend "retag" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `r` >> simp[] >>
  irule bodyFullExtCallPosTransportTheory.extcall_saved_physical_store_bound >>
  conj_tac >- (qexists `v` >> simp[]) >>
  qexists `post_value_type ce e` >> simp[]
QED

Resume create_ctor_borrowed_row[retag]:
  Cases_on `post_value_type ce e = lowered_value_type ce e`
  >- (Cases_on `vv` >> gvs[Abbr `sv`, ext_call_arg_value_def]
      >- (qexists `raw` >> simp[]) >>
      rename1 `compile_expr _ _ _ _ = (LocatedValue tag p,sb)` >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qexists `raw` >> gns[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
                             ptr_vv_ok_def, exprSimMemDefsTheory.vv_store_bound_def]) >>
      drule_all exprPtrUnwrapStorageShapeTheory.compile_nonmemory_lowered_value_type >> strip_tac >>
      `tag = expr_type e` by fs[loweringPostsTheory.post_value_type_lowered, loweringPostsTheory.vv_holds_def] >>
      gvs[] >> qexists `raw` >> simp[]) >>
  `post_value_type ce e = expr_type e` by
    (Cases_on `e` >> simp[loweringPostsTheory.post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     fs[loweringPostsTheory.post_value_type_def, expr_type_def] >> IF_CASES_TAC >> gvs[]) >>
  drule_all (Q.SPECL [`ce`,`e`] abiEncodeMaterializeTheory.materialize_post_lowered_classify) >>
  simp[] >> strip_tac >>
  Q.SUBGOAL_THEN
    `(?tag op. vv = StackValue tag op) \/ (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)`
    assume_tac
  >- (Cases_on `vv` >> simp[] >> CCONTR_TAC >> fs[] >>
      drule_all exprPtrUnwrapStorageShapeTheory.compile_nonmemory_lowered_value_type >> simp[]) >>
  qexists `Value v` >> simp[read_result_def, return_def] >>
  `vv_holds ce cx (lowered_value_type ce e) (Value v) sv ee s /\
   vv_at ce cx (lowered_value_type ce e) sa sb ee (Value v) sv s /\
   ptr_vv_ok cx (lowered_value_type ce e) (Value v) sv ee G tn s /\
   vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) sv s` by
    (simp[Abbr `sv`] >> match_mp_tac bodyFullExtCallPosAggregateTheory.snapshot_bytes_retag >> gns[]) >>
  simp[] >> Cases_on `vv` >> gvs[Abbr `sv`, ext_call_arg_value_def]
QED

Finalise create_ctor_borrowed_row

(* Reading a borrowed aggregate adds no target instruction. Its source
   read still runs immediately, before evaluating any later argument. *)
Theorem create_ctor_borrowed_head_outcome:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sh = (vv,shb) /\
  compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) sb = (sv,sb) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) /\
  ~is_word_type (lowered_value_type cenv e) /\
  (!gs pv ee tag p. eval_expr cx e (es with gas_obs := gs) = (INL pv,ee) /\
     vv = LocatedValue tag p /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
       tag = expr_type e /\ (!v. pv <> Value v)) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code sh shb shadow_func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op. sv = StackValue tag op) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
         ptr_buf_ok cenv e (vv_operand sv) G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
       (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
       (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible, exprSimMemorySourceTheory.forced_expr_admissible_raw] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_def] >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
          `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodySimFullTheory.expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >>
  suspend "read"
QED

Resume create_ctor_borrowed_head_outcome[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. _ ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists `tv` >> conj_tac >- REFL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[] >> disch_tac >>
  Cases_on `read_result cx tv ee` >>
  rename1 `read_result cx tv ee = (read_res,read_state)` >>
  drule_then SUBST_ALL_TAC read_result_state >>
  Cases_on `read_res`
  >- (rename1 `read_result cx tv ee = (INL v,ee)` >> suspend "package") >>
  metis_tac[exprSimUnwrapTheory.vv_post_failed_read]
QED

Resume create_ctor_borrowed_head_outcome[package]:
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`,`ee`,`INL v`,`t`,`tn1`] >>
  conj_tac
  >- drule_then ACCEPT_TAC exprSimMemorySourceTheory.read_result_gas_obs >>
  gen_tac >> disch_tac >>
  qpat_assum `ee with gas_obs := [] = ee` SUBST1_TAC >>
  conj_tac
  >- (irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      first_assum ACCEPT_TAC) >>
  BETA_TAC >> qexists `v` >> rewrite_tac[] >>
  rule_assum_tac BETA_RULE >>
  qpat_assum `!H. _ ==> (?p. INL tv = INL p /\ _) /\ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  suspend "endpoint"
QED

Resume create_ctor_borrowed_head_outcome[endpoint]:
  qabbrev_tac `entry = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `expr_body_pre cenv cx env e entry` by simp[Abbr `entry`] >>
  `valid_horizon cx entry H ee.storage_trace` by
    (qpat_assum `eval_expr cx e entry = (INL tv,ee)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame] >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by fs[Abbr `entry`] >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
     `(storage_well_formed_on cx entry (FST H) <=> storage_well_formed_on cx es (FST H))` by
       (irule storage_well_formed_on_backends >> simp[Abbr `entry`]) >>
     fs[valid_horizon_def]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
     simp[Abbr `entry`]) >>
  `~expr_has_effect e ==>
    (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
    (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)` by
    (strip_tac >> drule_all targetPureSourceFrameTheory.effect_free_source_projection >>
     simp[Abbr `entry`]) >>
  `vv_storage_live H cx vv ee t` by
    (`vv_post H ctx func cenv cx e entry sa sb s0 ee tv vv t` by
       simp[Abbr `entry`,exprSimPropsTheory.vv_post_initial_gas] >>
     qpat_assum `expr_body_pre cenv cx env e entry`
       (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
     qpat_assum `expr_body_pre cenv cx env e entry`
       (assume_tac o MATCH_MP exprBodyPreCallSafetyPropsTheory.expr_body_pre_call_evaluation_safe) >>
     `runtime_consistent env cx entry /\ functions_well_typed cx` by
       fs[expr_sim_inv_def,runtime_consistent_def] >>
     irule bodyFullAssignTheory.body_assign_rhs_storage_live >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`cenv`,`ctx`,`e`,`env`,`entry`,`func`,`tv`,`s0`,`sa`,`sb`,`tops`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
  `wb_frame cenv es ee sa s0 t` by
    (rewrite_tac[loweringPostsTheory.wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >>
     qpat_assum `compile_expr _ _ e sa = _`
       (mp_then Any mp_tac exprSimUnwrapTheory.compile_expr_extends) >>
     simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `sv = ext_call_arg_value (lowered_value_type cenv e) vv` by
    fs[compile_snapshot_vv_def, comp_return_def] >>
  `~is_word_type (post_value_type cenv e)` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >> strip_tac >>
     `~is_word_type (expr_type e)` by metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
     drule_all (Q.SPECL [`cenv`,`e`] abiEncodeMaterializeTheory.materialize_post_lowered_classify) >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  qpat_x_assum `!H. _ ==> (?p. INL tv = INL p /\ _) /\ _` kall_tac >>
  qpat_x_assum `!gs pv st tag p. eval_expr _ _ _ = _ /\ _ ==> _` kall_tac >>
  `((?tag op. sv = StackValue tag op) \/
    (?p. sv = LocatedValue (lowered_value_type cenv e) p /\ p.ptr_location = LocMemory) \/
    (?p. sv = LocatedValue (lowered_value_type cenv e) p /\ p.ptr_location <> LocMemory /\
        lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
       vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
       vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
       ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G1 tn1 t /\
       vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t)`
    suffices_by (disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >> suspend "representation") >>
  match_mp_tac (Q.GENL [`env`,`es`,`raw`,`vv`] create_ctor_borrowed_row) >>
  qexistsl [`env`,`entry`,`tv`] >> simp[]
QED

Resume create_ctor_borrowed_head_outcome[representation]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`sv = ext_call_arg_value _ vv`,
     `vv_storage_live H cx vv ee t`,
     `!tag op. vv = StackValue tag op /\ _ ==> ptr_buf_ok cenv e op G1 t`,
     `!tag p. vv = LocatedValue tag p /\ _ ==> ptr_buf_ok cenv e p.ptr_operand G1 t`,
     `~is_word_type (post_value_type cenv e)`,
     `compile_expr cenv (expr_type e) e sa = (vv,sb)`,
     `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ee = (INL v,ee) /\ _`,
     `read_result cx tv ee = (INL v,ee)`,
     `(?tag op. sv = StackValue tag op) \/ _`,
     `~expr_has_effect e ==> _ = _`] >>
  rpt (pop_assum kall_tac) >> ntac 10 disch_tac >>
  Cases_on `vv` >>
  gvs[ext_call_arg_value_def,vv_operand_def,vv_location_def,
      loweringPostsTheory.vv_storage_live_def] >>
  strip_tac >>
  qpat_assum `lowered_value_type cenv e = expr_type e`
    (assume_tac o MATCH_MP (SPEC_ALL loweringPostsTheory.post_value_type_lowered)) >>
  fs[arithmeticTheory.ADD_COMM]
QED

Finalise create_ctor_borrowed_head_outcome

(* The suffix changes the evaluation and machine endpoints, but not the
   compiler cuts of the immediate saved row. *)
Theorem create_ctor_saved_row_suffix:
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  local_ptrs_reserved cenv si /\ local_ptrs_reserved cenv ss /\
  si.cs_next_id <= sm.cs_next_id /\
  (!tag p. sv = LocatedValue tag p ==> tag = lowered_value_type cenv e /\
                                     ~is_word_type (lowered_value_type cenv e)) /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw sv mid t /\
    vv_at cenv cx (lowered_value_type cenv e) si ss mid raw sv t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv mid G1 tn1 t /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) mid raw sv t) /\
  vv_storage_live (H:(bool # bytes32 # type_value) list # num list) cx sv mid t /\
  ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
              | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok cenv e (vv_operand sv) G1 t) /\
  (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
      vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e /\
      eval_operand (vv_operand sv) t = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
      sm.cs_next_id < ss.cs_next_id /\
      (!n b len. local_region cenv mid.scopes t n b len ==>
        regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
  (~copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
    !tr. get_storage cx ee tr = get_storage cx mid tr) /\
  expr_sim_inv cenv cx env mid /\
  stmt_state_rel H ctx func cenv cx mid t /\ stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at D lo d cenv cx ee G2 tn2 u /\ dead_lo_ok H D lo cenv cx /\
  wb_frame cenv mid ee ss t u /\ ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2 /\
  MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
  u.vs_labels = t.vs_labels /\ t.vs_alloca_next <= u.vs_alloca_next ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
    vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
  vv_storage_live H cx sv ee u /\
  ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
              | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok cenv e (vv_operand sv) G2 u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    metis_tac[bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh] >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
       (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!n b len. local_region cenv mid.scopes t n b len <=> local_region cenv ee.scopes u n b len` by
    (irule (INST_TYPE [alpha |-> ``:256``] wordArgsPtrTheory.wb_frame_local_regions) >>
     simp[] >> conj_tac >- (qexistsl [`ee`,`ss`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  qpat_assum `wb_frame _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  namedCases_on `sv` ["tag op", "tag p"]
  >- suspend "stack" >>
  `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by simp[] >>
  qpat_x_assum `tag = _` SUBST_ALL_TAC >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `copy` >- suspend "copied" >> suspend "memory") >>
  `~copy` by (Cases_on `copy` >> fs[vv_location_def]) >>
  `ee.immutables = mid.immutables /\ (!tr. get_storage cx ee tr = get_storage cx mid tr)` by simp[] >>
  Cases_on `?tr. p.ptr_location = slot_loc tr` >- suspend "slot" >>
  Cases_on `p.ptr_location = LocCode` >- suspend "code" >>
  suspend "calldata"
QED

Resume create_ctor_saved_row_suffix[stack]:
  rule_assum_tac (SIMP_RULE (srw_ss()) [vv_operand_def,vv_location_def]) >>
  simp[vv_operand_def] >>
  irule bodyFullExtCallPosTransportTheory.extcall_request_saved_stack_endpoint >>
  simp[] >> qexistsl [`G1`,`func`,`lo`,`mid`,`ss`,`t`,`tn1`] >>
  simp[ci_mono_refl] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `is_word_type (lowered_value_type cenv e)` >> simp[] >>
  `~copy` by fs[] >>
  disj2_tac >> qexistsl [`env`,`H`,`H`,`ctx`] >> simp[]
QED

Resume create_ctor_saved_row_suffix[copied]:
  qpat_assum `T /\ _ ==> ?x w tv. _`
    (drule_then (qx_choosel_then [`x`,`w`,`tv`] (map_every assume_tac o CONJUNCTS)) o
     REWRITE_RULE []) >>
  fs[vv_operand_def, vv_location_def] >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var x) G1 tn1 t /\
   val_in_memory tv v (w2n w) t.vs_memory` by
    gvs[loweringPostsTheory.vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  `w2n w + type_memory_size tv <= t.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >> conj_tac
     >- (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
           (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
     qexists `sm.cs_next_id` >> simp[]) >>
  `lookup_var x t = SOME w` by fs[venomStateTheory.eval_operand_def] >>
  `read_result cx (Value v) ee = (INL v,ee) /\
   vv_holds cenv cx (lowered_value_type cenv e) (Value v) (LocatedValue (lowered_value_type cenv e) p) ee u /\
   vv_at cenv cx (lowered_value_type cenv e) si ss ee (Value v) (LocatedValue (lowered_value_type cenv e) p) u /\
   ptr_vv_ok cx (lowered_value_type cenv e) (Value v) (LocatedValue (lowered_value_type cenv e) p) ee G2 tn2 u /\
   vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee (Value v)
     (LocatedValue (lowered_value_type cenv e) p) u /\ ptr_buf_ok cenv e (Var x) G2 u` by
    (irule bodyFullExtCallPosTransportTheory.extcall_request_materialized_endpoint >>
     simp[vv_operand_def] >> suspend "copied_apply") >>
  simp[vv_operand_def] >> qexists `Value v` >> simp[]
QED

Resume create_ctor_saved_row_suffix[copied_apply]:
  conj_tac >- (qexistsl [`sm`,`ext_call_arg_value (lowered_value_type cenv e) vv`] >> simp[]) >>
  qexistsl [`G1`,`sm.cs_next_id`,`ss`,`lo`,`mid`,`type_memory_size tv`,`t`,`tn1`,`w`] >>
  simp[exprSimPropsTheory.val_footprint_le, arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >>
  qpat_assum `!n b len. local_region cenv ee.scopes u n b len ==> regions_disjoint _ _ _ _`
    (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM]
QED

Resume create_ctor_saved_row_suffix[memory]:
  rule_assum_tac (SIMP_RULE (srw_ss()) [vv_operand_def]) >>
  simp[vv_operand_def] >>
  irule bodyFullExtCallPosTransportTheory.extcall_request_saved_memory_endpoint >>
  simp[] >> qexistsl [`G1`,`func`,`lo`,`mid`,`ss`,`t`,`tn1`] >>
  simp[ci_mono_refl, vv_operand_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`env`,`H`,`H`,`ctx`] >> simp[]
QED

Resume create_ctor_saved_row_suffix[slot]:
  qpat_x_assum `?tr. _` (qx_choose_then `tr` assume_tac) >>
  simp[Excl "vv_storage_live_def"] >>
  irule bodyFullExtCallPosTransportTheory.extcall_request_saved_slot_endpoint >>
  conj_tac >- (qexistsl [`ctx`,`func`] >> simp[]) >>
  qexistsl [`D`,`G1`,`d`,`lo`,`mid`,`ss`,`t`,`tn1`,`tr`] >>
  simp[vv_operand_def, Excl "vv_storage_live_def"] >>
  qpat_assum `?raw. read_result cx raw mid = _ /\ _` (qx_choose_then `raw` strip_assume_tac) >>
  qexists `raw` >> simp[]
QED

Resume create_ctor_saved_row_suffix[code]:
  simp[] >>
  irule (cj 1 bodyFullExtCallPosTransportTheory.extcall_request_saved_code_endpoint) >>
  simp[] >> qexistsl [`G1`,`lo`,`mid`,`ss`,`t`,`tn1`] >> simp[vv_operand_def] >>
  qpat_assum `?raw. read_result cx raw mid = _ /\ _` (qx_choose_then `raw` strip_assume_tac) >>
  qexists `raw` >> simp[]
QED

Resume create_ctor_saved_row_suffix[calldata]:
  `p.ptr_location = LocCalldata` by
    (qpat_x_assum `~(?tr. _)` (mp_tac o CONV_RULE NOT_EXISTS_CONV) >>
     disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >>
     qpat_assum `p.ptr_location <> LocCode` mp_tac >>
     qpat_assum `p.ptr_location <> LocMemory` mp_tac >>
     Cases_on `p.ptr_location` >> simp[NoAsms, loweringPostsTheory.slot_loc_def]) >>
  qpat_x_assum `?raw. read_result cx raw mid = _ /\ _` (qx_choose_then `raw` strip_assume_tac) >>
  qpat_x_assum `vv_holds _ _ _ raw _ mid t`
    (mp_tac o REWRITE_RULE [loweringPostsTheory.vv_holds_def]) >> simp[]
QED

Finalise create_ctor_saved_row_suffix

(* A copying snapshot carries its own allocation witness to the suffix. *)
Theorem create_ctor_materialized_head_outcome:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre cenv cx env e es /\
  ~is_word_type (expr_type e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sh = (vv,shm) /\
  compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
  gas_shadow_state sa sh /\ gas_shadow_state ss shs /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa ss func /\
  fn_has_code sh shs shadow_func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           p.ptr_location = LocMemory /\ ~is_word_type (lowered_value_type cenv e)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\ ptr_buf_ok cenv e (vv_operand sv) G t /\
      (?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
        vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e /\
        eval_operand (vv_operand sv) t = SOME w /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
        FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        sm.cs_next_id < ss.cs_next_id /\
        (!n b len. local_region cenv ee.scopes t n b len ==>
          regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv ss t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
       (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
       (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_expr _ _ e sa = _`
    (mp_then Any mp_tac create_ctor_snapshot_retag) >> simp[] >>
  disch_then (drule_then strip_assume_tac) >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[] >>
  `?op. compile_materialize_vv cenv (lowered_value_type cenv e) vv sm = (op,ss) /\
        compile_materialize_vv cenv (lowered_value_type cenv e) vv shm = (op,shs) /\
        sv = LocatedValue (lowered_value_type cenv e) (mk_ptr op LocMemory)` by
    (Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
     Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv shm` >>
     gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def, mk_ptr_def]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `compile_expr _ _ e sa = _`
      (mp_then Any mp_tac exprSimUnwrapTheory.compile_expr_extends) >> simp[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >> disch_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  irule_at Any bodyFullExtCallDefaultKeywordTheory.extcall_operand_materialized_full >>
  qpat_assum `compile_materialize_vv _ _ _ sm = _` (irule_at Any) >>
  qpat_assum `compile_materialize_vv _ _ _ shm = _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
  asm_simp_tac bool_ss [] >> suspend "post"
QED

Resume create_ctor_materialized_head_outcome[post]:
  qexists_tac `sh` >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qexists_tac `v` >> simp[vv_location_def, vv_operand_def, mk_ptr_def] >>
  conj_tac
  >- (qexists_tac `Value v` >>
      `w2n w + type_memory_size tv <= t.vs_alloca_next` by
        (irule allocaSiteResourceTheory.alloca_site_registered_below >> conj_tac
         >- (qpat_assum `stmt_state_rel H ctx func cenv cx ee t`
               (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
         qexists `sm.cs_next_id` >> simp[]) >>
      `val_in_memory tv v (w2n w) t.vs_memory` by
        (irule bodyPtrBopHashFootprintTheory.ptr_mem_ok_representation >>
                  qexistsl [`G'`,`cx`,`op`,`lowered_value_type cenv e`,`tn'`] >> simp[]) >>
      `eval_operand (Var x) t = SOME w` by metis_tac[] >>
      fs[ptr_val_ok_def] >>
      simp[read_result_def, return_def, loweringPostsTheory.vv_holds_def,
           loweringPostsTheory.vv_at_def, ptr_vv_ok_def, exprSimMemDefsTheory.vv_store_bound_def] >>
      conj_tac
      >- (disj1_tac >> qexistsl [`sm.cs_next_id`,`w2n w`,`type_memory_size tv`] >>
          simp[exprSimPropsTheory.val_footprint_le] >>
          fs[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
      drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  fs[] >>
  qpat_assum `!tail. monad_bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (mp_then Any mp_tac stmtSimDefsTheory.eval_read_preserves_scopes_dom)) >>
  gvs[] >> metis_tac[]
QED

Finalise create_ctor_materialized_head_outcome

(* All constructor heads use the same packet at the immediate-read cut.
   A private allocation is required only when a nonword snapshot copies. *)
Theorem create_ctor_head_outcome[local]:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sh = (vv,shm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
  gas_shadow_state sa sh /\ gas_shadow_state ss shs /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa ss func /\
  fn_has_code sh shs shadow_func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op. sv = StackValue tag op) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
                  | LocatedValue _ p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t) /\
      (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
        ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
          eval_operand (vv_operand sv) t = SOME w /\
          evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
          FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          sm.cs_next_id < ss.cs_next_id /\
          (!n b len. local_region cenv ee.scopes t n b len ==>
             regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv ss t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_ctor_snapshot_retag >> strip_tac >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[] >>
  Cases_on `copy`
  >- suspend "materialized" >>
  suspend "borrowed"
QED

Resume create_ctor_head_outcome[word]:
  `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by fs[] >>
  `compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) =
   compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv)` by
    simp[compile_snapshot_vv_def] >>
  `compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
   compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs)` by
    metis_tac[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
              vyperTypeArgFitsTheory.arg_type_fits_prim_word, membership_element_word_boundary] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  irule_at Any bodyFullExtCallPosWordTheory.extcall_request_snapshot_word_owned_full >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
  qexistsl [`sv`,`shs`,`sh`,`ss`] >>
  gs[comp_bind_def, gas_shadow_expr_type, gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qexists `v` >> fs[loweringPostsTheory.vv_storage_live_def] >>
  qpat_assum `!tail. monad_bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (mp_then Any mp_tac stmtSimDefsTheory.eval_read_preserves_scopes_dom)) >>
  simp[] >> metis_tac[]
QED

Resume create_ctor_head_outcome[materialized]:
  irule gas_outcome_full_post_mono >>
  irule_at Any create_ctor_materialized_head_outcome >>
  qpat_assum `compile_expr _ _ e sa = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ T _ sm = (sv,ss)` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ T _ shm = (sv,shs)` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
  qexists `sh` >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qexists `v` >> simp[] >> Cases_on `sv` >> gvs[]
QED

Resume create_ctor_head_outcome[borrowed]:
  `sm = ss /\ shm = shs` by fs[compile_snapshot_vv_def, comp_return_def] >>
  gvs[] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >> disch_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  irule gas_outcome_full_post_mono >>
  irule_at Any create_ctor_borrowed_head_outcome >>
  qpat_assum `compile_expr _ _ e sa = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr e) sh = _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `vv = LocatedValue tag p` SUBST_ALL_TAC >>
      drule_all_then ACCEPT_TAC bodyFullAssignTheory.body_assign_storage_result_shape) >>
  rpt gen_tac >> disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qexists `v` >> simp[]
QED
Finalise create_ctor_head_outcome

(* Constructor operands are read before evaluating the suffix. Their row
   witnesses refer to the original compiler cuts and the final runtime cut. *)
Theorem create_ctor_rows_outcome[local]:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sb) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\
      LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        (?si sm ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,sm) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              sm.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
          sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
        vv_storage_live H cx sv ee t /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G t) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  map_every qid_spec_tac [`tn0`,`G0`,`s0`,`es`,`shadow_sb`,`shadow_sa`,`sb`,`sa`,`svs`] >>
  Induct_on `xs` >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- suspend "nil" >>
  suspend "cons"
QED

Resume create_ctor_rows_outcome[nil]:
  gvs[compile_create_ctor_args_def,comp_return_def] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  simp[vyperInterpreterTheory.evaluate_def,return_def] >>
  qexistsl [`G0`,`es`,`INL ([]:value list)`,`s0`,`tn0`] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
       wordArgsPtrTheory.ghost_kept_at_refl] >>
  qx_gen_tac `H` >> strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  fs[bodyPtrDefsTheory.ghost_inv_at_def,exprSimWordArgsTheory.wb_frame_refl] >>
  first_assum ACCEPT_TAC
QED

Resume create_ctor_rows_outcome[cons]:
  qmatch_asmsub_rename_tac `body_exprs_full_ok cx (e::xs)` >>
  `body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es` by
    (fs[Once body_exprs_full_ok_def] >> metis_tac[]) >>
  qabbrev_tac `copy = exprs_can_mutate cenv xs` >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ (expr_type e) (gas_shadow_expr e) shadow_sa = (vv',shm)` >>
  `vv' = vv /\ gas_shadow_state sm shm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
     drule_all bodyFullForArrayRoundTheory.nonslot_shadow_cut >> simp[]) >>
  qpat_x_assum `vv' = vv` SUBST_ALL_TAC >>
  qabbrev_tac `snap = compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  Cases_on `snap sm` >> rename1 `snap sm = (sv,ss)` >>
  Cases_on `snap shm` >> rename1 `snap shm = (sv',shs)` >>
  `sv' = sv /\ gas_shadow_state ss shs` by
    (`gas_shadow_compiles snap snap` by
       simp[Abbr `snap`,gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv] >>
     fs[gas_shadow_compiles_def] >> first_x_assum (qspecl_then [`sm`,`shm`] mp_tac) >> simp[]) >>
  qpat_x_assum `sv' = sv` SUBST_ALL_TAC >>
  Cases_on `compile_create_ctor_args compile_expr cenv xs ss` >>
  rename1 `compile_create_ctor_args _ _ xs ss = (tail_svs,sc)` >>
  Cases_on `compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs) shs` >>
  rename1 `compile_create_ctor_args _ _ (MAP gas_shadow_expr xs) shs = (tail_svs',shc)` >>
  `svs = sv::tail_svs /\ sb = sc /\ shadow_sb = shc /\ tail_svs' = tail_svs` by
    (qpat_assum `compile_create_ctor_args _ _ (e::xs) sa = _`
      (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def]) >>
     qpat_assum `compile_create_ctor_args _ _ (MAP _ (e::xs)) shadow_sa = _`
      (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def] o REWRITE_RULE [listTheory.MAP]) >>
     simp[comp_bind_def,comp_return_def,gas_shadow_expr_type,
          gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
          gasShadowCompilePureTheory.gas_shadow_lowered_value_type,
          Abbr `snap`,Abbr `copy`] >> strip_tac >> strip_tac >> gvs[]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`svs = _`,`sb = _`,`shadow_sb = _`,`tail_svs' = _`] >>
  qunabbrev_tac `snap` >>
  `ci_mono sa sm /\ ci_mono shadow_sa shm` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
     qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`]
       mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono sm ss /\ ci_mono shm shs` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >>
     qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`shm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono ss sc /\ ci_mono shs shc` by
    (qspecl_then [`compile_expr`,`cenv`,`xs`,`ss`] mp_tac ci_mono_compile_create_ctor_args >>
     qspecl_then [`compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr xs`,`shs`]
       mp_tac ci_mono_compile_create_ctor_args >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sa ss /\ ci_mono shadow_sa shs` by
    (conj_tac
     >- (irule ci_mono_trans >> qexists_tac `sm` >> asm_rewrite_tac[]) >>
     irule ci_mono_trans >> qexists_tac `shm` >> asm_rewrite_tac[]) >>
  `fn_has_code sa ss func /\ fn_has_code ss sc func` by
    (qspecl_then [`sa`,`ss`,`sc`,`func`] mp_tac fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code shadow_sa shs shadow_func /\ fn_has_code shs shc shadow_func` by
    (qspecl_then [`shadow_sa`,`shs`,`shc`,`shadow_func`] mp_tac fragExecTheory.fn_has_code_split >>
     fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    metis_tac[bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def]) >>
  suspend "head_code"
QED

Resume create_ctor_rows_outcome[head_code]:
  mp_tac (Q.INST [`sh` |-> `shadow_sa`] create_ctor_head_outcome) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "head_outcome") >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rowsQ rowsR` >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t`,`v`] >> gvs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      qpat_assum `gas_exempt_cert T _ _ (ignore_bind _ (return ())) _ _ _ _`
        (MATCH_ACCEPT_TAC o MATCH_MP gasExemptCertTheory.gas_exempt_cert_error_value))
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[cj 6 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return]) >>
  asm_x "head_outcome" assume_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  qexists `headQ` >> reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
      simp[Abbr `headR`,Abbr `rowsR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value list``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> disj1_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qunabbrev_tac `headR` >> qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v. res = INL v /\ _`
    (drule_then (qx_choose_then `v` (SUBST_ALL_TAC o CONJUNCT1))) >>
  qexists `v` >> simp[] >>
  suspend "tail_at_cut"
QED

Resume create_ctor_rows_outcome[tail_at_cut]:
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid`
    by (irule create_operand_const_cells_replay >> rpt (goal_assum (drule_at Any))) >>
  `body_exprs_full_ok cx xs` by
    (qpat_assum `body_exprs_full_ok cx (e::xs)`
       (irule o cj 2 o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL)) >>
     disch_then (qx_choosel_then [`raw`,`read_es`] strip_assume_tac) >>
     rpt (goal_assum (drule_at Any))) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.body_inv_no_phi >>
     qexistsl [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
     rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (irule_at Any) >>
     qexists `fn` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!svs' sa' sb' sh' shb' es' s' g' tn'. _ ==>
      gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (qspecl_then [`tail_svs`,`ss`,`sc`,`shs`,`shc`,`mid`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v'. INL v = INL v' /\ _`
      (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >> simp[])) >>
  disch_tac >>
  suspend "tail_mapped"
QED

Resume create_ctor_rows_outcome[tail_mapped]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ tailQ tailR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)
     (\H res ee G tn u. tailQ H res ee G tn u /\ u.vs_labels = t.vs_labels) tailR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ tailQ tailR` (irule_at Any) >> simp[] >>
     rpt strip_tac >> drule gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ tailQ tailR` kall_tac >>
  `!src. bind (eval_exprs cx xs) (\vs. return (v::vs)) src =
     (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs src)), SND (eval_exprs cx xs src))` by
    (gen_tac >> Cases_on `eval_exprs cx xs src` >>
     rename1 `eval_exprs cx xs src = (rs,ee)` >>
     Cases_on `rs` >> simp[bind_def,return_def,sumTheory.SUM_MAP_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (mp_then (Pos last)
       (mp_tac o BETA_RULE o Q.ISPECL
         [`bind (eval_exprs cx xs) (\vs. return ((v:value)::vs))`,
          `sum$SUM_MAP (CONS (v:value)) (I : exception -> exception)`])
       gasOutcomeFullComposeTheory.gas_outcome_full_source_map) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[sumTheory.SUM_MAP_def])) >>
  disch_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (simp[Abbr `tailR`,sumTheory.SUM_MAP_def,Abbr `rowsR`] >> rpt gen_tac >>
      disch_then (qx_choose_then `orig` (mp_tac o BETA_RULE)) >>
      Cases_on `orig` >>
      simp[sumTheory.SUM_MAP_def,exprSimDefsTheory.expr_exit_INL,
           exprSimDefsTheory.halt_exit_def]) >>
  BETA_TAC >> qx_genl_tac [`H`,`out`,`ee`,`G2`,`tn2`,`u`] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `obs` assume_tac)
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (qx_choose_then `orig` (map_every assume_tac o CONJUNCTS)))))) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _` kall_tac >>
  qunabbrev_tac `tailR` >>
  suspend "tail_endpoint"
QED

Resume create_ctor_rows_outcome[tail_endpoint]:
  `?rs. eval_exprs cx xs (mid with gas_obs := obs) = (rs,ee)` by
    (qpat_assum `!src. bind (eval_exprs cx xs) _ src = _` (fn mapped =>
       qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
         (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL,mapped]))) >>
     simp[] >> Cases_on `eval_exprs cx xs (mid with gas_obs := obs)` >>
     simp[evaluation_state_component_equality]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value list``] valid_horizon_frame) >>
     qexistsl [`eval_exprs cx xs`,`rs`,`ee`] >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl [`bind (eval_expr cx e) (read_result cx)`,`INL v`,`mid with gas_obs := []`] >>
     simp[] >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?v'. INL v = INL v' /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) []))) >>
  qunabbrev_tac `tailQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `?vs. orig = INL vs /\ _`
    (qx_choose_then `vs` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `orig = INL vs` SUBST_ALL_TAC >>
  suspend "rows_frame"
QED

Resume create_ctor_rows_outcome[rows_frame]:
  `sa.cs_next_var <= ss.cs_next_var /\ sa.cs_next_id <= ss.cs_next_id /\
    sa.cs_next_id <= sm.cs_next_id /\ ss.cs_next_var <= sc.cs_next_var /\
    ss.cs_next_id <= sc.cs_next_id /\ sm.cs_next_var <= sc.cs_next_var /\
    sm.cs_next_id <= sc.cs_next_id` by fs[ci_mono_def] >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss t u` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (INST_TYPE [beta |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >> simp[]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] wordArgsPtrTheory.wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss t u` (irule_at Any) >> simp[]) >>
  (* The source frame is used only for the uncopied head's backing. *)
  `~copy ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
     !tr. get_storage cx ee tr = get_storage cx mid tr` by
    (strip_tac >>
     `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs)` by
       (simp[bodyStorageCasesTheory.body_exprs_main_calls_every,EVERY_MEM] >> rpt strip_tac >>
        `expr_body_pre cenv cx env e' mid` by
          (qpat_assum `!e' st. MEM e' (e::xs) /\ _ ==> _`
             (qspecl_then [`e'`,`mid`] mp_tac) >> simp[]) >>
        drule_all_then assume_tac body_inv_expr_pre_calls >>
        qpat_assum `EVERY _ (int_calls_expr e')`
          (drule_then (strip_assume_tac o BETA_RULE) o REWRITE_RULE [EVERY_MEM]) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `~exprs_can_mutate cenv xs` by fs[Abbr `copy`] >>
     drule_all targetPureWalkSourceTheory.nonmutating_exprs_source_frame >>
     simp[vyperMachineFrameTheory.machine_frame_def] >> strip_tac >> gen_tac >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  suspend "rows_head"
QED

Resume create_ctor_rows_outcome[rows_head]:
  `!tag p. sv = LocatedValue tag p ==> tag = lowered_value_type cenv e /\
      ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `(?tag op. sv = StackValue tag op) \/ _` mp_tac >>
     Cases_on `sv` >> dsimp[]) >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e` by
    (drule_all create_ctor_snapshot_retag >> simp[]) >>
  `(?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
      vv_at cenv cx (lowered_value_type cenv e) sa ss ee raw sv u /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
    vv_storage_live H cx sv ee u /\
    ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
                | LocatedValue _ p => p.ptr_location = LocMemory) ==>
      ptr_buf_ok cenv e (vv_operand sv) G2 u)` by
    (mp_tac (Q.INST [`si` |-> `sa`, `D` |-> `DF H`] create_ctor_saved_row_suffix) >>
     impl_tac >- (simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       strip_tac >> first_x_assum drule >> simp[]) >> simp[]) >>
  qpat_assum `wb_frame cenv es ee sa s0 u`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `(!x. vv_operand sv = Var x ==> not_fresh_at sc x) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `ss` >> simp[]) >>
     fs[]) >>
  suspend "rows_pack"
QED

Resume create_ctor_rows_outcome[rows_pack]:
  `(copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
      eval_operand (vv_operand sv) u = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
      sm.cs_next_id < ss.cs_next_id /\
      (!n b sz. local_region cenv ee.scopes u n b sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) b sz))` by
    (strip_tac >>
     qpat_assum `copy /\ _ ==> ?x w tv. _`
       (drule_all_then (qx_choosel_then [`x`,`w`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
     `lookup_var x t = SOME w` by
       (qpat_assum `vv_operand sv = Var x` (fn th =>
          qpat_assum `eval_operand (vv_operand sv) t = SOME w`
            (mp_tac o REWRITE_RULE [th,venomStateTheory.eval_operand_def])) >>
        simp[]) >>
     `lookup_var x u = SOME w` by
       (qpat_assum `!x w. not_fresh_at ss x /\ lookup_var x t = SOME w ==> _`
         (qspecl_then [`x`,`w`] mp_tac) >> simp[]) >>
     `!n b sz. local_region cenv ee.scopes u n b sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) b sz` by
       (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz <=> _`
          (fn eq => qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _`
            (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
     qexistsl [`x`,`w`,`tv`] >> simp[venomStateTheory.eval_operand_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand sv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)` by
    (namedCases_on `sv` ["tag op","tag p"] >> simp[vv_location_def,vv_operand_def] >>
     strip_tac >> `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by simp[] >>
     qpat_x_assum `tag = _` SUBST_ALL_TAC >>
     `~copy` by
       (strip_tac >> qpat_assum `copy /\ _ ==> ?x w tv. _` mp_tac >> simp[vv_location_def]) >>
     `ee.immutables = mid.immutables` by simp[] >>
     `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand p.ptr_operand u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
         val_in_memory rt v (w2n w) mem` suffices_by simp[arithmeticTheory.ADD_COMM] >>
     MATCH_MP_TAC (Q.INST [`H` |-> `H`, `D` |-> `DF H`, `G` |-> `G2`,
                           `entry` |-> `mid`, `env` |-> `env`, `d` |-> `d`,
                           `ctx` |-> `ctx`, `func` |-> `func`, `tops` |-> `tops`]
       (INST_TYPE [alpha |-> ``:256``] bodyFullExtCallPosTransportTheory.extcall_request_saved_ctor_read)) >>
     simp[] >> qexists `raw` >> simp[]) >>
  simp[Abbr `rowsQ`,sumTheory.SUM_MAP_def,listTheory.ZIP] >>
  conj_tac
  >- (qexistsl [`sa`,`sm`,`ss`,`vv`,`raw`,`copy`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `sv = _` (fn th =>
        qpat_assum `_ ==> ptr_buf_ok cenv e (vv_operand sv) G2 u`
          (mp_tac o REWRITE_RULE [th,vv_operand_def])) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `sv = _` (fn th =>
        qpat_assum `_ ==> ptr_buf_ok cenv e (vv_operand sv) G2 u`
          (mp_tac o REWRITE_RULE [th,vv_operand_def])) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==> _`
        (mp_tac o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
      simp[] >> disch_then (qspecl_then [`rt`,`w`] mp_tac) >> simp[]) >>
  suspend "rows_list"
QED

Resume create_ctor_rows_outcome[rows_list]:
  irule listTheory.LIST_REL_mono >>
  qpat_assum `LIST_REL _ (ZIP (xs,tail_svs)) vs` (irule_at Any) >>
  Cases >> simp[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[] >>
  qpat_assum `?si sm ss vv raw copy. compile_expr _ _ _ _ = _ /\ _`
    (qx_choosel_then [`si`,`sm1`,`ss1`,`vv1`,`raw1`,`copy1`]
       (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`si`,`sm1`,`ss1`,`vv1`,`raw1`,`copy1`] >> simp[]
QED

Finalise create_ctor_rows_outcome

(* The continuation starts only after all constructor arguments were read.
   The row relation describes the actual saved values at the common cut. *)
Theorem create_ctor_rows_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sb) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!marks vs ee G tn t.
    (!tail. eval_exprs cx xs (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
            (INL vs,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G,tn)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        (?si sm ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,sm) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              sm.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
          sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
        vv_storage_live H cx sv ee t /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G t) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next vs) (ee,t,G,tn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx xs) next) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac create_ctor_rows_outcome >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rowQ rowR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      qexistsl [`mid`,`t`,`v`] >> gvs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> qexists `rowQ` >> reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ rowQ rowR` (irule_at Any) >>
      simp[Abbr `rowR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value list``]
        stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
  rpt gen_tac >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qunabbrev_tac `rowQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?vs. res = INL vs /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (qx_choose_then `vs` (SUBST_ALL_TAC o cj 1)))) >>
  qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?vs'. INL vs = INL vs' /\ _`
    (assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11,UNWIND_THM1]) >>
  qexists `vs` >> simp[] >>
  first_x_assum irule >> simp[] >> reverse conj_tac
  >- (qexists `marks` >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> LENGTH svs = LENGTH xs /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_assum `MAP FDOM mid.scopes = MAP FDOM es.scopes` (ACCEPT_TAC o SYM),
    qpat_assum `LIST_REL _ (ZIP (xs,svs)) _` mp_tac >>
      simp_tac bool_ss [arithmeticTheory.ADD_COMM]]
QED

(* The two checks are separate: pointer provenance and the permitted
   memory interval both refer to the fetched instruction. *)
Theorem create_checked_step_path[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx func G tn i s /\ mem_safe_step 0 ctx i s /\
  step_inst_base i s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)
Proof
  strip_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G i u,step_taint i s u tn)` by
    (irule bodyFullRawCallCallOriginTheory.non_gas_mem_safe_origin_ptr_edge >> simp[]) >>
  drule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[] >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  metis_tac[venomInstProofsTheory.step_preserves_halted]
QED

Theorem create_dynamic_mstore_path[local]:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\ fn_has_code sa sb func /\
  lookup_var p s = SOME a /\ eval_operand v s = SOME w /\
  ptr_covers G tn p s 32 /\ op_taint tn v = {} /\
  ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n a /\
  w2n a + 32 <= w2n s.vs_fmp /\ allocas_below_fmp s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n a) w s with vs_inst_idx := LENGTH sb.cs_current_insts),G,
     tn with t_mem := tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}))
Proof
  strip_tac >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  simp[] >> rpt gen_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var p;v] []` >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs,exec_write2_def,eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists `0` >> simp[fragExecPtrTheory.ptr_inst_ok_mstore]) >>
  `mem_safe_step 0 ctx i s` by
    simp[Abbr `i`,mk_inst_def,mem_safe_step_non_invoke,inst_mem_below_frontiers_def,
         inst_dload_in_section_def,source_memory_read_ranges_def,source_memory_write_ranges_def,
         fixed_source_write_range_def,eval_operand_def] >>
  `step_prov PG G i u = G /\
   step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}` by
    (drule_all wordLoadStorePtrTheory.mstore_ghost_frame >>
     simp[Abbr `i`,Abbr `u`,taint_component_equality] >>
     simp[step_taint_def,imm_taint_def,mk_inst_def]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode` by
    simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` suffices_by simp[] >>
  irule create_checked_step_path >> simp[] >> qexists `bb` >> simp[]
QED

Theorem create_dynamic_extcodecopy_path[local]:
  emit_void EXTCODECOPY [addr;Var p;off;cnt] sa = ((),sb) /\
  fn_has_code sa sb func /\ eval_operand addr s = SOME a /\
  eval_operand (Var p) s = SOME b /\ eval_operand off s = SOME k /\
  eval_operand cnt s = SOME n /\ op_taint tn addr = {} /\
  op_taint tn off = {} /\ op_taint tn cnt = {} /\ ptr_covers G tn p s (w2n n) /\
  ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n b /\
  w2n b + w2n n <= w2n s.vs_fmp /\ allocas_below_fmp s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (write_memory_with_expansion (w2n b) (TAKE (w2n n) (DROP (w2n k) (lookup_account (w2w a) s.vs_accounts).code ++ REPLICATE (w2n n) 0w)) s with vs_inst_idx := LENGTH sb.cs_current_insts),G,
     tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}))
Proof
  strip_tac >> simp[] >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  simp[] >> rpt gen_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id EXTCODECOPY [addr;Var p;off;cnt] []` >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n b) bytes s` >>
  qabbrev_tac `u = write_memory_with_expansion (w2n b) bytes s` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`, Abbr `bytes`] >>
     irule bodyPtrBytestringBuiltinsExternalSliceTheory.external_copy_step >> simp[] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists `0` >> simp[] >>
     irule bodyPtrBytestringBuiltinsExternalSliceTheory.ptr_inst_ok_external_copy >>
     simp[] >> qexistsl [`k`,`n`] >> simp[] >> metis_tac[]) >>
  `source_memory_write_ranges i s = [(w2n b,w2n n)] /\ source_memory_read_ranges i s = []` by
    simp[Abbr `i`,mk_inst_def,source_memory_read_ranges_def,source_memory_write_ranges_def,
         sized_source_write_range_def] >>
  `i.inst_opcode = EXTCODECOPY` by simp[Abbr `i`,mk_inst_def] >>
  `mem_safe_step 0 ctx i s` by
    simp[mem_safe_step_non_invoke,inst_mem_below_frontiers_def,inst_dload_in_section_def] >>
  `step_prov PG G i u = G /\
   step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}` by
    (simp[Abbr `i`,taint_component_equality,
          bodyPtrBytestringBuiltinsExternalSliceTheory.external_copy_ghost_frame] >>
     `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
       simp[Abbr `u`,write_memory_with_expansion_def] >>
     qabbrev_tac `cpy = mk_inst sa.cs_next_id EXTCODECOPY [addr;Var p;off;cnt] []` >>
     `(step_taint cpy s u tn).t_mem = tn.t_mem DIFF range_bytes (source_memory_write_ranges cpy s)` suffices_by
       simp[markerTheory.Abbrev_def,range_bytes_def,sized_source_write_range_def,
            source_memory_write_ranges_def,mk_inst_def] >>
     simp[Abbr `cpy`, IgnAsm `source_memory_write_ranges _ _ = _`] >>
     irule bodyPtrBytestringBuiltinsExternalSliceTheory.external_copy_ghost_memory >> simp[]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode` by
    simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` suffices_by simp[Abbr `u`] >>
  irule create_checked_step_path >> simp[] >> qexists `bb` >> simp[]
QED

(* Reuse the arithmetic edge at the actual next compiler cursor. *)
Theorem create_literal_add_path[local]:
  emit_op ADD [left;Lit off] sa = (dst,sb) /\ fn_has_code sa sb func /\
  eval_operand left s = SOME w /\ op_taint tn left = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'. dst = Var out /\
    t = (update_var out (w + off) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand dst t = SOME (w + off) /\
    FLOOKUP G' out = op_prov G left /\ op_taint tn' dst = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [left;Lit off] [tmp]` >>
  qabbrev_tac `u = update_var tmp (w + off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `gadd = step_prov PG G i u` >>
  qabbrev_tac `tadd = step_taint i s u tn` >>
  qexistsl [`tmp`,`t`,`gadd`,`tadd`] >>
  `dst = Var tmp /\
   (!D lo explicit. allocas_from lo s ==>
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,gadd,tadd)) /\
   FLOOKUP gadd tmp = op_prov G left /\ op_taint tadd dst = {} /\
   tadd.t_mem = tn.t_mem /\ tadd.t_stor = tn.t_stor /\
   tadd.t_trans = tn.t_trans /\ tadd.t_imm = tn.t_imm /\
   (!p. p <> tmp ==> FLOOKUP gadd p = FLOOKUP G p /\ op_taint tadd (Var p) = op_taint tn (Var p))` by
    (unabbrev_all_tac >> irule bodyFullAttributeAddTheory.attribute_add_full_frame >>
     simp[] >> metis_tac[]) >>
  simp[Abbr `t`,Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem create_copy_preamble_bytes[local]:
  (w:bytes32) <+ 0x1000000w ==>
  DROP 21 (word_to_bytes (0x620000003d81600b3d39f3w || (w << 56)) T) =
  [0x62w] ++ DROP 29 (word_to_bytes_be w) ++
  [0x3dw;0x81w;0x60w;0x0bw;0x3dw;0x39w;0xf3w]
Proof
  disch_tac >>
  rewrite_tac[byteTheory.word_to_bytes_be_def, byteTheory.word_to_bytes_def,
              fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  CONV_TAC (LHS_CONV (SIMP_CONV (srw_ss()) [byteTheory.word_to_bytes_aux_compute])) >>
  CONV_TAC (RHS_CONV (SIMP_CONV (srw_ss()) [byteTheory.word_to_bytes_aux_compute])) >>
  simp[NoAsms,byteTheory.get_byte_def, byteTheory.byte_index_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> pop_assum mp_tac >> BBLAST_TAC
QED

Theorem create_copy_initcode_stores[local]:
  LENGTH code <= 24576 ==>
  read_memory (b + 21) (11 + LENGTH code)
    (write_memory_with_expansion (b + 32) code
      (mstore b (0x620000003d81600b3d39f3w || (n2w (LENGTH code) << 56)) s)) =
  create_copy_initcode code
Proof
  strip_tac >>
  `((n2w (LENGTH code)):bytes32) <+ 0x1000000w` by
    (simp[wordsTheory.word_lo_n2w] >> decide_tac) >>
  drule_then assume_tac create_copy_preamble_bytes >>
  qmatch_goalsub_abbrev_tac `mstore b pre s` >>
  `read_memory (b + 21) 11 (mstore b pre s) = DROP 21 (word_to_bytes pre T)` by
    (mp_tac (Q.SPECL [`b`,`32`,`21`,`11`,`mstore b pre s`] read_memory_subwindow) >>
     simp[read_memory_eq_mem_bytes_at, valueEncodingPropsTheory.mem_bytes_at_mstore_same,
          listTheory.TAKE_LENGTH_TOO_LONG, LENGTH_DROP]) >>
  simp[Once read_memory_split, read_memory_write_disjoint, read_memory_write_self] >>
  rewrite_tac[create_copy_initcode_def, APPEND_ASSOC, APPEND]
QED

Theorem create_copy_written_path:
  emit_void MSTORE [Var p;pre] a6 = ((),a7) /\
  emit_op ADD [Var p;Lit 32w] a7 = (dst,a8) /\
  emit_void EXTCODECOPY [target;dst;Lit 0w;sz] a8 = ((),a9) /\
  emit_op ADD [Var p;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [sz;Lit 11w] a10 = (len,sc) /\
  fn_has_code a6 a7 func /\ fn_has_code a7 a8 func /\ fn_has_code a8 a9 func /\
  fn_has_code a9 a10 func /\ fn_has_code a10 sc func /\
  (!x. MEM (Var x) [Var p;target;sz] ==> not_fresh_at a6 x) /\
  0 < n /\ n = LENGTH code /\ n <= 24576 /\
  eval_operand target s = SOME aw /\ (lookup_account (w2w aw) s.vs_accounts).code = code /\
  eval_operand sz s = SOME (n2w n) /\
  eval_operand pre s = SOME (0x620000003d81600b3d39f3w || (n2w n << 56)) /\
  op_taint tn target = {} /\ op_taint tn sz = {} /\ op_taint tn pre = {} /\
  lookup_var p s = SOME (n2w B) /\ op_taint tn (Var p) = {} /\
  FLOOKUP G p = SOME (B,venomLayout$ceil32 (n+32)) /\
  ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= B /\
  B + venomLayout$ceil32 (n+32) = w2n s.vs_fmp /\
  allocas_below_fmp s /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = a6.cs_current_bb /\ s.vs_inst_idx = LENGTH a6.cs_current_insts ==>
  ?q t Gt tt.
    buf = Var q /\ eval_operand buf t = SOME (n2w (B+21)) /\
    eval_operand len t = SOME (n2w (n+11)) /\
    op_taint tt buf = {} /\ op_taint tt len = {} /\ ptr_covers Gt tt q t (n+11) /\
    read_memory (B+21) (n+11) t = create_copy_initcode code /\
    tt.t_mem = tn.t_mem DIFF {j | B <= j /\ j < B+32+n} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    t.vs_memory = (write_memory_with_expansion (B+32) code
      (mstore B (0x620000003d81600b3d39f3w || (n2w n << 56)) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_memory := s.vs_memory|>) = s /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (!x. not_fresh_at a6 x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt))
Proof
  strip_tac >>
  `n+32 <= venomLayout$ceil32 (n+32)` by simp[venomLayoutTheory.ceil32_ge] >>
  `B+n+32 <= w2n s.vs_fmp` by decide_tac >>
  `B+n+32 < dimword(:256)` by
    (qspec_then `s.vs_fmp` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  `w2n (n2w B:bytes32) = B /\ w2n (n2w (B+32):bytes32) = B+32 /\
   w2n (n2w (B+21):bytes32) = B+21 /\ w2n (n2w n:bytes32) = n` by
     (rpt conj_tac >> simp[wordsTheory.w2n_n2w] >>
      fs[wordsTheory.dimword_def] >> decide_tac) >>
  `ptr_covers G tn p s 32` by (simp[ptr_covers_def, IgnAsm `n = LENGTH code`] >> decide_tac) >>
  `w2n s.vs_initial_fmp <= w2n (n2w B:bytes32) /\
   w2n (n2w B:bytes32) + 32 <= w2n s.vs_fmp` by (simp[] >> decide_tac) >>
  drule_all create_dynamic_mstore_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK sm` >>
  qmatch_asmsub_abbrev_tac `tn with t_mem := tmemory` >>
  qabbrev_tac `tm = tn with t_mem := tmemory` >>
  `~sm.vs_halted /\ sm.vs_current_bb = a7.cs_current_bb /\
   sm.vs_inst_idx = LENGTH a7.cs_current_insts /\ allocas_from lo sm /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp sm) /\
   eval_operand (Var p) sm = SOME (n2w B) /\ op_taint tm (Var p) = {}` by
    (simp[Abbr `sm`,Abbr `tm`,mstore_def,allocas_from_def,allocas_below_fmp_def,
          eval_operand_def,lookup_var_def,op_taint_def] >>
     fs[allocas_from_def,allocas_below_fmp_def,op_taint_def,lookup_var_def] >>
     metis_tac[]) >>
  drule_all (Q.INST [`off` |-> `32w`] create_literal_add_path) >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `pd` (qx_choose_then `sd`
    (qx_choose_then `Gd` (qx_choose_then `td` strip_assume_tac))))) >>
  suspend "copy"
QED

Resume create_copy_written_path[copy]:
  `a6.cs_next_var <= a7.cs_next_var /\ a6.cs_next_var <= a9.cs_next_var /\
   a6.cs_next_var <= a10.cs_next_var` by
    (imp_res_tac (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >>
     imp_res_tac (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >> decide_tac) >>
  `!x. not_fresh_at a6 x ==>
    lookup_var x sd = lookup_var x s /\ FLOOKUP Gd x = FLOOKUP G x /\
    op_taint td (Var x) = op_taint tn (Var x)` by
     (gen_tac >> disch_tac >>
      `x <> pd` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
      qpat_assum `!p. p <> pd ==> _` drule >>
      simp[Abbr `sm`,Abbr `tm`,mstore_def,lookup_var_def,op_taint_def]) >>
  `!v. MEM v [Var p;target;sz] ==>
       eval_operand v sd = eval_operand v s /\ op_taint td v = op_taint tn v` by
     (Cases >- simp[eval_operand_def,op_taint_def]
      >- (simp[IgnAsm `sd = _`,eval_operand_def] >> metis_tac[]) >>
      simp[Abbr `sm`,mstore_def,update_var_def,op_taint_def,eval_operand_def]) >>
  `~sd.vs_halted /\ sd.vs_inst_idx = LENGTH a8.cs_current_insts /\
   sd.vs_accounts = s.vs_accounts /\ allocas_from lo sd /\ allocas_below_fmp sd /\
   w2n sd.vs_initial_fmp <= w2n (n2w (B+32):bytes32) /\
   w2n (n2w (B+32):bytes32) + w2n (n2w n:bytes32) <= w2n sd.vs_fmp` by
     (simp[Abbr `sm`,update_var_def,mstore_def] >>
      fs[allocas_from_def,allocas_below_fmp_def] >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> decide_tac) >>
  qpat_x_assum `dst = Var pd` SUBST_ALL_TAC >>
  `eval_operand (Var pd) sd = SOME (n2w (B+32)) /\
   eval_operand target sd = SOME aw /\ eval_operand sz sd = SOME (n2w n) /\
   op_taint td target = {} /\ op_taint td sz = {} /\
   eval_operand (Lit 0w) sd = SOME 0w /\ op_taint td (Lit 0w) = {}` by
     (simp[IgnAsm `sd = _`,wordsTheory.word_add_n2w] >>
      rpt conj_tac >> TRY (simp[eval_operand_def,op_taint_def]) >> metis_tac[MEM]) >>
  `ptr_covers Gd td pd sd (w2n (n2w n:bytes32))` by
    (simp[IgnAsm `sd = _`,IgnAsm `n = LENGTH code`,ptr_covers_def,op_prov_def,
          GSYM eval_operand_def] >> decide_tac) >>
  drule_all create_dynamic_extcodecopy_path >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[IgnAsm `sd = _`,TAKE_APPEND1, TAKE_LENGTH_ID] >> strip_tac >>
  qabbrev_tac `sx = write_memory_with_expansion (B+32) code sd with
                    vs_inst_idx := LENGTH a9.cs_current_insts` >>
  qabbrev_tac `tx = td with t_mem := tm.t_mem DIFF {j | B+32 <= j /\ j < B+(LENGTH code+32)}` >>
  suspend "results"
QED

Resume create_copy_written_path[results]:
  `sx.vs_allocas = sd.vs_allocas /\ sx.vs_fmp = sd.vs_fmp /\
   sx.vs_initial_fmp = sd.vs_initial_fmp /\ ~sx.vs_halted /\
   sx.vs_inst_idx = LENGTH a9.cs_current_insts /\ sx.vs_current_bb = a9.cs_current_bb /\
   eval_operand (Var p) sx = eval_operand (Var p) sd /\
   op_taint tx (Var p) = op_taint td (Var p)` by
    (qpat_x_assum `Abbrev (sx = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     qpat_x_assum `Abbrev (tx = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     simp[NoAsms,write_memory_with_expansion_def,eval_operand_def,lookup_var_def,op_taint_def] >>
     simp[]) >>
  `allocas_from lo sx /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sx)` by
    metis_tac[allocas_from_def,allocas_below_fmp_def] >>
  `eval_operand (Var p) sx = SOME (n2w B) /\ op_taint tx (Var p) = {}` by
    (qpat_assum `!v. MEM v _ ==> _` (qspec_then `Var p` mp_tac) >>
     simp[IgnAsm `sd = _`,eval_operand_def]) >>
  drule_all (Q.INST [`off` |-> `21w`] create_literal_add_path) >>
  disch_then (qspecl_then [`PG`,`Gd`] (qx_choose_then `qb` (qx_choose_then `su`
    (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))))) >>
  `!x. not_fresh_at a6 x ==>
    lookup_var x su = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> qb` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!p. p <> qb ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at a6 x ==> lookup_var x sd = _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[Abbr `sx`,Abbr `tx`,IgnAsm `sd = _`,IgnAsm `su = _`,
        write_memory_with_expansion_def,lookup_var_def,op_taint_def]) >>
  `~su.vs_halted /\ su.vs_inst_idx = LENGTH a10.cs_current_insts /\
   allocas_from lo su /\ (ctx_has_dalloca ctx ==> allocas_below_fmp su)` by
    (simp[update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     fs[allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  `eval_operand sz su = SOME (n2w n) /\ op_taint tu sz = {}` by
    (Cases_on `sz`
     >- fs[eval_operand_def,op_taint_def]
     >- (rename1 `eval_operand (Var k) s = SOME (n2w n)` >>
         `not_fresh_at a6 k` by
           (qpat_assum `!x. MEM (Var x) [Var p;target;Var k] ==> not_fresh_at a6 x`
              (qspec_then `k` mp_tac) >> simp[NoAsms,MEM]) >>
         qpat_assum `!x. not_fresh_at a6 x ==> lookup_var x su = _ /\ _`
           (drule_then strip_assume_tac) >>
         qpat_assum `eval_operand (Var k) s = SOME (n2w n)` (fn sz =>
           qpat_assum `lookup_var k su = lookup_var k s` (fn value =>
             qpat_assum `op_taint tu (Var k) = op_taint tn (Var k)` (fn taint =>
               qpat_assum `op_taint tn (Var k) = {}` (fn clean =>
                 simp[NoAsms,eval_operand_def,value,taint,clean,
                      REWRITE_RULE [eval_operand_def] sz]))))) >>
     `su.vs_labels = sx.vs_labels` by simp[update_var_def] >>
     `sx.vs_labels = sd.vs_labels` by
       simp[Abbr `sx`,IgnAsm `sd = _`,write_memory_with_expansion_def] >>
     `sd.vs_labels = sm.vs_labels` by simp[update_var_def] >>
     `sm.vs_labels = s.vs_labels` by simp[Abbr `sm`,mstore_def] >>
     qpat_assum `eval_operand (Label _) s = SOME _` mp_tac >>
     simp[NoAsms,eval_operand_def,op_taint_def] >>
     simp[IgnAsm `su = _`]) >>
  drule_all (Q.INST [`off` |-> `11w`] create_literal_add_path) >>
  disch_then (qspecl_then [`PG`,`Gu`] (qx_choose_then `ql` (qx_choose_then `sf`
    (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))))) >>
  suspend "pack"
QED

Resume create_copy_written_path[pack]:
  `qb <> ql` by
    (qpat_assum `emit_op ADD [Var p;Lit 21w] a9 = _`
       (mp_then Any mp_tac typedMemoryCopyTheory.typed_copy_emit_op_fresh) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `buf = Var qb` SUBST_ALL_TAC >>
  `eval_operand (Var qb) sf = SOME (n2w (B+21)) /\ op_taint tf (Var qb) = {} /\
   ptr_covers Gf tf qb sf (LENGTH code+11)` by
    (`not_fresh_at a6 p` by simp[] >>
     qpat_assum `!x. not_fresh_at a6 x ==> lookup_var x sd = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!p. p <> ql ==> _` (qspec_then `qb` mp_tac) >>
     qpat_assum `eval_operand (Var qb) su = SOME _`
       (assume_tac o REWRITE_RULE[eval_operand_def]) >>
     simp[IgnAsm `sf = _`,IgnAsm `su = _`,op_prov_def,ptr_covers_def,
          eval_operand_def,wordsTheory.word_add_n2w,venomLayoutTheory.ceil32_ge]) >>
  `sf.vs_memory = sx.vs_memory` by simp[update_var_def] >>
  `sd.vs_memory = (mstore B (0x620000003d81600b3d39f3w || (n2w n << 56)) s).vs_memory` by
    simp[Abbr `sm`,update_var_def] >>
  `sf.vs_memory = (write_memory_with_expansion (B+32) code
    (mstore B (0x620000003d81600b3d39f3w || (n2w n << 56)) s)).vs_memory` by
    (simp[IgnAsm `sf = _`, Abbr `sx`, IgnAsm `sd = _`] >>
     drule exprSimCalldataSliceTheory.write_memory_with_expansion_equal_memory >>
     disch_then (qspecl_then [`B+32`,`code`] (simp o single))) >>
  suspend "frame"
QED

Resume create_copy_written_path[frame]:
  qabbrev_tac `reset = \a. a with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars;
                                      vs_inst_idx := s.vs_inst_idx|>` >>
  `reset sf = reset su /\ reset su = reset sx` by
    (conj_tac
     >- simp[Abbr `reset`,IgnAsm `su = _`,update_var_def] >>
     simp[Abbr `reset`,update_var_def]) >>
  `reset sx = reset sd` by simp[Abbr `sx`,Abbr `reset`,IgnAsm `sd = _`,write_memory_with_expansion_def] >>
  `reset sd = reset sm /\ reset sm = s` by
    (conj_tac >- simp[Abbr `reset`,update_var_def] >>
     simp[Abbr `reset`,Abbr `sm`,mstore_def,IgnAsm `s.vs_inst_idx = _`]) >>
  `tf.t_mem = tn.t_mem DIFF {j | B <= j /\ j < B+(LENGTH code+32)}` by
    (simp[Abbr `tx`,Abbr `tm`,Abbr `tmemory`,pred_setTheory.EXTENSION] >>
     qx_gen_tac `j` >> Cases_on `j IN tn.t_mem` >> simp[] >> decide_tac) >>
  `!x. not_fresh_at a6 x ==> lookup_var x sf = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> ql` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!p. p <> ql ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at a6 x ==> lookup_var x su = _ /\ _` (qspec_then `x` mp_tac) >>
     simp[IgnAsm `sf = _`,IgnAsm `su = _`] >> metis_tac[]) >>
  `reset sf = s` by
    (qpat_assum `reset sf = reset su` (once_rewrite_tac o single) >>
     qpat_assum `reset su = reset sx` (once_rewrite_tac o single) >>
     qpat_assum `reset sx = reset sd` (once_rewrite_tac o single) >>
     qpat_assum `reset sd = reset sm` (once_rewrite_tac o single) >>
     simp[IgnAsm `sf = _`]) >>
  `read_memory (B+21) (LENGTH code+11) sf = create_copy_initcode code` by
    (mp_tac (Q.INST [`b` |-> `B`] create_copy_initcode_stores) >>
     simp[read_memory_def,IgnAsm `sf = _`,IgnAsm `sf.vs_memory = sx.vs_memory`,
          arithmeticTheory.ADD_COMM] >>
     metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tf)` by
    (rpt gen_tac >>
     map_every (fn q => qpat_assum q (qspecl_then [`D`,`explicit`] mp_tac))
       [`!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`,
        `!D explicit. gas_origin_ptr_path _ (sm,G,tm) [] _`,
        `!D explicit. gas_origin_ptr_path _ (sd,Gd,td) [] _`,
        `!D explicit. gas_origin_ptr_path _ (sx,Gd,tx) [] _`,
        `!D explicit. gas_origin_ptr_path _ (su,Gu,tu) [] _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `sf with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    (qpat_assum `reset sf = s` mp_tac >> simp[Abbr `reset`,NoAsms]) >>
  `~sf.vs_halted /\ sf.vs_inst_idx = LENGTH sc.cs_current_insts` by
    simp[update_var_def,IgnAsm `su = _`] >>
  qexistsl [`qb`,`sf`,`Gf`,`tf`] >>
  simp[IgnAsm `sf = _`,IgnAsm `su = _`,IgnAsm `sf.vs_memory = sx.vs_memory`,
       wordsTheory.word_add_n2w,IgnAsm `len = _`,Abbr `tx`,Abbr `tm`] >>
  qpat_assum `s.vs_inst_idx = LENGTH a6.cs_current_insts` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Finalise create_copy_written_path

(* The post-guard arithmetic uses only the clean size and literals. *)
Theorem create_copy_prealloc_scalars[local]:
  emit_op SHL [Lit 56w;Var p] a2 = (shift,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shift] a3 = (pre,a4) /\
  emit_op ADD [Var p;Lit 32w] a4 = (req,a5) /\
  not_fresh_at a2 p /\ lookup_var p s = SOME w ==>
  ?t. run_inst_seq (emitted_insts a2 a5) s = OK t /\
    eval_operand (Var p) t = SOME w /\
    eval_operand pre t = SOME (0x620000003d81600b3d39f3w || (w << 56)) /\
    eval_operand req t = SOME (w+32w) /\
    a5.cs_current_insts = a2.cs_current_insts ++ emitted_insts a2 a5 /\
    bodyPtrBopScalarSeq$bop_scalar_seq {x | not_fresh_at a2 x}
      {Var p;Lit 56w;Lit 0x620000003d81600b3d39f3w;Lit 32w}
      (emitted_insts a2 a5)
      {req;pre;shift;Var p;Lit 56w;Lit 0x620000003d81600b3d39f3w;Lit 32w}
Proof
  strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  `!x. not_fresh_at a2 x ==>
    x <> STRING #"%" (toString a2.cs_next_var) /\
    x <> STRING #"%" (toString a3.cs_next_var) /\
    x <> STRING #"%" (toString a4.cs_next_var)` by
    (rpt strip_tac >> imp_res_tac stmtFragPtrTheory.not_fresh_at_mono >>
     fs[not_fresh_at_def]) >>
  `emitted_insts a2 a5 = emitted_insts a2 a3 ++ emitted_insts a3 a4 ++ emitted_insts a4 a5` by
    (rewrite_tac[emitted_insts_def] >>
     qpat_assum `a5.cs_current_insts = _` (once_rewrite_tac o single) >>
     qpat_assum `a4.cs_current_insts = _` (once_rewrite_tac o single) >>
     qpat_assum `a3.cs_current_insts = _` (once_rewrite_tac o single) >>
     simp[listTheory.DROP_APPEND2]) >>
  qpat_assum `a3.cs_next_var = _` (fn th3 =>
    qpat_assum `a4.cs_next_var = _` (fn th4 =>
      qpat_assum `!x. not_fresh_at a2 x ==> _`
        (drule_then (strip_assume_tac o SRULE [th3,th4,GSYM arithmeticTheory.ADD_ASSOC])))) >>
  simp[run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure2_def,bind_outputs_def,
       eval_operand_def,emitHelperPropsTheory.lookup_var_update_var,mk_inst_def,
       emitHelperPropsTheory.fresh_var_distinct,
       bodyPtrBopScalarSeqTheory.bop_scalar_seq_def,not_fresh_at_def]
QED

(* Empty marks exclude GAS events, so the flag is immaterial. *)
Theorem create_copy_prealloc_path:
  emit_op EXTCODESIZE [target] sa = (sz,a1) /\
  emit_void ASSERT [sz] a1 = ((),a2) /\
  emit_op SHL [Lit 56w;sz] a2 = (shift,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shift] a3 = (pre,a4) /\
  emit_op ADD [sz;Lit 32w] a4 = (req,a5) /\
  fn_has_code sa a2 func /\ fn_has_code a2 a5 func /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (lookup_account (w2w aw) s.vs_accounts).code = code /\ LENGTH code <= 24576 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  if code = [] then
    ?p. sz = Var p /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort (revert_state (set_returndata []
            (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))),
         G \\ p, tn with t_var := tn.t_var |+ (p,{}))
  else
    ?t Gt tt.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt)) /\
      eval_operand sz t = SOME (n2w (LENGTH code)) /\
      eval_operand pre t = SOME (0x620000003d81600b3d39f3w || (n2w (LENGTH code) << 56)) /\
      eval_operand req t = SOME (n2w (LENGTH code + 32)) /\
      op_taint tt sz = {} /\ op_taint tt pre = {} /\ op_taint tt req = {} /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      ~t.vs_halted /\ t.vs_current_bb = a5.cs_current_bb /\
      t.vs_inst_idx = LENGTH a5.cs_current_insts /\
      tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `compile_extcodesize_check target sa = ((),a2)` by
    simp[compile_extcodesize_check_def,comp_bind_def] >>
  `sz = Var (STRING #"%" (toString sa.cs_next_var))` by
    metis_tac[cj 2 emitHelperPropsTheory.emitted_insts_emit_op] >>
  drule_all bodyFullExtCallPrecheckTheory.extcall_codesize_checked_path >>
  `w2n (n2w (LENGTH code):bytes32) = LENGTH code` by
    (simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >> decide_tac) >>
  `((n2w (LENGTH code):bytes32) = 0w) <=> code = []` by
    (eq_tac >> strip_tac >> fs[]) >>
  Cases_on `code = []` >> simp[] >> strip_tac >>
  TRY (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `sz = _` SUBST_ALL_TAC >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = n2w (LENGTH code):bytes32` >>
  qabbrev_tac `u = update_var p w s with vs_inst_idx := LENGTH a2.cs_current_insts` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (p,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G \\ p,tm)` by
    (simp[Abbr `u`,Abbr `tm`] >> metis_tac[]) >>
  `a2.cs_current_bb = sa.cs_current_bb /\ a5.cs_current_bb = a2.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[same_blocks_def]) >>
  `sa.cs_next_var < a2.cs_next_var` by
    (imp_res_tac (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >>
     imp_res_tac (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >> decide_tac) >>
  `not_fresh_at a2 p` by simp[Abbr `p`,not_fresh_at_def] >>
  `lookup_var p u = SOME w /\ ~u.vs_halted /\ u.vs_current_bb = a2.cs_current_bb /\
   u.vs_inst_idx = LENGTH a2.cs_current_insts /\ allocas_from lo u /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (simp[Abbr `u`,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,
          update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     fs[allocas_from_def,allocas_below_fmp_def]) >>
  drule_all create_copy_prealloc_scalars >> strip_tac >>
  `!op. op IN {Var p;Lit 56w;Lit 0x620000003d81600b3d39f3w;Lit 32w} ==>
    op_prov (G \\ p) op = NONE /\ op_taint tm op = {}` by
    (simp[DISJ_IMP_THM,FORALL_AND_THM] >>
     simp[Abbr `tm`,op_taint_def,op_prov_def,finite_mapTheory.FLOOKUP_UPDATE,
          GSYM finite_mapTheory.fmap_domsub,finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts a2 a5) (DROP u.vs_inst_idx bb.bb_instructions)` by
    simp[IgnAsm `a2.cs_current_bb = sa.cs_current_bb`] >>
  drule_all bodyFullBopWordSuccessTheory.bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`{}`,`PG`] (qx_choosel_then [`H`,`tf`] strip_assume_tac)) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH a5.cs_current_insts` >>
  qexistsl_tac [`v`,`H`,`tf`] >> conj_tac
  >- (rpt gen_tac >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`G \\ p`,`u`,`tm`] >> conj_tac >- simp[] >>
      irule abiDecodeValidFiniteLoopTheory.finite_array_empty_path_explicit >> qexists `{}` >>
      `LENGTH a5.cs_current_insts = u.vs_inst_idx + LENGTH (emitted_insts a2 a5)` by simp[] >>
      metis_tac[Abbr `v`]) >>
  `op_taint tf (Var p) = {} /\ op_taint tf pre = {} /\ op_taint tf req = {}` by
    (qpat_assum `!op. op IN {req;pre;shift;Var p;Lit _;Lit _;Lit _} ==> _` mp_tac >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  simp[Abbr `v`,Abbr `tm`,exprSimHashTheory.hash_eval_operand_inst_idx,
       wordsTheory.word_add_n2w] >>
  simp[Abbr `w`,wordsTheory.word_add_n2w] >>
  ntac 3 (conj_tac >-
    (qpat_assum `t = u with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[Abbr `u`,update_var_def,venom_state_component_equality])) >>
  qx_gen_tac `x` >> strip_tac >>
  `x <> p` by
    (qpat_assum `not_fresh_at sa x`
       (qspec_then `sa.cs_next_var` mp_tac o REWRITE_RULE[not_fresh_at_def]) >>
     simp[Abbr `p`]) >>
  `not_fresh_at a2 x` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  qpat_assum `!x. x IN _ ==> FLOOKUP H x = _ /\ _` (qspec_then `x` mp_tac) >>
  qpat_assum `!x. x IN _ ==> FLOOKUP t.vs_vars x = _` (qspec_then `x` mp_tac) >>
  simp[Abbr `u`,lookup_var_def,update_var_def,op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED

Theorem create_dalloca_cut_bound[local]:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i u. frag_reachable ctx func s0 fn i u ==> dalloca_fmp_headroom i u) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = DALLOCA /\
  venomLayout$ceil32 n <= 2 ** 255 + 2 ** 64 ==>
  w2n s.vs_fmp + venomLayout$ceil32 n < dimword (:256)
Proof
  strip_tac >>
  `!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  `frag_reachable ctx func s func inst s` by
    (irule contextRawReachableTheory.frag_reachable_start >>
     drule_all contextCodegenRelPropsTheory.lookup_instruction_active >> simp[]) >>
  `dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK s,G,tn)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
         bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (qspecl_then [`func`,`inst`,`s`] mp_tac) >> simp[] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `dalloca_fmp_headroom inst s` mp_tac >>
  qpat_x_assum `venomLayout$ceil32 n <= _` mp_tac >>
  simp[dalloca_fmp_headroom_def,arithmeticTheory.MAX_DEF] >>
  rw[] >> decide_tac
QED

(* The dispatch buffer, including its ghost, is chosen before any horizon
   or explicit-site quantifier. The zero-code branch stops at ASSERT. *)
Theorem create_copy_prepared_path:
  compile_create_copy target amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG)
    (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==>
            dalloca_fmp_headroom i v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
    ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!x. target = Var x \/ amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code ==>
  if code = [] then
    ?p Gh th. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata []
        (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))),Gh,th)
  else
    ?sc buf len p t Gmat tt pv sz.
      compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func t /\ allocas_below_fmp t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t) /\
      wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
      return_buf_frame d cenv sm t /\
      buf = Var p /\ eval_operand buf t = SOME pv /\ eval_operand len t = SOME sz /\
      sz = n2w (LENGTH code + 11) /\ ptr_covers Gmat tt p t (w2n sz) /\
      ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp /\
      read_memory (w2n pv) (w2n sz) t = create_copy_initcode code /\
      (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
      op_taint tt buf = {} /\ op_taint tt len = {} /\
      eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
      (case sop of NONE => sw = NONE | SOME op =>
        ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (strip_assume_tac o REWRITE_RULE[]) dallocaCreateGeometryTheory.create_copy_create_prefix >>
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE [compile_alloc_dynamic_def]) >>
  suspend "layout"
QED

Resume create_copy_prepared_path[layout]:
  `compile_create_dispatch buf len amount sop rof sc = (result,sb)` by
    (Cases_on `sop` >> fs[compile_create_dispatch_def,comp_bind_def]) >>
  `cs_extends sc sb` by
    (qspecl_then [`buf`,`len`,`amount`,`sop`,`rof`,`sc`] mp_tac
       externalEntryShapeTheory.compile_create_dispatch_labels >> simp[]) >>
  imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
  imp_res_tac stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows >>
  ntac 4 (imp_res_tac cs_extends_trans) >>
  `fn_has_code sm a2 func /\ fn_has_code a2 a5 func /\ fn_has_code a5 a6 func /\
   fn_has_code a6 a7 func /\ fn_has_code a7 a8 func /\ fn_has_code a8 a9 func /\
   fn_has_code a9 a10 func /\ fn_has_code a10 sc func /\ fn_has_code sc sb func /\
   fn_has_code sm sc func` by
    (rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     rewrite_tac[compileEnvTheory.cs_extends_refl] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
     asm_rewrite_tac[compileEnvTheory.cs_extends_refl]) >>
  suspend "guard"
QED

Resume create_copy_prepared_path[guard]:
  rpt (qpat_x_assum `!st. cs_extends _ _ ==> cs_extends _ _` kall_tac) >>
  qpat_assum `storage_trace_domain _ _ _`
    (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any (mp_then Any (map_every assume_tac o CONJUNCTS)
       accountsRelPropsTheory.state_rel_accounts)
       stateRelProjTheory.stmt_state_rel_state_rel) >>
  `LENGTH code <= 24576 /\
   (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) s.vs_accounts).code = code` by
    (drule_all_then strip_assume_tac exprSimSliceExtcodeTheory.slice_extcode_account >>
     asm_rewrite_tac[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx` by
    (qpat_assum `emit_op DALLOCA _ _ = _`
       (mp_then Any (map_every assume_tac o CONJUNCTS) exprLoweringPropsTheory.emit_op_extends) >>
     qpat_assum `emit_op DALLOCA _ _ = _`
       (mp_then Any (map_every assume_tac o CONJUNCTS) emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `same_blocks a5 a6` (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
     qpat_assum `fn_has_code a5 a6 func`
       (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >>
     disch_then (qspec_then `emitted_insts a5 a6` mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >>
     simp[ctx_has_dalloca_def,EXISTS_MEM] >> qexists `func` >> simp[] >>
     qexists `mk_inst a5.cs_next_id DALLOCA [size'] [STRING #"%" (toString a5.cs_next_var)]` >>
     reverse conj_tac >- simp[mk_inst_def] >>
     first_x_assum irule >> simp[]) >>
  `allocas_below_fmp s` by
    (drule stateRelProjTheory.stmt_state_rel_fmp_room >>
     simp[fmp_room_def,allocas_below_fmp_def] >> rpt strip_tac >>
     `alloca_inv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     fs[alloca_inv_def,alloca_next_valid_def] >> first_x_assum drule >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by asm_rewrite_tac[] >>
  drule_all create_copy_prealloc_path >> disch_then (qspecl_then [`PG`,`G`] mp_tac) >>
  Cases_on `code = []` >> asm_rewrite_tac[]
  >- (disch_then (qx_choose_then `p` strip_assume_tac) >>
      qexistsl [`p`,`G \\ p`,`tn with t_var := tn.t_var |+ (p,{})`] >>
      first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `pre` (qx_choose_then `Ga` (qx_choose_then `ta`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "allocate"
QED

Resume create_copy_prepared_path[allocate]:
  qpat_x_assum `code = _` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [SYM th]) >> REWRITE_TAC [SYM th]) >>
  `pre = s with <|vs_vars := pre.vs_vars; vs_inst_idx := pre.vs_inst_idx|>` by
    (qpat_assum `pre with <|vs_vars := _; vs_inst_idx := _|> = s`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := pre.vs_vars; vs_inst_idx := pre.vs_inst_idx|>``) >>
     simp[NoAsms]) >>
  `allocas_from lo pre /\ allocas_below_fmp pre` by
    (qpat_assum `pre:venom_state = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `allocas_below_fmp s` (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [allocas_below_fmp_def]) >>
     simp[allocas_from_def,allocas_below_fmp_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK pre,Ga,ta)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`s`,`G`,`tn`,`[]`,`OK pre`,`Ga`,`ta`] mp_tac) >> simp[]) >>
  qpat_assum `emit_op DALLOCA _ _ = _`
    (mp_then Any mp_tac bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary) >>
  disch_then (qspecl_then [`pre`,`func`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `p` (qx_choose_then `bb5` (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `alloc_inst = mk_inst a5.cs_next_id DALLOCA [size'] [p]` >>
  `alloc_inst.inst_opcode = DALLOCA /\ alloc_inst.inst_operands = [size'] /\
   alloc_inst.inst_outputs = [p]` by simp[Abbr `alloc_inst`,mk_inst_def] >>
  `get_instruction bb5 pre.vs_inst_idx = SOME alloc_inst` by simp[Abbr `alloc_inst`] >>
  `venomLayout$ceil32 (w2n (n2w (LENGTH code + 32):bytes32)) <=
   2 ** 255 + 2 ** 64` by
    (qspecl_then [`LENGTH code + 32`,`1024`] mp_tac
       (GEN_ALL dallocaBoundsTheory.ceil32_le_multiple) >>
     simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >>
     decide_tac) >>
  drule_all (Q.INST [`s` |-> `pre`, `inst` |-> `alloc_inst`,
    `n` |-> `w2n (n2w (LENGTH code + 32):bytes32)`] create_dalloca_cut_bound) >>
  strip_tac >>
  drule_all (Q.INST [`s` |-> `pre`, `tn` |-> `ta`]
    bodyFullDynamicBufferTheory.dalloca_origin_region_exact) >>
  disch_then (qspecl_then [`PG`,`Ga`]
    (qx_choosel_then [`al`,`Gb`,`tb`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `alloc_ptr = Var p` SUBST_ALL_TAC >>
  rpt (qpat_x_assum `cs_extends _ _` (fn th =>
    if aconv (concl th) ``cs_extends sm sc`` then NO_TAC else ALL_TAC)) >>
  `a5.cs_next_var <= a6.cs_next_var /\ sm.cs_next_var <= a5.cs_next_var /\
   a1.cs_next_var <= a5.cs_next_var /\ a1.cs_next_var <= a6.cs_next_var /\
   sm.cs_next_var <= sc.cs_next_var` by
    (every_drule_then assume_tac (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >> decide_tac) >>
  `!x. not_fresh_at sm x ==> lookup_var x al = lookup_var x s /\
    FLOOKUP Gb x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at a5 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     `x <> p` by metis_tac[] >>
     qpat_assum `!x. x <> p ==> _` drule >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x pre = _ /\ _` drule >> simp[]) >>
  `!x. MEM (Var x) [Var p;target;code'] ==> not_fresh_at a6 x` by
    (qpat_assum `emit_op DALLOCA _ _ = _`
       (mp_then Any assume_tac (cj 4 emitHelperPropsTheory.emitted_insts_emit_op)) >>
     qpat_assum `emit_op EXTCODESIZE _ _ = _`
       (mp_then Any (map_every assume_tac o CONJUNCTS) emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[] >> metis_tac[loweringShapeRulesTheory.fresh_output_props,
       stmtFragPtrTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `w2n (n2w (LENGTH code + 32):bytes32) = LENGTH code + 32` by
    (simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >> decide_tac) >>
  `0 < LENGTH code` by (Cases_on `code` >> fs[]) >>
  `pre.vs_labels = s.vs_labels /\ pre.vs_accounts = s.vs_accounts /\
   pre.vs_fmp = s.vs_fmp /\ pre.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `pre = _ with <|vs_vars := _; vs_inst_idx := _|>`
      (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
    eval_operand op al = eval_operand op s /\ op_taint tb op = op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_taint_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x al = _ /\ _` mp_tac >>
     simp[op_taint_def]) >>
  `eval_operand target al = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
   op_taint tb target = {}` by (first_x_assum (qspec_then `target` mp_tac) >> simp[]) >>
  `!op. MEM op [code';preamble] ==>
    eval_operand op al = eval_operand op pre /\ op_taint tb op = op_taint ta op` by
    (qpat_assum `emit_op EXTCODESIZE _ _ = _`
       (mp_then Any (map_every assume_tac o CONJUNCTS) emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `emit_op OR _ _ = _`
       (mp_then Any (map_every assume_tac o CONJUNCTS) emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[DISJ_IMP_THM,FORALL_AND_THM,IgnAsm `al = _`,IgnAsm `pre = _`] >>
     `!x. not_fresh_at a5 x ==> x <> p /\ lookup_var x al = lookup_var x pre /\
       op_taint tb (Var x) = op_taint ta (Var x)` by metis_tac[] >>
     `not_fresh_at a5 (STRING #"%" (toString sm.cs_next_var)) /\
      not_fresh_at a5 (STRING #"%" (toString a3.cs_next_var))` by
       metis_tac[loweringShapeRulesTheory.fresh_output_props,stmtFragPtrTheory.not_fresh_at_mono] >>
     simp[eval_operand_def,IgnAsm `al = _`]) >>
  `eval_operand code' al = SOME (n2w (LENGTH code)) /\
   eval_operand preamble al = SOME (0x620000003d81600b3d39f3w || (n2w (LENGTH code) << 56)) /\
   op_taint tb code' = {} /\ op_taint tb preamble = {}` by
    (first_x_assum mp_tac >> simp[DISJ_IMP_THM,FORALL_AND_THM]) >>
  `w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ _`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room) >>
     simp[exprLoweringPropsTheory.fmp_room_def]) >>
  `allocas_from lo al /\ al.vs_current_bb = a6.cs_current_bb /\
   al.vs_inst_idx = LENGTH a6.cs_current_insts` by
    (conj_tac
     >- (qpat_assum `allocas_from lo pre` mp_tac >>
         qpat_assum `al.vs_allocas = pre.vs_allocas`
           (fn th => rewrite_tac[allocas_from_def,th])) >>
     simp[IgnAsm `al = _`,IgnAsm `pre = _`]) >>
  suspend "write"
QED

Resume create_copy_prepared_path[write]:
  `lookup_var p al = SOME (n2w (w2n pre.vs_fmp)) /\
   FLOOKUP Gb p = SOME (w2n pre.vs_fmp,venomLayout$ceil32 (LENGTH code+32)) /\
   w2n al.vs_initial_fmp <= w2n pre.vs_fmp /\
   w2n pre.vs_fmp + venomLayout$ceil32 (LENGTH code+32) = w2n al.vs_fmp /\
   (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) al.vs_accounts).code = code` by
    (simp[IgnAsm `al = _`,IgnAsm `pre = _`] >> decide_tac) >>
  mp_tac (Q.INST [`n` |-> `LENGTH code`, `B` |-> `w2n pre.vs_fmp`,
    `s` |-> `al`, `tn` |-> `tb`, `G` |-> `Gb`, `dst` |-> `code_dst`,
    `sz` |-> `code'`, `aw` |-> `typed_val_to_w256 (BaseTV AddressT) (BytesV bs)`,
    `ctx` |-> `ctx`, `func` |-> `func`, `lo` |-> `lo`, `PG` |-> `PG`]
      (Q.INST [`pre` |-> `preamble`] create_copy_written_path)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC])) >>
  disch_then strip_assume_tac >>
  rename1 `ptr_covers Gwrite tt q t (LENGTH code + 11)` >>
  qpat_assum `pre.vs_fmp = s.vs_fmp` SUBST_ALL_TAC >>
  qabbrev_tac `B = w2n s.vs_fmp` >>
  `t = al with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                 vs_memory := t.vs_memory|>` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|> = al`
       (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                                        vs_memory := t.vs_memory|>``) >> simp[NoAsms]) >>
  `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s` by
    (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`,
        `al = update_var _ _ _ with vs_inst_idx := _`,
        `pre = _ with <|vs_vars := _; vs_inst_idx := _|>`] >>
     simp[NoAsms,update_var_def,venom_state_component_equality]) >>
  suspend "materialize"
QED

Resume create_copy_prepared_path[materialize]:
  `t.vs_fmp = al.vs_fmp /\ t.vs_allocas = al.vs_allocas /\
   t.vs_initial_fmp = al.vs_initial_fmp /\ t.vs_labels = al.vs_labels` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `pre.vs_memory = s.vs_memory` by
    (qpat_assum `pre = _ with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `B + LENGTH code + 32 <= LENGTH t.vs_memory /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `t.vs_memory = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[NoAsms,venomMemPropsTheory.LENGTH_write_memory_with_expansion,
          venomMemPropsTheory.LENGTH_mstore_eq] >>
     map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`al.vs_memory = _`, `pre.vs_memory = _`] >> simp[NoAsms]) >>
  `!b k. b+k <= B ==> mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = _` (PURE_ONCE_REWRITE_TAC o single) >>
     dep_rewrite.DEP_ONCE_REWRITE_TAC [valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint] >>
     conj_tac >- decide_tac >>
     dep_rewrite.DEP_ONCE_REWRITE_TAC [valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     conj_tac >- decide_tac >>
     map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`al.vs_memory = _`, `pre.vs_memory = _`] >> simp[NoAsms]) >>
  `!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem` by
    (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`tt.t_mem = _`, `tb.t_mem = _`, `ta.t_mem = _`] >>
     simp[NoAsms,pred_setTheory.IN_DIFF,pred_setTheory.IN_UNION] >>
     rpt strip_tac >> decide_tac) >>
  `tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm` by
    simp[IgnAsm `t = _`,IgnAsm `al = _`,IgnAsm `pre = _`] >>
  `sm.cs_next_var <= a6.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gwrite x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at a6 x` by (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `sm` >> simp[]) >>
     qpat_assum `!x. _ ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. _ ==> lookup_var x al = _ /\ _` (drule_then strip_assume_tac) >>
     simp[IgnAsm `t = _`,IgnAsm `al = _`,IgnAsm `pre = _`]) >>
  `w2n t.vs_fmp = B + venomLayout$ceil32 (LENGTH code + 32)` by
    (qpat_assum `t.vs_fmp = _` SUBST1_TAC >> sym_tac >> first_assum ACCEPT_TAC) >>
  `B = w2n s.vs_fmp` by simp[Abbr `B`] >>
  `(!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gwrite tt t) /\
   wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gwrite tt /\
   return_buf_frame d cenv sm t` by
    (`!H. valid_horizon cx st0 H ee.storage_trace ==>
          stmt_state_rel H ctx func cenv cx ee t /\
          storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gwrite tt t /\
          wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gwrite tt /\
          return_buf_frame d cenv sm t` by
       (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
          (drule_then strip_assume_tac) >>
        `B + (LENGTH code + 32) <= LENGTH t.vs_memory` by
          (rewrite_tac[arithmeticTheory.ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
        qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
          (mp_then (Pos (el 2)) (drule_all_then strip_assume_tac)
             bodyFullDynamicBufferTheory.dynamic_buffer_materialized_frame) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac
     >- (gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then strip_assume_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gwrite,tt)` by
    (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Ga`,`pre`,`ta`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gb`,`al`,`tb`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `allocas_below_fmp t` by
    (qpat_assum `allocas_below_fmp al` mp_tac >> rewrite_tac[allocas_below_fmp_def] >>
     map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`t.vs_fmp = _`,`t.vs_allocas = _`,`t.vs_initial_fmp = _`] >> simp[NoAsms]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_alloca_next``) >> simp[NoAsms]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
    eval_operand op t = eval_operand op s /\ op_taint tt op = op_taint tn op` by
    (Cases >> simp[NoAsms,eval_operand_def,op_taint_def]
     >- (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _` mp_tac >>
         simp[NoAsms,op_taint_def]) >>
     map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`t.vs_labels = _`,`al.vs_labels = _`,`pre.vs_labels = _`] >> simp[NoAsms]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by
    (qpat_assum `!op. _ ==> eval_operand op t = _ /\ _` (qspec_then `amount` mp_tac) >>
     impl_tac >- metis_tac[] >> simp[IgnAsm `t = _`,IgnAsm `al = _`,IgnAsm `pre = _`]) >>
  `(case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})` by
    (qpat_assum `case sop of NONE => _ | SOME op => _` mp_tac >>
     namedCases_on `sop` ["","salt_op"] >> simp[NoAsms] >> strip_tac >>
     qpat_assum `!op. _ ==> eval_operand op t = _ /\ _` (qspec_then `salt_op` mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >> qexists `w` >> metis_tac[]) >>
  suspend "pack"
QED

Resume create_copy_prepared_path[pack]:
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_allocas,z.vs_current_bb)``) >> simp[NoAsms]) >>
  `?insts. sc.cs_current_insts = sm.cs_current_insts ++ insts /\
     EVERY (\i. i.inst_opcode <> ALLOCA) insts` by
    (imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
     qexists `[mk_inst sm.cs_next_id EXTCODESIZE [target] [STRING #"%" (toString sm.cs_next_var)];
               mk_inst a1.cs_next_id ASSERT [code'] [];
               mk_inst a2.cs_next_id SHL [Lit 56w;code'] [STRING #"%" (toString a2.cs_next_var)];
               mk_inst a3.cs_next_id OR [Lit 0x620000003d81600b3d39f3w;shifted] [STRING #"%" (toString a3.cs_next_var)];
               mk_inst a4.cs_next_id ADD [code';Lit 32w] [STRING #"%" (toString a4.cs_next_var)];
               mk_inst a5.cs_next_id DALLOCA [size'] [STRING #"%" (toString a5.cs_next_var)];
               mk_inst a6.cs_next_id MSTORE [Var p;preamble] [];
               mk_inst a7.cs_next_id ADD [Var p;Lit 32w] [STRING #"%" (toString a7.cs_next_var)];
               mk_inst a8.cs_next_id EXTCODECOPY [target;code_dst;Lit 0w;code'] [];
               mk_inst a9.cs_next_id ADD [Var p;Lit 21w] [STRING #"%" (toString a9.cs_next_var)];
               mk_inst a10.cs_next_id ADD [code';Lit 11w] [STRING #"%" (toString a10.cs_next_var)]]` >>
     reverse conj_tac >- simp[NoAsms,mk_inst_def] >>
     map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`sc.cs_current_insts = _`,`a10.cs_current_insts = _`,`a9.cs_current_insts = _`,
        `a8.cs_current_insts = _`,`a7.cs_current_insts = _`,`a6.cs_current_insts = _`,
        `a5.cs_current_insts = _`,`a4.cs_current_insts = _`,`a3.cs_current_insts = _`,
        `a2.cs_current_insts = _`,`a1.cs_current_insts = _`] >>
     simp[NoAsms,GSYM listTheory.APPEND_ASSOC]) >>
  `alloca_history func t` by
    (qpat_assum `fn_has_code sm sc func`
       (strip_assume_tac o REWRITE_RULE[fragExecTheory.fn_has_code_def,rich_listTheory.IS_PREFIX_APPEND]) >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
     `DROP s.vs_inst_idx bb.bb_instructions = insts ++ l` by
       (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
          [`s.vs_inst_idx = _`,`bb.bb_instructions = _`,`sc.cs_current_insts = _`] >>
        PURE_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
     `t.vs_inst_idx = s.vs_inst_idx + LENGTH insts` by
       (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
          [`t.vs_inst_idx = _`,`sc.cs_current_insts = _`,`s.vs_inst_idx = _`] >> simp[NoAsms]) >>
     drule_all_then mp_tac bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
     qpat_assum `t.vs_inst_idx = s.vs_inst_idx + LENGTH insts`
       (fn th => simp[NoAsms,GSYM th])) >>
  `B + LENGTH code + 32 <= w2n t.vs_fmp` by
    (qpat_assum `w2n t.vs_fmp = _` SUBST1_TAC >>
     qspec_then `LENGTH code + 32` mp_tac (GEN_ALL venomLayoutTheory.ceil32_ge) >> decide_tac) >>
  `w2n (n2w (B+21):bytes32) = B+21 /\
   w2n (n2w (LENGTH code+11):bytes32) = LENGTH code+11` by
    (qspec_then `t.vs_fmp` assume_tac wordsTheory.w2n_lt >>
     `B+21 < dimword (:256) /\ LENGTH code+11 < dimword (:256)` by decide_tac >>
     PURE_REWRITE_TAC [wordsTheory.w2n_n2w] >>
     conj_tac >> irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `w2n t.vs_initial_fmp <= B + 21` by
    (qpat_assum `t.vs_initial_fmp = _` SUBST1_TAC >> decide_tac) >>
  `B+21+(LENGTH code+11) <= w2n t.vs_fmp` by decide_tac >>
  `!i. B+21 <= i /\ i < B+21+(LENGTH code+11) ==> i NOTIN tt.t_mem` by
    (qpat_assum `tt.t_mem = _` SUBST1_TAC >> simp[NoAsms,pred_setTheory.IN_DIFF] >>
     rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`sc`,`buf`,`len`,`q`,`t`,`Gwrite`,`tt`,`n2w (B+21)`,`n2w (LENGTH code+11)`] >>
  map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
    [`w2n (n2w (B+21):bytes32) = _`,`w2n (n2w (LENGTH code+11):bytes32) = _`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)
QED

Finalise create_copy_prepared_path

(* EXTCODESIZE itself does not reject empty code: even empty code can pass
   the subsequent signed Blueprint check when the literal offset wraps. *)
Theorem create_blueprint_extcodesize_path[local]:
  emit_op EXTCODESIZE [target] sa = (sz,sb) /\ fn_has_code sa sb func /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out. sz = Var out /\ not_fresh_at sb out /\
    (!x. not_fresh_at sa x ==> x <> out) /\ sb.cs_current_bb = sa.cs_current_bb /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
             with vs_inst_idx := LENGTH sb.cs_current_insts),
       G \\ out, tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  `not_fresh_at sb tmp` by metis_tac[exprSimSliceExtcodeTheory.slice_extcodesize_fresh] >>
  `~not_fresh_at sa tmp /\ sb.cs_current_bb = sa.cs_current_bb` by metis_tac[] >>
  qexists `tmp` >> simp[] >> rpt gen_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id EXTCODESIZE [target] [tmp]` >>
  qabbrev_tac `u = update_var tmp (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s` >>
  `step_inst_base i s = OK u` by simp[Abbr `i`, Abbr `u`, exprSimSliceExtcodeTheory.slice_extcodesize_step] >>
  `taint_ok func tn i s` by
    (irule ptrDisciplineTaintPropsTheory.taint_ok_clean_step >>
     simp[Abbr `i`, mk_inst_def, source_memory_read_ranges_def, mem_read_ops_def]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
   ptr_inst_ok D lo 0 ctx func G tn i s /\ mem_safe_step 0 ctx i s` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def, ptr_inst_ok_def,
         step_inst_non_invoke, exprSimSliceExtcodeTheory.slice_extcodesize_step, Abbr `u`,
         access_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
         mem_safe_step_non_invoke,inst_mem_below_frontiers_def,inst_mem_below_frontier_def,
         inst_dload_in_section_def,update_var_def] >>
  `step_prov PG G i u = G \\ tmp /\
   step_taint i s u tn = tn with t_var := tn.t_var |+ (tmp,{})` by
    simp[Abbr `i`, Abbr `u`, mk_inst_def, step_prov_def, set_prov_def,
         out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
         mem_taint_def, step_writes_def, imm_taint_def, new_site_bytes_def,
         written_taint_def, source_memory_write_ranges_def, store_taint_def,
         adopt_reset_def, range_bytes_def, update_var_def, finite_mapTheory.FLOOKUP_DEF,
         GSYM finite_mapTheory.fmap_domsub, SF CONJ_ss, taint_component_equality] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` suffices_by simp[Abbr `u`] >>
  irule create_checked_step_path >> gvs[]
QED

Theorem create_blueprint_guard_size[local]:
  LENGTH code <= 24576 ==>
  (if lit then blueprint_size_ok (blueprint_copy_size (w2n (off:bytes32)) code) else w2n off < LENGTH code) ==>
    0 < (blueprint_copy_size (w2n (off:bytes32)) code) /\ (blueprint_copy_size (w2n (off:bytes32)) code) < 2 ** 255
Proof
  strip_tac >> Cases_on `lit` >> simp[]
  >- (pure_rewrite_tac[blueprint_copy_size_def,blueprint_size_ok_def,wordsTheory.n2w_w2n] >>
      qmatch_goalsub_abbrev_tac `w2i w` >>
      simp[integer_wordTheory.w2i_eq_w2n,wordsTheory.INT_MIN_def,
           wordsTheory.dimword_def,venomMemPropsTheory.dimindex_256] >>
      Cases_on `w2n w < 2 ** 255` >> gvs[] >>
      `w2n w < dimword (:256)` by MATCH_ACCEPT_TAC wordsTheory.w2n_lt >>
      fs[wordsTheory.dimword_def] >> intLib.COOPER_TAC) >>
  strip_tac >> pure_rewrite_tac[blueprint_copy_size_def,wordsTheory.n2w_w2n] >>
  `w2n (n2w (LENGTH code):bytes32) = LENGTH code` by
    (simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >> decide_tac) >>
  `off <=+ (n2w (LENGTH code):bytes32)` by (simp[wordsTheory.WORD_LS] >> decide_tac) >>
  simp[wordsTheory.word_sub_w2n] >> decide_tac
QED

(* The common EXTCODESIZE is outside the scalar tail so that replay can use
   the established scalar success and assertion-revert interfaces. *)
Theorem create_blueprint_check_tail[local]:
  compile_create_blueprint_check lit target off sa = (csz,sb) ==>
  ?full sc hi qi.
    emit_op EXTCODESIZE [target] sa = (full,sc) /\
    cs_extends sa sc /\ cs_extends sc sb /\ sb.cs_current_bb = sc.cs_current_bb /\
    csz = Var (if lit then hi else qi) /\
    hi = STRING #"%" (toString sc.cs_next_var) /\
    qi = STRING #"%" (toString (sc.cs_next_var + 1)) /\
    sb.cs_next_var = sc.cs_next_var + 2 /\
    sb.cs_current_insts = sc.cs_current_insts ++
      (if lit then [mk_inst sc.cs_next_id SUB [full;off] [hi];
                    mk_inst (sc.cs_next_id+1) SGT [Var hi;Lit 0w] [qi];
                    mk_inst (sc.cs_next_id+2) ASSERT [Var qi] []]
       else [mk_inst sc.cs_next_id GT [full;off] [hi];
             mk_inst (sc.cs_next_id+1) SUB [full;off] [qi];
             mk_inst (sc.cs_next_id+2) ASSERT [Var hi] []])
Proof
  Cases_on `emit_op EXTCODESIZE [target] sa` >> rename1 `_ = (full,sc)` >>
  strip_tac >>
  qexistsl [`full`,`sc`,`STRING #"%" (toString sc.cs_next_var)`,
            `STRING #"%" (toString (sc.cs_next_var+1))`] >>
  `cs_extends sa sc` by metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  simp[] >> qpat_x_assum `compile_create_blueprint_check _ _ _ _ = _` mp_tac >>
  simp[compile_create_blueprint_check_def,comp_bind_def] >> Cases_on `lit` >>
  simp[] >> rpt (pairarg_tac >> fs[]) >>
  simp[emit_op_def,emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,fresh_var_def,emit_def,cs_extends_def,
       arithmeticTheory.ADD1,APPEND_ASSOC] >> strip_tac >> gvs[APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem create_blueprint_scalar_tail_run[local]:
  eval_operand full s = SOME (n2w (LENGTH code)) /\ eval_operand off s = SOME ow /\
  full <> Var p /\ off <> Var p /\ p <> q /\ LENGTH code <= 24576 /\
  ~not_fresh_at sc p /\ ~not_fresh_at sc q ==>
  bop_scalar_seq {x | not_fresh_at sc x} {full;off;Lit 0w} (if lit then [mk_inst sc.cs_next_id SUB [full;off] [p];
                          mk_inst (sc.cs_next_id+1) SGT [Var p;Lit 0w] [q];
                          mk_inst (sc.cs_next_id+2) ASSERT [Var q] []]
             else [mk_inst sc.cs_next_id GT [full;off] [p];
                   mk_inst (sc.cs_next_id+1) SUB [full;off] [q];
                   mk_inst (sc.cs_next_id+2) ASSERT [Var p] []])
    {Var q;Var p;full;off;Lit 0w} /\
  ?u. run_inst_seq (if lit then [mk_inst sc.cs_next_id SUB [full;off] [p];
                          mk_inst (sc.cs_next_id+1) SGT [Var p;Lit 0w] [q];
                          mk_inst (sc.cs_next_id+2) ASSERT [Var q] []]
             else [mk_inst sc.cs_next_id GT [full;off] [p];
                   mk_inst (sc.cs_next_id+1) SUB [full;off] [q];
                   mk_inst (sc.cs_next_id+2) ASSERT [Var p] []]) s = (if (if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code) else w2n ow < LENGTH code) then OK u else Abort Revert_abort (revert_state (set_returndata [] u))) /\
    eval_operand (Var (if lit then p else q)) u = SOME (n2w (blueprint_copy_size (w2n ow) code))
Proof
  strip_tac >> simp[] >>
  `w2n (n2w (LENGTH code):bytes32) = LENGTH code` by
    (simp[wordsTheory.w2n_n2w,wordsTheory.dimword_def] >> decide_tac) >>
  pure_rewrite_tac[blueprint_copy_size_def,blueprint_size_ok_def,wordsTheory.n2w_w2n] >>
  qmatch_goalsub_abbrev_tac `w2i sz` >>
  `sz > 0w <=> 0i < w2i sz` by
    simp[integer_wordTheory.WORD_GTi,integer_wordTheory.word_0_w2i,integerTheory.int_gt] >>
  `!v. eval_operand full (update_var p v s) = SOME (n2w (LENGTH code)) /\
       eval_operand off (update_var p v s) = SOME ow` by
    (rpt gen_tac >> conj_tac >> irule emitHelperPropsTheory.eval_operand_update_var_mstore >> metis_tac[]) >>
  Cases_on `lit` >> simp[] >>
  (conj_tac >- simp[bodyPtrBopScalarSeqTheory.bop_scalar_seq_def,mk_inst_def])
  >- (Cases_on `0i < w2i sz` >>
      qexists `update_var q (if 0i < w2i sz then 1w else 0w) (update_var p sz s)` >>
      simp[NoAsms,run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def] >>
      fs[exec_pure2_def,bind_outputs_def,eval_operand_def,emitHelperPropsTheory.lookup_var_update_var,
         Abbr `sz`,venomExecSemanticsTheory.bool_to_word_def]) >>
  Cases_on `w2n ow < LENGTH code` >>
  qexists `update_var q sz (update_var p (if w2n ow < LENGTH code then 1w else 0w) s)` >>
  simp[NoAsms,run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def] >>
  fs[exec_pure2_def,bind_outputs_def,emitHelperPropsTheory.eval_operand_update_var,
     arithmeticTheory.GREATER_DEF,venomExecSemanticsTheory.bool_to_word_def] >>
  simp[eval_operand_def,emitHelperPropsTheory.lookup_var_update_var]
QED

Theorem create_blueprint_check_path:
  compile_create_blueprint_check lit target off sa = (csz,sb) /\ fn_has_code sa sb func /\
  eval_operand target s = SOME aw /\ eval_operand off s = SOME ow /\
  op_taint tn target = {} /\ op_taint tn off = {} /\ op_prov G off = NONE /\
  (!x. off = Var x ==> not_fresh_at sa x) /\
  code = (lookup_account (w2w aw) s.vs_accounts).code /\ LENGTH code <= 24576 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  if (if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code) else w2n ow < LENGTH code) then
    ?t G' tn'. cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
      eval_operand csz t = SOME (n2w (blueprint_copy_size (w2n ow) code)) /\ op_taint tn' csz = {} /\ op_prov G' csz = NONE /\
      (!x. csz = Var x ==> not_fresh_at sb x) /\ 0 < (blueprint_copy_size (w2n ow) code) /\ (blueprint_copy_size (w2n ow) code) < 2 ** 255 /\
      t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      t.vs_current_bb = sb.cs_current_bb /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
  else ?t G' tn'. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort t,G',tn')
Proof
  strip_tac >> simp[] >>
  drule_then (qx_choosel_then [`full`,`sc`,`p`,`q`] strip_assume_tac) create_blueprint_check_tail >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid,cs_extends_refl] >>
  drule_all create_blueprint_extcodesize_path >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `out` strip_assume_tac)) >>
  qabbrev_tac `u = update_var out (n2w (LENGTH code)) s with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  qabbrev_tac `Gu = G \\ out` >> qabbrev_tac `tu = tn with t_var := tn.t_var |+ (out,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (unabbrev_all_tac >> metis_tac[]) >>
  `~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (simp[Abbr `u`,update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     fs[allocas_from_def,allocas_below_fmp_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ x <> out` by
    metis_tac[exprSimSliceExtcodeTheory.slice_extcodesize_fresh] >>
  `eval_operand full u = SOME (n2w (LENGTH code)) /\ eval_operand off u = SOME ow /\
   (!z. z IN {full;off;Lit 0w} ==> op_prov Gu z = NONE /\ op_taint tu z = {})` by
    (Cases_on `off` >>
     gvs[Abbr `u`, Abbr `Gu`, Abbr `tu`, eval_operand_def,lookup_var_def,update_var_def,
         DISJ_IMP_THM,FORALL_AND_THM,op_taint_def,op_prov_def,
         finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.DOMSUB_FLOOKUP_THM]) >>
  `~not_fresh_at sc p /\ ~not_fresh_at sc q /\ p <> q` by
    simp[not_fresh_at_def,emitHelperPropsTheory.fresh_var_distinct] >>
  `full <> Var p /\ off <> Var p` by metis_tac[operand_11] >>
  drule_all create_blueprint_scalar_tail_run >> disch_then (qspec_then `lit` mp_tac) >>
  simp[] >> disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `raw` strip_assume_tac)) >>
  qpat_x_assum `code = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE[SYM th]) >> pure_rewrite_tac[SYM th]) >>
  qmatch_asmsub_abbrev_tac `bop_scalar_seq R A tail B` >>
  `sb.cs_current_insts = sc.cs_current_insts ++ tail` by simp[Abbr `tail`] >>
  drule_all_then strip_assume_tac stmtReasonLitFragMemoryTheory.fn_has_code_code >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\ isPREFIX tail (DROP u.vs_inst_idx bb.bb_instructions)` by
    simp[IgnAsm `sc.cs_current_bb = sa.cs_current_bb`] >>
  `!z. z IN A ==> op_prov Gu z = NONE /\ op_taint tu z = {}` by simp[Abbr `A`] >>
  qmatch_goalsub_abbrev_tac `if good then _ else _` >>
  Cases_on `good` >> simp[] >> fs[IgnAsm `p = _`, IgnAsm `q = _`, IgnAsm `full = _`]
  >- suspend "check_success"
  >> suspend "check_failure"
QED

Resume create_blueprint_check_path[check_success]:
  drule_all bodyFullBopWordSuccessTheory.bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`{}`,`PG`] (qx_choosel_then [`H`,`tf`] strip_assume_tac)) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl [`t`,`H`,`tf`] >>
  `sa.cs_next_var <= sc.cs_next_var` by metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `op_taint tf csz = {} /\ op_prov H csz = NONE` by
    (`csz IN B` by (Cases_on `lit` >> simp[Abbr `B`]) >> metis_tac[]) >>
  qpat_assum `csz = Var _` (fn th =>
    map_every (fn q => qpat_x_assum q (assume_tac o PURE_REWRITE_RULE [th]))
      [`op_taint tf csz = {}`, `op_prov H csz = NONE`]) >>
  `0 < blueprint_copy_size (w2n ow) code /\ blueprint_copy_size (w2n ow) code < 2 ** 255` by
    (drule create_blueprint_guard_size >> disch_then (qspecl_then [`ow`,`lit`] mp_tac) >> simp[]) >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  qpat_x_assum `tail = if _ then _ else _` kall_tac >>
  `tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[Abbr `tu`] >>
  simp[Abbr `t`,exprSimHashTheory.hash_eval_operand_inst_idx] >>
  conj_tac
  >- (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl [`Gu`,`u`,`tu`] >> conj_tac >- simp[] >>
      irule abiDecodeValidFiniteLoopTheory.finite_array_empty_path_explicit >> qexists `{}` >>
      qpat_assum `!D. gas_origin_ptr_path (D,lo,{},ctx,func,PG) (u,Gu,tu) [] _`
        (qspec_then `D` mp_tac) >> simp[] >> gvs[arithmeticTheory.ADD_COMM]) >>
  `!x. csz = Var x ==> not_fresh_at sb x` by
    (Cases_on `lit` >> simp[not_fresh_at_def]) >>
  qpat_x_assum `_ < 2 ** 255` (assume_tac o SRULE []) >>
  simp[] >>
  conj_tac
  >- (qpat_assum `raw = u with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
      simp[Abbr `u`, update_var_def,venom_state_component_equality]) >>
  conj_tac
  >- (qpat_assum `raw = u with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  qx_gen_tac `x` >> strip_tac >>
  `x IN R /\ x <> out` by simp[Abbr `R`] >>
  qpat_assum `!x. x IN R ==> FLOOKUP H x = _ /\ _` (qspec_then `x` mp_tac) >>
  qpat_assum `!x. x IN R ==> FLOOKUP raw.vs_vars x = _` (qspec_then `x` mp_tac) >>
  simp[Abbr `u`,Abbr `Gu`,Abbr `tu`,lookup_var_def,update_var_def,op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED

Resume create_blueprint_check_path[check_failure]:
  drule_all bodyFullBopWordAbortTheory.bop_word_scalar_abort_joint >>
  disch_then (qspecl_then [`{}`,`PG`] (qx_choosel_then [`j`,`H`,`tf`] strip_assume_tac)) >>
  qexistsl [`revert_state (set_returndata [] raw) with vs_inst_idx := j`,`H`,`tf`] >>
  rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> conj_tac >- simp[] >>
  irule abiDecodeValidFiniteLoopTheory.finite_array_empty_path_explicit >> qexists `{}` >> simp[]
QED

Finalise create_blueprint_check_path

(* The constructor bytes are read below the static frontier but written
   above it. A runtime zero count still executes the emitted MCOPY. *)
Theorem create_blueprint_mixed_mcopy_path[local]:
  compile_copy_memory_dynamic (Var dst) (Var src) cnt sa = ((),sb) /\
  fn_has_code sa sb func /\ lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  eval_operand cnt s = SOME n /\ op_taint tn cnt = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  (w2n n = 0 \/ w2n a + w2n n <= s.vs_alloca_next) /\
  (w2n n = 0 \/ w2n s.vs_initial_fmp <= w2n b /\ w2n b + w2n n <= w2n s.vs_fmp) /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mcopy (w2n b) (w2n a) (w2n n) s with vs_inst_idx := LENGTH sb.cs_current_insts),G,
     tn with t_mem := tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  simp[] >> rpt gen_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;cnt] []` >>
  qabbrev_tac `u = mcopy (w2n b) (w2n a) (w2n n) s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists `0` >> simp[] >>
     irule fragExecPtrTheory.ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]) >>
  `mem_safe_step 0 ctx i s` by
    (simp[Abbr `i`,mk_inst_def,mem_safe_step_non_invoke,inst_mem_below_frontiers_def,
          inst_dload_in_section_def,source_memory_read_ranges_def,
          source_memory_write_ranges_def,sized_source_write_range_def,eval_operand_def] >>
     gvs[]) >>
  `step_prov PG G i u = G /\
   step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}` by
    (`!j. j < w2n n ==> j + w2n a NOTIN tn.t_mem` by
       (gen_tac >> disch_tac >>
        qpat_assum `!k. _ <= k /\ k < _ ==> k NOTIN tn.t_mem` (qspec_then `j + w2n a` mp_tac) >> simp[]) >>
     simp[Abbr `i`,Abbr `u`,taint_component_equality,fragExecPtrTheory.mcopy_operand_ghost_frame,
          mk_inst_def,step_taint_def,imm_taint_def,eval_operand_def,pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode` by
    simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),step_prov PG G i u,step_taint i s u tn)`
    suffices_by simp[Abbr `u`] >>
  irule create_checked_step_path >> simp[] >> qexists `bb` >> simp[]
QED

(* Runtime ADD, also used to address the trailing constructor bytes.
   A scalar right operand cannot contribute a second provenance site. *)
Theorem create_blueprint_add_path[local]:
  emit_op ADD [left;right] sa = (dst,sb) /\ fn_has_code sa sb func /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sb out /\
    t = (update_var out (a+b) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand dst t = SOME (a+b) /\
    FLOOKUP G' out = op_prov G left /\ op_taint tn' dst = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  drule (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [left;right] [tmp]` >>
  qabbrev_tac `u = update_var tmp (a+b) s` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  qexistsl [`tmp`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`gf`,`tf`] >>
  `not_fresh_at sb tmp` by simp[loweringShapeRulesTheory.fresh_output_props] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),gf,tf)` by
    (rpt gen_tac >> simp[Abbr `gf`,Abbr `tf`] >>
     qpat_assum `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     irule create_checked_step_path >> simp[] >>
     `ptr_inst_ok D lo 0 ctx func G tn i s` by
       (simp[Abbr `i`] >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
        simp[] >> qexists `0` >> simp[typedCopyPtrTheory.ptr_inst_ok_copy_len_binop]) >>
     gvs[Abbr `i`,Abbr `u`,mk_inst_def,is_terminator_def,step_inst_base_opcode_eqs,
         exec_pure2_def,mem_safe_step_non_invoke,inst_mem_below_frontier_def,
         inst_dload_in_section_def,source_memory_read_ranges_def,source_memory_write_ranges_def]) >>
  `FLOOKUP gf tmp = op_prov G left` by
    (Cases_on `op_prov G left` >>
     simp[Abbr `gf`,Abbr `i`,step_prov_def,out_prov_def,first_prov_def,set_prov_def,
          mk_inst_def,finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `op_taint tf (Var tmp) = {} /\ tf.t_mem = tn.t_mem /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!p. p <> tmp ==> FLOOKUP gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `gf`,Abbr `tf`,Abbr `i`,Abbr `u`,typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
     irule (cj 3 decoderGhostFramePtrTheory.step_taint_nonmemory_frame) >> simp[mk_inst_def]) >>
  qpat_x_assum `tmp = STRING _ _` SUBST_ALL_TAC >>
  simp[Abbr `u`,update_var_def,lookup_var_def,eval_operand_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* The compiler elides the suffix only for Lit 0w. An emitted MCOPY is
   proved even if the encoded argument length evaluates to zero. *)
Theorem create_blueprint_args_append_path[local]:
  (if cnt = Lit 0w then sc = se else
     ?dst sx. emit_op ADD [Var p;code] se = (dst,sx) /\
       compile_copy_memory_dynamic dst args_ptr cnt sx = ((),sc)) /\
  fn_has_code se sc func /\ lookup_var p s = SOME b /\
  eval_operand code s = SOME (n2w (LENGTH prefix)) /\
  op_prov G code = NONE /\ op_taint tn code = {} /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\
  (!x. MEM (Var x) [Var p;args_ptr;cnt] ==> not_fresh_at se x) /\
  ptr_covers G tn p s (LENGTH prefix + LENGTH args) /\
  (cnt <> Lit 0w ==>
   ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\
     ptr_covers G tn q s (LENGTH args) /\
     (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
     (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
     read_memory (w2n a) (LENGTH args) s = args) /\
  LENGTH prefix + LENGTH args < dimword (:256) /\
  w2n s.vs_initial_fmp <= w2n b /\
  w2n b + LENGTH prefix + LENGTH args <= w2n s.vs_fmp /\
  w2n b + LENGTH prefix <= LENGTH s.vs_memory /\
  read_memory (w2n b) (LENGTH prefix) s = prefix /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?t H z. cs_extends se sc /\ se.cs_next_var <= sc.cs_next_var /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_memory := s.vs_memory|>) = s /\
    w2n b + LENGTH prefix + LENGTH args <= LENGTH t.vs_memory /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    read_memory (w2n b) (LENGTH prefix + LENGTH args) t = prefix ++ args /\
    (!j k. j+k <= w2n b ==> read_memory j k t = read_memory j k s) /\
    z.t_mem = tn.t_mem DIFF {i | w2n b + LENGTH prefix <= i /\
                                 i < w2n b + LENGTH prefix + LENGTH args} /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!x. not_fresh_at se x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `cnt = Lit 0w`
  >- (fs[eval_operand_def,wordsTheory.n2w_11,wordsTheory.ZERO_LT_dimword] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[cs_extends_refl,fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
           venom_state_component_equality]) >>
  suspend "emitted"
QED

Resume create_blueprint_args_append_path[emitted]:
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`dst`,`sx`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `cnt <> Lit 0w ==> _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`q`,`a`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `args_ptr = Var q` SUBST_ALL_TAC >>
  `cs_extends se sx /\ cs_extends sx sc /\
   se.cs_next_var <= sx.cs_next_var /\ sx.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
       (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     imp_res_tac stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows >>
     drule (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >> simp[]) >>
  `fn_has_code se sx func /\ fn_has_code sx sc func` by
    metis_tac[fragExecTheory.fn_has_code_mid,cs_extends_refl] >>
  `op_taint tn (Var p) = {}` by fs[ptr_covers_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  `eval_operand (Var p) s = SOME b` by simp[eval_operand_def] >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`out`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  suspend "copy"
QED

Resume create_blueprint_args_append_path[copy]:
  `!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `!v. MEM v [Var p;Var q;cnt] ==>
        eval_operand v u = eval_operand v s /\ op_taint tu v = op_taint tn v` by
    (Cases >> simp[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `lookup_var q u = SOME a /\ eval_operand cnt u = SOME (n2w (LENGTH args)) /\
   op_taint tu cnt = {} /\ ptr_covers Gu tu q u (LENGTH args)` by
    (rpt conj_tac
     >- metis_tac[MEM,eval_operand_def]
     >- metis_tac[MEM]
     >- metis_tac[MEM] >>
     irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
     qexistsl [`G`,`s`,`se`,`tn`] >> simp[] >> metis_tac[MEM]) >>
  `w2n s.vs_fmp < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `w2n b + LENGTH prefix < dimword (:256)` by decide_tac >>
  `w2n (b + n2w (LENGTH prefix)) = w2n b + LENGTH prefix` by
    simp[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  `w2n (n2w (LENGTH args):bytes32) = LENGTH args` by
    (fs[wordsTheory.w2n_n2w] >> decide_tac) >>
  `lookup_var out u = SOME (b + n2w (LENGTH prefix))` by fs[eval_operand_def] >>
  `ptr_covers Gu tu out u (LENGTH args)` by
    (irule logAbiPrefixPtrTheory.ptr_covers_offset_transport >>
     simp[op_prov_def] >> qexistsl [`G`,`LENGTH prefix`,`p`,`s`,`tn`,`b`] >>
     qpat_assum `ptr_covers G tn p s _` (irule_at Any) >> fs[]) >>
  suspend "copy_edge"
QED

Resume create_blueprint_args_append_path[copy_edge]:
  `allocas_from lo u /\ allocas_below_fmp u /\ ~u.vs_halted /\
   u.vs_inst_idx = LENGTH sx.cs_current_insts /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_alloca_next = s.vs_alloca_next` by
    (fs[allocas_from_def,allocas_below_fmp_def,update_var_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `dest = b + n2w (LENGTH prefix)` >>
  qabbrev_tac `cntw = n2w (LENGTH args):bytes32` >>
  qabbrev_tac `t = mcopy (w2n dest) (w2n a) (w2n cntw) u with
                   vs_inst_idx := LENGTH sc.cs_current_insts` >>
  qabbrev_tac `z = tu with t_mem := tu.t_mem DIFF
                     {i | w2n dest <= i /\ i < w2n dest + w2n cntw}` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gu,z)` by
    (rpt gen_tac >>
     qpat_assum `Abbrev (t = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (z = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule (cj 2 create_blueprint_mixed_mcopy_path) >>
     rpt conj_tac >>
     FIRST_PROVE [qexistsl [`cnt`,`out`,`sx`,`q`] >> simp[IgnAsm `u = _`],
                  fs[IgnAsm `u = _`],
                  Cases_on `args` >> fs[IgnAsm `u = _`] >> decide_tac]) >>
  `sc.cs_current_bb = sx.cs_current_bb` by
    (qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
       (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac) >>
  suspend "endpoints"
QED

Resume create_blueprint_args_append_path[endpoints]:
  `u.vs_memory = s.vs_memory` by simp[update_var_def] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gu,z)` by
    (rpt gen_tac >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND]) >>
  `sx.cs_current_bb = se.cs_current_bb` by
    (qpat_assum `u.vs_current_bb = sx.cs_current_bb` (SUBST1_TAC o SYM) >>
     qpat_assum `u = update_var _ _ s with vs_inst_idx := _` SUBST1_TAC >>
     simp[update_var_def]) >>
  `t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
   (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_memory := s.vs_memory|>) = s /\
   (!x. lookup_var x t = lookup_var x u)` by
    (qpat_assum `u.vs_current_bb = sx.cs_current_bb` mp_tac >>
     qpat_assum `sc.cs_current_bb = sx.cs_current_bb` mp_tac >>
     simp[NoAsms,Abbr `t`,mcopy_def,write_memory_with_expansion_def,lookup_var_def] >>
     qpat_assum `u = update_var _ _ s with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms,update_var_def,venom_state_component_equality]) >>
  `w2n b + LENGTH prefix + LENGTH args <= LENGTH t.vs_memory /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    simp[Abbr `t`,mcopy_def,IgnAsm `u = _`,LENGTH_write_memory_with_expansion,
         LENGTH_TAKE_EQ,arithmeticTheory.MAX_DEF] >>
  suspend "bytes"
QED

Resume create_blueprint_args_append_path[bytes]:
  `!j k. read_memory j k u = read_memory j k s` by
    simp[IgnAsm `u = _`,read_memory_def] >>
  `!j k. read_memory j k t =
         read_memory j k (mcopy (w2n b + LENGTH prefix) (w2n a) (LENGTH args) u)` by
    simp[Abbr `t`,IgnAsm `u = _`,read_memory_def] >>
  `read_memory (w2n b) (LENGTH prefix + LENGTH args) t = prefix ++ args` by
    (pure_once_rewrite_tac [memoryReadPropsTheory.read_memory_split] >>
     simp[IgnAsm `u = _`,memoryReadPropsTheory.read_memory_mcopy_self,
          memoryReadPropsTheory.read_memory_mcopy_disjoint]) >>
  `!j k. j+k <= w2n b ==> read_memory j k t = read_memory j k s` by
    (rpt strip_tac >>
     qpat_assum `!j k. read_memory j k t = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[memoryReadPropsTheory.read_memory_mcopy_disjoint]) >>
  qexistsl [`t`,`Gu`,`z`] >>
  `cs_extends se sc` by metis_tac[cs_extends_trans] >>
  `se.cs_next_var <= sc.cs_next_var` by decide_tac >>
  simp[IgnAsm `u = _`,Abbr `z`,op_taint_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gvs[] >>
  rpt strip_tac >> fs[op_taint_def] >> metis_tac[]
QED

Finalise create_blueprint_args_append_path

(* Successful check already supplies the exact length of the account-code
   suffix. This theorem runs the remaining instruction-only prefix and
   leaves the dispatch unexecuted, even for an oversized initcode. *)
Theorem create_blueprint_materialize[local]:
  compile_create_blueprint_append target amount sop off code args_ptr cnt rof sa = (result,sb) /\
  fn_has_code sa sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  s.vs_alloca_next <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\
  take_pad_0 (LENGTH prefix) (DROP (w2n ow) (lookup_account (w2w aw) s.vs_accounts).code) = prefix /\
  eval_operand code s = SOME (n2w (LENGTH prefix)) /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\
  op_taint tn code = {} /\ op_taint tn cnt = {} /\
  op_prov G code = NONE /\ op_prov G cnt = NONE /\
  (!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sa x) /\
  (cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\ ptr_covers G tn q s (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
      read_memory (w2n a) (LENGTH args) s = args) /\
  LENGTH prefix + LENGTH args < dimword (:256) /\
  venomLayout$ceil32 (LENGTH prefix + LENGTH args) <= 2 ** 255 + 2 ** 64 ==>
  ?sc p size t H z.
    compile_create_dispatch (Var p) size amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\ cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
    lookup_var p t = SOME s.vs_fmp /\ ptr_covers H z p t (LENGTH prefix + LENGTH args) /\
    eval_operand size t = SOME (n2w (LENGTH prefix + LENGTH args)) /\ op_taint z size = {} /\
    (!x. Var x = size \/ x = p ==> not_fresh_at sc x) /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (LENGTH prefix + LENGTH args) /\
    w2n s.vs_fmp + LENGTH prefix + LENGTH args <= LENGTH t.vs_memory /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    read_memory (w2n s.vs_fmp) (LENGTH prefix + LENGTH args) t = prefix ++ args /\
    (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
    (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + LENGTH prefix + LENGTH args ==> i NOTIN z.t_mem) /\
    (!i. i < w2n s.vs_fmp /\ i IN z.t_mem ==> i IN tn.t_mem) /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dallocaCreateGeometryTheory.create_blueprint_create_prefix >>
  disch_then (qx_choosel_then [`tot_op`,`sm`,`buf`,`sn`,`se`,`sc`,`created`,`sd`]
    (map_every assume_tac o CONJUNCTS)) >>
  `compile_create_dispatch buf tot_op amount sop rof sc = (result,sb)` by
    (Cases_on `sop` >> fs[compile_create_dispatch_def,comp_bind_def]) >>
  `cs_extends sc sb` by
    (qspecl_then [`buf`,`tot_op`,`amount`,`sop`,`rof`,`sc`] mp_tac
       externalEntryShapeTheory.compile_create_dispatch_labels >> simp[]) >>
  suspend "layout"
QED

Resume create_blueprint_materialize[layout]:
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE [compile_alloc_dynamic_def]) >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn se /\ cs_extends se sc /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sn.cs_next_var <= se.cs_next_var /\ se.cs_next_var <= sc.cs_next_var` by
    (Cases_on `cnt = Lit 0w` >> gvs[cs_extends_refl] >>
     RULE_ASSUM_TAC (REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     imp_res_tac stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows >>
     imp_res_tac (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >>
     simp[] >> metis_tac[cs_extends_trans,arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn se func /\
   fn_has_code se sc func /\ fn_has_code sc sb func` by
    (ntac 4 (imp_res_tac cs_extends_trans) >>
     rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     qpat_assum `fn_has_code sa sb func` (irule_at Any) >>
     simp[cs_extends_refl]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`tot_var`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "total"
QED

Resume create_blueprint_materialize[total]:
  qabbrev_tac `N = LENGTH prefix + LENGTH args` >>
  qabbrev_tac `B = w2n s.vs_fmp` >>
  `eval_operand tot_op u = SOME (n2w N)` by
    simp[Abbr `N`,IgnAsm `u = _`,wordsTheory.word_add_n2w] >>
  `w2n (n2w N:bytes32) = N` by fs[wordsTheory.w2n_n2w] >>
  `w2n (n2w (LENGTH prefix):bytes32) = LENGTH prefix` by
    (fs[Abbr `N`,IgnAsm `prefix = _`,wordsTheory.w2n_n2w] >> decide_tac) >>
  `~u.vs_halted /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   allocas_from lo u /\ allocas_below_fmp u /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_alloca_next = s.vs_alloca_next` by
    (fs[update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu)` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL] >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
  disch_then (qx_choosel_then [`p`,`bb`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  qabbrev_tac `i = mk_inst sm.cs_next_id DALLOCA [tot_op] [p]` >>
  `i.inst_opcode = DALLOCA /\ i.inst_operands = [tot_op] /\ i.inst_outputs = [p]` by
    simp[Abbr `i`,mk_inst_def] >>
  `venomLayout$ceil32 (w2n (n2w N:bytes32)) <= 2 ** 255 + 2 ** 64` by
    asm_rewrite_tac[] >>
  drule_all (Q.INST [`s` |-> `u`, `inst` |-> `i`,
    `n` |-> `w2n (n2w N:bytes32)`] create_dalloca_cut_bound) >>
  strip_tac >>
  drule_all (Q.INST [`s` |-> `u`, `tn` |-> `tu`]
    bodyFullDynamicBufferTheory.dalloca_origin_region_exact) >>
  disch_then (qspecl_then [`PG`,`Gu`]
    (qx_choosel_then [`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "allocated"
QED

Resume create_blueprint_materialize[allocated]:
  `not_fresh_at sn p` by
    (drule (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[loweringShapeRulesTheory.fresh_output_props]) >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
     FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `v.vs_labels = s.vs_labels /\ v.vs_accounts = s.vs_accounts /\
   v.vs_memory = s.vs_memory /\ v.vs_initial_fmp = s.vs_initial_fmp /\
   v.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo v` by
    (fs[update_var_def,allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `!x. (!p. x = Var p ==> not_fresh_at sa p) ==>
     eval_operand x v = eval_operand x s /\ op_taint tv x = op_taint tn x /\
     op_prov Gv x = op_prov G x` by
    (Cases >> simp[eval_operand_def,op_taint_def,op_prov_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
     metis_tac[op_taint_def]) >>
  `eval_operand target v = SOME aw /\ eval_operand off v = SOME ow /\
   eval_operand code v = SOME (n2w (LENGTH prefix)) /\
   eval_operand cnt v = SOME (n2w (LENGTH args)) /\
   op_taint tv target = {} /\ op_taint tv off = {} /\
   op_taint tv code = {} /\ op_taint tv cnt = {} /\ op_prov Gv code = NONE` by
    (rpt conj_tac >> metis_tac[MEM]) >>
  `w2n s.vs_initial_fmp <= B` by
    (qpat_assum `allocas_below_fmp s` (mp_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     simp[Abbr `B`]) >>
  `w2n v.vs_fmp = B + venomLayout$ceil32 N` by
    (qpat_assum `w2n v.vs_fmp = _` mp_tac >>
     simp[Abbr `B`,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `N <= venomLayout$ceil32 N` by simp[venomLayoutTheory.ceil32_ge] >>
  `LENGTH prefix <= N` by simp[Abbr `N`] >>
  `B + LENGTH prefix <= w2n v.vs_fmp /\ B + N <= w2n v.vs_fmp` by decide_tac >>
  `ptr_covers Gv tv p v (w2n (n2w (LENGTH prefix):bytes32))` by
    (qpat_assum `ptr_covers Gv tv p v _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`] >>
     decide_tac) >>
  suspend "copy_code"
QED

Resume create_blueprint_materialize[copy_code]:
  `eval_operand (Var p) v = SOME s.vs_fmp` by
    simp[eval_operand_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `v.vs_current_bb = sn.cs_current_bb /\ v.vs_inst_idx = LENGTH sn.cs_current_insts` by
    metis_tac[] >>
  `w2n v.vs_initial_fmp <= w2n s.vs_fmp /\
   w2n s.vs_fmp + w2n (n2w (LENGTH prefix):bytes32) <= w2n v.vs_fmp` by
    simp[GSYM markerTheory.Abbrev_def,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`,Abbr `B`] >>
  drule_all create_dynamic_extcodecopy_path >> disch_then (qspec_then `PG` mp_tac) >>
  simp[IgnAsm `v = _`,IgnAsm `u = _`,evmStepSimTheory.take_pad_replicate] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `y = write_memory_with_expansion B prefix v with vs_inst_idx := LENGTH se.cs_current_insts` >>
  qabbrev_tac `ty = tv with t_mem := tv.t_mem DIFF {i | B <= i /\ i < B + LENGTH prefix}` >>
  suspend "written"
QED

Resume create_blueprint_materialize[written]:
  `y.vs_current_bb = se.cs_current_bb /\ y.vs_inst_idx = LENGTH se.cs_current_insts /\
   ~y.vs_halted /\ y.vs_fmp = v.vs_fmp /\ y.vs_initial_fmp = s.vs_initial_fmp /\
   y.vs_allocas = v.vs_allocas /\ y.vs_alloca_next = s.vs_alloca_next /\
   y.vs_labels = v.vs_labels /\ (!x. lookup_var x y = lookup_var x v)` by
    simp[Abbr `y`,write_memory_with_expansion_def,lookup_var_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `!x. op_taint ty x = op_taint tv x` by (Cases >> simp[Abbr `ty`,op_taint_def]) >>
  `allocas_from lo y /\ allocas_below_fmp y` by
    metis_tac[allocas_from_def,allocas_below_fmp_def] >>
  `B + LENGTH prefix <= LENGTH y.vs_memory /\ LENGTH s.vs_memory <= LENGTH y.vs_memory` by
    simp[Abbr `y`,LENGTH_write_memory_with_expansion,arithmeticTheory.MAX_DEF,
         IgnAsm `v = _`,IgnAsm `u = _`] >>
  `!j k. read_memory j k y = read_memory j k (write_memory_with_expansion B prefix v)` by
    simp[Abbr `y`,read_memory_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `read_memory B (LENGTH prefix) y = prefix` by
    simp[memoryReadPropsTheory.read_memory_write_self,IgnAsm `prefix = _`] >>
  `!j k. j+k <= B ==> read_memory j k y = read_memory j k s` by
    (rpt strip_tac >>
     qpat_assum `!j k. read_memory j k y = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[memoryReadPropsTheory.read_memory_write_disjoint] >>
     simp[read_memory_def,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `!i. i < B /\ i IN ty.t_mem ==> i IN tn.t_mem` by
    (simp[Abbr `ty`,IgnAsm `u = _`,IgnAsm `v = _`,Abbr `B`] >>
     rpt strip_tac >> decide_tac) >>
  suspend "args"
QED

Resume create_blueprint_materialize[args]:
  `!x. not_fresh_at sa x ==> lookup_var x y = lookup_var x s /\
        FLOOKUP Gv x = FLOOKUP G x /\ op_taint ty (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q y = SOME a /\ ptr_covers Gv ty q y (LENGTH args) /\
       (args = [] \/ w2n a + LENGTH args <= y.vs_alloca_next) /\
       (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN ty.t_mem) /\
       read_memory (w2n a) (LENGTH args) y = args` by
    (disch_tac >> qpat_assum `cnt <> Lit 0w ==> _` drule >>
     disch_then (qx_choosel_then [`q`,`a`] (map_every assume_tac o CONJUNCTS)) >>
     `not_fresh_at sa q` by metis_tac[MEM] >>
     `lookup_var q y = SOME a /\ ptr_covers Gv ty q y (LENGTH args)` by
       (simp[ptr_covers_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
        qpat_assum `ptr_covers G tn q s _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
        simp[]) >>
     qexistsl [`q`,`a`] >> simp[IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`] >>
     Cases_on `args = []` >- simp[read_memory_def] >>
     `w2n a + LENGTH args <= y.vs_alloca_next` by
       (qpat_assum `y.vs_alloca_next = s.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `args <> []` (fn nonempty =>
          qpat_assum `args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next`
            (ACCEPT_TAC o SIMP_RULE bool_ss [nonempty]))) >>
     `w2n a + LENGTH args <= B` by decide_tac >>
     conj_tac >- (disj2_tac >> decide_tac) >>
     conj_tac >- (rpt strip_tac >> rename1 `j IN ty.t_mem` >>
        `j < B` by decide_tac >>
        qpat_assum `!i. i < B /\ i IN ty.t_mem ==> _` (drule_all_then assume_tac) >>
        qpat_assum `!i. w2n a <= i /\ i < _ ==> i NOTIN tn.t_mem` (qspec_then `j` mp_tac) >>
        simp[] >> decide_tac) >>
     simp[memoryReadPropsTheory.read_memory_write_disjoint,IgnAsm `prefix = _`,
          IgnAsm `v = _`,IgnAsm `u = _`] >>
     qpat_assum `read_memory (w2n a) (LENGTH args) s = args`
        (assume_tac o REWRITE_RULE [read_memory_def]) >>
     simp[read_memory_def,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `ptr_covers Gv ty p y (LENGTH prefix + LENGTH args)` by
    (qpat_assum `ptr_covers Gv tv p v (w2n (n2w N))` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,Abbr `N`,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `!x. MEM (Var x) [Var p;args_ptr;cnt] ==> not_fresh_at se x` by
    (simp[] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono,MEM]) >>
  `!x. eval_operand x y = eval_operand x v` by
    (Cases >> simp[eval_operand_def,IgnAsm `u = _`,IgnAsm `v = _`]) >>
  `lookup_var p y = SOME s.vs_fmp /\ eval_operand code y = SOME (n2w (LENGTH prefix)) /\
   op_prov Gv code = NONE /\ op_taint ty code = {} /\
   eval_operand cnt y = SOME (n2w (LENGTH args)) /\ op_taint ty cnt = {}` by
    simp[IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`] >>
  `w2n y.vs_initial_fmp <= w2n s.vs_fmp /\
   w2n s.vs_fmp + LENGTH prefix + LENGTH args <= w2n y.vs_fmp /\
   w2n s.vs_fmp + LENGTH prefix <= LENGTH y.vs_memory /\
   read_memory (w2n s.vs_fmp) (LENGTH prefix) y = prefix` by
    (simp[Abbr `N`,Abbr `B`,IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`,
          memoryReadPropsTheory.read_memory_write_self] >>
     qspec_then `LENGTH args + LENGTH prefix` mp_tac (GEN_ALL venomLayoutTheory.ceil32_ge) >> decide_tac) >>
  `LENGTH prefix + LENGTH args < dimword (:256)` by simp[Abbr `N`,IgnAsm `prefix = _`] >>
  drule_all create_blueprint_args_append_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`t`,`H`,`z`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "finish"
QED

Resume create_blueprint_materialize[finish]:
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK y,Gv,ty)` by
    simp[Abbr `ty`,IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (v,Gv,tv) [] (OK y,Gv,ty)`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (y,Gv,ty) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     POP_ASSUM_LIST kall_tac >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND]) >>
  `t = y with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx; vs_memory := t.vs_memory|>` by
    (qpat_assum `_ with <|vs_vars := y.vs_vars; vs_inst_idx := y.vs_inst_idx; vs_memory := y.vs_memory|> = y`
       (mp_tac o AP_TERM ``\st. st with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                                            vs_memory := t.vs_memory|>``) >> simp[NoAsms]) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
             vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `Abbrev (y = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `v = update_var _ _ _ with vs_inst_idx := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `u = update_var _ _ _ with vs_inst_idx := _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[NoAsms,write_memory_with_expansion_def,update_var_def]) >>
  `~t.vs_halted /\ t.vs_fmp = v.vs_fmp` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  suspend "results"
QED

Resume create_blueprint_materialize[results]:
  `!x. not_fresh_at sn x ==> not_fresh_at se x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==> not_fresh_at se x /\ not_fresh_at sc x /\ x <> p` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `eval_operand tot_op t = SOME (n2w N) /\ op_taint z tot_op = {}` by
    (qpat_assum `tot_op = Var tot_var` SUBST_ALL_TAC >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> p ==> lookup_var x v = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `eval_operand (Var tot_var) u = SOME (n2w N)`
        (assume_tac o REWRITE_RULE [eval_operand_def]) >>
     simp[eval_operand_def,IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`]) >>
  `lookup_var p t = SOME s.vs_fmp /\ ptr_covers H z p t N` by
    (qpat_assum `!x. not_fresh_at sn x ==> not_fresh_at se x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `ptr_covers Gv tv p v (w2n (n2w N))` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at se x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
     qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x y = _ /\ _` (drule_then strip_assume_tac) >>
     simp[IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`]) >>
  qexistsl [`sc`,`p`,`tot_op`,`t`,`H`,`z`] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `not_fresh_at sc p` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `!x. Var x = tot_op \/ x = p ==> not_fresh_at sc x` by metis_tac[operand_11] >>
  `!i. B <= i /\ i < B + LENGTH prefix + LENGTH args ==> i NOTIN z.t_mem` by
    (qpat_assum `z.t_mem = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[NoAsms,Abbr `ty`,Abbr `B`,pred_setTheory.IN_DIFF] >>
     rpt strip_tac >> POP_ASSUM_LIST kall_tac >>
     metis_tac[arithmeticTheory.NOT_LESS]) >>
  `!i. i < B /\ i IN z.t_mem ==> i IN tn.t_mem` by
    (qx_gen_tac `j` >>
     qpat_assum `z.t_mem = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `!i. i < B /\ i IN ty.t_mem ==> i IN tn.t_mem` (qspec_then `j` mp_tac) >>
     POP_ASSUM_LIST kall_tac >> simp[pred_setTheory.IN_DIFF,CONJ_ASSOC]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`,Abbr `B`,Abbr `N`,Abbr `ty`] >>
  TRY (rpt strip_tac >> decide_tac) >>
  qpat_assum `s.vs_inst_idx = _` (fn pc =>
     qpat_assum `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                        vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s`
       (mp_tac o REWRITE_RULE [pc])) >> simp[NoAsms]
QED

Finalise create_blueprint_materialize

(* Match the offset guard before entering the allocation path. The signed
   literal guard is deliberately not used to rule out EXTCODECOPY padding. *)
Theorem create_blueprint_prepared_path:
  compile_create_blueprint_check lit target off sa = (code,sm) /\
  compile_create_blueprint_append target amount sop off code args_ptr cnt rof sm = (result,sb) /\
  fn_has_code sa sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  s.vs_alloca_next <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\ op_prov G off = NONE /\
  code_bytes = (lookup_account (w2w aw) s.vs_accounts).code /\ LENGTH code_bytes <= 24576 /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  LENGTH args < 2 ** 64 /\
  (!x. MEM (Var x) [target;off;args_ptr;cnt;amount] \/ sop = SOME (Var x) ==> not_fresh_at sa x) /\
  (cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\ ptr_covers G tn q s (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
      read_memory (w2n a) (LENGTH args) s = args) ==>
  if (if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code_bytes) else w2n ow < LENGTH code_bytes) then
    ?sc p size t H z.
      compile_create_dispatch (Var p) size amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
      eval_operand (Var p) t = SOME s.vs_fmp /\ ptr_covers H z p t (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) /\
      eval_operand size t = SOME (n2w (blueprint_copy_size (w2n ow) code_bytes + LENGTH args)) /\ op_taint z (Var p) = {} /\ op_taint z size = {} /\
      (!x. Var x = size \/ x = p ==> not_fresh_at sc x) /\
      (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) < dimword (:256) /\ w2n t.vs_initial_fmp <= w2n s.vs_fmp /\
      w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) /\
      w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) <= w2n t.vs_fmp /\ w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) <= LENGTH t.vs_memory /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\ allocas_below_fmp t /\
      read_memory (w2n s.vs_fmp) (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) t = blueprint_initcode (blueprint_copy_size (w2n ow) code_bytes) (w2n ow) code_bytes args /\
      (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
      (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) ==> i NOTIN z.t_mem) /\
      (!i. i < w2n s.vs_fmp /\ i IN z.t_mem ==> i IN tn.t_mem) /\
      z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
  else ?t H z. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort t,H,z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[NoAsms] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[externalEntryShapeTheory.compile_create_blueprint_check_labels,
              externalEntryShapeTheory.compile_create_blueprint_append_labels,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (mp_tac (Q.SPECL [`sa`,`sm`,`sb`,`func`] fragExecTheory.fn_has_code_split) >>
     asm_rewrite_tac[]) >>
  `!x. off = Var x ==> not_fresh_at sa x` by metis_tac[MEM] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all create_blueprint_check_path >> simp[NoAsms] >>
  qabbrev_tac `n = blueprint_copy_size (w2n ow) code_bytes` >>
  qabbrev_tac `good = if lit then blueprint_size_ok n else w2n ow < LENGTH code_bytes` >>
  Cases_on `good` >> simp[NoAsms] >- suspend "append" >> metis_tac[]
QED

Resume create_blueprint_prepared_path[append]:
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  `n + LENGTH args < dimword (:256)` by fs[] >>
  `u.vs_labels = s.vs_labels /\ u.vs_fmp = s.vs_fmp /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_accounts = s.vs_accounts /\ u.vs_initial_fmp = s.vs_initial_fmp /\
   u.vs_memory = s.vs_memory /\ ~u.vs_halted /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   allocas_from lo u /\ allocas_below_fmp u` by
    (qpat_assum `u = _ with <|vs_vars := _; vs_inst_idx := _|>` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[allocas_from_def,allocas_below_fmp_def] >>
     metis_tac[allocas_from_def,allocas_below_fmp_def]) >>
  `!x. MEM (Var x) [target;off;args_ptr;cnt] ==> not_fresh_at sa x` by metis_tac[MEM] >>
  `!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sm x` by
    (simp[MEM] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono,MEM]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op` by
    (match_mp_tac bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >> simp[]) >>
  `!op. MEM op [target;off;args_ptr;cnt] ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op` by
    (gen_tac >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `eval_operand target u = SOME aw /\ eval_operand off u = SOME ow /\
   eval_operand cnt u = SOME (n2w (LENGTH args)) /\ op_prov Gu cnt = NONE /\
   op_taint tu target = {} /\ op_taint tu off = {} /\ op_taint tu cnt = {}` by
    metis_tac[MEM] >>
  `cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q u = SOME a /\ ptr_covers Gu tu q u (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= u.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tu.t_mem) /\
      read_memory (w2n a) (LENGTH args) u = args` by
    (disch_tac >>
     qpat_assum `cnt <> Lit 0w ==> _`
       (drule_then (qx_choosel_then [`q`,`a`] (map_every assume_tac o CONJUNCTS))) >>
     `not_fresh_at sa q` by metis_tac[MEM] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` (drule_then strip_assume_tac) >>
     `ptr_covers Gu tu q u (LENGTH args)` by
       (rewrite_tac[ptr_covers_def] >>
        map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
          [`lookup_var q u = _`, `FLOOKUP Gu q = _`, `op_taint tu (Var q) = _`] >>
        qpat_assum `ptr_covers G tn q s _` (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
     `read_memory (w2n a) (LENGTH args) u = args` by
       (rewrite_tac[read_memory_def] >>
        qpat_assum `u.vs_memory = s.vs_memory` SUBST1_TAC >>
        qpat_assum `read_memory _ _ s = args` (ACCEPT_TAC o REWRITE_RULE[read_memory_def])) >>
     qexistsl_tac [`q`,`a`] >> simp[IgnAsm `u = _`] >>
     qpat_assum `args = [] \/ _` mp_tac >> simp[NoAsms,arithmeticTheory.ADD_COMM]) >>
  `gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu)` by
    (`gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) (marks ++ []) (OK u,Gu,tu)`
       suffices_by simp[] >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
     disch_then irule >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
  qabbrev_tac `prefix = take_pad_0 n (DROP (w2n ow) code_bytes)` >>
  `LENGTH prefix = n` by simp[Abbr `prefix`] >>
  `take_pad_0 (LENGTH prefix) (DROP (w2n ow) (lookup_account (w2w aw) u.vs_accounts).code) = prefix` by
    simp[Abbr `prefix`,IgnAsm `u = _`] >>
  `u.vs_alloca_next <= w2n u.vs_fmp` by simp[IgnAsm `u = _`] >>
  `LENGTH prefix + LENGTH args < dimword (:256)` by
    (qpat_assum `LENGTH prefix = n` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `eval_operand code u = SOME (n2w (LENGTH prefix))` by
    (qpat_assum `LENGTH prefix = n` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `venomLayout$ceil32 (LENGTH prefix + LENGTH args) <= 2 ** 255 + 2 ** 64` by
    (qpat_assum `LENGTH prefix = n` SUBST1_TAC >>
     qspecl_then [`n + LENGTH args`,`2 ** 250 + 2 ** 59`] mp_tac
       (GEN_ALL dallocaBoundsTheory.ceil32_le_multiple) >>
     (impl_tac >-
       (qpat_assum `n < _` mp_tac >>
        qpat_assum `LENGTH args < _` mp_tac >>
        simp[NoAsms] >> decide_tac)) >>
     simp[NoAsms]) >>
  drule_all create_blueprint_materialize >> strip_tac >>
  suspend "result"
QED

Resume create_blueprint_prepared_path[result]:
  rename1 `compile_create_dispatch (Var p) sz amount sop rof sc = (result,sb)` >>
  `cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var` by
    metis_tac[cs_extends_trans,arithmeticTheory.LESS_EQ_TRANS] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)` by
    (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
             vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s` by
    (qpat_assum `t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx;
                          vs_memory := u.vs_memory; vs_fmp := u.vs_fmp|> = u`
       (mp_tac o AP_TERM ``\v:venom_state. v with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                   vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>``) >>
     simp[NoAsms] >>
     qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                          vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s`
       (fn th => mp_tac (AP_TERM ``\v:venom_state. v.vs_allocas`` th) >>
                 mp_tac (AP_TERM ``\v:venom_state. v.vs_initial_fmp`` th)) >> simp[]) >>
  `w2n s.vs_fmp + (n + LENGTH args) <= w2n t.vs_fmp` by
    (qpat_assum `w2n t.vs_fmp = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[IgnAsm `u = _`] >>
     qspec_then `n + LENGTH args` mp_tac (GEN_ALL venomLayoutTheory.ceil32_ge) >> decide_tac) >>
  `allocas_below_fmp t` by
    (qpat_assum `allocas_below_fmp s`
       (strip_assume_tac o REWRITE_RULE[allocas_below_fmp_def]) >>
     simp[allocas_below_fmp_def,IgnAsm `u = _`] >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` (drule_then strip_assume_tac) >>
     simp[IgnAsm `u = _`]) >>
  `op_taint z (Var p) = {}` by
    qpat_assum `ptr_covers H z p t _`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def]) >>
  qexistsl_tac [`sc`,`p`,`sz`,`t`,`H`,`z`] >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  qpat_assum `t.vs_initial_fmp = s.vs_initial_fmp` (PURE_ONCE_REWRITE_TAC o single) >>
  map_every (fn pat => qpat_assum pat (rule_assum_tac o PURE_ONCE_REWRITE_RULE o single))
    [`u.vs_fmp = s.vs_fmp`,`LENGTH prefix = n`,`u.vs_initial_fmp = s.vs_initial_fmp`,
     `tu.t_mem = tn.t_mem`,`tu.t_stor = tn.t_stor`,
     `tu.t_trans = tn.t_trans`,`tu.t_imm = tn.t_imm`] >>
  qpat_assum `u.vs_memory = s.vs_memory` (fn th =>
    qpat_x_assum `!j k. _ ==> read_memory j k t = read_memory j k u`
      (assume_tac o PURE_REWRITE_RULE[read_memory_def,th]) >>
    rule_assum_tac (PURE_ONCE_REWRITE_RULE[th])) >>
  simp[NoAsms,eval_operand_def,blueprint_initcode_def] >>
  qpat_x_assum `read_memory _ _ t = prefix ++ args`
    (assume_tac o SRULE[Abbr `prefix`]) >>
  rule_assum_tac (SRULE[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[read_memory_def]
QED

Finalise create_blueprint_prepared_path

Theorem copy_pre_args[local]:
  expr_body_pre cenv cx env
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts.
    args = target :: amount :: salts /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = [])
Proof
  strip_tac >> drule expr_body_pre_static_facts >>
  Cases_on `salted` >>
  simp[well_typed_expr_def, create_arg_types_ok_def, listTheory.MAP_EQ_CONS] >>
  metis_tac[]
QED

Theorem copy_cut_code[local]:
  lower_value compile_expr cenv ty e sa = (x,a) /\
  lower_value compile_expr cenv ty' e' a = (y,b) /\
  compile_create_salt compile_expr cenv salt b = (sop,c) /\
  compile_create_copy x y sop rof c = (out,sb) /\
  fn_has_code sa sb fn ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\
  fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c sb fn
Proof
  strip_tac >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b c` by
    (rpt conj_tac >> FIRST
       [metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND],
        metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND]]) >>
  `cs_extends c sb` by
    metis_tac[externalEntryShapeTheory.compile_create_copy_labels,pairTheory.SND] >>
  fs[ci_mono_def] >>
  `cs_extends a sb /\ cs_extends b sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a fn /\ fn_has_code a sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code a b fn /\ fn_has_code b sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem copy_read_prepared[local]:
  IS_SOME es.outcomes /\ dest_AddressV target = SOME addr /\
  dest_NumV amount = SOME value /\ dest_optional_salt salt = SOME sw /\
  LENGTH ts = (if IS_SOME salt then 3 else 2) /\
  code = (lookup_account addr es.accounts).code ==>
  bind (eval_create_operands cx CreateCopyOf (IS_SOME salt) rof ts off
        (target::amount::(case salt of NONE => [] | SOME v => [v])))
    (read_result cx) es =
  if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),es)
  else bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw value (create_copy_initcode code) rof))
    (read_result cx) es
Proof
  Cases_on `salt` >>
  simp[eval_create_operands_def,create_operand_layout_def,eval_create_def,
       dest_create_args_def,make_create_operands_def,dest_optional_num_def,
       dest_optional_salt_def,build_create_code_def] >>
  rpt strip_tac >>
  qpat_x_assum `LENGTH ts = _` mp_tac >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  simp[dest_create_args_def,make_create_operands_def,dest_optional_num_def,
       dest_optional_salt_def,create_arg_ctor_types_def,build_create_code_def,
       bind_def,ignore_bind_def,lift_option_type_def,lift_option_def,
       get_accounts_def,check_def,check_not_static_def,assert_def,return_def,raise_def] >>
  Cases_on `(lookup_account addr es.accounts).code = []` >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

(* Once the scalars have been read, Copy either reverts at EXTCODESIZE's
   guard or reaches exactly the dynamic window needed by dispatch. *)
Theorem create_copy_finish[local]:
  compile_create_copy target amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i z. frag_reachable ctx func s0 fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 ee.storage_trace /\ valid_horizon cx st0 H ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\ outcomes_accounts_typed ee.outcomes /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\ eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
    ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!x. target = Var x \/ amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),
                        ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (create_copy_initcode code) rof))
      (read_result cx) (ee with gas_obs := tail)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `gas_origin_ptr_path _ _ _ _`
    (mp_then Any (drule_all_then mp_tac) create_copy_prepared_path) >>
  Cases_on `code = []` >> asm_rewrite_tac[]
  >- (disch_then (qx_choose_then `p` (qx_choose_then `Gh` (qx_choose_then `th` assume_tac))) >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`Gh`,`ee`,
        `Abort Revert_abort (revert_state (set_returndata []
          (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx)))`,
        `INR (Error (RuntimeError "create source has no deployable code"))`,`th`] >>
      simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
           exprSimDefsTheory.halt_exit_def]) >>
  disch_then (qx_choose_then `sc` (qx_choose_then `buf` (qx_choose_then `len`
    (qx_choose_then `p` (qx_choose_then `t` (qx_choose_then `Gmat` (qx_choose_then `tt`
      (qx_choose_then `pv` (qx_choose_then `sz` (map_every assume_tac o CONJUNCTS)))))))))) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gmat`,`t`,`tt`] >> conj_tac >- simp[] >>
  suspend "dispatch"
QED

Resume create_copy_finish[dispatch]:
  `LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code <= 24576` by
    fs[accounts_well_typed_def,account_well_typed_def] >>
  `~(w2n sz > 2 * max_code_size)` by
    (qpat_assum `sz = _` SUBST1_TAC >>
     qspec_then `LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code + 11`
       mp_tac (INST_TYPE [``:'a`` |-> ``:256``] wordsTheory.word_n2w_le2) >>
     simp[vfmConstantsTheory.max_code_size_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  irule create_dispatch_outcome_full >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand buf t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand len t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand amount t = SOME _` (irule_at Any) >>
  qexistsl [`sw`,`create_copy_initcode (lookup_account (word_of_bytes_be bs) ee.accounts).code`] >>
  simp[] >> qpat_x_assum `ptr_covers Gmat tt p t (w2n sz)` mp_tac >> simp[]
QED
Finalise create_copy_finish

Theorem create_copy_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx (create_operand_order CreateCopyOf s es) ==>
    body_expr_full_ok cx (Call ty (CreateTarget CreateCopyOf s r ks) es d)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[Once body_expr_full_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule copy_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (drule copy_pre_args >> strip_tac >> gvs[] >>
      `LENGTH salts = (if s then 1 else 0)` by (Cases_on `s` >> gvs[]) >>
      rewrite_tac[bodySimFullTheory.expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
      drule_all copy_compile_cuts >> strip_tac >>
      qpat_assum `lower_value _ _ _ target sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) copy_cut_code) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) copy_cut_code) >>
      simp[NoAsms,create_eval_read,create_operand_order_def,vyperASTTheory.expr_type_def,
           loweringPostsTheory.post_value_type_def,is_word_type_def] >>
      suspend "target") >>
  irule bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[create_compile_stack,loweringPostsTheory.post_value_type_def,
       vyperASTTheory.expr_type_def,is_word_type_def] >>
  metis_tac[create_eval_value]
QED

Resume create_copy_expr_full_ok[target]:
  `expr_body_pre cenv cx env target es'` by
    (irule create_operand_pre >> simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_full_ok_def]) >>
  strip_tac >> rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  qexistsl [`tops`,`a'`,`shadow_func`,`shadow_sa`,`a`,`sa`,`x`,`env`,`d'`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env amount et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_full_ok_def] >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  qexistsl [`tops`,`b'`,`shadow_func`,`a'`,`b`,`a`,`y`,`env`,`d'`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> fs[loweringPostsTheory.expr_post_def])
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`av`,`ea`,`Gamt`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "scalar_frames"
QED

Resume create_copy_expr_full_ok[scalar_frames]:
  qpat_x_assum `_ ==> body_exprs_full_ok _ salts` (drule_then assume_tac) >>
  `is_word_type (BaseT AddressT) /\ is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) et.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) es'.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ea.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_facts) >>
  qpat_assum `expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_facts) >>
  `wb_frame cenv es' et sa s0 st /\ wb_frame cenv et ea a st samt` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `MAP FDOM es'.scopes = MAP FDOM et.scopes /\ MAP FDOM et.scopes = MAP FDOM ea.scopes` by
    fs[loweringPostsTheory.expr_post_def,loweringPostsTheory.locals_kept_def] >>
  `eval_operand x samt = SOME (typed_val_to_w256 (BaseTV AddressT) tv) /\ op_taint tna x = {}` by
    (qpat_assum `wb_frame cenv et ea a st samt`
      (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_id <= a.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id`
    by fs[ci_mono_def] >>
  `wb_frame cenv es' ea sa s0 samt` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`et`,`a`,`st`] >> simp[]) >>
     qexistsl [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es' sa G0 tn0 s0 Gamt tna` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv et a Gtar tnt st Gamt tna` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea samt /\ storage_well_formed_on cx ea (FST H) /\
    ghost_inv_at (DF H) lo d' cenv cx ea Gamt tna samt` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[loweringPostsTheory.expr_post_def]) >>
  suspend "scalar_paths"
QED

Resume create_copy_expr_full_ok[scalar_paths]:
  qpat_x_assum `?marks. !H. _ ==> gas_origin_ptr_path _ _ marks (OK st,_,_)`
    (qx_choose_then `mt` assume_tac) >>
  qpat_x_assum `?marks. !H. _ ==> gas_origin_ptr_path _ _ marks (OK samt,_,_)`
    (qx_choose_then `ma` assume_tac) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) (mt ++ ma) (OK samt,Gamt,tna)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H et.storage_trace` by first_assum (drule_then ACCEPT_TAC) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ mt _` (drule_then (mp_then Any irule fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     simp[]) >>
  `local_ptrs_reserved cenv b` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS,exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= b.cs_next_id` by decide_tac >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z. x = Var z ==> not_fresh_at b z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `?bs. tv = BytesV bs /\ LENGTH bs = 20` by
    (qpat_x_assum `value_has_type (BaseTV AddressT) tv` mp_tac >>
     Cases_on `tv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  `dest_NumV av = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) av))`
    by simp[exprSimSendTheory.uint256_typed_dest] >>
  `s0.vs_alloca_next <= samt.vs_alloca_next` by decide_tac >>
  Cases_on `s` >> gvs[compile_create_salt_def,comp_return_def]
  >- suspend "salt_cut" >>
  suspend "no_salt"
QED

Resume create_copy_expr_full_ok[salt_cut]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt b` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) b'` >>
  gvs[comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt b = (salt_op,c)` >>
  `expr_body_pre cenv cx env salt ea` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  fs[Once body_exprs_full_ok_def] >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,Once vyperInterpreterTheory.evaluate_def,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  qexistsl [`tops`,`c'`,`shadow_func`,`b'`,`c`,`b`,`salt_op`,`env`,`d'`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[] >- simp[]
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`sv`,`ew`,`Gsalt`,`tns`,`ssalt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "salt_frames"
QED

Resume create_copy_expr_full_ok[no_salt]:
  simp[NoAsms,Once vyperInterpreterTheory.evaluate_def,bind_return] >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) et.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) es'.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ea.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0) (mt ++ ma) (OK samt,Gamt,tna)` by
    first_assum (drule_then ACCEPT_TAC) >>
  `accounts_well_typed ea.accounts /\ outcomes_accounts_typed ea.outcomes` by
    fs[expr_sim_inv_def] >>
  `IS_SOME ea.outcomes` by
    (qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[stmt_state_rel_def,state_rel_def]) >>
  irule (Q.INST [`sw` |-> `NONE`] create_copy_finish) >>
  qpat_assum `compile_create_copy x y NONE _ b = _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK samt,Gamt,tna)` (irule_at Any) >>
  qpat_assum `eval_operand x samt = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y samt = SOME _` (irule_at Any) >>
  simp[vyperASTTheory.expr_type_def,is_word_type_def,
       supportedExprTraverseTheory.expr_has_effect_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_effect_root_def] >>
  qexists `tops` >> simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [SIMP_RULE (srw_ss()) [dest_optional_salt_def]
          (Q.INST [`salt` |-> `NONE`, `sw` |-> `NONE`,
                   `addr` |-> `word_of_bytes_be bs`,
                   `value` |-> `w2n (typed_val_to_w256 (BaseTV (UintT 256)) av)`,
                   `code` |-> `(lookup_account (word_of_bytes_be bs) (ea:evaluation_state).accounts).code`]
            copy_read_prepared)] >>
      simp[vyperValueTheory.dest_AddressV_def]) >>
  rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)
QED

Resume create_copy_expr_full_ok[salt_frames]:
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ew.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ea.storage_trace`
    by (qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> valid_horizon _ _ H ea.storage_trace`
          (qspec_then `storage_trace_horizon ew.storage_trace` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) et.storage_trace`
    by (qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> valid_horizon _ _ H et.storage_trace`
          (qspec_then `storage_trace_horizon ew.storage_trace` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) es'.storage_trace`
    by (qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> valid_horizon _ _ H es'.storage_trace`
          (qspec_then `storage_trace_horizon ew.storage_trace` mp_tac) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ew.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `is_word_type (BaseT (BytesT (Fixed 32)))` by simp[is_word_type_def] >>
  `lower_value compile_expr cenv (expr_type salt) salt b = (salt_op,c)` by simp[] >>
  qpat_assum `expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_facts) >>
  `wb_frame cenv ea ew b samt ssalt` by
    (qpat_assum `expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _`
      (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `sa.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= b.cs_next_id /\
   b.cs_next_var <= c.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es' ew sa s0 ssalt` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`ea`,`b`,`samt`] >> simp[]) >>
     qexistsl [`storage_trace_horizon ew.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es' sa G0 tn0 s0 Gsalt tns` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv ea b Gamt tna samt Gsalt tns` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `eval_operand x ssalt = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\ op_taint tns x = {}` by
    (qpat_assum `eval_operand x samt = SOME _`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  `eval_operand y ssalt = SOME (typed_val_to_w256 (BaseTV (UintT 256)) av) /\ op_taint tns y = {}` by
    (qpat_assum `eval_operand y samt = SOME _`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  suspend "salt_finish"
QED

Resume create_copy_expr_full_ok[salt_finish]:
  qpat_x_assum `?marks. !H. _ ==> gas_origin_ptr_path _ _ marks (OK ssalt,_,_)`
    (qx_choose_then `ms` assume_tac) >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ew.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0)
      ((mt ++ ma) ++ ms) (OK ssalt,Gsalt,tns)` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ (mt ++ ma) _`
      (drule_then (mp_then Any irule fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H ew.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ew ssalt /\ storage_well_formed_on cx ew (FST H) /\
    ghost_inv_at (DF H) lo d' cenv cx ew Gsalt tns ssalt` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[loweringPostsTheory.expr_post_def]) >>
  `accounts_well_typed ew.accounts /\ outcomes_accounts_typed ew.outcomes` by
    (qpat_assum `expr_sim_inv _ _ _ ew`
       (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  `IS_SOME ew.outcomes` by
    (qpat_assum `!H. valid_horizon _ _ H ew.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[stmt_state_rel_def,state_rel_def]) >>
  `sa.cs_next_var <= c.cs_next_var /\ s0.vs_alloca_next <= ssalt.vs_alloca_next` by decide_tac >>
  qpat_assum `local_ptrs_reserved cenv sa` (fn reserved =>
    qpat_assum `sa.cs_next_var <= c.cs_next_var`
      (assume_tac o MATCH_MP exprLoweringPropsTheory.local_ptrs_reserved_next_var o CONJ reserved)) >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z. x = Var z ==> not_fresh_at c z) /\ (!z. y = Var z ==> not_fresh_at c z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qabbrev_tac `salt_word = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `dest_create_salt sv = SOME salt_word` by
    (simp[Abbr `salt_word`] >> irule create_salt_word >> first_assum ACCEPT_TAC) >>
  irule (Q.INST [`sw` |-> `SOME salt_word`] create_copy_finish) >>
  qpat_assum `compile_create_copy x y (SOME salt_op) _ c = _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK ssalt,Gsalt,tns)` (irule_at Any) >>
  qpat_assum `eval_operand x ssalt = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y ssalt = SOME _` (irule_at Any) >>
  simp[vyperASTTheory.expr_type_def,is_word_type_def,
       supportedExprTraverseTheory.expr_has_effect_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_effect_root_def] >>
  qexists `tops` >> simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [SIMP_RULE (srw_ss()) [dest_optional_salt_def]
          (Q.INST [`salt` |-> `SOME sv`, `sw` |-> `SOME salt_word`,
                   `addr` |-> `word_of_bytes_be bs`,
                   `value` |-> `w2n (typed_val_to_w256 (BaseTV (UintT 256)) av)`,
                   `code` |-> `(lookup_account (word_of_bytes_be bs) (ew:evaluation_state).accounts).code`]
            copy_read_prepared)] >>
      simp[vyperValueTheory.dest_AddressV_def]) >>
  rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)
QED
Finalise create_copy_expr_full_ok

Theorem blueprint_pre_args[local]:
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts offset ctor.
    args = target :: amount :: (salts ++ offset :: ctor) /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    expr_type offset = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = []) /\
    (raw ==> ?e n. ctor = [e] /\ expr_type e = BaseT (BytesT (Dynamic n)))
Proof
  strip_tac >> drule expr_body_pre_static_facts >>
  Cases_on `salted` >>
  simp[well_typed_expr_def, create_arg_types_ok_def, listTheory.MAP_EQ_CONS] >>
  strip_tac >> gvs[]
  >- (rename1 `expr_type salt = BaseT (BytesT (Fixed 32))` >>
      qexists_tac `[salt]` >> simp[] >>
      metis_tac[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]) >>
  metis_tac[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]
QED

Theorem blueprint_read_prepared[local]:
  IS_SOME ee.outcomes /\ dest_AddressV target = SOME addr /\
  dest_NumV amount = SOME value /\ dest_NumV offset = SOME off /\
  dest_optional_salt salt = SOME sw /\
  LENGTH tys = (if IS_SOME salt then 4 else 3) + LENGTH ctor_tys /\
  DROP (if IS_SOME salt then 4 else 3) tys = ctor_tys /\
  (if raw then vals = [BytesV args]
   else encode_create_ctor_args (get_tenv cx) ctor_tys vals = SOME args) /\
  code = (lookup_account addr ee.accounts).code ==>
  bind (eval_create_operands cx (CreateFromBlueprint raw) (IS_SOME salt) rof tys lit
    (target :: (vals ++ (amount :: ((case salt of NONE => [] | SOME v => [v]) ++ [offset])))))
    (read_result cx) ee =
  if ~(if lit then blueprint_size_ok (blueprint_copy_size off code) else off < LENGTH code) then
    (INR (Error (RuntimeError "create source has no deployable code")),ee)
  else if (blueprint_copy_size off code) + LENGTH args > 2 * max_code_size then
    (INR (Error (RuntimeError "create initcode too large")),ee)
  else bind (ignore_bind (check_not_static cx)
    (create_oracle_result sw value (blueprint_initcode (blueprint_copy_size off code) off code args) rof)) (read_result cx) ee
Proof
  Cases_on `salt` >>
  simp[eval_create_operands_def,create_operand_layout_def,
       rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND] >>
  strip_tac >>
  `?t u v. tys = t::u::v::ctor_tys \/ ?w. tys = t::u::v::w::ctor_tys` by
    (qpat_x_assum `LENGTH tys = _` mp_tac >> qpat_x_assum `DROP _ tys = _` mp_tac >>
     Cases_on `tys` >> simp[] >> rename1 `DROP _ t = _` >>
     Cases_on `t` >> simp[] >> rename1 `DROP _ t = _` >>
     Cases_on `t` >> simp[] >> TRY (rename1 `DROP _ t = _` >> Cases_on `t` >> simp[]) >>
     metis_tac[]) >>
  fs[check_create_blueprint_def,blueprint_prefix_size_def,eval_create_def,
     dest_create_args_def,make_create_operands_def,create_arg_ctor_types_def,
     dest_optional_num_def,dest_optional_salt_def,bind_def,ignore_bind_def,
     lift_option_type_def,lift_option_def,get_accounts_def,check_def,
     check_not_static_def,assert_def,return_def,raise_def,build_create_code_def] >>
  Cases_on `raw` >> Cases_on `lit` >>
  simp[return_def,raise_def] >>
  TRY (Cases_on `blueprint_size_ok (blueprint_copy_size off (lookup_account addr ee.accounts).code)` >>
       gvs[return_def,raise_def] >>
       rename1 `blueprint_size_ok _`) >>
  TRY (Cases_on `off < LENGTH (lookup_account addr ee.accounts).code` >>
       gvs[return_def,raise_def]) >>
  Cases_on `LENGTH args + blueprint_copy_size off (lookup_account addr ee.accounts).code <= 2 * max_code_size` >>
  gvs[return_def,raise_def,arithmeticTheory.NOT_GREATER] >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

Theorem blueprint_cut_code[local]:
  lower_value compile_expr cenv ty target sa = (x,a) /\
  compile_create_blueprint_args compile_expr cenv raw later ctor a = ((p,n),b) /\
  lower_value compile_expr cenv ty' amount b = (y,c) /\
  compile_create_salt compile_expr cenv salt c = (sop,d) /\
  (case offlit of SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv ty'' offset) d = (off,f) /\
  compile_create_blueprint_check (IS_SOME offlit) x off f = (sz,k) /\
  compile_create_blueprint_append x y sop off sz p n rof k = (result,sb) /\
  fn_has_code sa sb fn ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d f /\
  fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\
  fn_has_code c d fn /\ fn_has_code d f fn /\ fn_has_code f sb fn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d f` by
    (rpt conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_compile_create_blueprint_args,compile_expr_ci_mono,pairTheory.SND]
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND] >>
     Cases_on `offlit` >> gvs[comp_return_def,ci_mono_refl] >>
     metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]) >>
  asm_rewrite_tac[] >>
  `cs_extends f k /\ cs_extends k sb` by
    (conj_tac >- metis_tac[externalEntryShapeTheory.compile_create_blueprint_check_labels,pairTheory.SND] >>
     metis_tac[externalEntryShapeTheory.compile_create_blueprint_append_labels,pairTheory.SND]) >>
  fs[ci_mono_def] >>
  ntac 3 (imp_res_tac cs_extends_trans) >>
  qpat_x_assum `fn_has_code sa sb fn` (fn th =>
    rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
    irule_at Any th >> simp[cs_extends_refl])
QED

(* Project the original cut at a single horizon for the compiler witnesses.
   Storage liveness is re-projected at each horizon on the same saved row. *)
Theorem create_rows_encoder_inputs:
  EVERY (\e. expr_body_pre ce cx env e entry) ctor /\
  EVERY (\e. expr_body_pre ce cx env e ee) ctor /\
  eval_exprs cx ctor entry = (INL vs,fin) /\
  expr_sim_inv ce cx env ee /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    LENGTH vals = LENGTH ctor /\
    LIST_REL (\(e,sv) v.
      (?si sm ss vv raw copy.
        compile_expr ce (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv ce copy
          (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
        (copy /\ ~is_word_type (lowered_value_type ce e) ==>
          ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
            eval_operand (vv_operand sv) t = SOME w /\
            evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
            val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
              SOME (w2n w,type_memory_size tv) /\
            sm.cs_next_id < ss.cs_next_id /\
            (!n b sz. local_region ce ee.scopes t n b sz ==>
              regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
        sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
        sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
        ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
        local_ptrs_reserved ce si /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type ce e) p /\
           ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
         (?p. sv = LocatedValue (lowered_value_type ce e) p /\
           ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
           lowered_value_type ce e = expr_type e /\ sv = vv)) /\
        read_result cx raw ee = (INL v,ee) /\
        vv_holds ce cx (lowered_value_type ce e) raw sv ee t /\
        vv_at ce cx (lowered_value_type ce e) si ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type ce e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G t) /\
      (ce.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))) (ZIP (ctor,vals)) vs) ==>
  LENGTH ctor = LENGTH vals /\ LENGTH ctor = LENGTH vs /\
  (!i. i < LENGTH ctor ==>
    ?e saved v raw si sm ss vv copy tv.
      e = EL i ctor /\ saved = EL i vals /\ v = EL i vs /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr ce (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,ss) /\
      ((?tag op0. saved = StackValue tag op0) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type ce e = expr_type e /\ saved = vv)) /\
      local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand saved <> Label l) /\ read_result cx raw ee = (INL v,ee) /\
      vv_holds ce cx (lowered_value_type ce e) raw saved ee t /\
      vv_at ce cx (lowered_value_type ce e) si ss ee raw saved t /\
      ptr_vv_ok cx (lowered_value_type ce e) raw saved ee G tn t /\
      vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved t /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx saved ee t) /\
      ((case saved of StackValue tag op0 => ~is_word_type (lowered_value_type ce e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce e (vv_operand saved) G t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _.storage_trace ==> LENGTH vals = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `LENGTH ctor = LENGTH vals /\ LENGTH ctor = LENGTH vs` by
    (qpat_assum `LIST_REL _ (ZIP (ctor,vals)) vs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     simp[LENGTH_ZIP]) >>
  asm_rewrite_tac[] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) ctor vs` by
    (irule exprSimHypsTheory.eval_exprs_physical_runtime_typed >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[exprSimHypsTheory.memory_rhs_read_lowered_typed_unwidened]) >>
  qx_gen_tac `i` >> disch_tac >>
  `expr_body_pre ce cx env (EL i ctor) ee` by fs[EVERY_EL] >>
  `?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i ctor)) = SOME tv /\
        value_has_type tv (EL i vs)` by
    (drule expr_body_pre_env_type_defs >> disch_tac >>
     qpat_assum `LIST_REL _ ctor vs` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[] >> disch_then (qspec_then `i` mp_tac) >>
     simp[value_runtime_typed_def]) >>
  qpat_assum `LIST_REL _ (ZIP (ctor,vals)) vs`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  simp[LENGTH_ZIP,EL_ZIP] >> disch_then (qspec_then `i` mp_tac) >>
  simp[EL_ZIP] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] (map_every assume_tac o CONJUNCTS))
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`raw`,`si`,`sm`,`ss`,`vv`,`copy`] >>
  asm_rewrite_tac[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule exprSimHypsTheory.expr_sim_inv_memory_size >> metis_tac[])
  >- suspend "size"
  >- suspend "nonlabel"
  >- suspend "live"
  >> Cases_on `EL i vals` >> gvs[vv_operand_def]
QED

Resume create_rows_encoder_inputs[size]:
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv` >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >> metis_tac[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
    (irule (cj 1 abiEncodeArgsCaseTheory.abi_args_fits_memory_bytes) >>
     metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits]) >>
  Cases_on `is_word_type (expr_type e)`
  >- (`type_memory_bytes ce (expr_type e) = 32` by
        (irule (DISCH_ALL (cj 3 (UNDISCH (SPEC_ALL
           entryDecodeStaticPropsTheory.word_type_dec_sizes)))) >> first_assum ACCEPT_TAC) >>
      decide_tac) >>
  drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[] >> decide_tac
QED

Resume create_rows_encoder_inputs[nonlabel]:
  rename1 `compile_expr ce (expr_type e) e si = (vv,sm)` >>
  `!l. vv_operand vv <> Label l` by
    (qpat_assum `expr_body_pre ce cx env e ee` (fn pre =>
       qpat_assum `compile_expr ce (expr_type e) e si = (vv,sm)`
         (ACCEPT_TAC o MATCH_MP assignPlaceOperandFactsTheory.assign_place_operand_not_label o
          CONJ pre))) >>
  `vv_operand (ext_call_arg_value (lowered_value_type ce e) vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def,vv_operand_def]) >>
  drule_all (cj 1 create_ctor_snapshot_retag) >> disch_tac >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
      simp[compile_snapshot_vv_def,comp_bind_def] >> pairarg_tac >>
      simp[comp_return_def] >> strip_tac >> gvs[vv_operand_def] >>
      drule exprSafeOperandTheory.unwrap_value_not_label >> simp[]) >>
  Cases_on `copy`
  >- (qpat_x_assum `_ /\ _ ==> ?p w. _` mp_tac >> simp[] >>
      strip_tac >> simp[]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,comp_return_def] >> strip_tac >> gvs[]
QED

Resume create_rows_encoder_inputs[live]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _.storage_trace ==> LENGTH vals = _ /\ _`
    (qspec_then `H` (drule_then (mp_tac o CONJUNCT2))) >>
  rewrite_tac[LIST_REL_EL_EQN] >> simp[LENGTH_ZIP,EL_ZIP] >>
  disch_then (qspec_then `i` mp_tac) >> simp[EL_ZIP]
QED

Finalise create_rows_encoder_inputs

Theorem blueprint_rows_encoder_inputs:
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) es /\
  LENGTH salts = (if salted then 1 else 0) /\ ctor <> [] /\
  EVERY (\e. expr_body_pre ce cx env e entry) ctor /\
  EVERY (\e. expr_body_pre ce cx env e ee) ctor /\
  eval_exprs cx ctor entry = (INL vs,fin) /\
  expr_sim_inv ce cx env ee /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    LENGTH vals = LENGTH ctor /\
    LIST_REL (\(e,sv) v.
      (?si sm ss vv raw copy.
        compile_expr ce (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv ce copy
          (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
        (copy /\ ~is_word_type (lowered_value_type ce e) ==>
          ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
            eval_operand (vv_operand sv) t = SOME w /\
            evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
            val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
              SOME (w2n w,type_memory_size tv) /\
            sm.cs_next_id < ss.cs_next_id /\
            (!n b sz. local_region ce ee.scopes t n b sz ==>
              regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
        sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
        sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
        ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
        local_ptrs_reserved ce si /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type ce e) p /\
           ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
         (?p. sv = LocatedValue (lowered_value_type ce e) p /\
           ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
           lowered_value_type ce e = expr_type e /\ sv = vv)) /\
        read_result cx raw ee = (INL v,ee) /\
        vv_holds ce cx (lowered_value_type ce e) raw sv ee t /\
        vv_at ce cx (lowered_value_type ce e) si ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type ce e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G t) /\
      (ce.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))) (ZIP (ctor,vals)) vs) ==>
  LENGTH ctor = LENGTH vals /\ LENGTH ctor = LENGTH vs /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctor)) < 2**64 /\
  (!i. i < LENGTH ctor ==>
    ?e saved v raw si sm ss vv copy tv.
      e = EL i ctor /\ saved = EL i vals /\ v = EL i vs /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr ce (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,ss) /\
      ((?tag op0. saved = StackValue tag op0) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type ce e = expr_type e /\ saved = vv)) /\
      local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand saved <> Label l) /\ read_result cx raw ee = (INL v,ee) /\
      vv_holds ce cx (lowered_value_type ce e) raw saved ee t /\
      vv_at ce cx (lowered_value_type ce e) si ss ee raw saved t /\
      ptr_vv_ok cx (lowered_value_type ce e) raw saved ee G tn t /\
      vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved t /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx saved ee t) /\
      ((case saved of StackValue tag op0 => ~is_word_type (lowered_value_type ce e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce e (vv_operand saved) G t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_rows_encoder_inputs >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule expr_body_pre_static_facts >>
  simp[alloc_limits_expr_def] >> strip_tac >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type ctor)) < 2**64` by
    (qpat_assum `ext_call_alloc_ok _ _ _` mp_tac >>
     Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute,ext_call_alloc_ok_def]) >>
  drule dallocaBlueprintArgsTheory.create_ctor_args_abi_bound >> disch_tac >>
  fs[] >> decide_tac
QED

(* Start the encoder at the root of its registered buffer, before any
   constructor bytes have been written. *)
Theorem create_alloc_buffer_saved_start:
  compile_alloc_buffer cap se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  cap < dimword (:256) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?root pbase u Gu tu inst.
    buf.buf_operand = Var root /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase cap root root 0 [] a u Gu tu /\
    return_buf_frame d ce a u /\ allocas_from lo u /\
    (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    u.vs_memory = s.vs_memory /\ FLOOKUP Gu root = SOME (pbase,cap) /\
    pbase + cap < dimword (:256) /\ pbase + cap <= u.vs_alloca_next /\
    (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < pbase+cap)) /\
    (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint pbase cap b n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?H. valid_horizon cx st0 H ee.storage_trace` by
    (qexists `storage_trace_horizon ee.storage_trace` >> fs[storage_trace_domain_def]) >>
  `stmt_state_rel H ctx func ce cx ee s` by metis_tac[] >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `root` (qx_choose_then `w` (qx_choose_then `u`
      (qx_choose_then `Gu` (qx_choose_then `tu`
         (map_every assume_tac o CONJUNCTS))))))) >>
  `se.cs_next_var <= a.cs_next_var /\ se.cs_next_id < a.cs_next_id` by
    (drule compilerInstructionSuffixTheory.added_insts_allocate >> simp[ci_mono_def]) >>
  `not_local_ptr ce ee.scopes root` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`)
       (cj 1 bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_frame_separation) >>
     disch_then irule >> simp[] >> qexists `se` >> simp[]) >>
  drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `out` (qx_choose_then `raw` strip_assume_tac)) >>
  `out = root` by metis_tac[operand_11] >>
  qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u.vs_halted = s.vs_halted /\ u.vs_memory = s.vs_memory` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  qexistsl [`root`,`w2n w`,`u`,`Gu`,`tu`,
           `mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [root]`] >>
  simp[mk_inst_def] >> conj_tac >- suspend "saved_state" >>
  conj_tac >- (drule bodyMemoryDefsTheory.return_buf_frame_frame >> disch_then irule >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Resume create_alloc_buffer_saved_start[saved_state]:
  simp[bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def,
       eval_operand_def,read_memory_def,valueEncodingDefsTheory.mem_bytes_at_def] >>
  conj_tac >- suspend "horizons" >>
  conj_tac >- suspend "wb" >>
  suspend "kept"
QED

Resume create_alloc_buffer_saved_start[horizons]:
  qx_gen_tac `H'` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  simp[] >>
  drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [``:'a`` |-> ``:256``] bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexists `w2n w + cap` >> simp[]) >>
  conj_tac >- (qexists `se` >> simp[]) >>
  qexistsl [`H'`,`ctx`,`func`] >> simp[]
QED

Resume create_alloc_buffer_saved_start[wb]:
  irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
  qexistsl [`se`,`s`] >> simp[exprSimWordArgsTheory.wb_frame_refl]
QED

Resume create_alloc_buffer_saved_start[kept]:
  `alloca_inv s` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> b+n <= s.vs_alloca_next`
    by fs[alloca_inv_def,alloca_next_valid_def] >>
  `!name b n. local_region ce ee.scopes s name b n ==> b+n <= s.vs_alloca_next`
    by metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
  qexistsl [`G`,`w2n w + cap`,`s`,`tn`] >>
  simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  metis_tac[]
QED

Finalise create_alloc_buffer_saved_start

(* A successful edge entering the instruction after an MLOAD must have
   executed that load: block entry cannot skip a non-PHI instruction. *)
Theorem create_mload_exit_edge[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK z,Gz,tz) /\
  lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\ z.vs_inst_idx = SUC k /\
  get_instruction bb k = SOME (mk_inst id MLOAD [src] [x]) ==>
  op_prov Gz (Var x) = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fuel`,`input_bb`,`inst`,`middle`]
      (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `_ \/ _ \/ _ \/ _ \/ _` strip_assume_tac
  >- suspend "fallthrough"
  >- gvs[]
  >- suspend "phis"
  >- gvs[jump_to_def] >>
  qpat_assum `OK _ = middle`
    (fn th => fs[GSYM th,fragExecTheory.exit_result_def])
QED

Resume create_mload_exit_edge[fallthrough]:
  `t.vs_current_bb = s.vs_current_bb` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- metis_tac[intCallStepTheory.step_inst_invoke_OK_control] >>
     metis_tac[step_inst_non_invoke,venomInstProofs1Theory.step_inst_base_preserves_all]) >>
  `inst = mk_inst id MLOAD [src] [x]` by
    (gvs[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by simp[mk_inst_def] >>
  `step_inst fuel ctx inst s = OK t` by metis_tac[] >>
  `ghost_step fuel ctx PG G tn inst s =
     (step_prov PG G inst t, step_taint inst s t tn)` by
    metis_tac[ghost_step_non_invoke] >>
  `op_prov (step_prov PG G inst t) (Var x) = NONE` by
    (irule bodyPtrDefsTheory.step_prov_out_none >> simp[mk_inst_def,out_prov_def]) >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Resume create_mload_exit_edge[phis]:
  drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
  strip_tac >>
  `bb = target` by gvs[] >>
  `k < phi_prefix_length target.bb_instructions` by (gvs[] >> decide_tac) >>
  drule venomExecProofsTheory.phi_prefix_length_el_phi >>
  gvs[get_instruction_def,mk_inst_def,AllCaseEqs()]
QED

Finalise create_mload_exit_edge

Theorem create_origin_ptr_path_last_edge[local]:
  !cfg st marks out. fragGasOriginPtr$gas_origin_ptr_path cfg st marks out ==>
    !z Gz tz. out = (OK z,Gz,tz) ==>
      st = (z,Gz,tz) \/ ?v Gv tv em.
        fragGasOriginPtr$gas_origin_ptr_edge cfg (v,Gv,tv) em (OK z,Gz,tz)
Proof
  ho_match_mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_ind >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

(* The predecessor at the input cut (an ALLOCA for Blueprint, an ADD for
   RawCreate) distinguishes it from the cursor-load exit even if the two
   cuts have the same block label. *)
Theorem create_encoded_length_no_prov:
  emit_op opc inputs a = (dst,st) /\ opc <> MLOAD /\ fn_has_code a st func /\
  compile_abi_encode_values_to_buf ce dst rows st = (alen,en) /\
  fn_has_code st en func /\
  u.vs_current_bb = st.cs_current_bb /\ u.vs_inst_idx = LENGTH st.cs_current_insts /\
  z.vs_current_bb = en.cs_current_bb /\ z.vs_inst_idx = LENGTH en.cs_current_insts /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) marks (OK z,Gz,tz) ==>
  op_prov Gz alen = NONE
Proof
  strip_tac >>
  drule abiEncodeValuesCodeTheory.abi_encode_values_to_buf_trace >>
  disch_then (qx_choosel_then [`cursor`,`allocated`,`ready`,`stored`] strip_assume_tac) >>
  `ci_mono st allocated /\ ci_mono allocated ready` by
    metis_tac[ci_mono_emit_op,ci_mono_emit_void,pairTheory.SND] >>
  `ci_mono ready stored /\ ci_mono stored en` by
    metis_tac[ci_mono_compile_abi_encode_value_rows,ci_mono_emit_op,pairTheory.SND] >>
  `fn_has_code stored en func` by
    metis_tac[ci_mono_def,cs_extends_trans,fragExecTheory.fn_has_code_split] >>
  qpat_assum `emit_op opc _ _ = _` (mp_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  disch_then (qx_choose_then `x` strip_assume_tac) >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  `?bb. lookup_block a.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH a.cs_current_insts) =
          SOME (mk_inst a.cs_next_id opc inputs [p])` by
    (qspecl_then [`a`,`st`,`func`,`[mk_inst a.cs_next_id opc inputs [p]]`]
       mp_tac fragExecTheory.fn_has_code_same_block >> simp[]) >>
  `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH stored.cs_current_insts) =
          SOME (mk_inst stored.cs_next_id MLOAD [cursor] [x])` by
    (qspecl_then [`stored`,`en`,`func`,`[mk_inst stored.cs_next_id MLOAD [cursor] [x]]`]
       mp_tac fragExecTheory.fn_has_code_same_block >> simp[]) >>
  `z.vs_inst_idx = SUC (LENGTH stored.cs_current_insts)` by simp[] >>
  `u <> z` by
    (strip_tac >>
     `LENGTH a.cs_current_insts = LENGTH stored.cs_current_insts` by gvs[] >>
     gvs[mk_inst_def]) >>
  drule create_origin_ptr_path_last_edge >> simp[] >> strip_tac >>
  metis_tac[create_mload_exit_edge]
QED

Theorem create_clean_mload_path[local]:
  emit_op MLOAD [Var p] sa = (op,sb) /\ fn_has_code sa sb func /\
  eval_operand (Var p) s = SOME w /\ ptr_covers G tn p s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x t G' tn'. op = Var x /\ not_fresh_at sb x /\
    t = (update_var x (mload (w2n w) s) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand op t = SOME (mload (w2n w) s) /\ op_prov G' op = NONE /\ op_taint tn' op = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!q. q <> x ==> lookup_var q t = lookup_var q s /\
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q)) /\
    (!q. not_fresh_at sa q ==> q <> x)
Proof
  strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  drule (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MLOAD [Var p] [tmp]` >>
  qabbrev_tac `u = update_var tmp (mload (w2n w) s) s` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),gf,tf)` by
    (rpt gen_tac >> simp[Abbr `gf`,Abbr `tf`] >>
     qpat_assum `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     irule create_checked_step_path >> simp[] >>
     gvs[Abbr `i`,Abbr `u`,emitHelperPropsTheory.step_MLOAD,
         exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo,
         mk_inst_def,is_terminator_def,mem_safe_step_non_invoke,inst_mem_below_frontier_def,
         inst_dload_in_section_def,source_memory_read_ranges_def,source_memory_write_ranges_def]) >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[mem_word_taint_def,pred_setTheory.EXTENSION] >> qx_gen_tac `k` >>
     Cases_on `k < 32` >> simp[] >>
     `w2n w <= k + w2n w /\ k + w2n w < w2n w + 32` by decide_tac >>
     metis_tac[]) >>
  `gf = DRESTRICT G (COMPL {tmp}) /\ tf = tn with t_var := tn.t_var |+ (tmp,{})` by
    simp[Abbr `gf`,Abbr `tf`,Abbr `i`,Abbr `u`,assignBasePtrStoragePathTheory.assign_base_mload_ghost] >>
  qexistsl [`tmp`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`gf`,`tf`] >>
  qpat_x_assum `tmp = STRING _ _` SUBST_ALL_TAC >>
  simp[Abbr `u`,loweringShapeRulesTheory.fresh_output_props,update_var_def,lookup_var_def,
       eval_operand_def,op_prov_def,op_taint_def,finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem blueprint_raw_header_path:
  emit_op MLOAD [Var p] sa = (len,sm) /\ emit_op ADD [Var p;Lit 32w] sm = (data,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ not_fresh_at sa p /\
  eval_operand (Var p) s = SOME (n2w b) /\ mload b s = n2w (LENGTH bs) /\
  ptr_covers G tn p s (32 + LENGTH bs) /\ b + 32 < dimword (:256) /\
  b + 32 + LENGTH bs <= s.vs_alloca_next /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?l q z Gz tz. len = Var l /\ data = Var q /\ not_fresh_at sb l /\ not_fresh_at sb q /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_prov Gz len = NONE /\ op_taint tz len = {} /\
    eval_operand data z = SOME (n2w (b + 32)) /\ op_prov Gz data = op_prov G (Var p) /\
    ptr_covers Gz tz q z (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) z.vs_memory = bs /\
    (!i. b + 32 <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tz.t_mem) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (tz with t_var := tn.t_var) = tn /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn p s 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `32 + LENGTH bs` >> simp[]) >>
  `!i. b <= i /\ i < b + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> `i < b + 32 + LENGTH bs` by decide_tac >> metis_tac[]) >>
  `b + 32 <= s.vs_alloca_next` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `w2n (n2w b : bytes32) + 32 <= s.vs_alloca_next /\
   (!i. w2n (n2w b : bytes32) <= i /\ i < w2n (n2w b : bytes32) + 32 ==> i NOTIN tn.t_mem)` by simp[] >>
  drule_all create_clean_mload_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`l`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `p <> l /\ op_taint tn (Var p) = {}` by metis_tac[ptr_covers_def] >>
  `eval_operand (Var p) u = SOME (n2w b) /\ op_taint tu (Var p) = {}` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Lit 32w) u = SOME 32w /\ op_taint tu (Lit 32w) = {} /\
   op_prov Gu (Lit 32w) = NONE` by simp[eval_operand_def,op_taint_def,op_prov_def] >>
  `allocas_from lo u = allocas_from lo s /\ allocas_below_fmp u = allocas_below_fmp s` by
    (qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms,update_var_def,allocas_from_def,allocas_below_fmp_def]) >>
  `allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
   ~u.vs_halted /\ u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[update_var_def] >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`q`,`z`,`Gz`,`tz`] strip_assume_tac)) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_emit_op,ci_mono_def,pairTheory.SND] >>
  `l <> q /\ not_fresh_at sb l` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> x <> l /\ x <> q` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `FLOOKUP Gz q = FLOOKUP G p` by fs[op_prov_def] >>
  `ptr_covers Gz tz q z (LENGTH bs)` by
    (`?base cap. FLOOKUP G p = SOME (base,cap)` by metis_tac[ptr_covers_def] >>
     qpat_assum `ptr_covers _ _ _ _ (32 + LENGTH bs)`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         assignBasePtrOffsetTheory.assign_base_ptr_covers_offset_address)) >>
     disch_then irule >>
     fs[eval_operand_def] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists `32` >> simp[update_var_def,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
     metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `tz with t_var := tn.t_var = tn` by
    (qpat_assum `tu with t_var := _ = tn` (mp_tac) >> simp[taint_component_equality]) >>
  `z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\ z.vs_memory = s.vs_memory /\
   z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `z = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms,update_var_def,venom_state_component_equality]) >>
  qexistsl [`l`,`q`,`z`,`Gz`,`tz`] >>
  simp[op_prov_def,wordsTheory.word_add_n2w] >>
  simp[eval_operand_def,lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- (qpat_x_assum `op_prov Gu len = NONE` mp_tac >> simp[op_prov_def]) >>
  conj_tac >- (qpat_x_assum `op_taint tu len = {}` mp_tac >> simp[]) >>
  `tu.t_mem = tn.t_mem` by
    (qpat_assum `tu with t_var := _ = tn` mp_tac >> simp[taint_component_equality]) >>
  qx_gen_tac `k` >> strip_tac >> `b <= k /\ k < b + 32 + LENGTH bs` by decide_tac >> metis_tac[]
QED

(* A folded offset performs no target instructions, but does contribute
   a successful source operand to the replay of the later list. *)
Theorem blueprint_offset_cut[local]:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\
  expr_type e = BaseT (UintT 256) /\
  (case expr_int_literal (origin_fold_value e) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv (expr_type e) e) sa = (op,sb) /\
  (case expr_int_literal (origin_fold_value e) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)) sh = (op,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t ow marks.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    expr_sim_inv cenv cx env ee /\
    dest_NumV v = SOME (w2n ow) /\ eval_operand op t = SOME ow /\
    op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
    (!x. op = Var x ==> not_fresh_at sb x) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next v) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >> Cases_on `expr_int_literal (origin_fold_value e)`
  >- (fs[] >> irule create_body_operand_cut_replay >>
      rpt (goal_assum (drule_at Any)) >> simp[] >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
        by fs[storage_trace_domain_def] >>
      qpat_assum `!H. _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
      drule_all create_word_cut_facts >> strip_tac >>
      `op_prov G1 op = NONE` by fs[ptr_val_ok_def,loweringPostsTheory.post_value_type_def] >>
      `wb_frame cenv es ee sa s t` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
      qpat_assum `!v ee G1 tn1 t ow marks. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
      simp[exprSimSendTheory.uint256_typed_dest] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `marks` >> simp[] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      fs[loweringPostsTheory.expr_post_def]) >>
  rename1 `expr_int_literal (origin_fold_value e) = SOME i` >>
  `bind (eval_expr cx e) (read_result cx) = return (IntV i)` by
    simp[FUN_EQ_THM,blueprintLiteralOffsetPropsTheory.blueprint_literal_offset_read,return_def] >>
  `dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32))` by
    metis_tac[blueprintLiteralOffsetPropsTheory.blueprint_literal_offset_word] >>
  gvs[comp_return_def,bind_return] >>
  qpat_assum `!v ee G1 tn1 t ow marks. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[eval_operand_def,op_taint_def,op_prov_def,exprSimWordArgsTheory.wb_frame_refl,
       wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `[]` >> simp[return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules]
QED

(* The size/count window is recovered at the actual endpoint of the
   scalar reads, not assumed to survive arbitrary evaluation. *)
Theorem blueprint_scalar_suffix_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target_e::amount::(salts ++ offset::ctor)) dflt) entry /\
  expr_sim_inv cenv cx env es /\ body_exprs_full_ok cx (amount::(salts ++ [offset])) /\
  expr_type amount = BaseT (UintT 256) /\ expr_type offset = BaseT (UintT 256) /\
  (if salted then ?e. salts = [e] /\ expr_type e = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sn) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shn) /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv (expr_type offset) offset) sn = (off,sb) /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type offset)
       (gas_shadow_expr offset)) shn = (off,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sn shn /\
  gas_shadow_state sb shb /\ gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shn shadow_func /\
  fn_has_code shn shb shadow_func /\ ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) /\ (!l. target <> Label l) /\
  (!x. args_ptr = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\ LENGTH args < 2 ** 64 /\
  (!av sv ov. storage_trace_frame (next av sv ov)) /\
  (!av sv ov ee G1 tn1 t gs.
    (!tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args)) /\
  (!av sv ov yw sw ow ee G1 tn1 t marks.
    dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\
    dest_NumV ov = SOME (w2n ow) /\ IS_SOME sv = salted /\
    blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)) =
      IS_SOME (expr_int_literal (origin_fold_value offset)) /\
    eval_operand target t = SOME aw /\ op_taint tn1 target = {} /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    eval_operand off t = SOME ow /\ op_taint tn1 off = {} /\ op_prov G1 off = NONE /\
    (!x. MEM (Var x) [target;off;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ expr_sim_inv cenv cx env ee /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    return_buf_frame d cenv sb t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next av sv ov) (ee,t,G1,tn1) Q
      (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_exprs cx (amount::(salts ++ [offset])))
      (\vs. next (HD vs) (if salted then SOME (EL 1 vs) else NONE) (LAST vs)))
    (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env amount es` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env offset es` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `LENGTH salts = (if salted then 1 else 0)` by (Cases_on `salted` >> gvs[]) >>
  drule_all blueprintLiteralOffsetPropsTheory.blueprint_offset_literal_bit >> strip_tac >>
  qpat_x_assum `body_exprs_full_ok _ (amount::_)` mp_tac >>
  rewrite_tac[Once body_exprs_full_ok_def] >> strip_tac >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac >-
    simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexistsl [`cenv`,`d`,`env`,`y`,`sa`,`sm`,`sh`,`shadow_func`,`shm`,`tops`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `lower_value _ _ _ _ _` >>
       qpat_assum `expr_type amount = _` (fn th => once_rewrite_tac [GSYM th]) >>
       first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`av`,`em`,`Gm`,`tm`,`m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ma` strip_assume_tac) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ _` (drule_then assume_tac) >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  qabbrev_tac `yw = typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  `dest_NumV av = SOME (w2n yw)` by simp[Abbr `yw`,exprSimSendTheory.uint256_typed_dest] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\ sn.cs_next_var <= sb.cs_next_var`
    by fs[ci_mono_def] >>
  `ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `!z. (target = Var z \/ args_ptr = Var z \/ cnt = Var z) ==> not_fresh_at sb z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> decide_tac) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,arithmeticTheory.LESS_EQ_TRANS] >>
  qsuff_tac `!sv sw en n Gn tnn mn.
    IS_SOME sv = salted /\ dest_optional_salt sv = SOME sw /\
    OPTREL (\op w. eval_operand op n = SOME w /\ op_taint tnn op = {} /\
      (!x. op = Var x ==> not_fresh_at sn x) /\ (!l. op <> Label l)) sop sw /\
    body_const_cells_agree [(NONE,tops)] cx env en /\
    expr_sim_inv cenv cx env en /\ body_expr_full_ok cx offset /\
    storage_trace_domain cx st0 en.storage_trace /\
    (!H. valid_horizon cx st0 H en.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx en n /\
      storage_well_formed_on cx en (FST H) /\ ghost_inv_at (DF H) lo d cenv cx en Gn tnn n /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) mn (OK n,Gn,tnn)) /\
    ~n.vs_halted /\ n.vs_current_bb = sn.cs_current_bb /\ n.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func n /\ return_buf_frame d cenv sn n /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp n) /\
    (!fn i z. frag_reachable ctx func n fn i z ==> dalloca_fmp_headroom i z) /\
    s.vs_alloca_next <= n.vs_alloca_next /\ wb_frame cenv es en sa s n /\
    ghost_kept_at lo cenv es sa G tn s Gn tnn /\
    eval_operand y n = SOME yw /\ op_taint tnn y = {} /\
    (!ov ee go.
      (!tail. eval_exprs cx [offset] (en with gas_obs := go ++ tail) = (INL [ov],ee with gas_obs := tail)) ==>
      ?gs. !tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
        (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (bind (eval_expr cx offset) (read_result cx)) (next av sv))
      (en,n,Gn,tnn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))`
  >- suspend "scalar_salt" >>
  suspend "scalar_offset"
QED

Resume blueprint_scalar_suffix_cut[scalar_salt]:
  disch_tac >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  Cases_on `salted` >> PURE_REWRITE_TAC [COND_CLAUSES] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES])
  >- (qpat_x_assum `?e. salts = [e] /\ _`
        (qx_choose_then `salt` (fn shape =>
           assume_tac (cj 2 shape) >> SUBST_ALL_TAC (cj 1 shape))) >>
      qpat_assum `expr_type salt = _` (fn ty =>
        map_every (fn pat => qpat_x_assum pat
          (assume_tac o SIMP_RULE (srw_ss())
            [compile_create_salt_def,gas_shadow_expr_type,ty]))
          [`compile_create_salt compile_expr cenv _ sm = _`,
           `compile_create_salt compile_expr (gas_shadow_env T cenv) _ shm = _`]) >>
      suspend "salt_some") >>
  qpat_x_assum `salts = []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_salt compile_expr cenv NONE sm = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
     PURE_REWRITE_RULE [compile_create_salt_def,comp_return_def,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `compile_create_salt compile_expr (gas_shadow_env T cenv) _ shm = _`
    (SUBST_ALL_TAC o SYM o cj 2 o
     PURE_REWRITE_RULE [optionTheory.OPTION_MAP_DEF,compile_create_salt_def,
                        comp_return_def,pairTheory.PAIR_EQ]) >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  PURE_REWRITE_TAC [APPEND] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  qpat_assum `eval_exprs cx [] = return []` (fn empty =>
    simp[NoAsms,empty,bind_assoc,bind_return,ETA_THM]) >>
  once_rewrite_tac[GSYM bind_assoc] >> rewrite_tac[ETA_THM] >>
  fs[Once body_exprs_full_ok_def] >>
  qpat_assum `!en n Gn tnn mn. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[dest_optional_salt_def] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexists `ma` >> simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  map_every qx_gen_tac [`ov`,`ef`,`go`] >> disch_tac >>
  qexists `gas_explicit ma s.vs_gas_readings ++ go` >>
  irule create_eval_exprs_cons_replay >> qexists `em` >> simp[]
QED

Resume blueprint_scalar_suffix_cut[salt_some]:
  rename1 `expr_type salt = BaseT (BytesT (Fixed 32))` >>
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt sm` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) shm` >>
  gvs[comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt sm = (sop1,sn)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr salt) _ = (sop1,shn)` >>
  `expr_body_pre cenv cx env salt em` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  fs[Once body_exprs_full_ok_def] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac >-
    simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexistsl [`cenv`,`d`,`env`,`sop1`,`sm`,`sn`,`shm`,`shadow_func`,`shn`,`tops`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`sv`,`en`,`Gn`,`tnn`,`n`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ms` strip_assume_tac) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ _` (drule_then assume_tac) >>
  `is_word_type (BaseT (BytesT (Fixed 32)))` by simp[is_word_type_def] >>
  `lower_value compile_expr cenv (expr_type salt) salt sm = (sop1,sn)` by simp[] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) es.storage_trace`
    by (fs[storage_trace_domain_def] >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `eval_operand y m = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  qabbrev_tac `sw = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `dest_create_salt sv = SOME sw` by
    (simp[Abbr `sw`] >> irule create_salt_word >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,Once vyperInterpreterTheory.evaluate_def,bind_assoc,bind_return,ETA_THM] >>
  once_rewrite_tac[GSYM bind_assoc] >> rewrite_tac[ETA_THM] >>
  qpat_assum `!sv sw en n Gn tnn mn. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[dest_optional_salt_def,optionTheory.OPTREL_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexists `ma ++ ms` >> gen_tac >> disch_tac >>
      irule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
      qexistsl [`Gm`,`m`,`(OK m,Gm,tm)`,`tm`] >> simp[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`ov`,`ef`,`go`] >> disch_tac >>
      qexists `gas_explicit ma s.vs_gas_readings ++ (gas_explicit ms m.vs_gas_readings ++ go)` >>
      irule create_eval_exprs_cons_replay >> qexists `em` >> simp[] >>
      irule create_eval_exprs_cons_replay >> qexists `en` >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env en`
    by (irule create_operand_const_cells_replay >> rpt (goal_assum (drule_at Any))) >>
  qpat_x_assum `body_exprs_full_ok cx [offset]` mp_tac >>
  rewrite_tac[Once body_exprs_full_ok_def] >> simp[]
QED

Resume blueprint_scalar_suffix_cut[scalar_offset]:
  map_every qx_gen_tac [`sv`,`sw`,`en`,`n`,`Gn`,`tnn`,`mn`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env offset en` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  irule blueprint_offset_cut >>
  rpt (goal_assum (drule_at Any)) >> conj_tac
  >- (qpat_assum `!av sv ov. storage_trace_frame (next av sv ov)`
        (qspecl_then [`av`,`sv`] ACCEPT_TAC)) >>
  qexistsl [`cenv`,`d`,`env`,`off`,`sn`,`sb`,`shn`,`shadow_func`,`shb`,`tops`] >>
  simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `lower_value _ _ _ _` >>
       qpat_assum `expr_type offset = _` (fn th => once_rewrite_tac [GSYM th]) >>
       first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`ov`,`ee`,`G1`,`tn1`,`t`,`ow`,`mo`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. eval_exprs cx [offset]
       (en with gas_obs := gas_explicit mo n.vs_gas_readings ++ tail) =
       (INL [ov],ee with gas_obs := tail)` by
    (gen_tac >> once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     pure_once_rewrite_tac[bind_def] >>
     simp[Once vyperInterpreterTheory.evaluate_def,bind_return,return_def]) >>
  qpat_assum `!ov ee go. _ ==> ?gs. _` (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon en.storage_trace) en.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon en.storage_trace) es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >> simp[] >> conj_tac
     >- (qexistsl [`storage_trace_horizon en.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`Gn`,`en`,`n`,`sn`,`tnn`] >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `eval_operand target t = SOME aw /\ op_taint tn1 target = {}` by
    (qpat_assum `eval_operand target s = SOME aw`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  `!x. y = Var x ==> not_fresh_at sn x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `eval_operand y t = SOME yw /\ op_taint tn1 y = {}` by
    (qpat_assum `eval_operand y n = SOME yw`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  `OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
   (!x. sop = SOME (Var x) ==> not_fresh_at sb x)` by
    (namedCases_on `sop` ["","salt_op"] >> Cases_on `sw` >>
     qpat_x_assum `OPTREL _ _ _`
       (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [optionTheory.OPTREL_def]) >>
     simp[optionTheory.OPTREL_def] >>
     conj_tac
     >- (qpat_assum `eval_operand salt_op n = SOME _`
           (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
     rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sn` >> simp[]) >>
  qpat_assum `!av sv ov ee G1 tn1 t gs. _ ==> eval_operand cnt _ = _ /\ _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  `!z. y = Var z ==> not_fresh_at sb z` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qpat_assum `!av sv ov yw sw ow ee G1 tn1 t marks. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[] >> conj_tac
  >- (simp[MEM] >> rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (simp[NoAsms,MEM] >> qx_gen_tac `x` >>
      map_every (fn pat => qpat_assum pat (qspec_then `x` mp_tac))
        [`!z. target = Var z \/ args_ptr = Var z \/ cnt = Var z ==> not_fresh_at sb z`,
         `!z. off = Var z ==> not_fresh_at sb z`,
         `!z. y = Var z ==> not_fresh_at sb z`,
         `!z. sop = SOME (Var z) ==> not_fresh_at sb z`] >>
      rpt (pop_assum kall_tac) >> metis_tac[EQ_SYM_EQ]) >>
  qexists `mn ++ mo` >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ _ /\ _ /\ gas_origin_ptr_path _ _ mo _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  irule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
  qexistsl [`Gn`,`n`,`(OK n,Gn,tnn)`,`tnn`] >> simp[]
QED

Finalise blueprint_scalar_suffix_cut

Theorem blueprint_raw_args_parts[local]:
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((dp,len),sb) ==>
  ?vv sm sv ss ptr su sn.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
    unwrap_value cenv sv ss = (ptr,su) /\
    emit_op MLOAD [ptr] su = (len,sn) /\ emit_op ADD [ptr; Lit 32w] sn = (dp,sb)
Proof
  simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

(* Convert the byte representation into the precise input of the two
   header instructions. The static bound comes from the location, not
   from the ghost provenance entry alone. *)
Theorem blueprint_raw_header_input[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
     SOME (BaseTV (BytesT (Dynamic n))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op s /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sb es (BytesV bs) op s /\
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s ==>
  ?p w. op = Var p /\ eval_operand (Var p) s = SOME w /\
    mload (w2n w) s = n2w (LENGTH bs) /\
    ptr_covers G tn p s (32 + LENGTH bs) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 + LENGTH bs <= s.vs_alloca_next /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all exprSimConvertFromBytesTheory.dynamic_bytes_operand_memory >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  `op_taint tn op = {} /\ ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s` by
    fs[ptr_val_ok_def,is_word_type_def] >>
  drule_all rawCallBufferPtrTheory.ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all rawCallBufferPtrTheory.ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  `w2n w + 32 + LENGTH bs <= s.vs_alloca_next` by
    (`~is_word_type (BaseT (BytesT (Dynamic n)))` by simp[is_word_type_def] >>
     drule_all abiEncodeOwnershipTheory.abi_encode_owned_footprint_frontier >>
     simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    fs[stmt_state_rel_def,alloca_room_def] >>
  `lookup_var x s = SOME w /\ op_taint tn (Var x) = {}` by fs[eval_operand_def] >>
  `ptr_covers G tn x s (32 + LENGTH bs)` by
    (simp[ptr_covers_def] >> qexistsl [`w`,`b`,`sz`] >> simp[] >> decide_tac) >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  qexistsl [`x`,`w`] >> simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload,eval_operand_def] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `i < w2n w + 32`
  >- metis_tac[] >>
  `w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs` by decide_tac >> metis_tac[]
QED

(* The raw snapshot is sized by the returned tag, not by the physical
   type of the source window. Both possible tags have their own fit proof. *)
Theorem blueprint_raw_snapshot_type[local]:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL (BytesV bs),ee) ==>
  ?k. vv_type vv = BaseT (BytesT (Dynamic k)) /\
    evaluate_type (get_tenv cx) (vv_type vv) = SOME (BaseTV (BytesT (Dynamic k))) /\
    value_has_type (BaseTV (BytesT (Dynamic k))) (BytesV bs) /\ LENGTH bs <= k /\
    type_memory_bytes ce (vv_type vv) = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    0 < type_memory_bytes ce (vv_type vv) /\ type_memory_bytes ce (vv_type vv) < 2 ** 64
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type ce e` by
    (`well_typed_expr env e /\
      (!id t. FLOOKUP env.var_types id = SOME t ==>
         ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz))` by
       (drule_then strip_assume_tac expr_body_pre_static_facts >>
        fs[expr_sim_inv_def]) >>
     `reason_uniform_shape compile_expr ce (expr_type e) e` by
       metis_tac[exprReasonOperandTheory.compile_expr_reason_uniform] >>
     qpat_x_assum `reason_uniform_shape _ _ _ _`
       (qx_choosel_then [`loc`,`t`] (map_every assume_tac o CONJUNCTS) o
        REWRITE_RULE [exprReasonOperandTheory.reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[exprReasonOperandTheory.reason_result_shape_def,vv_type_def]) >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  Cases_on `vv_type vv = expr_type e`
  >- (drule_all exprSimHypsTheory.memory_rhs_read_annotation_typed >>
      simp[value_runtime_typed_def] >> strip_tac >>
      drule expr_body_pre_env_type_defs >> strip_tac >>
      `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by metis_tac[] >>
      drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> strip_tac >>
      `tv = BaseTV (BytesT (Dynamic n))` by
        metis_tac[abiValueEncodingTheory.evaluate_type_base_result] >>
      gvs[vyperTypingTheory.value_has_type_def,valueEncodingTheory.type_memory_size_def]) >>
  `?k. lowered_value_type ce e = BaseT (BytesT (Dynamic k))` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >>
     simp[] >> Cases_on `lowered_value_type ce e` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT bt) _` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT (BytesT b)) _` >> Cases_on `b` >> simp[arg_type_fits_def]) >>
  drule_all abiEncodeArgsCaseTheory.abi_args_success_ready >>
  disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `tv = BaseTV (BytesT (Dynamic k))` by
    metis_tac[abiValueEncodingTheory.evaluate_type_base_result] >>
  gvs[vyperTypingTheory.value_has_type_def,valueEncodingTheory.type_memory_size_def]
QED

(* Uncopied bytes can point into the locals. Recover the original
   header view at the actual suffix endpoint, rather than pretending
   the local alias is a separately owned allocation. *)
Theorem blueprint_raw_borrowed_window[local]:
  body_inv tops ctx ce cx /\ ~exprs_can_mutate ce later /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs later) /\
  (!tail. eval_exprs cx later (es with gas_obs := gs ++ tail) =
            (INL vs,ee with gas_obs := tail)) /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  stmt_state_rel (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\
  local_ptrs_reserved ce sh /\ su.cs_next_id <= sh.cs_next_id /\ ci_mono sh ss /\
  wb_frame ce es es sh s z /\ ghost_kept_at lo ce es sh G tn s Gz tz /\
  wb_frame ce es ee ss z t /\ ghost_kept_at lo ce es ss Gz tz z G1 tn1 /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME (BaseTV (BytesT (Dynamic n))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) (Var p) s /\
  expr_val_at ce cx (BaseT (BytesT (Dynamic n))) sa su es (BytesV bs) (Var p) s /\
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) (Var p) G tn s /\
  not_fresh_at sh p /\ eval_operand (Var p) s = SOME w /\
  not_fresh_at ss l /\ not_fresh_at ss q /\
  eval_operand (Var l) z = SOME (n2w (LENGTH bs)) /\
  op_taint tz (Var l) = {} /\ op_prov Gz (Var l) = NONE /\
  lookup_var q z = SOME (n2w (w2n w + 32)) /\ ptr_covers Gz tz q z (LENGTH bs) ==>
  eval_operand (Var l) t = SOME (n2w (LENGTH bs)) /\
  op_taint tn1 (Var l) = {} /\ op_prov G1 (Var l) = NONE /\
  ?a. lookup_var q t = SOME a /\ ptr_covers G1 tn1 q t (LENGTH bs) /\
      (bs = [] \/ w2n a + LENGTH bs <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH bs) t = bs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee.scopes = es.scopes` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all targetPureWalkSourceTheory.nonmutating_exprs_source_frame >> simp[]) >>
  `wb_frame ce es ee sh s t /\ ghost_kept_at lo ce es sh G tn s G1 tn1` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame ce es ee ss z t` (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce es sh G tn s Gz tz` (irule_at Any) >> simp[]) >>
  `expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) (Var p) t /\
   expr_val_at ce cx (BaseT (BytesT (Dynamic n))) sa su ee (BytesV bs) (Var p) t /\
   ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) (Var p) G1 tn1 t` by
    (irule bodyFullAbiEncodeBorrowedTheory.abi_encode_borrowed_operand_retained >>
     qpat_assum `wb_frame ce es ee sh s t` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce es sh G tn s G1 tn1` (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s` (irule_at Any) >>
     qpat_assum `stmt_state_rel H1 ctx func ce cx ee t` (irule_at Any) >>
     simp[] >> qexists `env` >> simp[]) >>
  `eval_operand (Var p) t = SOME w` by
    (fs[eval_operand_def] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `FLOOKUP G1 l = FLOOKUP Gz l /\ FLOOKUP G1 q = FLOOKUP Gz q /\
   op_taint tn1 (Var l) = op_taint tz (Var l) /\
   op_taint tn1 (Var q) = op_taint tz (Var q)` by fs[ghost_kept_at_def] >>
  `eval_operand (Var l) t = SOME (n2w (LENGTH bs))` by
    (fs[eval_operand_def] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `lookup_var q t = lookup_var q z` by metis_tac[exprSimWordArgsTheory.wb_frame_vars] >>
  `ptr_covers G1 tn1 q t (LENGTH bs)` by fs[ptr_covers_def] >>
  drule_all blueprint_raw_header_input >>
  disch_then (qx_choosel_then [`x`,`u`] (map_every assume_tac o CONJUNCTS)) >>
  `x = p` by fs[] >>
  `u = w` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `u = w` SUBST_ALL_TAC >>
  `!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >> `w2n w <= i` by decide_tac >> metis_tac[]) >>
  `w2n (n2w (w2n w + 32) : bytes32) = w2n w + 32` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  fs[op_prov_def,memoryReadPropsTheory.read_memory_eq_mem_bytes_at]
QED

(* The destination ALLOCA uses the returned tag. The source unwrap
   still uses the child's checked post/physical type pair. *)
Theorem blueprint_raw_copy_store_entry[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) sm = (buf,sn) /\
  unwrap_value ce vv sn = (op,sc) /\
  fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_bytes ce (vv_type vv) < dimword (:256) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
  0 < type_memory_size ltv /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  read_result cx tv ee = (INL (BytesV bs),ee) /\
  value_has_type ptv (BytesV bs) /\ value_has_type ltv (BytesV bs) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sm s /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q dw z Gz tz x sw.
    buf.buf_operand = Var q /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       expr_post H ctx func ce cx e es sa sc s0 ee (BytesV bs) op z /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s /\
         FLOOKUP Gz v = FLOOKUP G v /\ op_taint tz (Var v) = op_taint tn (Var v)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ return_buf_frame d ce sc z /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\
    ptr_covers Gz tz q z (type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP Gz q = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (vv_type vv)))] [q]) (fn_insts func) /\
    lo <= w2n dw /\ w2n dw + type_memory_bytes ce (vv_type vv) <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    op = Var x /\ not_fresh_at sc x /\ lookup_var x z = SOME sw /\
    val_wf ltv (BytesV bs) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory ltv (BytesV bs) (w2n sw) mem) /\
    ptr_covers Gz tz x z (type_memory_size ltv) /\ w2n sw + type_memory_size ltv <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
     simp[loweringShapeRulesTheory.emit_op_eq] >> strip_tac >> gvs[]) >>
  drule_all bodyFullExtCallDefaultAllocTheory.extcall_default_alloc_cut >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`q`,`dw`,`u`,`Ga`,`ta`] (map_every assume_tac o CONJUNCTS))) >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e es sa sm s0 ee tv vv s` by
    (qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >> simp[]) >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type ptv v /\ value_has_type ltv v` by simp[] >>
  mp_tac (Q.INST [`n` |-> `type_memory_bytes ce (vv_type vv)`, `cenv` |-> `ce`]
    bodyFullExtCallDefaultUnwrapTheory.extcall_default_unwrap_store_entry) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`v`,`z`,`Gz`,`tz`,`sw`] (map_every assume_tac o CONJUNCTS)) >>
  `v = BytesV bs` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
  `!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s /\
       FLOOKUP Gz v = FLOOKUP G v /\ op_taint tz (Var v) = op_taint tn (Var v)` by
    (qx_gen_tac `v'` >> strip_tac >>
     `not_fresh_at sn v'` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  `?x. op = Var x /\ ptr_covers Gz tz x z (type_memory_size ltv)` by fs[] >>
  `z.vs_labels = s.vs_labels` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `return_buf_frame d ce sc z` by suspend "retbuf" >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (vv_type vv)))] [q]) (fn_insts func)` by
    suspend "site" >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo z` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  qexistsl [`q`,`dw`,`z`,`Gz`,`tz`,`x`,`sw`] >>
  simp[eval_operand_def] >> rpt conj_tac
  >- suspend "path"
  >- suspend "old_allocas"
  >> fs[eval_operand_def]
QED

Resume blueprint_raw_copy_store_entry[retbuf]:
  `sn.cs_next_var <= sc.cs_next_var` by metis_tac[ci_mono_unwrap_value,ci_mono_def,pairTheory.SND] >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qpat_assum `return_buf_frame d ce sm s` (irule_at Any) >> simp[] >> decide_tac
QED

Resume blueprint_raw_copy_store_entry[site]:
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[loweringPostsTheory.vv_post_def] >>
  drule_all_then strip_assume_tac bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  gvs[]
QED

Resume blueprint_raw_copy_store_entry[path]:
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Resume blueprint_raw_copy_store_entry[old_allocas]:
  metis_tac[cj 2 (iffLR loweringPostsTheory.wb_frame_def)]
QED

Finalise blueprint_raw_copy_store_entry

(* Store at the snapshot tag, reading from the separately sized physical
   source. The cumulative frames are based before allocation of dst. *)
Theorem blueprint_raw_copy_store_exit[local]:
  compile_store_memory ce (Var src) (Var dst) dt dt sc = ((),sb) /\
  dt = BaseT (BytesT (Dynamic cap)) /\ tv = BaseTV (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) dt = SOME tv /\ value_has_type tv (BytesV bs) /\
  is_bytestring_type sty /\ evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type stv (BytesV bs) /\ val_wf stv (BytesV bs) /\ LENGTH bs <= cap /\
  type_memory_bytes ce dt = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  not_fresh_at sc src /\ not_fresh_at sc dst /\
  lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv (BytesV bs) (w2n sw) mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\ ptr_covers G tn dst s (type_memory_size tv) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n dw /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
  FLOOKUP G dst = SOME (w2n dw,type_memory_size tv) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [dst]) (fn_insts func) /\
  sa.cs_next_id <= aid /\ aid < sc.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sc /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  return_buf_frame d ce sc s /\ wb_frame ce es ee sa s0 s /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tm)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at (DF H) lo d ce cx ee Gf tm u) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tm /\ wb_frame ce es ee sa s0 u /\
    return_buf_frame d ce sb u /\ alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    aid < sb.cs_next_id /\ not_fresh_at sb dst /\ lookup_var dst u = SOME dw /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
    FLOOKUP Gf dst = SOME (w2n dw,type_memory_size tv) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    ptr_covers Gf tm dst u (type_memory_size tv) /\
    ptr_val_ok cx dt (BytesV bs) (Var dst) Gf tm u /\ val_wf tv (BytesV bs) /\
    val_footprint tv (BytesV bs) <= type_memory_size tv /\
    eval_operand (Var dst) u = SOME dw /\ mload (w2n dw) u = n2w (LENGTH bs) /\
    ptr_covers Gf tm dst u (32 + LENGTH bs) /\ w2n dw + 32 < dimword (:256) /\
    w2n dw + 32 + LENGTH bs <= u.vs_alloca_next /\
    mem_bytes_at (w2n dw + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tm.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type dt /\ ~is_word_type dt` by simp[is_bytestring_type_def,is_word_type_def] >>
  `32 + LENGTH bs <= type_memory_size tv` by
    (mp_tac (Q.SPEC `cap` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >>
     simp[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `val_wf tv (BytesV bs) /\ val_footprint tv (BytesV bs) <= type_memory_size tv` by
    (gvs[valueEncodingDefsTheory.val_wf_def,loweringPostsTheory.val_footprint_def] >> decide_tac) >>
  `type_memory_size tv + 64 < dimword (:256)` by (gvs[] >> decide_tac) >>
  `compile_store_memory ce (Var src) (Var dst) dt sty sc = ((),sb)` by
    (qpat_assum `compile_store_memory _ _ _ dt dt _ = _` mp_tac >>
     gvs[contextTheory.compile_store_memory_def,compileEnvTheory.is_bytestring_type_def,is_word_type_def]) >>
  drule_all bodyFullExtCallDefaultBytesStoreTheory.extcall_default_bytes_store_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gf`,`tm`] (map_every assume_tac o CONJUNCTS))) >>
  `typed_copy_state_frame sc (w2n dw) (type_memory_size tv) s u` by
    suspend "copy_frame" >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    gvs[venom_state_component_equality] >>
  `ci_mono sc sb` by
    (mp_tac (Q.SPECL [`ce`,`Var src`,`Var dst`,`dt`,`dt`,`sc`]
       ci_mono_compile_store_memory) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >> simp[]) >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  `ptr_covers Gf tm dst u (type_memory_size tv)` by suspend "covers" >>
  `allocas_non_overlapping s` by fs[venomMemDefsTheory.alloca_inv_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
      b+len <= w2n dw \/ w2n dw + type_memory_size tv <= b` by suspend "old_locals" >>
  `!D. ghost_inv_at D lo d ce cx ee G tn s ==>
     ghost_inv_at D lo d ce cx ee Gf tm u /\ ghost_kept_at lo ce es sa Gi ti s0 Gf tm` by
    suspend "ghost" >>
  `ghost_kept_at lo ce es sa Gi ti s0 Gf tm` by suspend "kept" >>
  qexistsl [`u`,`Gf`,`tm`] >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "semantic" >>
  conj_tac >- suspend "wb" >>
  conj_tac >- suspend "retbuf" >>
  conj_tac >- suspend "history" >>
  suspend "owner_and_header"
QED

Resume blueprint_raw_copy_store_exit[copy_frame]:
  simp[typedMemoryCopyTheory.typed_copy_state_frame_def,typedMemoryCopyTheory.typed_copy_frame_def] >>
  conj_tac >- gvs[venom_state_component_equality] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!off k. _ ==> mem_bytes_at off k u.vs_memory = _`
    (qspecl_then [`a`,`n`] irule) >>
  gvs[] >> intLib.COOPER_TAC
QED

Resume blueprint_raw_copy_store_exit[covers]:
  qpat_assum `ptr_covers G tn dst s _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
  qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _` (qspec_then `dst` mp_tac) >>
  simp[ptr_covers_def]
QED

Resume blueprint_raw_copy_store_exit[semantic]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule exprSimIfExpWidenedCountedTheory.typed_copy_semantic_frame >>
      goal_assum (drule_at (Pat `typed_copy_state_frame sc _ _ s u`)) >>
      goal_assum (drule_at (Pat `MEM _ (fn_insts func)`)) >>
      simp[venomInstTheory.mk_inst_def] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
        (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!D. ghost_inv_at D _ _ _ _ _ _ _ s ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume blueprint_raw_copy_store_exit[old_locals]:
  rpt gen_tac >> disch_tac >>
  `local_region ce ee.scopes s name b len` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qpat_assum `local_region ce es.scopes s0 name b len` (irule_at Any) >>
     qexists `sa` >> simp[] >>
     drule (cj 1 (iffLR loweringPostsTheory.wb_frame_def)) >> simp[]) >>
  qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
    (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume blueprint_raw_copy_store_exit[ghost]:
  gen_tac >> disch_tac >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
    (i IN tm.t_mem <=> i IN tn.t_mem)` by
      (rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sc x` by
    fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
  irule bodyFullStructLitFramesTheory.structlit_store_ghost_frame >>
  qpat_assum `typed_copy_state_frame sc _ _ s u` (irule_at Any) >>
  qpat_assum `ghost_inv_at D lo d ce cx ee G tn s` (irule_at Any) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
        (drule_then mp_tac) >> gvs[] >> decide_tac)
  >- (rpt gen_tac >> strip_tac >>
      `local_region ce ee.scopes s name (w2n w) sz` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      drule_all nameLoweringPropsTheory.local_ptrs_rel_value >> strip_tac >>
      `val_footprint entry.type entry.value <= sz` by
        (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
      qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
        (drule_then mp_tac) >> gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
  >> rpt gen_tac >> strip_tac >>
  drule (cj 2 (iffLR loweringPostsTheory.wb_frame_def)) >>
  disch_then (drule_then assume_tac) >>
  `aid' <> aid` by decide_tac >>
  qpat_assum `allocas_non_overlapping s`
    (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
  disch_then (qspecl_then [`aid'`,`aid`,`off`,`sz`,`w2n dw`,`type_memory_size tv`] mp_tac) >>
  gvs[] >> decide_tac
QED

Resume blueprint_raw_copy_store_exit[kept]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[storage_trace_domain_def]) >> strip_tac >>
  qpat_assum `!D. ghost_inv_at D _ _ _ _ _ _ _ s ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume blueprint_raw_copy_store_exit[wb]:
  irule abiEncodeMaterializeTheory.materialize_fresh_store_frame >>
  qpat_assum `FLOOKUP s.vs_allocas aid = SOME _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume blueprint_raw_copy_store_exit[retbuf]:
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qpat_assum `return_buf_frame d ce sc s` (irule_at Any) >> fs[ci_mono_def]
QED

Resume blueprint_raw_copy_store_exit[history]:
  irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK u,Gf,tm)`
    (qspec_then `DF (storage_trace_horizon ee.storage_trace)` (irule_at Any)) >> simp[]
QED

Resume blueprint_raw_copy_store_exit[owner_and_header]:
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    metis_tac[typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  `sc.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `not_fresh_at sb dst` by metis_tac[freshWritesTheory.not_fresh_at_mono,ci_mono_def] >>
  `FLOOKUP Gf dst = SOME (w2n dw,type_memory_size tv)` by simp[] >>
  `ptr_val_ok cx dt (BytesV bs) (Var dst) Gf tm u` by
    (irule rawCallBufferPtrTheory.ptr_val_ok_from_type_covers >>
     asm_rewrite_tac[] >> qexists `tv` >> asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  `ptr_covers Gf tm dst u (32 + LENGTH bs)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `type_memory_size tv` >> simp[]) >>
  `w2n dw + 32 < dimword (:256) /\ w2n dw + 32 + LENGTH bs <= u.vs_alloca_next` by
    (fs[] >> decide_tac) >>
  `!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len` by suspend "owner" >>
  `mload (w2n dw) u = n2w (LENGTH bs) /\
   mem_bytes_at (w2n dw + 32) (LENGTH bs) u.vs_memory = bs /\
   (!i. w2n dw <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tm.t_mem)` by
    suspend "header" >>
  gvs[eval_operand_def] >> first_assum ACCEPT_TAC
QED

Resume blueprint_raw_copy_store_exit[owner]:
  rpt gen_tac >> disch_tac >>
  `local_region ce ee.scopes s name b len` by
    (irule (iffLR loweringStateRelDefsTheory.local_region_lookup_cong) >>
     goal_assum (drule_at (Pat `local_region _ _ u _ _ _`)) >>
     rpt strip_tac >> `not_fresh_at sc p` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> simp[]) >>
  qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume blueprint_raw_copy_store_exit[header]:
  `val_in_memory tv (BytesV bs) (w2n dw) u.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule representationCleanPtrTheory.robust_val_in_memory_bytes_clean >>
  gvs[valueEncodingDefsTheory.val_in_memory_def,GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  strip_tac >> gen_tac >> strip_tac >> Cases_on `i < w2n dw + 32`
  >- (qpat_assum `!k. w2n dw <= k /\ k < w2n dw + 32 ==> _`
        (qspec_then `i` mp_tac) >> simp[]) >>
  `w2n dw + 32 <= i` by decide_tac >>
  qpat_assum `!k. w2n dw + 32 <= k /\ _ ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Finalise blueprint_raw_copy_store_exit

(* The raw argument is read before any scalar, even when its snapshot
   borrows the original bytes. Recover the window at the actual suffix exit. *)
Theorem blueprint_raw_args_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs later) /\
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T (MAP gas_shadow_expr later)
    [gas_shadow_expr e] sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!bs ee Gu tu u marks.
    LENGTH bs < 2 ** 64 /\
    (!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\
    wb_frame cenv es ee sa s u /\ ghost_kept_at lo cenv es sa G tn s Gu tu /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= u.vs_alloca_next /\
    alloca_history func u /\ return_buf_frame d cenv sb u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    (!vs ef Gf tf f gs.
      (!tail. eval_exprs cx later (ee with gas_obs := gs ++ tail) = (INL vs,ef with gas_obs := tail)) /\
      wb_frame cenv ee ef sb u f /\ ghost_kept_at lo cenv ee sb Gu tu u Gf tf /\
      MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ u.vs_alloca_next <= f.vs_alloca_next /\
      storage_trace_domain cx st0 ef.storage_trace /\
      (!H. valid_horizon cx st0 H ef.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
        storage_well_formed_on cx ef (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ef Gf tf f) ==>
      eval_operand cnt f = SOME (n2w (LENGTH bs)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bs) f = bs)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next [BytesV bs]) (ee,u,Gu,tu) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx [e]) next) (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_create_blueprint_args _ _ T later [e] _ = _`
    (mp_tac o MATCH_MP blueprint_raw_args_parts) >>
  strip_tac >>
  rename1 `compile_expr _ _ e sa = (vv,sm)` >>
  rename1 `compile_snapshot_vv _ _ vv sm = (saved,ss)` >>
  rename1 `unwrap_value _ saved ss = (op,su)` >>
  rename1 `emit_op MLOAD [op] su = (cnt,sn)` >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _`
    (mp_tac o MATCH_MP blueprint_raw_args_parts) >>
  strip_tac >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) sh = (shv,shm)` >>
  rename1 `compile_snapshot_vv _ _ shv shm = (shsaved,shs)` >>
  rename1 `unwrap_value _ shsaved shs = (shop,shu)` >>
  rename1 `emit_op MLOAD [shop] shu = (cnt,shn)` >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr e) _ = _` mp_tac >>
  rewrite_tac[gas_shadow_expr_type] >> strip_tac >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
      (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_then (drule_all_then strip_assume_tac) bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  qpat_x_assum `gas_shadow_compiles (compile_expr _ _ _) _` kall_tac >>
  gvs[gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv) >>
  strip_tac >> gvs[] >>
  drule_all (MATCH_MP bodyFullForArrayRoundTheory.nonslot_shadow_cut gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
  strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ e sa = (vv,sm)` >>
  `ci_mono sa sm /\ ci_mono sm ss /\ ci_mono ss su /\ ci_mono su sn /\ ci_mono sn sb` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`cenv`,`exprs_can_mutate cenv later`,`vv`,`sm`]
       ci_mono_compile_snapshot_vv) >>
     mp_tac (Q.SPECL [`cenv`,`saved`,`ss`] ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`MLOAD`,`[op]`,`su`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[op;Lit 32w]`,`sn`] ci_mono_emit_op) >>
     asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono sh shm /\ ci_mono shm shs /\ ci_mono shs shu /\ ci_mono shu shn /\ ci_mono shn shb` by
    (mp_tac (Q.SPECL [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`sh`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`cenv`,`exprs_can_mutate cenv later`,`vv`,`shm`]
       ci_mono_compile_snapshot_vv) >>
     mp_tac (Q.SPECL [`cenv`,`saved`,`shs`] ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`MLOAD`,`[op]`,`shu`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[op;Lit 32w]`,`shn`] ci_mono_emit_op) >>
     asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code sa sm func /\ fn_has_code sm ss func /\ fn_has_code ss su func /\
   fn_has_code su sn func /\ fn_has_code sn sb func` by
    (map_every (fn (a,b) =>
        qspecl_then [a,b,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
        (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> strip_tac)
       [(`sa`,`sm`),(`sm`,`ss`),(`ss`,`su`),(`su`,`sn`)] >> simp[]) >>
  `fn_has_code sh shm shadow_func /\ fn_has_code shm shs shadow_func /\
   fn_has_code shs shu shadow_func` by
    (map_every (fn (a,b) =>
        qspecl_then [a,b,`shb`,`shadow_func`] mp_tac fragExecTheory.fn_has_code_split >>
        (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> strip_tac)
       [(`sh`,`shm`),(`shm`,`shs`),(`shs`,`shu`)] >> simp[]) >>
  `~is_word_type (vv_type vv)` by
    (`well_typed_expr env e /\
       (!id t. FLOOKUP env.var_types id = SOME t ==>
          ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
       (drule_then strip_assume_tac expr_body_pre_static_facts >>
        fs[expr_sim_inv_def]) >>
     `reason_uniform_shape compile_expr cenv (BaseT (BytesT (Dynamic cap))) e` by
       (irule exprReasonOperandTheory.compile_expr_reason_uniform >> qexists `env` >> simp[]) >>
     qpat_x_assum `reason_uniform_shape _ _ _ _`
       (qx_choosel_then [`loc`,`t`] (map_every assume_tac o CONJUNCTS) o
        REWRITE_RULE [exprReasonOperandTheory.reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
     `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
       metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
     `is_word_type (lowered_value_type cenv e) = is_word_type (expr_type e)` by
       qpat_assum `arg_type_fits (lowered_value_type cenv e) (expr_type e)`
         (ACCEPT_TAC o MATCH_MP aggregateEvaluatedLayoutTheory.arg_type_fits_word_type) >>
     `~is_word_type t` by
       (qpat_assum `t = expr_type e \/ t = lowered_value_type cenv e`
          (DISJ_CASES_THEN SUBST1_TAC) >>
        qpat_assum `is_word_type (lowered_value_type cenv e) = is_word_type (expr_type e)`
          (PURE_ONCE_REWRITE_TAC o single) >>
        qpat_assum `expr_type e = _` (fn ty => simp[NoAsms,ty,is_word_type_def])) >>
     qpat_assum `reason_result_shape _ _ vv` mp_tac >>
     Cases_on `vv` >> simp_tac (srw_ss()) [exprReasonOperandTheory.reason_result_shape_def,vv_type_def] >>
     disch_then (SUBST1_TAC o cj 1) >>
     first_assum ACCEPT_TAC) >>
  once_rewrite_tac[exprSimAbiEncodeArgsLabelReplayTheory.abi_args_singleton_source] >>
  simp[bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  Cases_on `exprs_can_mutate cenv later`
  >- suspend "copy" >>
  gvs[compile_snapshot_vv_def,comp_return_def] >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
   lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) sh = (op,shu)` by
    simp[lower_value_def,comp_bind_def] >>
  `fn_has_code sa su func /\ fn_has_code sh shu shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split,ci_mono_def,ci_mono_trans] >>
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl [`cenv`,`d`,`env`,`op`,`sa`,`su`,`sh`,`shadow_func`,`shu`,`tops`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `lower_value _ _ _ _ _` >>
    qpat_assum `expr_type e = _` (fn th => once_rewrite_tac[GSYM th]) >>
    first_assum ACCEPT_TAC) >>
  suspend "borrow"
QED

Resume blueprint_raw_args_cut[borrow]:
  map_every qx_gen_tac [`v`,`ee`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `marks` (map_every assume_tac o CONJUNCTS)) >>
  `?bs. v = BytesV bs /\ LENGTH bs < 2 ** 64 /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_assum `!tail. monad_bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimHypsTheory.memory_rhs_read_annotation_typed) >>
     simp[value_runtime_typed_def] >> strip_tac >>
     `tv = BaseTV (BytesT (Dynamic cap))` by
       metis_tac[abiValueEncodingTheory.evaluate_type_base_result] >>
     `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
       (drule expr_body_pre_env_type_defs >> simp[] >> metis_tac[]) >>
     `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
     drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> strip_tac >>
     Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,valueEncodingTheory.type_memory_size_def] >>
     mp_tac (Q.SPEC `cap` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >> decide_tac) >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  `post_value_type cenv e = BaseT (BytesT (Dynamic cap))` by
    simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post H ctx func cenv cx e es sa su s ee _ op t /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `post_value_type cenv e = _` (fn ty_eq =>
    qpat_assum `expr_post _ ctx func cenv cx e es sa su s ee _ op t`
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.expr_post_def,ty_eq]) >>
    qpat_x_assum `ptr_val_ok cx (post_value_type cenv e) _ op G1 tn1 t`
      (assume_tac o REWRITE_RULE [ty_eq])) >>
  drule_all blueprint_raw_header_input >>
  disch_then (qx_choosel_then [`p`,`w`] (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at su p` by
    (drule_all exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  qpat_x_assum `op = Var p` SUBST_ALL_TAC >>
  drule_all (PURE_REWRITE_RULE [wordsTheory.n2w_w2n]
    (Q.INST [`b` |-> `w2n (w:bytes32)`] blueprint_raw_header_path)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = t`
    (mp_tac o Q.AP_TERM `\r. (r.vs_memory,r.vs_allocas,r.vs_alloca_next,
        r.vs_fmp,r.vs_initial_fmp,r.vs_call_ctx,r.vs_accounts,
        r.vs_transient,r.vs_immutables,r.vs_halted)`) >> simp[] >> strip_tac >>
  `state_frame z = state_frame (t with vs_inst_idx := z.vs_inst_idx)` by
    (qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = t`
      (mp_tac o Q.AP_TERM `\r:venom_state. r with <|vs_vars := FEMPTY; vs_inst_idx := z.vs_inst_idx|>`) >>
     simp[stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `tz with t_var := _ = tn1`
    (mp_tac o Q.AP_TERM `\r. (r.t_mem,r.t_stor,r.t_trans,r.t_imm)`) >> simp[] >> strip_tac >>
  `ci_mono sa su /\ ci_mono su sb` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sb.cs_next_var /\
   su.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv su` by metis_tac[local_ptrs_reserved_next_var] >>
  `wb_frame cenv ee ee su t z` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl [`su`,`t`] >> simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
  `ghost_kept_at lo cenv ee su G1 tn1 t Gz tz` by simp[ghost_kept_at_def] >>
  `wb_frame cenv es ee sa s t` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace`
       (drule_then assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H _ _ _ _ es s /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame cenv ee ee su t z` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >> simp[] >>
     qpat_assum `ghost_kept_at lo cenv ee su G1 tn1 t Gz tz` (irule_at Any) >> simp[]) >>
  `!x. ((?k. cenv.ce_return_buf = SOME (PtrVar (Var x) k)) \/
         (?k. cenv.ce_return_pc = SOME (PtrVar (Var x) k))) ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> expr_post H ctx func cenv cx e es sa su s ee _ _ t /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `expr_post H ctx func cenv cx e es sa su s ee _ _ t` (fn th =>
       drule_then assume_tac exprSimWordArgsTheory.expr_post_state >>
       assume_tac (cj 2 (REWRITE_RULE [loweringPostsTheory.expr_post_def] th))) >> simp[] >>
     conj_tac
     >- (irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ee t` (irule_at Any) >>
         qpat_assum `state_frame z = _` (irule_at Any) >>
         qexists `su` >> simp[] >> rpt strip_tac >>
         qpat_assum `!x. not_fresh_at su x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
         qexistsl [`G1`,`ee`,`t`,`su`,`tn1`] >> simp[] >> metis_tac[]) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
       (drule_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  `alloca_history func z` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (t,G1,tn1) [] (OK z,Gz,tz)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`gas_explicit_sites ctx shadow_ctx`]
         (irule_at Any)) >> simp[] >> metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `return_buf_frame d cenv sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv su t` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (disch_tac >>
     `allocas_below_fmp t` by (first_assum (fn th => drule_then ACCEPT_TAC th)) >>
     pop_assum (fn th =>
       pure_rewrite_tac[allocas_below_fmp_def] >>
       map_every (fn sel => qpat_assum sel SUBST1_TAC)
         [`z.vs_initial_fmp = t.vs_initial_fmp`,`z.vs_fmp = t.vs_fmp`,`z.vs_allocas = t.vs_allocas`] >>
       ACCEPT_TAC (REWRITE_RULE[allocas_below_fmp_def] th))) >>
  `!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (t,G1,tn1) [] (OK z,Gz,tz)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`gas_explicit_sites ctx shadow_ctx`]
         (irule_at Any)) >>
     qexists `fn` >> simp[] >> metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    qpat_assum `locals_kept cenv es ee s t`
      (ACCEPT_TAC o SYM o cj 2 o REWRITE_RULE [loweringPostsTheory.locals_kept_def]) >>
  `!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)` by
    (simp[exprSimAbiEncodeArgsLabelReplayTheory.abi_args_singleton_source] >>
     gen_tac >> simp[Once bind_def, return_def]) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gz`,`z`,`tz`] >> simp[] >>
  qpat_assum `!bs ee Gu tu u marks. _ ==> gas_outcome_full _ _ _ _ (next [BytesV bs]) _ _ _`
    (qspecl_then [`bs`,`ee`,`Gz`,`tz`,`z`,`marks`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qmatch_goalsub_rename_tac `not_fresh_at sb _` >> gen_tac >>
         fs[] >> strip_tac >> gvs[] >> NO_TAC) >>
    TRY (qmatch_goalsub_rename_tac `LENGTH bs < _` >> fs[] >> NO_TAC) >>
    TRY (qmatch_goalsub_rename_tac `s.vs_alloca_next <= z.vs_alloca_next` >> simp[]) >>
    TRY (qmatch_goalsub_rename_tac `valid_horizon cx st0 _ es.storage_trace` >>
         gen_tac >> disch_tac >>
         qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee z /\ _`
           (drule_then strip_assume_tac) >> simp[] >> NO_TAC) >>
    map_every qx_gen_tac [`vs`,`ef`,`Gf`,`tf`,`f`,`gs`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    `valid_horizon cx st0 (storage_trace_horizon ef.storage_trace) ef.storage_trace` by
      fs[storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==> _`
      (drule_then strip_assume_tac) >>
    qpat_x_assum `cnt = Var l` SUBST_ALL_TAC >>
    qpat_x_assum `data = Var q` SUBST_ALL_TAC >>
    `lookup_var q z = SOME (n2w (w2n w + 32))` by
      (qpat_assum `eval_operand (Var q) z = SOME _`
        (ACCEPT_TAC o REWRITE_RULE[eval_operand_def])) >>
    `su.cs_next_id <= su.cs_next_id` by simp[] >>
    drule_all blueprint_raw_borrowed_window >> simp[]) >> simp[]
QED

Resume blueprint_raw_args_cut[copy]:
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv (vv_type vv)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,sa1)` >>
  Cases_on `unwrap_value cenv vv sa1` >>
  rename1 `unwrap_value cenv vv sa1 = (src,sc)` >>
  Cases_on `compile_store_memory cenv src buf.buf_operand (vv_type vv) (vv_type vv) sc` >>
  rename1 `compile_store_memory _ src _ _ _ sc = (ur,sd)` >>
  Cases_on `ur` >>
  qpat_x_assum `compile_snapshot_vv _ _ _ sm = _` mp_tac >>
  simp[compile_snapshot_vv_def,compile_materialize_vv_def,comp_ignore_bind_def,
       comp_bind_def,comp_return_def] >>
  disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >>
  gvs[unwrap_value_def,mk_ptr_def,comp_return_def,
      IgnAsm `unwrap_value _ vv sa1 = _`] >>
  `ci_mono sm sa1 /\ ci_mono sa1 sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `ci_mono sa1 sd` by metis_tac[ci_mono_trans] >>
  `fn_has_code sm sa1 func /\ fn_has_code sa1 sc func /\ fn_has_code sc sd func` by
    (qspecl_then [`sm`,`sa1`,`sd`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- metis_tac[ci_mono_def]) >> strip_tac >>
     qspecl_then [`sa1`,`sc`,`sd`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- metis_tac[ci_mono_def]) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible,exprSimMemorySourceTheory.forced_expr_admissible_raw] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok cx e` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_def] >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`, `shadow_ctx`,
          `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodySimFullTheory.expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sh`,`shm`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qmatch_goalsub_rename_tac `compile_expr _ (expr_type e) _ _` >>
       qpat_assum `expr_type e = _` (fn th => once_rewrite_tac[th]) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt gen_tac >> disch_tac >> first_assum (drule_then ACCEPT_TAC))) >> strip_tac >>
  rewrite_tac[bind_assoc] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_expr cx e) _ childQ childR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl [`mid`,`t`,`v`] >> gvs[ignore_bind_def,bind_assoc])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >- (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists `\H res ee G1 tn1 t. childQ H res ee G1 tn1 t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >> disj1_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr cx e) _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. _ ==> (?raw. res = INL raw /\ _) /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  rename1 `vv_post _ ctx func cenv cx e es sa sm s ee raw vv t` >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    (drule_then ACCEPT_TAC exprSimAggregateSourceTheory.vv_post_materialises) >>
  `!tail. read_result cx raw (ee with gas_obs := tail) = (INL v,ee with gas_obs := tail)` by
    (drule_then ACCEPT_TAC exprSimMemorySourceTheory.read_result_gas_obs) >>
  qexists `raw` >> simp[] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_lands >> BETA_TAC >> rpt conj_tac
  >- (gen_tac >> rename1 `storage_trace_frame (next [x])` >>
      qpat_assum `!vs. storage_trace_frame (next vs)` (qspec_then `[x]` ACCEPT_TAC))
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t'`,`v'`] >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G1`,`ee`,`INL v`,`t`,`tn1`] >>
  simp[cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules,evaluation_state_component_equality] >>
  gen_tac >> disch_then kall_tac >>
  qpat_x_assum `Abbrev (childR = _)` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr cx e) expr_vv_res_ok es` kall_tac >>
  suspend "copy_store"
QED

Resume blueprint_raw_args_cut[copy_store]:
  `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  once_asm_rewrite_tac[] >>
  `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []) = (INL v,ee)` by
    (simp[Once bind_def]) >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abiEncodeArgsCaseTheory.abi_args_success_ready) >>
  qpat_assum `~is_word_type (expr_type e)` (fn nonword => simp[NoAsms,nonword]) >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `?bs. v = BytesV bs /\ LENGTH bs < 2 ** 64 /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
    value_has_type (BaseTV (BytesT (Dynamic cap))) v` by
    (drule_all (REWRITE_RULE [ETA_AX] exprSimHypsTheory.memory_rhs_read_annotation_typed) >>
     qpat_assum `expr_type e = _` (fn ty => simp[NoAsms,value_runtime_typed_def,ty]) >>
     strip_tac >>
     rename1 `evaluate_type env.type_defs _ = SOME atv` >>
     `atv = BaseTV (BytesT (Dynamic cap))` by
       (drule_then ACCEPT_TAC abiValueEncodingTheory.evaluate_type_base_result) >>
     `evaluate_type (get_tenv cx) (expr_type e) = SOME atv` by
       (qpat_assum `expr_body_pre cenv cx env e es` (fn pre =>
          qpat_assum `evaluate_type env.type_defs _ = SOME atv`
            (mp_tac o REWRITE_RULE [MATCH_MP expr_body_pre_env_type_defs pre])) >>
        qpat_assum `expr_type e = _` (fn ty => simp_tac (srw_ss()) [ty])) >>
     drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> strip_tac >>
     `post_value_type cenv e = expr_type e` by
       simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def] >>
     qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME atv` mp_tac >>
     qpat_assum `value_has_type atv v` mp_tac >>
     qpat_assum `type_memory_size atv < 2 ** 64` mp_tac >>
     qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_assum `atv = BaseTV (BytesT (Dynamic cap))` mp_tac >>
     POP_ASSUM_LIST kall_tac >> rpt strip_tac >>
     Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,valueEncodingTheory.type_memory_size_def] >>
     mp_tac (Q.SPEC `cap` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >> decide_tac) >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  drule_at (Pat `bind (eval_expr _ _) _ _ = _`)
    (REWRITE_RULE [ETA_AX] blueprint_raw_snapshot_type) >>
  simp[] >> disch_then (qspecl_then [`vv`,`sm`,`sa`,`env`,`cenv`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `dk` (map_every assume_tac o CONJUNCTS)) >>
  `post_value_type cenv e = expr_type e` by
    simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def] >>
  `?lk. lowered_value_type cenv e = BaseT (BytesT (Dynamic lk))` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >>
     simp[] >> Cases_on `lowered_value_type cenv e` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT bt) _` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT (BytesT b)) _` >> Cases_on `b` >> simp[arg_type_fits_def]) >>
  `tv = BaseTV (BytesT (Dynamic lk))` by
    (qpat_assum `lowered_value_type cenv e = _` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv`
         (mp_tac o REWRITE_RULE [eq])) >>
     MATCH_ACCEPT_TAC abiValueEncodingTheory.evaluate_type_base_result) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s ee raw vv t /\
     ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (qx_gen_tac `hk` >> disch_tac >>
     qpat_assum `!H. _ ==> (?r. INL raw = INL r /\ _) /\ _`
       (qspec_then `hk` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [sumTheory.INL_11]) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (qx_gen_tac `hk` >> disch_tac >>
     `valid_horizon cx st0 hk (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:eval_result``] vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl [`eval_expr cx e`,`INL raw`,`ee`] >>
     simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace`
       (drule_then assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx es s /\ _`
       (drule_then strip_assume_tac)) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx ee G1 tn1 t`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `return_buf_frame d cenv sm t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >> simp[] >>
     qpat_assum `vv_post (storage_trace_horizon _) ctx func cenv cx e es sa sm s ee raw vv t`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >> simp[]) >>
  `~is_word_type (post_value_type cenv e) /\ is_bytestring_type (post_value_type cenv e) /\
   is_bytestring_type (lowered_value_type cenv e)` by simp[is_word_type_def,is_bytestring_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_assum `post_value_type cenv e = expr_type e` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size (BaseTV (BytesT (Dynamic cap))) /\
   type_memory_size (BaseTV (BytesT (Dynamic cap))) < 2 ** 64` by
    (drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  `0 < type_memory_size tv` by simp[valueEncodingTheory.type_memory_size_def] >>
  `type_memory_bytes cenv (vv_type vv) < dimword (:256)` by
    fs[wordsTheory.dimword_def] >>
  `!ty op. vv = StackValue ty op ==> ptr_buf_ok cenv e op G1 t` by simp[] >>
  qpat_assum `compile_expr _ _ e sa = (vv,sm)`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac blueprint_raw_copy_store_entry) >>
  disch_then (fn entry => qpat_assum `compile_alloc_buffer _ sm = (buf,sa1)`
    (mp_then (Pat `compile_alloc_buffer _ _ = _`) mp_tac entry)) >>
  disch_then (fn entry => qpat_assum `unwrap_value cenv vv sa1 = (src,sc)`
    (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac entry)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (post_value_type _ _) = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ sm _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ es s`)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then (qx_choosel_then [`dst`,`dw`,`z`,`Gz`,`tz`,`x`,`sw`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `src = Var x` SUBST_ALL_TAC >>
  `compile_store_memory cenv (Var x) (Var dst) (vv_type vv) (vv_type vv) sc = ((),sd)` by
    (qpat_assum `buf.buf_operand = Var dst` (fn eq =>
       qpat_assum `compile_store_memory _ _ buf.buf_operand _ _ _ = _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee z /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tz z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> _ /\ expr_post H ctx func cenv cx e es sa sc s ee _ _ z /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     drule_then assume_tac exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  `wb_frame cenv es ee sa s z` by
    (qpat_assum `!H. _ ==> _ /\ expr_post H ctx func cenv cx e es sa sc s ee _ _ z /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_then ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame) >>
  `sa.cs_next_var <= sc.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `sm.cs_next_id < sc.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> asm_rewrite_tac[] >>
         qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
           (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> asm_rewrite_tac[] >>
     qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `compile_store_memory _ (Var x) (Var dst) _ _ sc = ((),sd)`
    (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac blueprint_raw_copy_store_exit) >>
  disch_then (fn exit => qpat_assum `lookup_var dst z = SOME dw`
    (mp_then (Pat `lookup_var dst z = _`) mp_tac exit)) >>
  disch_then (drule_at (Pat `lookup_var x z = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ Gz tz`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ sc z`)) >>
  disch_then (fn exit => qpat_assum `fn_has_code sc sd func`
    (mp_then (Pat `fn_has_code sc sd _`) mp_tac exit)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (fn exit => qpat_assum `evaluate_type (get_tenv cx) (vv_type vv) = SOME _`
    (mp_then (Pat `evaluate_type _ (vv_type vv) = _`) mp_tac exit)) >>
  disch_then (qspecl_then [`lowered_value_type cenv e`,`tv`,
    `gas_explicit_sites ctx shadow_ctx`,`ctx`,`dk`,`bs`,`sm.cs_next_id`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (
    qpat_assum `type_memory_bytes cenv (vv_type vv) = _`
      (fn eq => rule_assum_tac (REWRITE_RULE [eq]) >> rewrite_tac[eq]) >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >> fs[])) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `buf.buf_operand = Var dst` (fn eq =>
    rule_assum_tac (REWRITE_RULE [eq]) >> assume_tac eq) >>
  qpat_assum `emit_op MLOAD [Var dst] sd = (cnt,sn)`
    (mp_then (Pat `emit_op MLOAD _ _ = _`) mp_tac
      (PURE_REWRITE_RULE [wordsTheory.n2w_w2n]
        (Q.INST [`b` |-> `w2n (dw:bytes32)`] blueprint_raw_header_path))) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `mload (w2n dw) u = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ dst u (32 + LENGTH bs)`)) >>
  disch_then (drule_at (Pat `fn_has_code sd sn _`)) >>
  disch_then (drule_at (Pat `allocas_from lo u`)) >>
  disch_then (qspecl_then [`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`l`,`q`,`h`,`Gh`,`th`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `h with <|vs_vars := _; vs_inst_idx := _|> = u`
    (mp_tac o Q.AP_TERM `\r. (r.vs_memory,r.vs_allocas,r.vs_alloca_next,
        r.vs_fmp,r.vs_initial_fmp,r.vs_call_ctx,r.vs_accounts,
        r.vs_transient,r.vs_immutables,r.vs_halted)`) >> simp[] >> strip_tac >>
  `state_frame h = state_frame (u with vs_inst_idx := h.vs_inst_idx)` by
    (qpat_assum `h with <|vs_vars := _; vs_inst_idx := _|> = u`
      (mp_tac o Q.AP_TERM `\r:venom_state. r with <|vs_vars := FEMPTY; vs_inst_idx := h.vs_inst_idx|>`) >>
     simp[stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `th with t_var := _ = tu`
    (mp_tac o Q.AP_TERM `\r. (r.t_mem,r.t_stor,r.t_trans,r.t_imm)`) >> simp[] >> strip_tac >>
  `ci_mono sa sd /\ ci_mono sd sb` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= sb.cs_next_var /\
   sd.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `ci_mono sa sd` (mp_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono sd sb` (mp_tac o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     simp_tac bool_ss []) >>
  `local_ptrs_reserved cenv sd` by metis_tac[local_ptrs_reserved_next_var] >>
  `wb_frame cenv ee ee sd u h` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl [`sd`,`u`] >> simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
  `ghost_kept_at lo cenv ee sd Gu tu u Gh th` by simp[ghost_kept_at_def] >>
  `wb_frame cenv es ee sa s h /\ ghost_kept_at lo cenv es sa G tn s Gh th` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame cenv ee ee sd u h` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >> simp[] >>
     qpat_assum `ghost_kept_at lo cenv ee sd Gu tu u Gh th` (irule_at Any) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sc` >> conj_tac
     >- qpat_assum `ci_mono sc sd` (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sc x`
       (drule_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK h,Gh,th)` by suspend "copy_header_path" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee h /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gh th h /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK h,Gh,th)` by suspend "copy_header_semantics" >>
  `alloca_history func h` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] (OK h,Gh,th)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`gas_explicit_sites ctx shadow_ctx`]
         (irule_at Any)) >> simp[] >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `return_buf_frame d cenv sb h` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sd u` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp h` by
    (disch_tac >>
     `allocas_below_fmp u` by (first_assum (fn th => drule_then ACCEPT_TAC th)) >>
     qpat_assum `h with <|vs_vars := _; vs_inst_idx := _|> = u` (fn eq =>
       qpat_assum `allocas_below_fmp u` (mp_tac o ONCE_REWRITE_RULE [GSYM eq])) >>
     simp[allocas_below_fmp_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!fn i r. frag_reachable ctx func h fn i r ==> dalloca_fmp_headroom i r` by suspend "copy_reach" >>
  `!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)` by
    (qx_gen_tac `tail` >>
     `bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (INL (BytesV bs),ee with gas_obs := tail)` by simp[Once bind_def] >>
     simp[exprSimAbiEncodeArgsLabelReplayTheory.abi_args_singleton_source, Once bind_def, return_def]) >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >> simp[] >>
  qexistsl [`Gh`,`h`,`th`] >> simp[] >> suspend "copy_continue"
QED

Resume blueprint_raw_args_cut[copy_header_path]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] (OK z,Gz,tz) /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  goal_assum (drule_at Any) >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> simp[]
QED

Resume blueprint_raw_args_cut[copy_header_semantics]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] (OK z,Gz,tz) /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac
  >- (irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
      qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
      qpat_assum `state_frame h = _` (irule_at Any) >>
      qexists `sd` >> simp[] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sd x ==> _ /\ _ /\ _` (drule_then strip_assume_tac))
  >- drule_then ACCEPT_TAC (cj 2 (iffLR loweringPostsTheory.expr_post_def))
  >- (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
      qexistsl [`Gu`,`ee`,`u`,`sd`,`tu`] >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] (OK h,Gh,th)`
    (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
    (drule_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK h`,`Gh`,`th`] mp_tac) >> simp[]
QED

Resume blueprint_raw_args_cut[copy_reach]:
  rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee h /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK h,Gh,th)` (irule_at Any) >>
  qexists `fn` >> simp[] >> conj_tac
  >- (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
        qpat_assum `MEM func ctx.ctx_functions`
          (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  first_assum ACCEPT_TAC
QED

Resume blueprint_raw_args_cut[copy_continue]:
  qpat_assum `!bs ee Gu tu u marks. _ ==> gas_outcome_full _ _ _ _ (next [BytesV bs]) _ _ _`
    (qspecl_then [`bs`,`ee`,`Gh`,`th`,`h`,`marks`] irule) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
  >~ [`!x'. q = x' \/ l = x' ==> not_fresh_at sb x'`]
  >- (gen_tac >> disch_then (DISJ_CASES_THEN (SUBST1_TAC o SYM)) >>
      first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `valid_horizon cx st0 _ es.storage_trace` >>
       gen_tac >> disch_tac >>
       qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee h /\ _`
         (drule_then strip_assume_tac) >> simp[] >> NO_TAC)
  >- suspend "copy_window"
  >- (qexists `marks` >> simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee h /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  fs[]
QED

Resume blueprint_raw_args_cut[copy_window]:
  qx_genl_tac [`vs`,`ef`,`Gf`,`tf`,`f`,`gs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cnt = Var l` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var q` SUBST_ALL_TAC >>
  qpat_assum `eval_operand (Var l) h = _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  qpat_assum `eval_operand (Var q) h = _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  `lookup_var l f = SOME (n2w (LENGTH bs)) /\ lookup_var q f = SOME (n2w (w2n dw + 32))` by
    (conj_tac >> irule exprSimWordArgsTheory.wb_frame_vars >>
     qpat_assum `wb_frame cenv ee ef sb h f` (irule_at Any) >> simp[]) >>
  `FLOOKUP Gf l = FLOOKUP Gh l /\ FLOOKUP Gf q = FLOOKUP Gh q /\
   op_taint tf (Var l) = op_taint th (Var l) /\ op_taint tf (Var q) = op_taint th (Var q)` by
    (qpat_assum `ghost_kept_at lo cenv ee sb Gh th h Gf tf`
       (mp_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (fn th => mp_tac (Q.SPEC `l` th) >> mp_tac (Q.SPEC `q` th)) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee u` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv ee ef sd u f /\ ghost_kept_at lo cenv ee sd Gu tu u Gf tf` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame cenv ee ef sb h f` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx ee u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee sb Gh th h Gf tf` (irule_at Any) >> simp[]) >>
  `compile_snapshot_vv cenv T vv sm =
     (LocatedValue (vv_type vv) (mk_ptr (Var dst) LocMemory),sd)` by
    simp[compile_snapshot_vv_def,compile_materialize_vv_def,comp_bind_def,
         comp_ignore_bind_def,comp_return_def,
         IgnAsm `type_memory_bytes cenv (vv_type vv) = _`, IgnAsm `vv_type vv = _`] >>
  `!n b len. local_region cenv ee.scopes u n b len ==>
      w2n dw + type_memory_size (BaseTV (BytesT (Dynamic dk))) <= b \/ b + len <= w2n dw` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!n b len. _ ==> regions_disjoint _ _ b len`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `mem_bytes_at (w2n dw) (type_memory_size (BaseTV (BytesT (Dynamic dk)))) f.vs_memory =
   mem_bytes_at (w2n dw) (type_memory_size (BaseTV (BytesT (Dynamic dk)))) u.vs_memory` by
    (qpat_assum `compile_snapshot_vv cenv T vv sm = _`
       (mp_then (Pat `compile_snapshot_vv _ _ _ _ = _`) mp_tac
         bodyFullOperandSnapshotTheory.compile_snapshot_vv_materialized_frame) >>
     disch_then (drule_at (Pat `wb_frame cenv ee ef sd u f`)) >>
     disch_then (irule o cj 4) >>
     qpat_assum `ptr_val_ok cx _ (BytesV bs) (Var dst) Gu tu u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee sd Gu tu u Gf tf` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas (sm.cs_next_id) = _` (irule_at Any) >>
     qexists `BaseTV (BytesT (Dynamic dk))` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[vv_operand_def,mk_ptr_def]) >>
  `32 + LENGTH bs <= type_memory_size (BaseTV (BytesT (Dynamic dk)))` by
    (mp_tac (Q.SPEC `dk` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >>
     simp[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `!i. w2n dw + 32 <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tf.t_mem` by
    (rpt strip_tac >>
     `w2n dw <= i /\ i < w2n dw + type_memory_size (BaseTV (BytesT (Dynamic dk)))` by decide_tac >>
     qpat_assum `ghost_kept_at lo cenv ee sd Gu tu u Gf tf`
       (mp_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n dw`,
       `type_memory_size (BaseTV (BytesT (Dynamic dk)))`,`i`] mp_tac) >>
     simp[] >> rpt gen_tac >> disch_tac >>
     qpat_assum `!n b len. local_region cenv ee.scopes u n b len ==> _ <= b \/ _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  `mem_bytes_at (w2n dw + 32) (LENGTH bs) f.vs_memory = bs` by
    (qpat_assum `mem_bytes_at (w2n dw) _ f.vs_memory = _`
       (mp_tac o cj 1 o MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window o SYM) >>
     disch_then (qspecl_then [`w2n dw + 32`,`LENGTH bs`] mp_tac) >> simp[]) >>
  `w2n (n2w (w2n dw + 32) : bytes32) = w2n dw + 32` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `ptr_covers Gf tf q f (LENGTH bs)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gh th q h (LENGTH bs)` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  `LENGTH bs + (w2n dw + 32) <= f.vs_alloca_next` by decide_tac >>
  simp[eval_operand_def,op_prov_def,memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  qpat_assum `op_prov Gh (Var l) = NONE`
    (ACCEPT_TAC o SIMP_RULE (srw_ss()) [op_prov_def])
QED

Finalise blueprint_raw_args_cut

(* The check uses the post-operand account view. Only its success arm
   constructs a DALLOCA window; size failure still belongs to dispatch. *)
Theorem create_blueprint_finish[local]:
  compile_create_blueprint_check lit target off sm = (codep,sn) /\
  compile_create_blueprint_append target amount sop off codep args_ptr cnt rof sn = (result,sb) /\
  fn_has_code sm sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\ outcomes_accounts_typed ee.outcomes /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\ eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  OPTREL (\op w. eval_operand op s = SOME w /\ op_taint tn op = {}) sop sw /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\ op_prov G off = NONE /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  LENGTH args < 2 ** 64 /\
  (!x. MEM (Var x) [target;off;args_ptr;cnt;amount] \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\
    ptr_covers G tn q s (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
    read_memory (w2n a) (LENGTH args) s = args) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if ~(if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code) else w2n ow < LENGTH code) then
      (INR (Error (RuntimeError "create source has no deployable code")),ee with gas_obs := tail)
    else if (blueprint_copy_size (w2n ow) code) + LENGTH args > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (blueprint_initcode (blueprint_copy_size (w2n ow) code) (w2n ow) code args) rof))
      (read_result cx) (ee with gas_obs := tail)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx` by suspend "dalloca" >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any (mp_then Any (map_every assume_tac o CONJUNCTS)
       accountsRelPropsTheory.state_rel_accounts)
       stateRelProjTheory.stmt_state_rel_state_rel) >>
  `LENGTH code <= 24576 /\
   (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) s.vs_accounts).code = code` by
    (drule_all_then strip_assume_tac exprSimSliceExtcodeTheory.slice_extcode_account >> simp[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `allocas_below_fmp s /\ s.vs_alloca_next <= w2n s.vs_fmp` by suspend "frontier" >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK s,G,tn)` by simp[cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  qpat_assum `(lookup_account _ s.vs_accounts).code = code` (assume_tac o SYM) >>
  drule_all create_blueprint_prepared_path >>
  qpat_x_assum `code = (lookup_account _ s.vs_accounts).code` kall_tac >>
  qpat_x_assum `(lookup_account _ s.vs_accounts).code = code` kall_tac >>
  qpat_x_assum `code = (lookup_account _ ee.accounts).code` kall_tac >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qabbrev_tac `n = blueprint_copy_size (w2n ow) code` >>
  reverse (Cases_on `if lit then blueprint_size_ok n else w2n ow < LENGTH code`)
  >- (qpat_assum `~(if lit then _ else _)`
        (fn th => pure_rewrite_tac [EQF_INTRO th,COND_CLAUSES]) >> suspend "bad") >>
  qpat_assum `if lit then _ else _`
    (fn th => pure_rewrite_tac [EQT_INTRO th,COND_CLAUSES]) >> suspend "good"
QED

Resume create_blueprint_finish[dalloca]:
  drule dallocaCreateGeometryTheory.create_blueprint_create_prefix >>
  disch_then (qx_choosel_then [`len`,`u`,`buf`,`v`,`w`,`r`,`created`,`r'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE [compile_alloc_dynamic_def]) >>
  `cs_extends sm sn` by
    metis_tac[externalEntryShapeTheory.compile_create_blueprint_check_labels,pairTheory.SND] >>
  `cs_extends sm u /\ cs_extends u v /\ cs_extends v w` by
    (rpt conj_tac
     >- (irule cs_extends_trans >> qexists_tac `sn` >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qpat_assum `emit_op ADD _ sn = (_,u)`
           (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_op_grows))
     >- qpat_assum `emit_op DALLOCA _ u = (_,v)`
          (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_op_grows) >>
     qpat_assum `emit_void EXTCODECOPY _ v = ((),w)`
       (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows)) >>
  `cs_extends w r` by
    (Cases_on `cnt = Lit 0w`
     >- (qpat_assum `cnt = Lit 0w` (fn empty =>
           qpat_assum `if cnt = Lit 0w then r = w else _`
             (SUBST1_TAC o SIMP_RULE bool_ss [empty])) >>
         simp[NoAsms,cs_extends_refl]) >>
     qpat_assum `cnt <> Lit 0w` (fn nonempty =>
       qpat_assum `if cnt = Lit 0w then r = w else _`
         (qx_choosel_then [`args_dest`,`sx`] strip_assume_tac o
          SIMP_RULE bool_ss [nonempty,compile_copy_memory_dynamic_def])) >>
     irule cs_extends_trans >> qexists_tac `sx` >> conj_tac
     >- qpat_assum `emit_op ADD _ w = (args_dest,sx)`
          (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_op_grows) >>
     qpat_assum `emit_void MCOPY _ sx = ((),r)`
       (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows)) >>
  `cs_extends r r'` by
    (qpat_assum `(case sop of NONE => _ | SOME _ => _) r = (created,r')` mp_tac >>
     Cases_on `sop` >> simp[NoAsms] >>
     disch_then (ACCEPT_TAC o MATCH_MP stmtSimAugAssignPlaceTheory.aug_place_emit_op_grows)) >>
  `cs_extends r' sb` by
    (mp_tac (Q.SPECL [`created`,`rof`,`r'`]
       externalEntryShapeTheory.compile_check_create_result_labels) >> simp[]) >>
  `fn_has_code u v func` by
    (`cs_extends v sb` by
       (irule cs_extends_trans >> qexists `w` >> conj_tac >- first_assum ACCEPT_TAC >>
        irule cs_extends_trans >> qexists `r` >> conj_tac >- first_assum ACCEPT_TAC >>
        irule cs_extends_trans >> qexists `r'` >> conj_tac >> first_assum ACCEPT_TAC) >>
     match_mp_tac (Q.SPECL [`sm`,`u`,`v`,`sb`,`func`] fragExecTheory.fn_has_code_mid) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `emit_op DALLOCA _ _ = _`
    (mp_then Any (map_every assume_tac o CONJUNCTS) exprLoweringPropsTheory.emit_op_extends) >>
  qpat_assum `emit_op DALLOCA _ _ = _`
    (mp_then Any (map_every assume_tac o CONJUNCTS) emitHelperPropsTheory.emitted_insts_emit_op) >>
  qpat_assum `same_blocks u v` (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
  qpat_assum `fn_has_code u v func` (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >>
  disch_then (qspec_then `emitted_insts u v` mp_tac) >> simp[] >> strip_tac >>
  simp[ctx_has_dalloca_def,EXISTS_MEM] >> qexists `func` >> simp[] >>
  qexists `mk_inst u.cs_next_id DALLOCA [len] [STRING #"%" (toString u.cs_next_var)]` >>
  reverse conj_tac >- simp[mk_inst_def] >> first_x_assum irule >> simp[]
QED

Resume create_blueprint_finish[frontier]:
  `s.vs_alloca_next <= w2n s.vs_initial_fmp /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
       (mp_tac o REWRITE_RULE [fmp_room_def] o
        MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room) >>
     qpat_assum `ctx_has_dalloca ctx` (fn th => simp[NoAsms,th]) >>
     rpt strip_tac >> decide_tac) >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by decide_tac >>
  simp[allocas_below_fmp_def] >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (b,sz)` >>
  `b+sz <= s.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> first_assum ACCEPT_TAC) >>
  decide_tac
QED

Resume create_blueprint_finish[bad]:
  disch_then (qx_choosel_then [`tbad`,`Gbad`,`tbad_taint`] assume_tac) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gbad`,`ee`,`Abort Revert_abort tbad`,
    `INR (Error (RuntimeError "create source has no deployable code"))`,`tbad_taint`] >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED

Resume create_blueprint_finish[good]:
  disch_then (qx_choosel_then [`sc`,`p`,`lenop`,`t`,`Gmat`,`tt`]
    (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `N = n + LENGTH args` >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gmat`,`t`,`tt`] >> conj_tac >- simp[] >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (conj_tac
     >- (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = _`
           (mp_tac o AP_TERM ``\u:venom_state. u.vs_alloca_next``) >> simp[])
     >> qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = _`
          (mp_tac o AP_TERM ``\u:venom_state. u.vs_labels``) >> simp[]) >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gmat,tt)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`explicit`] (irule_at Any)) >>
     simp[] >> metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t /\ wb_frame cenv es ee sa s0 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt` by suspend "materialized" >>
  suspend "dispatch"
QED

Resume create_blueprint_finish[materialized]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!b k. _ ==> read_memory b k t = _`
    (assume_tac o REWRITE_RULE [memoryReadPropsTheory.read_memory_eq_mem_bytes_at]) >>
  `w2n s.vs_fmp = w2n s.vs_fmp` by REFL_TAC >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0`
    (mp_then (Pos (el 2))
      (drule_all_then (map_every assume_tac o CONJUNCTS))
      bodyFullDynamicBufferTheory.dynamic_buffer_materialized_frame) >>
  simp[]
QED

Resume create_blueprint_finish[dispatch]:
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
      eval_operand op t = eval_operand op s /\ op_prov Gmat op = op_prov G op /\
      op_taint tt op = op_taint tn op` by
    (match_mp_tac bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >> simp[]) >>
  `!x. amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x` by
    (qpat_assum `!x. MEM (Var x) _ \/ _ ==> _` mp_tac >> simp[MEM] >> metis_tac[]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by metis_tac[] >>
  `(case sop of NONE => sw = NONE | SOME op =>
      ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})` by
    (Cases_on `sop` >> Cases_on `sw` >> gvs[optionTheory.OPTREL_def] >> metis_tac[]) >>
  `w2n (n2w N:bytes32) = N` by simp[wordsTheory.w2n_n2w] >>
  `!tail. source (ee with gas_obs := tail) =
    if N > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (blueprint_initcode n (w2n ow) code args) rof))
      (read_result cx) (ee with gas_obs := tail)` by
    (qpat_assum `!tail. source (ee with gas_obs := tail) = _`
       (fn th => simp[Once th,Abbr `N`])) >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  irule create_dispatch_outcome_full >>
  qpat_assum `compile_create_dispatch (Var p) lenop _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand (Var p) t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand lenop t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand amount t = SOME _` (irule_at Any) >>
  qexistsl [`sw`,`blueprint_initcode n (w2n ow) code args`] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise create_blueprint_finish

(* Constructor values are evaluated before the scalar suffix. The encoder
   keeps only its registered byte window live across that suffix. *)
Theorem blueprint_encoded_args_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  ctor <> [] /\ LENGTH salts = (if salted then 1 else 0) /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) entry /\
  expr_sim_inv cenv cx env es /\ body_exprs_full_ok cx ctor /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  compile_create_blueprint_args compile_expr cenv F later ctor sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) F (MAP gas_shadow_expr later)
    (MAP gas_shadow_expr ctor) sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!vs bytes ee Gz tz z marks.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes /\
    LENGTH bytes < 2 ** 64 /\
    (!tail. eval_exprs cx ctor (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL vs,ee with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= z.vs_alloca_next /\
    alloca_history func z /\ return_buf_frame d cenv sb z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    (!vs' ef Gf tf f gs.
      (!tail. eval_exprs cx later (ee with gas_obs := gs ++ tail) = (INL vs',ef with gas_obs := tail)) /\
      wb_frame cenv ee ef sb z f /\ ghost_kept_at lo cenv ee sb Gz tz z Gf tf /\
      MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ z.vs_alloca_next <= f.vs_alloca_next /\
      storage_trace_domain cx st0 ef.storage_trace /\
      (!H. valid_horizon cx st0 H ef.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
        storage_well_formed_on cx ef (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ef Gf tf f) ==>
      eval_operand cnt f = SOME (n2w (LENGTH bytes)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bytes) /\ (bytes = [] \/ w2n a + LENGTH bytes <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bytes ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bytes) f = bytes)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next vs) (ee,z,Gz,tz) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx ctor) next) (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ ctor _ = _`
    (mp_then Any mp_tac dallocaBlueprintArgsTheory.create_blueprint_encoded_args_compile) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`rows`,`se`,`buf`,`st`] (map_every assume_tac o CONJUNCTS)) >>
  `MAP gas_shadow_expr ctor <> []` by simp[] >>
  qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctor) _ = _`
    (mp_then Any mp_tac dallocaBlueprintArgsTheory.create_blueprint_encoded_args_compile) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`shrows`,`she`,`shbuf`,`sht`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "rows"
QED

Resume blueprint_encoded_args_cut[rows]:
  `gas_shadow_compiles (compile_create_ctor_args compile_expr cenv ctor)
     (compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr ctor))` by
    irule (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_ctor_args
             (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env) |>
           Q.INST [`sh` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_then (drule_all_then strip_assume_tac) bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  qpat_x_assum `rows = shrows` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sa se /\ ci_mono se st /\ ci_mono st sb /\
   ci_mono sh she /\ ci_mono she sht /\ ci_mono sht shb` by
    metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,
      ci_mono_compile_alloc_buffer,ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
  `fn_has_code sa se func /\ fn_has_code se st func /\ fn_has_code st sb func /\
   fn_has_code sh she shadow_func` by
    (`cs_extends sa se /\ cs_extends se st /\ cs_extends st sb /\
      cs_extends sh she /\ cs_extends she sht /\ cs_extends sht shb` by fs[ci_mono_def] >>
     rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     (qpat_assum `fn_has_code sa sb func` (irule_at Any) ORELSE
      qpat_assum `fn_has_code sh shb shadow_func` (irule_at Any)) >>
     simp[cs_extends_refl] >> irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `!e u. MEM e ctor /\ expr_sim_inv cenv cx env u ==> expr_body_pre cenv cx env e u` by
    (rpt strip_tac >> irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) entry` (irule_at Any) >> simp[]) >>
  irule create_ctor_rows_cut >>
  qpat_assum `compile_create_ctor_args _ _ ctor sa = _` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) sh = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "encode"
QED

Resume blueprint_encoded_args_cut[encode]:
  qx_genl_tac [`marks`,`vs`,`ee`,`Gr`,`tr`,`rs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `!tail. eval_exprs cx ctor _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value list``] valid_horizon_frame) >>
     qexistsl [`eval_exprs cx ctor`,`INL vs`,`ee with gas_obs := []`] >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee rs /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gr tr rs` by
    (gen_tac >> disch_tac >> qpat_assum `!H. _ ==> LENGTH rows = LENGTH ctor /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  qpat_assum `!H. _ ==> LENGTH rows = LENGTH ctor /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved cenv se /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (qpat_assum `ci_mono sa se` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> asm_rewrite_tac[] >>
         qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
           (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> asm_rewrite_tac[] >>
     qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  qabbrev_tac `cap = abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) ctor))` >>
  suspend "inputs"
QED

Resume blueprint_encoded_args_cut[inputs]:
  `EVERY (\e. expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings)) ctor /\
   EVERY (\e. expr_body_pre cenv cx env e ee) ctor` by
    (simp[EVERY_MEM] >> metis_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  qpat_assum `!tail. eval_exprs cx ctor _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `vals` |-> `rows`, `t` |-> `rs`,
                  `G` |-> `Gr`, `tn` |-> `tr`, `es` |-> `entry`,
                  `entry` |-> `es with gas_obs := gas_explicit marks s.vs_gas_readings`,
                  `fin` |-> `ee with gas_obs := []`] blueprint_rows_encoder_inputs) >>
  impl_tac
  >- (simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. _ ==> LENGTH rows = LENGTH ctor /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cap < 2**64` by
    (qpat_assum `Abbrev (cap = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `cap < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2**64` >> simp[] >> EVAL_TAC) >>
  `allocas_from lo rs /\ lo <= rs.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx ee Gr tr rs`
      (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  drule_all create_alloc_buffer_saved_start >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`root`,`pbase`,`u`,`Gu`,`tu`,`inst`]
      (map_every assume_tac o CONJUNCTS))) >>
  `compile_abi_encode_values_to_buf cenv (Var root)
     (ZIP (rows,MAP (lowered_value_type cenv) ctor)) st = (cnt,sb)` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee rs` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee rs /\ _`
       (drule_then strip_assume_tac)) >>
  mp_tac (Q.INST [`prefix` |-> `[]`, `capacity` |-> `cap`, `args` |-> `ctor`,
      `ce` |-> `cenv`, `vals` |-> `rows`, `s` |-> `rs`, `G` |-> `Gr`, `tn` |-> `tr`,
      `shared` |-> `se.cs_next_id`, `payload_var` |-> `root`, `alen` |-> `cnt`,
      `fin` |-> `sb`, `disp` |-> `d`, `initial` |-> `u`, `Gi` |-> `Gu`, `ti` |-> `tu`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] create_encoded_rows_window) >>
  impl_tac >- simp[Abbr `cap`] >>
  disch_then (qx_choosel_then [`bytes`,`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "transport"
QED

Resume blueprint_encoded_args_cut[transport]:
  qpat_assum `compile_alloc_buffer cap se = _`
    (strip_assume_tac o MATCH_MP abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st u _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb z _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  `data = Var root` by metis_tac[] >>
  `op_prov Gz cnt = NONE` by
    (irule create_encoded_length_no_prov >>
     qpat_assum `emit_op ALLOCA _ se = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_values_to_buf _ buf.buf_operand _ st = _` (irule_at Any) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gz,tz)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` (irule_at Any)) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (rs,Gr,tr) [] (OK z,Gz,tz)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (rs,Gr,tr) [] (OK u,Gu,tu)`
       (qspec_then `D` (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK rs,Gr,tr)`
       (drule_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`rs`,`Gr`,`tr`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  suspend "apply_next"
QED

Resume blueprint_encoded_args_cut[apply_next]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `ci_mono sa se` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `wb_frame cenv es ee sa s z` by
    (irule (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `wb_frame cenv es ee sa s rs` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >>
     qexists `se` >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s Gz tz` by
    (irule (INST_TYPE [beta |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv es sa G tn s Gr tr` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee se Gr tr rs Gz tz` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >>
     qexists `ee` >> simp[]) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `rs.vs_alloca_next` >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `se.cs_next_var` >> simp[]) >>
  `return_buf_frame d cenv sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     simp[] >>
     qpat_assum `wb_frame cenv es ee sa s z`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee z`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK z,Gz,tz)`
       (drule_then (irule_at Any)) >> qexists `fn` >>
     simp[] >> conj_tac
     >- (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
           qpat_assum `MEM func ctx.ctx_functions`
             (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
     first_assum ACCEPT_TAC) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gz`,`z`,`tz`] >> simp[] >>
  qpat_assum `!vs bytes ee Gz tz z marks. _ ==> gas_outcome_full _ _ _ _ (next vs) _ _ _`
    (qspecl_then [`vs`,`bytes`,`ee`,`Gz`,`tz`,`z`,`marks`] mp_tac) >>
  impl_tac >- suspend "next_inputs" >> simp[]
QED

Resume blueprint_encoded_args_cut[next_inputs]:
  `LENGTH bytes <= cap` by
    (qpat_assum `LENGTH [] + LENGTH bytes <= cap`
      (ACCEPT_TAC o REWRITE_RULE [LENGTH,arithmeticTheory.ADD_CLAUSES])) >>
  `LENGTH bytes < 2**64` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists `cap` >> fs[]) >>
  simp[operand_11] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac
      >- (qpat_x_assum `root = x` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!x. cnt = Var x ==> not_fresh_at sb x` (drule_then ACCEPT_TAC)) >>
  qx_genl_tac [`later_vals`,`ef`,`Gf`,`tf`,`f`,`gs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `wb_frame cenv ee ef sb z f`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  qpat_assum `ghost_kept_at lo cenv ee sb Gz tz z Gf tf`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `compile_abi_encode_values_to_buf _ (Var root) _ st = (cnt,sb)`
    (strip_assume_tac o MATCH_MP abiEncodeValuesCodeTheory.abi_encode_values_to_buf_trace) >>
  qpat_assum `emit_op MLOAD _ _ = (cnt,sb)`
    (qx_choose_then `len` (map_every assume_tac o CONJUNCTS) o
      MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  `eval_operand cnt f = SOME (n2w (LENGTH bytes)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE` by
    (simp[eval_operand_def,ptrDisciplineTheory.op_prov_def] >>
     qpat_assum `eval_operand cnt z = SOME _` (mp_tac o REWRITE_RULE [eval_operand_def]) >>
     fs[eval_operand_def,ptrDisciplineTheory.op_prov_def]) >>
  simp[] >> qexists `n2w pbase` >>
  `lookup_var root z = SOME (n2w pbase) /\ lookup_var root f = SOME (n2w pbase)` by
    (fs[eval_operand_def]) >>
  `ptr_covers Gf tf root f cap` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gz tz root z cap` (irule_at Any) >> simp[]) >>
  `ptr_covers Gf tf root f (LENGTH bytes)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `pbase < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists `z.vs_alloca_next` >>
     conj_tac
     >- (irule exprLoweringPropsTheory.alloca_room_next_lt >>
         qpat_assum `stmt_state_rel _ ctx func cenv cx ee z`
           (irule_at Any o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room)) >>
     qpat_assum `pbase + cap <= z.vs_alloca_next` mp_tac >> numLib.ARITH_TAC) >>
  simp[wordsTheory.w2n_n2w] >>
  suspend "window"
QED

Resume blueprint_encoded_args_cut[window]:
  `!n b sz. local_region cenv ee.scopes z n b sz ==> pbase + cap <= b \/ b + sz <= pbase` by
    (rpt gen_tac >> disch_tac >>
     rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx ee z`
       (map_every (irule_at Any) o CONJUNCTS o
         MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `local_region cenv ee.scopes z n b sz` (irule_at Any) >>
     qpat_assum `inst.inst_outputs = [root]` (irule_at Any) >> simp[]) >>
  `pbase + LENGTH bytes <= f.vs_alloca_next` by
    (qpat_assum `LENGTH bytes <= cap` mp_tac >>
     qpat_assum `pbase + cap <= z.vs_alloca_next` mp_tac >>
     qpat_assum `z.vs_alloca_next <= f.vs_alloca_next` mp_tac >> numLib.ARITH_TAC) >>
  `mem_bytes_at pbase cap f.vs_memory = mem_bytes_at pbase cap z.vs_memory` by
    (qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz f.vs_memory = _`
       (qspecl_then [`se.cs_next_id`,`pbase`,`cap`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `mem_bytes_at pbase (LENGTH bytes) f.vs_memory = mem_bytes_at pbase (LENGTH bytes) z.vs_memory` by
    (qspecl_then [`pbase`,`pbase`,`cap`,`f.vs_memory`,`z.vs_memory`,`0`,`LENGTH bytes`]
      mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window >> simp[]) >>
  simp[memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >> strip_tac >>
      `i < pbase + cap` by
        (qpat_assum `LENGTH bytes <= cap` mp_tac >>
         qpat_assum `i < pbase + LENGTH bytes` mp_tac >> numLib.ARITH_TAC) >>
      `i IN tz.t_mem` by
        (qpat_assum `!aid off sz j. _ ==> j IN tz.t_mem`
           (qspecl_then [`se.cs_next_id`,`pbase`,`cap`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      qpat_assum `!j. pbase <= j /\ j < pbase + LENGTH ([] ++ bytes) ==> j NOTIN tz.t_mem`
        (qspec_then `i` (mp_tac o REWRITE_RULE [APPEND])) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `read_memory pbase (LENGTH ([] ++ bytes)) z = [] ++ bytes`
    (ACCEPT_TAC o REWRITE_RULE [APPEND,memoryReadPropsTheory.read_memory_eq_mem_bytes_at])
QED

Finalise blueprint_encoded_args_cut

Theorem create_eval_exprs_append[local]:
  !xs ys cx. eval_exprs cx (xs ++ ys) =
    bind (eval_exprs cx xs) (\vs. bind (eval_exprs cx ys) (\ws. return (vs ++ ws)))
Proof
  Induct
  >- (simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,bind_def,return_def] >>
      rpt gen_tac >> Cases_on `eval_exprs cx ys x` >> Cases_on `q` >> simp[]) >>
  simp[exprSimWordArgsTheory.eval_exprs_cons_action,bind_assoc,bind_return]
QED

Theorem create_body_exprs_split[local]:
  !xs ys cx. body_exprs_full_ok cx (xs ++ ys) ==>
    body_exprs_full_ok cx xs /\
    (!st vs en. eval_exprs cx xs st = (INL vs,en) ==> body_exprs_full_ok cx ys)
Proof
  Induct >- simp[body_exprs_full_ok_def,exprSimWordArgsTheory.eval_exprs_nil] >>
  rpt gen_tac >> rewrite_tac[APPEND] >>
  once_rewrite_tac[body_exprs_full_ok_def] >> strip_tac >> conj_tac
  >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[Once exprSimWordArgsTheory.eval_exprs_cons_action,bind_def,return_def,AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem blueprint_scalar_source_split[local]:
  LENGTH salts = (if salted then 1 else 0) ==>
  bind (eval_exprs cx (amount::(salts ++ [offset]))) (next:value list -> evaluation_state -> 'a evaluation_result) =
  bind (eval_exprs cx (amount::(salts ++ [offset])))
    (\vs. next (HD vs::((case (if salted then SOME (EL 1 vs) else NONE) of
                         NONE => [] | SOME v => [v]) ++ [LAST vs])))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >> irule bind_cong >> simp[] >>
  rpt gen_tac >> disch_then (mp_tac o MATCH_MP eval_exprs_length) >>
  Cases_on `salted` >> simp[] >>
  simp[listTheory.LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[]
QED

Theorem create_blueprint_expr_full_ok:
  !cx ty b s r ks es d.
    body_exprs_full_ok cx (create_operand_order (CreateFromBlueprint b) s es) ==>
    body_expr_full_ok cx
      (Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[Once body_expr_full_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule blueprint_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (drule blueprint_pre_args >> strip_tac >> gvs[] >>
      `LENGTH salts = (if s then 1 else 0)` by (Cases_on `s` >> gvs[]) >>
      `create_operand_order (CreateFromBlueprint b) s (target::amount::(salts ++ offset::ctor)) =
       target::(ctor ++ amount::(salts ++ [offset]))` by
        (Cases_on `s` >> gvs[create_operand_order_def]) >>
      rewrite_tac[bodySimFullTheory.expr_sim_full_def,GSYM APPEND_ASSOC,APPEND] >>
      rpt gen_tac >> strip_tac >>
      drule_all blueprint_compile_cuts >> strip_tac >>
      qpat_assum `lower_value _ _ _ target sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) blueprint_cut_code) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr target) _ = _`
        (mp_then Any (drule_all_then strip_assume_tac) blueprint_cut_code) >>
      simp[create_eval_read,vyperASTTheory.expr_type_def,
           loweringPostsTheory.post_value_type_def,is_word_type_def] >>
      suspend "target") >>
  irule bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[create_compile_stack,loweringPostsTheory.post_value_type_def,
       vyperASTTheory.expr_type_def,is_word_type_def] >>
  metis_tac[create_eval_value]
QED

Resume create_blueprint_expr_full_ok[target]:
  `expr_body_pre cenv cx env target es'` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     simp[] >> metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts]) >>
  qpat_assum `create_operand_order _ _ _ = _` (fn order_th =>
    qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def] o REWRITE_RULE [order_th])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut) >>
  qexistsl [`tops`,`a'`,`shadow_func`,`shadow_sa`,`a`,`sa`,`x`,`env`,`d'`,`cenv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  qx_genl_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "ctor"
QED

Resume create_blueprint_expr_full_ok[ctor]:
  qpat_assum `( ?a tv b a' v' b'. eval_expr cx target a = _ /\ _) ==> body_exprs_full_ok _ _`
    (drule_then (strip_assume_tac o MATCH_MP create_body_exprs_split)) >>
  rename1 `compile_create_blueprint_args _ _ b _ ctor a = ((p,n),ca)` >>
  rename1 `compile_create_blueprint_args _ _ b _ (MAP gas_shadow_expr ctor) a' = ((p,n),sha)` >>
  rename1 `compile_create_salt _ _ _ c = (sop,cs)` >>
  `valid_horizon cx st0 (storage_trace_horizon et.storage_trace) et.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `is_word_type (BaseT AddressT)` by simp[is_word_type_def] >>
  qpat_assum `expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then (map_every assume_tac o CONJUNCTS)) create_word_cut_facts) >>
  `!H. valid_horizon cx st0 H et.storage_trace ==>
    stmt_state_rel H ctx func cenv cx et st /\ storage_well_formed_on cx et (FST H) /\
    ghost_inv_at (DF H) lo d' cenv cx et Gtar tnt st` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac)) >>
     qpat_assum `expr_post H _ _ _ _ target _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
  `local_ptrs_reserved cenv a /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at a x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at a x)` by
    (qpat_assum `ci_mono sa a` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono]) >>
  rewrite_tac[create_eval_exprs_append] >>
  simp[NoAsms,bind_assoc,bind_return] >>
  qabbrev_tac `src_action = eval_create_operands cx (CreateFromBlueprint b) s r
     (BaseT AddressT::BaseT (UintT 256)::(MAP expr_type salts ++ BaseT (UintT 256)::MAP expr_type ctor))
     (blueprint_literal_offset cx s (target::amount::(salts ++ offset::ctor)))` >>
  qabbrev_tac `Q = \H (res:value + exception) ee G tn t. ?v. res = INL v /\
    expr_post H ctx func cenv cx
      (Call (BaseT AddressT) (CreateTarget (CreateFromBlueprint b) s r ks)
        (target::amount::(salts ++ offset::ctor)) d) es' sa sb s0 ee v op t /\
    expr_store_bound cx (BaseT AddressT) v op t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d' cenv cx ee G tn t /\
    ptr_val_ok cx (BaseT AddressT) v op G tn t /\ ghost_kept_at lo cenv es' sa G0 tn0 s0 G tn` >>
  `!vs bytes eu Gu tu u ctor_marks.
    (if b then vs = [BytesV bytes]
     else encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes) /\
    LENGTH bytes < 2 ** 64 /\
    (!tail. eval_exprs cx ctor (et with gas_obs := gas_explicit ctor_marks st.vs_gas_readings ++ tail) =
      (INL vs,eu with gas_obs := tail)) /\
    expr_sim_inv cenv cx env eu /\
    wb_frame cenv et eu a st u /\ ghost_kept_at lo cenv et a Gtar tnt st Gu tu /\
    st.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    return_buf_frame d' cenv ca u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts /\
    (!v. p = Var v \/ n = Var v ==> not_fresh_at ca v) /\
    storage_trace_domain cx st0 eu.storage_trace /\
    (!H. valid_horizon cx st0 H eu.storage_trace ==>
      valid_horizon cx st0 H et.storage_trace /\ stmt_state_rel H ctx func cenv cx eu u /\
      storage_well_formed_on cx eu (FST H) /\ ghost_inv_at (DF H) lo d' cenv cx eu Gu tu u) /\
    (!vs' ee Gf tf z gs.
      (!tail. eval_exprs cx (amount::(salts ++ [offset])) (eu with gas_obs := gs ++ tail) =
         (INL vs',ee with gas_obs := tail)) /\
      wb_frame cenv eu ee ca u z /\ ghost_kept_at lo cenv eu ca Gu tu u Gf tf /\
      MAP FDOM eu.scopes = MAP FDOM ee.scopes /\ u.vs_alloca_next <= z.vs_alloca_next /\
      storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        valid_horizon cx st0 H eu.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d' cenv cx ee Gf tf z) ==>
      eval_operand n z = SOME (n2w (LENGTH bytes)) /\ op_taint tf n = {} /\ op_prov Gf n = NONE /\
      (n <> Lit 0w ==> ?q a. p = Var q /\ lookup_var q z = SOME a /\ ptr_covers Gf tf q z (LENGTH bytes) /\
        (bytes = [] \/ w2n a + LENGTH bytes <= z.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bytes ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bytes) z = bytes)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (eval_exprs cx (amount::(salts ++ [offset])))
         (\ws. bind (src_action (tv::(vs ++ ws))) (read_result cx))) (eu,u,Gu,tu) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))`
    by suspend "ctor_values" >>
  Cases_on `b` >- suspend "ctor_raw" >>
  Cases_on `ctor = []` >- suspend "ctor_empty" >>
  ho_match_mp_tac (GEN_ALL blueprint_encoded_args_cut) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ ctor a = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctor) _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ a st` (irule_at Any) >>
  qexists `shadow_func` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,Abbr `src_action`,vyperStorageTraceTheory.storage_trace_frame_bind_all,
        vyperStorageTraceTheory.evaluate_storage_trace_frame,
        vyperStorageTraceTheory.storage_trace_frame_read_result,
        vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  suspend "ctor_encoded"
QED

Resume create_blueprint_expr_full_ok[ctor_encoded]:
  qx_genl_tac [`vs`,`bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!vs bytes eu Gu tu u ms. _ ==> gas_outcome_full _ _ _ _ _ _ Q _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `ctor_marks` >> first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  qexists `bytes` >> pure_rewrite_tac[COND_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_expr_full_ok[ctor_values]:
  qx_genl_tac [`vs`,`bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_exprs env ctor` by
    (simp[constSubstCorrectTheory.frame_well_typed_exprs_every,EVERY_MEM] >>
     qx_gen_tac `arg` >> strip_tac >>
     `expr_body_pre cenv cx env arg et` by
       (irule create_operand_pre >>
        qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
     drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env eu` by
    (qpat_assum `!tail. eval_exprs cx ctor _ = (INL vs,_)` (qspec_then `[]` assume_tac) >>
     `body_const_cells_agree [(NONE,tops)] cx env (eu with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_exprs >>
     qexistsl [`ctor`,`INL vs`,
       `et with gas_obs := gas_explicit ctor_marks st.vs_gas_readings`] >> fs[]) >>
  `body_exprs_full_ok cx (amount::(salts ++ [offset]))` by
    (qpat_assum `!st vs en. eval_exprs cx ctor st = (INL vs,en) ==> _` mp_tac >>
     qpat_assum `!tail. eval_exprs cx ctor _ = (INL vs,_)` (qspec_then `[]` mp_tac) >>
     metis_tac[]) >>
  qpat_assum `LENGTH salts = _` (mp_then Any
    (CONV_TAC o RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV o REWR_CONV)
    blueprint_scalar_source_split) >>
  BETA_TAC >>
  ho_match_mp_tac (GEN_ALL (BETA_RULE (Q.INST
    [`next` |-> `\(av:value) sv ov. bind (src_action (tv::(vs ++ av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])))) (read_result cx)`]
    (SPEC_ALL blueprint_scalar_suffix_cut)))) >>
  qpat_assum `return_buf_frame _ _ ca u` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ amount ca = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) _ = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ c = (sop,cs)` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ (OPTION_MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
  qpat_assum `(case _ of NONE => _ | SOME i => comp_return (Lit (i2w i))) cs = _`
    (irule_at Any) >>
  qpat_assum `(case _ of NONE => lower_value _ _ _ (gas_shadow_expr offset)
                | SOME i => comp_return (Lit (i2w i))) _ = _` (irule_at Any) >>
  qexistsl [`x`,`shadow_func`,`n`,`typed_val_to_w256 (BaseTV AddressT) tv`,`p`,`bytes`] >>
  `local_ptrs_reserved cenv ca /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at ca x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at ca x) /\
   (!v. x = Var v ==> not_fresh_at ca v)` by
    (qpat_assum `ci_mono a ca` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono]) >>
  `eval_operand x u = SOME (typed_val_to_w256 (BaseTV AddressT) tv) /\ op_taint tu x = {}` by
    (qpat_assum `wb_frame cenv et eu a st u`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[])
  >- simp[Abbr `src_action`,vyperStorageTraceTheory.storage_trace_frame_bind_all,
      vyperStorageTraceTheory.storage_trace_frame_read_result,
      vyperStorageTraceTheory.storage_trace_frame_create_operands]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!ws ef Gf tf z gs. _ ==> eval_operand n z = SOME (n2w (LENGTH bytes)) /\ _` irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`ee`,`gs`,`av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "scalar_finish"
QED

Resume create_blueprint_expr_full_ok[scalar_finish]:
  qx_genl_tac [`av`,`sv`,`ov`,`yw`,`sw`,`ow`,`ee`,`Gf`,`tf`,`z`,`scalar_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es'.storage_trace`
    by (first_assum irule >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon _ _ H es'.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es' et sa s0 st` by
    (qpat_assum `expr_post _ _ _ _ _ target _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv es' eu sa s0 u /\ ghost_kept_at lo cenv es' sa G0 tn0 s0 Gu tu` by
    (qpat_assum `wb_frame cenv et eu a st u`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sa ca` by metis_tac[ci_mono_trans] >>
  `wb_frame cenv es' ee sa s0 z /\ ghost_kept_at lo cenv es' sa G0 tn0 s0 Gf tf` by
    (qpat_assum `wb_frame cenv eu ee ca u z`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sa f` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= f.cs_next_var /\ s0.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `ci_mono sa f` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  `local_ptrs_reserved cenv f /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at f x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at f x)` by
    metis_tac[local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono] >>
  `accounts_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes` by
    (qpat_assum `expr_sim_inv cenv cx env ee` (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  `IS_SOME ee.outcomes` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee z`
       (SUBST1_TAC o cj 10 o REWRITE_RULE [state_rel_def] o
        MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     simp[NoAsms]) >>
  `?bs. tv = BytesV bs /\ LENGTH bs = 20` by
    (qpat_x_assum `value_has_type (BaseTV AddressT) tv` mp_tac >>
     Cases_on `tv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `tv = BytesV bs` SUBST_ALL_TAC >>
  simp[NoAsms,Abbr `Q`] >>
  irule create_blueprint_finish >>
  qpat_assum `compile_create_blueprint_check _ x off f = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_append x y sop off _ p n r _ = _` (irule_at Any) >>
  qpat_assum `eval_operand x z = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y z = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand off z = SOME _` (irule_at Any) >>
  qpat_assum `OPTREL _ sop sw` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qexistsl [`(lookup_account (word_of_bytes_be bs) ee.accounts).code`,`bytes`] >>
  simp[loweringPostsTheory.post_value_type_def,vyperASTTheory.expr_type_def,
       supportedExprTraverseTheory.expr_has_effect_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_effect_root_def] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (gen_tac >> simp[NoAsms,Abbr `src_action`] >>
      qpat_assum `blueprint_literal_offset _ _ _ <=> _` (pure_once_rewrite_tac o single) >>
      qpat_assum `IS_SOME sv <=> s` (pure_once_rewrite_tac o single o GSYM) >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [Q.INST [`ctor_tys` |-> `MAP expr_type ctor`,
                 `addr` |-> `word_of_bytes_be bs`,
                 `value` |-> `w2n (yw:256 word)`, `off` |-> `w2n (ow:256 word)`,
                 `code` |-> `(lookup_account (word_of_bytes_be bs) (ee:evaluation_state).accounts).code`,
                 `args` |-> `bytes`, `sw` |-> `sw`] blueprint_read_prepared] >>
      simp[NoAsms,vyperValueTheory.dest_AddressV_def,arithmeticTheory.ADD_SYM] >>
      `LENGTH salts = (if IS_SOME sv then 1 else 0)` by
        (qpat_assum `LENGTH salts = _` mp_tac >>
         qpat_assum `IS_SOME sv <=> s` (pure_once_rewrite_tac o single o GSYM) >> simp[NoAsms]) >>
      Cases_on `IS_SOME sv` >>
      simp[IgnAsm `IS_SOME sv <=> s`,listTheory.DROP_APPEND2]) >>
  qpat_assum `!x'. MEM (Var x') [x;off;p;n;y] \/ _ ==> _` mp_tac >> simp[NoAsms]
QED

Resume create_blueprint_expr_full_ok[ctor_raw]:
  qpat_x_assum `T ==> ?e cap. _` (strip_assume_tac o REWRITE_RULE []) >>
  qpat_x_assum `ctor = [e]` SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env e et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `body_expr_full_ok cx e` by
    (qpat_assum `body_exprs_full_ok cx [e]`
       (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >> simp[NoAsms]) >>
  `get_module_code cx NONE = SOME tops` by
    (drule bodyInvCodePropsTheory.body_inv_main_code >> simp[]) >>
  `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
      (int_calls_exprs (amount::(salts ++ [offset])))` by
    (qpat_assum `if s then (?salt. _) else salts = []` mp_tac >> Cases_on `s` >>
     simp[NoAsms] >> strip_tac >> qpat_x_assum `salts = _` SUBST_ALL_TAC >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (fn pre =>
       qpat_assum `body_inv _ _ _ _` (fn inv =>
         mp_tac (MATCH_MP body_inv_expr_pre_calls (CONJ inv pre)))) >>
     simp[NoAsms,int_calls_expr_def,EVERY_APPEND] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_create_blueprint_args _ _ T _ (MAP gas_shadow_expr [e]) _ = _`
    (assume_tac o CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV (SIMP_CONV bool_ss [MAP]))))) >>
  ho_match_mp_tac (GEN_ALL blueprint_raw_args_cut) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [e] a = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ e et` (irule_at Any) >>
  qpat_assum `expr_type e = BaseT (BytesT (Dynamic _))` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ a st` (irule_at Any) >>
  qexists `shadow_func` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,Abbr `src_action`,vyperStorageTraceTheory.storage_trace_frame_bind_all,
        vyperStorageTraceTheory.evaluate_storage_trace_frame,
        vyperStorageTraceTheory.storage_trace_frame_read_result,
        vyperStorageTraceTheory.storage_trace_frame_create_operands]) >>
  qx_genl_tac [`bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!vs bytes eu Gu tu u ms. _ ==> gas_outcome_full _ _ _ _ _ _ Q _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `ctor_marks` >> first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  qexists `bytes` >> pure_rewrite_tac[COND_CLAUSES] >>
  rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)
QED

Resume create_blueprint_expr_full_ok[ctor_empty]:
  qpat_x_assum `ctor = []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_blueprint_args _ _ F _ [] a = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_create_blueprint_args_def,comp_return_def]) >>
  qpat_x_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr []) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_create_blueprint_args_def,comp_return_def]) >>
  gvs[NoAsms] >>
  `eval_exprs cx [] = return []` by
    simp[NoAsms,FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  simp[bind_return] >>
  qpat_assum `!vs bytes eu Gu tu u ms. _ ==> gas_outcome_full _ _ _ _ _ _ Q _`
    (qspec_then `[]` (irule o REWRITE_RULE [APPEND])) >>
  simp[exprSimWordArgsTheory.wb_frame_refl,wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists `[]` >> simp[return_def]) >>
  qexists `[]` >>
  simp[eval_operand_def,op_taint_def] >> EVAL_TAC
QED

Finalise create_blueprint_expr_full_ok

(* The snapshot destination is always the freshly allocated physical buffer.
   This is the compiler-level boundary used by the RawCreate runtime cut. *)
Theorem raw_create_bytecode_physical_input:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  vv_post H ctx func ce cx e es sa sm s0 ee raw vv s ==>
  expr_sim_inv ce cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  vv_location vv <> SOME LocCalldata /\
  ?bs k. v = BytesV bs /\ lowered_value_type ce e = BaseT (BytesT (Dynamic k)) /\
    LENGTH bs <= k /\ k <= n /\
    32 + LENGTH bs <= type_memory_bytes ce (lowered_value_type ce e) /\
    type_memory_bytes ce (lowered_value_type ce e) =
      type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64 /\
    (!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
      vv_type vv = lowered_value_type ce e /\
      32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) =
        type_memory_bytes ce (lowered_value_type ce e))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abiEncodeArgsCaseTheory.abi_args_success_ready) >>
  simp[] >> strip_tac >>
  `?k. lowered_value_type ce e = BaseT (BytesT (Dynamic k)) /\ k <= n` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >> simp[] >>
     Cases_on `lowered_value_type ce e` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT bt) _` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def]) >>
  `tv = BaseTV (BytesT (Dynamic k))` by
    metis_tac[abiValueEncodingTheory.evaluate_type_base_result] >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  drule exprSimConvertFromBytesTheory.dynamic_bytes_value_typed >> strip_tac >>
  `LENGTH bs <= 32 * word_size k` by
    (mp_tac (Q.SPEC `k` exprSimPropsTheory.le_word_size_mul) >> decide_tac) >>
  simp[] >>
  conj_tac
  >- (Cases_on `vv` >> simp[vv_location_def] >>
      drule exprPtrUnwrapMarkedTheory.vv_post_not_calldata >> simp[]) >>
  conj_tac >- simp[valueEncodingTheory.type_memory_size_def] >>
  gen_tac >> strip_tac >>
  `vv_type vv = BaseT (BytesT (Dynamic k))` by
    (Cases_on `vv` >> gvs[vv_location_def,vv_type_def] >>
     drule_all exprPtrUnwrapStorageShapeTheory.compile_nonmemory_lowered_value_type >>
     simp[] >> strip_tac >>
     drule exprPtrUnwrapMarkedTheory.vv_post_located_type >>
     simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def]) >>
  gvs[bodyImmutableCopyMemoryTheory.body_immutable_copy_aligned_size]
QED

(* The second RawCreate allocation is also static. Its MCOPY uses the
   static frontier even when the enclosing context contains DALLOCA. *)
Theorem raw_create_static_mcopy_path[local]:
  compile_copy_memory_dynamic (Var dst) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ lookup_var dst s = SOME (n2w db) /\
  lookup_var src s = SOME (n2w sb) /\ eval_operand len s = SOME (n2w n) /\
  op_taint tn len = {} /\ ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
  db < dimword (:256) /\ sb < dimword (:256) /\ n < dimword (:256) /\
  db+n <= s.vs_alloca_next /\ sb+n <= s.vs_alloca_next /\
  (!i. sb <= i /\ i < sb+n ==> i NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  b.cs_current_bb = a.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mcopy db sb n s with vs_inst_idx := LENGTH b.cs_current_insts),G,
     tn with t_mem := tn.t_mem DIFF {i | db <= i /\ i < db+n}))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  `w2n (n2w db:bytes32) = db /\ w2n (n2w sb:bytes32) = sb /\
   w2n (n2w n:bytes32) = n` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  qabbrev_tac `i = mk_inst a.cs_next_id MCOPY [Var dst;Var src;len] []` >>
  `step_taint i s (mcopy db sb n s) tn =
   tn with t_mem := tn.t_mem DIFF {j | db <= j /\ j < db+n}` by
    (`{db+q | q < n /\ q+sb IN tn.t_mem} = {}` by
       (simp[pred_setTheory.EXTENSION] >> gen_tac >> Cases_on `q < n` >> simp[] >>
        qpat_assum `!i. sb <= i /\ i < sb+n ==> _`
          (qspec_then `q+sb` mp_tac) >> simp[]) >>
     `i.inst_opcode = MCOPY /\ i.inst_outputs = [] /\
      i.inst_operands = [Var dst;Var src;len] /\
      eval_operand (Var dst) s = SOME (n2w db) /\ eval_operand (Var src) s = SOME (n2w sb)`
       by simp[Abbr `i`,mk_inst_def,eval_operand_def] >>
     drule_all taintAgreeTheory.step_taint_mcopy >> simp[pred_setTheory.EXTENSION]) >>
  `get_instruction bb s.vs_inst_idx = SOME i /\
   lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `i`] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`,inst_mem_below_frontier_def,inst_dload_in_section_def,mk_inst_def,
         source_memory_read_ranges_def,source_memory_write_ranges_def,
         sized_source_write_range_def,eval_operand_def] >>
  `ptr_covers G tn dst s (w2n (n2w n:bytes32)) /\
   ptr_covers G tn src s (w2n (n2w n:bytes32))` by simp[] >>
  `SUC s.vs_inst_idx = LENGTH b.cs_current_insts` by simp[] >>
  simp[] >> rpt gen_tac >>
  qpat_x_assum `Abbrev (i = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all bodyFullAbiEncodeCopyTheory.abi_encode_mcopy_origin_path >> simp[]
QED

(* Only the live bytecode is copied. The static owner is the start of
   initcode; the encoder destination is the byte immediately after bs. *)
Theorem raw_create_encoder_saved_prefix:
  compile_alloc_buffer cap se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) len a = ((),b) /\
  emit_op ADD [buf.buf_operand;len] b = (op,c) /\
  fn_has_code a b func /\ fn_has_code b c func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  LENGTH bs <= cap /\ cap < dimword (:256) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  not_fresh_at se src /\ (!x. len = Var x ==> not_fresh_at se x) /\
  (!label. len <> Label label) /\ source < dimword (:256) /\
  lookup_var src s = SOME (n2w source) /\ ptr_covers G tn src s (LENGTH bs) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  read_memory source (LENGTH bs) s = bs /\ source + LENGTH bs <= s.vs_alloca_next /\
  (!i. source <= i /\ i < source+LENGTH bs ==> i NOTIN tn.t_mem) ==>
  ?root dst pbase inst z Gz tz.
    buf.buf_operand = Var root /\ op = Var dst /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase cap root dst (LENGTH bs) bs c z Gz tz /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_alloc_buffer_saved_start >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`root`,`pbase`,`u`,`Gu`,`tu`,`inst`]
      (map_every assume_tac o CONJUNCTS))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  drule bodyFullExtCallDirectStateTheory.abi_encode_saved_state_resources >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  `eval_operand len u = SOME (n2w (LENGTH bs)) /\ op_taint tu len = {} /\ op_prov Gu len = NONE` by
    (Cases_on `len` >> gvs[eval_operand_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  `lookup_var src u = SOME (n2w source) /\ ptr_covers Gu tu src u (LENGTH bs)` by
    (conj_tac >- metis_tac[] >> irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
     qexistsl [`G`,`s`,`se`,`tn`] >> simp[]) >>
  `!i. source <= i /\ i < source+LENGTH bs ==> i NOTIN tu.t_mem` by
    (rpt strip_tac >> `i < s.vs_alloca_next` by
       (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists `source+LENGTH bs` >> simp[]) >>
     qpat_assum `!j. j IN tu.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `!j. source <= j /\ j < source+LENGTH bs ==> _` (qspec_then `i` mp_tac) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `source+LENGTH bs <= u.vs_alloca_next /\ pbase+LENGTH bs <= u.vs_alloca_next /\
   pbase < dimword (:256) /\ LENGTH bs < dimword (:256)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`source+LENGTH bs <= s.vs_alloca_next`,`s.vs_alloca_next <= u.vs_alloca_next`,
        `LENGTH bs <= cap`,`pbase+cap <= u.vs_alloca_next`,`pbase+cap < dimword (:256)`] >>
     numLib.ARITH_TAC) >>
  `ptr_covers Gu tu root u (LENGTH bs)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `lookup_var root u = SOME (n2w pbase)` by fs[eval_operand_def] >>
  qpat_x_assum `buf.buf_operand = Var root` SUBST_ALL_TAC >>
  drule_all raw_create_static_mcopy_path >> disch_then (qspec_then `PG` strip_assume_tac) >>
  qabbrev_tac `v = mcopy pbase source (LENGTH bs) u with vs_inst_idx := LENGTH b.cs_current_insts` >>
  qabbrev_tac `tv = tu with t_mem := tu.t_mem DIFF {i | pbase <= i /\ i < pbase+LENGTH bs}` >>
  `allocas_from lo v = allocas_from lo u /\ allocas_below_fmp v = allocas_below_fmp u` by
    simp[NoAsms,Abbr `v`,mcopy_def,write_memory_with_expansion_def,write_memory_def,
         allocas_from_def,allocas_below_fmp_def] >>
  `v.vs_current_bb = b.cs_current_bb /\ v.vs_inst_idx = LENGTH b.cs_current_insts /\
   ~v.vs_halted /\ allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    simp[Abbr `v`,mcopy_def,write_memory_with_expansion_def,write_memory_def] >>
  `eval_operand (Var root) v = SOME (n2w pbase) /\ eval_operand len v = SOME (n2w (LENGTH bs)) /\
   op_taint tv (Var root) = {} /\ op_taint tv len = {} /\ op_prov Gu len = NONE` by
    (qpat_assum `ptr_covers Gu tu root u (LENGTH bs)`
       (assume_tac o cj 1 o REWRITE_RULE [ptr_covers_def]) >>
     `!x. eval_operand x v = eval_operand x u` by
       (Cases >> simp[NoAsms,Abbr `v`,mcopy_def,write_memory_with_expansion_def,
         write_memory_def,eval_operand_def,lookup_var_def]) >>
     `!x. op_taint tv x = op_taint tu x` by
       (Cases >> simp[NoAsms,Abbr `tv`,op_taint_def]) >>
     asm_rewrite_tac[arithmeticTheory.ADD_CLAUSES]) >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`dst`,`z`,`Gz`,`tz`]
    (map_every assume_tac o CONJUNCTS))) >>
  `ci_mono a b` by
    (qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     metis_tac[ci_mono_emit_void,pairTheory.SND]) >>
  `ci_mono b c` by metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `a.cs_next_var <= b.cs_next_var /\ b.cs_next_var <= c.cs_next_var /\
   se.cs_next_var <= c.cs_next_var /\ se.cs_next_id < c.cs_next_id` by
    (fs[ci_mono_def] >> numLib.ARITH_TAC) >>
  `!x. not_fresh_at a x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at b x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     `x <> dst` by simp[] >>
     qpat_assum `!p. p <> dst ==> _` (drule_then strip_assume_tac) >>
     simp[Abbr `v`,Abbr `tv`,mcopy_def,write_memory_with_expansion_def,write_memory_def,
          lookup_var_def,op_taint_def]) >>
  `!x. not_fresh_at se x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit',ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
       metis_tac[abiDecodeValidFiniteLoopTheory.finite_array_empty_path_explicit] >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
   z.vs_memory = (mcopy pbase source (LENGTH bs) u).vs_memory /\
   ~z.vs_halted /\ z.vs_inst_idx = LENGTH c.cs_current_insts` by
    (qpat_assum `z = _` SUBST1_TAC >>
     simp[Abbr `v`,update_var_def,mcopy_def,write_memory_with_expansion_def,write_memory_def]) >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,explicit,ctx,func,PG)
     (u,Gu,tu) [] (OK z,Gz,tz)` by metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `alloca_history func z` by
    (drule_all bodyFullPathHistoryTheory.body_full_path_alloca_history >> simp[]) >>
  `!off k. off+k <= pbase \/ pbase+LENGTH bs <= off ==>
    mem_bytes_at off k z.vs_memory = mem_bytes_at off k u.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `z.vs_memory = _` SUBST1_TAC >>
     irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> simp[]) >>
  `!name b k. local_region ce ee.scopes u name b k ==>
    pbase+LENGTH bs <= b \/ b+k <= pbase` by
    (rpt strip_tac >> qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _`
       (drule_then mp_tac) >> rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `typed_copy_state_frame se pbase (LENGTH bs) u z` by
    (rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     conj_tac
     >- (qpat_assum `z = _` SUBST1_TAC >>
         simp[Abbr `v`,update_var_def,mcopy_def,write_memory_with_expansion_def,
              write_memory_def,venom_state_component_equality]) >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     rewrite_tac[typedMemoryCopyTheory.typed_copy_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `z.vs_memory = _` SUBST1_TAC >>
     irule exprSimAbiEncodeMemoryLengthTheory.abi_encode_mcopy_memory_length) >>
  `tz.t_mem = tu.t_mem DIFF {i | pbase <= i /\ i < pbase+LENGTH bs}` by simp[Abbr `tv`] >>
  `lo <= pbase` by
    (qpat_assum `allocas_from lo u`
       (qspec_then `se.cs_next_id` mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gz tz` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE` by
    (Cases_on `len` >> fs[eval_operand_def,op_taint_def,op_prov_def]) >>
  qexistsl [`root`,`dst`,`pbase`,`inst`,`z`,`Gz`,`tz`] >>
  simp[IgnAsm `z = _`] >> suspend "saved"
QED

Resume raw_create_encoder_saved_prefix[saved]:
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (simp[IgnAsm `z = _`,allocas_from_def] >> fs[IgnAsm `z = _`,allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  `!j. j < pbase \/ pbase+LENGTH bs <= j ==> (j IN tz.t_mem <=> j IN tu.t_mem)` by
    (rpt gen_tac >> disch_tac >> simp[IgnAsm `z = _`,pred_setTheory.IN_DIFF] >>
     numLib.ARITH_TAC) >>
  `!name b k. local_region ce ee.scopes u name b k ==>
     loweringStateRelDefs$regions_disjoint pbase (LENGTH bs) b k` by
    (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gz tz z` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (irule placeStoreDynPrepareTheory.place_typed_copy_alloca_state_frame >>
         qpat_assum `typed_copy_state_frame _ _ _ u z` (irule_at Any) >>
         qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
         qexists `cap` >> simp[IgnAsm `z = _`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `local_ptrs_rel func ce ee.scopes u` by
       (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `stor_taint_ok_at (DF H) tu u` by fs[ghost_inv_at_def,IgnAsm `z = _`] >>
     `stor_taint_ok_at (DF H) tz z` by
       (qpat_assum `z = _` SUBST1_TAC >>
        fs[stor_taint_ok_at_def,Abbr `v`,Abbr `tv`,update_var_def,mcopy_def,
           write_memory_with_expansion_def,write_memory_def]) >>
     drule_all bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at >> simp[]) >>
  `wb_frame ce ee ee se s z` by
    (irule exprSimHashTheory.wb_frame_allocating_tail >>
     conj_tac >- simp[] >>
     qexistsl [`u`,`ee.scopes`,`se`] >>
     simp[IgnAsm `z = _`,IgnAsm `z.vs_memory = _`,IgnAsm `u.vs_memory = _`] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!off k. _ ==> mem_bytes_at off k z.vs_memory = _` irule >>
         metis_tac[]) >>
     qx_gen_tac `aid` >> rpt gen_tac >> strip_tac >>
     qpat_assum `!off k. _ ==> mem_bytes_at off k z.vs_memory = _` irule >>
     qpat_assum `alloca_inv u` (mp_tac o REWRITE_RULE
       [alloca_inv_def,allocas_non_overlapping_def]) >> strip_tac >>
     `aid <> se.cs_next_id` by
       (qpat_assum `aid < se.cs_next_id` mp_tac >> numLib.ARITH_TAC) >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _` (drule_all_then mp_tac) >>
     qpat_assum `LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `not_fresh_at c root` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (Var root) z = SOME (n2w pbase) /\ ptr_covers Gz tz root z cap` by
    (conj_tac >- simp[IgnAsm `z = _`,eval_operand_def] >>
     irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
     qexistsl [`Gu`,`u`,`a`,`tu`] >> simp[IgnAsm `z = _`]) >>
  qpat_x_assum `op = Var dst` SUBST_ALL_TAC >>
  `lookup_var dst z = SOME (n2w pbase + n2w (LENGTH bs)) /\
   FLOOKUP Gz dst = SOME (pbase,cap)` by
    fs[IgnAsm `z = _`,eval_operand_def,op_prov_def] >>
  `pbase + LENGTH bs < dimword (:256)` by
    (qpat_assum `pbase+cap < dimword (:256)` mp_tac >>
     qpat_assum `LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `ptr_covers Gz tz dst z (cap - LENGTH bs)` by
    (irule assignBasePtrOffsetTheory.assign_base_ptr_covers_offset_address >>
     qpat_assum `ptr_covers Gu tu root u cap` (irule_at Any) >>
     qpat_assum `lookup_var root u = SOME _` (irule_at (Pat `lookup_var root u = SOME _`)) >>
     qpat_assum `FLOOKUP Gu root = SOME _` (irule_at Any) >>
     qexists `LENGTH bs` >>
     fs[IgnAsm `z = _`,wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  `read_memory pbase (LENGTH bs) z = bs` by
    (`read_memory pbase (LENGTH bs) z = read_memory pbase (LENGTH bs)
       (mcopy pbase source (LENGTH bs) u)` by
       simp[IgnAsm `z = _`,memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
     fs[IgnAsm `z = _`,memoryReadPropsTheory.read_memory_mcopy_self,
        memoryReadPropsTheory.read_memory_eq_mem_bytes_at]) >>
  simp[IgnAsm `z = _`,bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def,
       wordsTheory.word_add_n2w,pred_setTheory.IN_DIFF]
QED

Finalise raw_create_encoder_saved_prefix

Theorem raw_create_pre_args:
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?code amount ctor salts bound.
    args = code :: amount :: (ctor ++ salts) /\
    expr_type code = BaseT (BytesT (Dynamic bound)) /\ bound <= 49152 /\
    expr_type amount = BaseT (UintT 256) /\
    LENGTH salts = (if salted then 1 else 0) /\
    EVERY (\e. expr_type e = BaseT (BytesT (Fixed 32))) salts /\
    create_operand_order RawCreate salted args = code :: (ctor ++ amount :: salts) /\
    EVERY (\e. expr_body_pre ce cx env e es) args /\
    (ctor <> [] ==> bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type ctor)) < 2 ** 64)
Proof
  strip_tac >> drule expr_body_pre_static_facts >>
  simp[well_typed_expr_def,create_arg_types_ok_def,listTheory.MAP_EQ_CONS] >>
  strip_tac >>
  `?code amount ctor salts bound.
    args = code :: amount :: (ctor ++ salts) /\
    expr_type code = BaseT (BytesT (Dynamic bound)) /\ bound <= 49152 /\
    expr_type amount = BaseT (UintT 256) /\
    MAP expr_type salts = (if salted then [BaseT (BytesT (Fixed 32))] else [])` by
    (Cases_on `salted` >> fs[listTheory.MAP_EQ_APPEND] >> metis_tac[]) >>
  `EVERY (\e. expr_body_pre ce cx env e es) args` by
    (rewrite_tac[listTheory.EVERY_MEM] >> rpt strip_tac >>
     drule_all create_operand_pre >> simp[]) >>
  qexistsl [`code`,`amount`,`ctor`,`salts`,`bound`] >>
  Cases_on `salted` >>
  gvs[listTheory.MAP_EQ_CONS,listTheory.MAP_EQ_NIL,alloc_limits_expr_def,ext_call_alloc_ok_def,
      vyperTypeSystemTheory.bytelike_type_bound_def,create_operand_order_def,
      rich_listTheory.FRONT_APPEND,rich_listTheory.DROP_LENGTH_APPEND,
      rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem raw_create_read_prepared:
  IS_SOME ee.outcomes /\ dest_NumV amount = SOME value /\
  dest_optional_salt salt = SOME sw /\ LENGTH salt_tys = (if IS_SOME salt then 1 else 0) /\
  (if ctor_tys = [] /\ cvs = [] then encoded = []
   else encode_create_ctor_args (get_tenv cx) ctor_tys cvs = SOME encoded) ==>
  bind (eval_create_operands cx RawCreate (IS_SOME salt) rof
    (code_ty :: amount_ty :: (ctor_tys ++ salt_tys)) lit
    (BytesV bs :: (cvs ++ amount :: (case salt of NONE => [] | SOME v => [v]))))
    (read_result cx) ee =
  if LENGTH (bs ++ encoded) > 2 * max_code_size then
    (INR (Error (RuntimeError "create initcode too large")),ee)
  else bind (ignore_bind (check_not_static cx)
    (create_oracle_result sw value (bs ++ encoded) rof)) (read_result cx) ee
Proof
  strip_tac >>
  `encode_create_ctor_args (get_tenv cx) ctor_tys cvs = SOME encoded` by
    (Cases_on `ctor_tys = [] /\ cvs = []` >> gvs[] >> EVAL_TAC) >>
  `create_operand_layout RawCreate (IS_SOME salt)
     (BytesV bs :: (cvs ++ amount :: (case salt of NONE => [] | SOME v => [v]))) =
   BytesV bs :: amount :: (cvs ++ (case salt of NONE => [] | SOME v => [v]))` by
    (Cases_on `salt` >> simp[create_operand_layout_def,rich_listTheory.DROP_LENGTH_APPEND,
      rich_listTheory.TAKE_LENGTH_APPEND]) >>
  `dest_create_args RawCreate (IS_SOME salt)
     (BytesV bs :: amount :: (cvs ++ (case salt of NONE => [] | SOME v => [v]))) =
   SOME <|co_code_src := BytecodeCodeSource bs; co_ctor_args := cvs;
          co_value := value; co_code_offset := NONE; co_salt := sw|>` by
    (Cases_on `salt` >> fs[dest_optional_salt_def] >>
     simp[dest_create_args_def,make_create_operands_def,vyperValueTheory.dest_BytesV_def,
          dest_optional_num_def,dest_optional_salt_def,
          rich_listTheory.FRONT_APPEND,listTheory.LAST_CONS_cond]) >>
  `create_arg_ctor_types RawCreate (IS_SOME salt)
    (code_ty :: amount_ty :: (ctor_tys ++ salt_tys)) = SOME ctor_tys` by
    (Cases_on `salt` >> fs[LENGTH_EQ_NUM_compute] >>
     simp[create_arg_ctor_types_def,rich_listTheory.FRONT_APPEND]) >>
  simp[eval_create_operands_def,eval_create_def,
       bind_def,ignore_bind_def,lift_option_type_def,lift_option_def,get_accounts_def] >>
  simp[build_create_code_def,raw_create_initcode_def,check_def,check_not_static_def,
       assert_def,return_def,raise_def] >>
  Cases_on `LENGTH bs + LENGTH encoded <= 2 * max_code_size` >>
  Cases_on `cx.txn.is_static` >> fs[arithmeticTheory.ADD_COMM,arithmeticTheory.NOT_GREATER]
QED

(* Protect the containing allocation, then restrict its frame to the live
   subrange. The data operand may point inside the owner's allocation. *)
Theorem raw_create_owned_window_frame:
  stmt_state_rel H ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [root] /\ not_local_ptr ce es.scopes root /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (pbase,cap) /\ inst.inst_id < sa.cs_next_id /\
  pbase + cap <= s.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
  w2n pv = pbase + off /\ off + LENGTH bs <= cap /\
  not_fresh_at sa p /\ lookup_var p s = SOME pv /\
  ptr_covers G tn p s (LENGTH bs) /\ op_taint tn (Var p) = {} /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ (!l. len <> Label l) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  read_memory (pbase+off) (LENGTH bs) s = bs /\
  (!i. pbase+off <= i /\ i < pbase+off+LENGTH bs ==> i NOTIN tn.t_mem) /\
  wb_frame ce es ef sa s t /\ ghost_kept_at lo ce es sa G tn s Gtail tt ==>
  FLOOKUP t.vs_allocas inst.inst_id = SOME (pbase,cap) /\
  lookup_var p t = SOME pv /\ ptr_covers Gtail tt p t (LENGTH bs) /\ op_taint tt (Var p) = {} /\
  eval_operand len t = SOME (n2w (LENGTH bs)) /\ op_taint tt len = {} /\ op_prov Gtail len = NONE /\
  w2n pv + LENGTH bs <= t.vs_alloca_next /\
  read_memory (w2n pv) (LENGTH bs) t = bs /\
  (!i. w2n pv <= i /\ i < w2n pv+LENGTH bs ==> i NOTIN tt.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n b sz. local_region ce es.scopes s n b sz ==> pbase + cap <= b \/ b + sz <= pbase` by
    (rpt gen_tac >> disch_tac >>
     rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qpat_assum `stmt_state_rel _ ctx func ce cx es s`
       (map_every (irule_at Any) o CONJUNCTS o
         MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `local_region ce es.scopes s n b sz` (irule_at Any) >>
     qpat_assum `inst.inst_outputs = [root]` (irule_at Any) >> simp[]) >>
  `eval_operand len t = SOME (n2w (LENGTH bs)) /\ op_taint tt len = {}` by
    (drule_all create_operand_cut_frame >> simp[]) >>
  qpat_assum `wb_frame ce es ef sa s t`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  qpat_assum `ghost_kept_at lo ce es sa G tn s Gtail tt`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  `lookup_var p t = SOME pv` by simp[] >>
  `ptr_covers Gtail tt p t (LENGTH bs)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers G tn p s (LENGTH bs)` (irule_at Any) >> simp[]) >>
  `op_prov Gtail len = NONE` by
    (Cases_on `len` >> gvs[ptrDisciplineTheory.op_prov_def]) >>
  `pbase + off + LENGTH bs <= t.vs_alloca_next` by
    (qpat_assum `off + LENGTH bs <= cap` mp_tac >>
     qpat_assum `pbase + cap <= s.vs_alloca_next` mp_tac >>
     qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >> numLib.ARITH_TAC) >>
  `mem_bytes_at pbase cap t.vs_memory = mem_bytes_at pbase cap s.vs_memory` by
    (qpat_assum `!aid b sz. _ ==> mem_bytes_at b sz t.vs_memory = _`
       (qspecl_then [`inst.inst_id`,`pbase`,`cap`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `mem_bytes_at (pbase+off) (LENGTH bs) t.vs_memory =
   mem_bytes_at (pbase+off) (LENGTH bs) s.vs_memory` by
    (irule valueEncodingPropsTheory.mem_bytes_at_translated_window >> qexists `cap` >> simp[]) >>
  `!i. pbase+off <= i /\ i < pbase+off+LENGTH bs ==> i NOTIN tt.t_mem` by
    (qx_gen_tac `i` >> strip_tac >> strip_tac >>
     `pbase <= i /\ i < pbase + cap` by
       (qpat_assum `pbase+off <= i` mp_tac >> qpat_assum `i < pbase+off+LENGTH bs` mp_tac >>
        qpat_assum `off + LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
     qpat_assum `!aid b sz i. _ ==> i IN tn.t_mem`
       (qspecl_then [`inst.inst_id`,`pbase`,`cap`,`i`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i. pbase+off <= i /\ i < pbase+off+LENGTH bs ==> i NOTIN tn.t_mem`
       (qspec_then `i` mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  fs[memoryReadPropsTheory.read_memory_eq_mem_bytes_at]
QED

(* The three bytecode sources write only the snapshot allocation. *)
Theorem raw_create_snapshot_wb[local]:
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  (?u. z.vs_allocas = u.vs_allocas /\
    !aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz) /\
  (!aid a sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
      regions_disjoint b cap a sz) /\
  (!a sz. a+sz <= b \/ b+cap <= a ==>
      mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory) ==>
  wb_frame ce ee ee sa s z
Proof
  strip_tac >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule exprSimHashTheory.wb_frame_allocating_tail >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`s`,`ee.scopes`,`sa`] >>
  simp[NoAsms,exprSimWordArgsTheory.wb_frame_refl] >>
  rpt conj_tac
  >~ [`!name a sz. local_region ce ee.scopes s name a sz ==>
         mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory`]
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!a sz. _ ==> mem_bytes_at a sz z.vs_memory = _` irule >>
      qpat_assum `!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz`
        (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM])
  >~ [`!aid a sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
         mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory`]
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a sz. _ ==> mem_bytes_at a sz z.vs_memory = _` irule >>
      qpat_assum `!aid a sz. _ ==> regions_disjoint b cap a sz` (drule_all_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  first_assum ACCEPT_TAC
QED

Theorem raw_create_snapshot_kept[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  lo <= s.vs_alloca_next /\ lo <= b /\ ci_mono sa sm /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+cap)) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
      FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
  (!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz) /\
  (!aid a sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
      regions_disjoint b cap a sz) /\
  (!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem) ==>
  ghost_kept_at lo ce ee sa G tn s Gz tz
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G x /\
       op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sm x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists `sa` >> fs[ci_mono_def]) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `!aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) ==> a+sz <= s.vs_alloca_next` by
    fs[alloca_inv_def,alloca_next_valid_def] >>
  `!name a sz. local_region ce ee.scopes s name a sz ==> a+sz <= s.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >> drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
  `ghost_kept_at lo ce ee sa G tn s Gu tu` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl [`G`,`b+cap`,`s`,`tn`] >>
     simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at >>
  qpat_assum `ghost_kept_at lo ce ee sa G tn s Gu tu` (irule_at Any) >>
  rpt conj_tac
  >~ [`!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!name base len. local_region ce ee.scopes s name base len ==>
          off+sz <= base \/ base+len <= off) /\
        off <= i /\ i < off+sz /\ i IN tz.t_mem ==> i IN tu.t_mem`]
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem` irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!aid a sz. _ ==> regions_disjoint b cap a sz`
        (drule_all_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
      intLib.COOPER_TAC)
  >~ [`!name off sz i. local_region ce ee.scopes s name off sz /\
        off <= i /\ i < off+sz /\ i IN tz.t_mem ==> i IN tu.t_mem`]
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem` irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz`
        (drule_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
      intLib.COOPER_TAC)
  >~ [`!i. i < lo /\ i IN tz.t_mem ==> i IN tu.t_mem`]
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem` irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists `lo` >> asm_rewrite_tac[]) >>
  first_assum ACCEPT_TAC
QED

Theorem raw_create_snapshot_copy_horizon[local]:
  stmt_state_rel H ctx func ce cx ee u /\ typed_copy_state_frame sm b cap u z /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,cap) /\ local_ptrs_reserved ce sm /\
  ghost_inv_at (DF H) lo d ce cx ee Gu tu u /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!name a sz. local_region ce ee.scopes u name a sz ==> regions_disjoint b cap a sz) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
  (!a sz. a+sz <= b \/ b+cap <= a ==>
       mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz u.vs_memory) /\
  (!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem) /\
  z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
  z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables /\
  tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
  lo <= b /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  stmt_state_rel H ctx func ce cx ee z /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z
Proof
  strip_tac >> conj_tac
  >- (irule placeStoreDynPrepareTheory.place_typed_copy_alloca_state_frame >>
      qpat_assum `typed_copy_state_frame _ _ _ u z` (irule_at Any) >>
      qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
      qexists `cap` >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `local_ptrs_rel func ce ee.scopes u` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ u`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at (DF H) tz z` by
    (qpat_assum `ghost_inv_at (DF H) lo d ce cx ee Gu tu u`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     strip_tac >> simp[stor_taint_ok_at_def] >>
     qpat_assum `stor_taint_ok_at (DF H) tu u`
       (ACCEPT_TAC o REWRITE_RULE [stor_taint_ok_at_def])) >>
  `!name a sz. local_region ce ee.scopes u name a sz ==> b+cap <= a \/ a+sz <= b` by
    (qpat_assum `!name a sz. local_region ce ee.scopes u name a sz ==> regions_disjoint b cap a sz`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `!j. j < b \/ b+cap <= j ==> (j IN tz.t_mem ==> j IN tu.t_mem)` by
    (gen_tac >> disch_tac >> disch_tac >>
     qpat_assum `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> _` irule >>
     asm_rewrite_tac[]) >>
  drule_all bodyFullUnwrapSlotFrameTheory.unwrap_slot_copy_ghost_inv_at_mono >> simp[]
QED

(* The slot branches both emit a counted loop, even when the buffer has
   room for only the length word. *)
Theorem raw_create_snapshot_slot_path:
  compile_create_snapshot ce (LocatedValue tag p) (BaseT (BytesT (Dynamic k))) sa = (out,sb) /\
  p.ptr_location = slot_loc tr /\
  storage_holds cx tr (BaseT (BytesT (Dynamic k))) tv key ee s /\
  ptr_vv_ok cx (BaseT (BytesT (Dynamic k))) tv (LocatedValue tag p) ee G tn s /\
  read_result cx tv ee = (INL (BytesV bs),ee) /\
  eval_operand p.ptr_operand s = SOME key /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  cap = type_memory_bytes ce (BaseT (BytesT (Dynamic k))) /\
  cap = 32 * type_slot_size (BaseTV (BytesT (Dynamic k))) /\
  32 + LENGTH bs <= cap /\ cap < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root b inst z Gz tz.
    out = Var root /\ MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root /\ not_fresh_at sb root /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (b,cap) /\
    eval_operand out z = SOME (n2w b) /\ ptr_covers Gz tz root z cap /\
    b+cap < dimword (:256) /\ b+cap <= z.vs_alloca_next /\
    mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem) /\
    wb_frame ce ee ee sa s z /\ ghost_kept_at lo ce ee sa G tn s Gz tz /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    return_buf_frame d ce sb z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_alloc_buffer cap sa` >>
  rename1 `compile_alloc_buffer cap sa = (buf,sm)` >>
  qabbrev_tac `n = type_slot_size (BaseTV (BytesT (Dynamic k)))` >>
  `(cap+31) DIV 32 = n` by
    (qpat_assum `cap = 32 * n` mp_tac >> simp[]) >>
  Cases_on `compile_slot_to_memory p.ptr_operand buf.buf_operand n p.ptr_location sm` >>
  rename1 `compile_slot_to_memory _ _ _ _ _ = (lab,sc)` >>
  `out = buf.buf_operand /\ sc = sb` by
    (Cases_on `tr` >> fs[loweringPostsTheory.slot_loc_def] >>
     gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,
         comp_return_def,vv_location_def,vv_operand_def]) >>
  qpat_x_assum `sc = sb` SUBST_ALL_TAC >>
  `ci_mono sa sm` by
    (qspecl_then [`cap`,`sa`] mp_tac exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`p.ptr_operand`,`buf.buf_operand`,`n`,`p.ptr_location`,`sm`] mp_tac
      (cj 3 stmtLoweringMonoTheory.ci_mono_context_helpers) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`]
      (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `b = w2n (w:bytes32)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\ u.vs_halted = s.vs_halted /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `compile_word_copy_loop p.ptr_operand (Var root) n p.ptr_location LocMemory F sm = (lab,sb)` by
    fs[compile_slot_to_memory_def] >>
  `eval_operand p.ptr_operand u = SOME key /\ op_taint tu p.ptr_operand = {}` by
    (`op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
     Cases_on `p.ptr_operand` >> fs[eval_operand_def,op_taint_def]) >>
  `lookup_var root u = SOME (n2w b)` by simp[Abbr `b`] >>
  `n < 2**256` by
    (qpat_assum `cap = 32 * n` mp_tac >>
     qpat_assum `cap < dimword (:256)` mp_tac >> simp[NoAsms] >> numLib.ARITH_TAC) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` assume_tac
  >- (Cases_on `tr` >> fs[loweringPostsTheory.slot_loc_def]) >>
  `ptr_covers Gu tu root u (32*n) /\ b+32*n < 2**256 /\ b+32*n <= u.vs_alloca_next` by
    (qpat_assum `cap = 32 * n` (SUBST1_TAC o SYM) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `b+cap < dimword (:256)` mp_tac >> simp[NoAsms]) >>
     first_assum ACCEPT_TAC) >>
  `~u.vs_halted` by simp[] >>
  drule_all fragGasCopyLoopTheory.storage_copy_loop_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`cv`,`ds`] strip_assume_tac)) >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_destination >> strip_tac >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE
    [exprSimStorageCopyTheory.storage_copy_inv_def,exprSimStorageCopyTheory.copy_prefix_def,
     exprSimStorageCopyTheory.storage_copy_frame_def]) >>
  `z with <|vs_vars := u.vs_vars;vs_memory := u.vs_memory;vs_prev_bb := u.vs_prev_bb;
            vs_current_bb := u.vs_current_bb;vs_inst_idx := u.vs_inst_idx|> = u` by
    (qpat_assum `copy_static z = copy_static u` mp_tac >>
     simp[NoAsms,exprSimStorageCopyTheory.copy_static_def,
          venomStateTheory.venom_state_component_equality]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
   z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
   z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables /\ z.vs_fmp = u.vs_fmp` by
    (qpat_assum `z with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;
                         vs_current_bb := _;vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_storage_taint >> strip_tac >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_transient_taint >> strip_tac >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_immutable_taint >> strip_tac >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
      FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)` by
    (gen_tac >> strip_tac >> `~MEM x ds` by simp[] >>
     drule_all exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_ghost_frame >> simp[]) >>
  drule exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_inv_memory_taint >> strip_tac >>
  `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `tz.t_mem SUBSET _` (mp_tac o SIMP_RULE (srw_ss())
       [exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_taint_bound_def,
        exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_region_def,
        exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_translated_taint_def,
        pred_setTheory.SUBSET_DEF]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >> gvs[] >> intLib.COOPER_TAC) >>
  `!j r. j < n /\ r < 32 /\ b+32*j+r IN tz.t_mem ==>
      r IN key_taint (if tr then tn.t_trans else tn.t_stor) (key+n2w j)` by
    (rpt gen_tac >> strip_tac >>
     `b <= b+32*j+r /\ b+32*j+r < b+32*n` by intLib.COOPER_TAC >>
     qpat_assum `tz.t_mem SUBSET _` (mp_tac o SIMP_RULE (srw_ss())
       [exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_taint_bound_def,
        exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_region_def,
        exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_translated_taint_def,
        pred_setTheory.SUBSET_DEF]) >>
     disch_then (qspec_then `b+32*j+r` mp_tac) >> simp[] >> strip_tac >>
     rename1 `(key+n2w i,h) IN toplevel_copy_source_taint _ tu` >>
     `i = j /\ h = r` by intLib.COOPER_TAC >>
     qpat_x_assum `(key+n2w i,h) IN _` mp_tac >> Cases_on `tr` >>
     simp[loweringPostsTheory.slot_loc_def,key_taint_def,
          exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]) >>
  `!j. j < n ==> mem_word_at (b+32*j) z.vs_memory =
         slot_copy_word (if tr then TLOAD else SLOAD) s (key+n2w j)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < n ==> mem_word_at _ _ = _` (drule_then SUBST1_TAC) >>
     Cases_on `tr` >>
     simp[loweringPostsTheory.slot_loc_def,exprSimStorageCopyTheory.copy_runtime_word_def,
          slotCopyExecutionTheory.slot_copy_word_def,sload_def,tload_def,venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `storage_holds _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,loweringPostsTheory.storage_holds_def] >>
     strip_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME _`
       (fn ev => ACCEPT_TAC
          (REWRITE_RULE [MATCH_MP abiValueEncodingTheory.evaluate_type_base_result ev] ev))) >>
  `!m. mem_agree_outside tz.t_mem z.vs_memory m ==>
       val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) b m` by
    (`?v. read_result cx tv ee = (INL v,ee) /\
          !m. mem_agree_outside tz.t_mem z.vs_memory m ==>
              val_in_memory (BaseTV (BytesT (Dynamic k))) v b m` by
       (qpat_x_assum `Abbrev (b = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        irule exprPtrUnwrapStoragePostTheory.unwrap_storage_copied_robust >>
        qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
        qexistsl [`key`,`tr`] >>
        qpat_assum `Abbrev (n = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        asm_rewrite_tac[]) >>
     `v = BytesV bs` by fs[] >> qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  `mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs` by
    (qpat_assum `!m. mem_agree_outside _ _ m ==> _` (qspec_then `z.vs_memory` mp_tac) >>
     simp[NoAsms,mem_agree_outside_def,exprSimConvertFromBytesTheory.dynamic_bytes_memory_boundary,
          valueEncodingPropsTheory.mem_word_at_eq_mload,memoryReadPropsTheory.read_memory_eq_mem_bytes_at]) >>
  `!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem` by
    (drule representationCleanPtrTheory.robust_val_in_memory_bytes_clean >> simp[] >>
     strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `i < b+32` >> simp[] >>
     `b+32 <= i` by intLib.COOPER_TAC >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by simp[] >>
  `!off len. off+len <= b \/ b+cap <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (qpat_assum `cap = 32*n` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `typed_copy_state_frame sm b cap u z` by
    (rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def,typedMemoryCopyTheory.typed_copy_frame_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (gen_tac >> strip_tac >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce sm` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by simp[] >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any (strip_assume_tac o REWRITE_RULE []) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func z` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gz,tz)` (irule_at Any) >> simp[]) >>
  `lo <= b` by (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
                disch_then (drule_then ACCEPT_TAC)) >>
  `lo <= z.vs_alloca_next /\ allocas_from lo z` by
    (conj_tac
     >- (qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >> simp[] >> intLib.COOPER_TAC)
     >> (rewrite_tac[allocas_from_def] >>
         qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
         qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
  `return_buf_frame d ce sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s` (irule_at Any) >> fs[ci_mono_def] >>
     intLib.COOPER_TAC) >>
  drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `other` (qx_choose_then `raw` strip_assume_tac)) >>
  `other = root` by metis_tac[operand_11] >> qpat_x_assum `other = root` SUBST_ALL_TAC >>
  `not_local_ptr ce ee.scopes root` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`)
       (cj 1 bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_frame_separation) >>
     disch_then irule >> simp[] >> qexists `sa` >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root]` by
    simp[Abbr `inst`,mk_inst_def] >>
  `MEM inst (fn_insts func)` by simp[Abbr `inst`] >>
  `!name a sz. local_region ce ee.scopes s name a sz ==> local_region ce ee.scopes u name a sz` by
    (rpt gen_tac >> strip_tac >>
     irule exprSimPropsTheory.local_region_frame_fwd >>
     qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >>
     qpat_assum `local_region ce ee.scopes s _ _ _` (irule_at Any) >> simp[]) >>
  `!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!name a sz. local_region _ _ s name a sz ==> local_region _ _ u name a sz`
       (drule_then assume_tac) >>
     qpat_assum `!name a sz. local_region _ _ u name a sz ==> regions_disjoint b cap a sz`
       (drule_then ACCEPT_TAC)) >>
  `!a sz. a+sz <= b \/ b+cap <= a ==> mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `wb_frame ce ee ee sa s z` by suspend "slot_wb" >>
  `ghost_kept_at lo ce ee sa G tn s Gz tz` by suspend "slot_kept" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by suspend "slot_horizon" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `not_fresh_at sb root` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  qexistsl [`root`,`b`,`inst`,`z`,`Gz`,`tz`] >>
  simp[eval_operand_def] >> first_assum ACCEPT_TAC
QED

Resume raw_create_snapshot_slot_path[slot_wb]:
  irule raw_create_snapshot_wb >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`b`,`cap`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `u` >> conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume raw_create_snapshot_slot_path[slot_kept]:
  irule raw_create_snapshot_kept >>
  qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `ci_mono sa sm` (irule_at Any) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         qexistsl [`z`,`u`,`tu`,`cap`,`b`,`Gu`] >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Resume raw_create_snapshot_slot_path[slot_horizon]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee u` by simp[] >>
  `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by
    (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [``:'a`` |-> ``:256``] bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     disch_then irule >> simp[] >>
     conj_tac >- (qexists `b+cap` >> simp[]) >> conj_tac >- (qexists `sa` >> simp[]) >>
     qexistsl [`H`,`ctx`,`func`] >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee z /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z` by
    (irule raw_create_snapshot_copy_horizon >>
     qpat_assum `typed_copy_state_frame _ _ _ u z` (irule_at Any) >>
     qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl [`Gu`,`u`,`tu`] >> conj_tac >- simp[] >>
      irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
      first_assum ACCEPT_TAC)
QED

Finalise raw_create_snapshot_slot_path

(* The code-source count is computed from the located tag. Its physical
   span equals the destination capacity in this branch. *)
Theorem raw_create_snapshot_code_path:
  compile_create_snapshot ce (LocatedValue tag p) (BaseT (BytesT (Dynamic k))) sa = (out,sb) /\
  p.ptr_location = LocCode /\ eval_operand p.ptr_operand s = SOME src /\
  exprSimCopy$copy_old_operand sa p.ptr_operand /\
  op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
  immutable_holds ce cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) src ee s /\
  cap = type_memory_bytes ce (BaseT (BytesT (Dynamic k))) /\
  cap = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
  32 * ((type_memory_bytes ce tag + 31) DIV 32) = cap /\
  32 + LENGTH bs <= cap /\ cap < dimword (:256) /\
  (ce.ce_is_ctor ==> w2n src + cap <= lo /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) (w2n src) mem)) /\
  (!region. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ exprSimCopy$copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  (~ce.ce_is_ctor ==> w2n src + cap <= LENGTH s.vs_data_section /\
    w2n src + cap < dimword (:256)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root b inst z Gz tz.
    out = Var root /\ MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root /\ not_fresh_at sb root /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (b,cap) /\
    eval_operand out z = SOME (n2w b) /\ ptr_covers Gz tz root z cap /\
    b+cap < dimword (:256) /\ b+cap <= z.vs_alloca_next /\
    mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem) /\
    wb_frame ce ee ee sa s z /\ ghost_kept_at lo ce ee sa G tn s Gz tz /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    return_buf_frame d ce sb z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = (type_memory_bytes ce tag + 31) DIV 32` >>
  `n = type_slot_size (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `32*n = cap` mp_tac >> qpat_assum `cap = type_memory_size _` mp_tac >>
     simp[NoAsms,valueEncodingPropsTheory.type_memory_size_slots]) >>
  Cases_on `compile_alloc_buffer cap sa` >>
  rename1 `compile_alloc_buffer cap sa = (buf,sm)` >>
  Cases_on `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand buf.buf_operand n 0 sm` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ _ = (res,sc)` >> Cases_on `res` >>
  `out = buf.buf_operand /\ sc = sb` by
    (qpat_assum `compile_create_snapshot _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,
                               comp_return_def,vv_type_def,vv_location_def,vv_operand_def]) >>
     qpat_assum `cap = type_memory_bytes _ _` (SUBST1_TAC o SYM) >>
     qpat_assum `Abbrev (n = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `p.ptr_location = LocCode` (SUBST1_TAC) >>
     qpat_assum `compile_alloc_buffer cap sa = _`
       (fn th => simp[NoAsms,th,comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
     qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
       (fn th => simp[NoAsms,th,comp_bind_def,comp_ignore_bind_def,comp_return_def])) >>
  qpat_x_assum `sc = sb` SUBST_ALL_TAC >>
  `ci_mono sa sm` by
    (qspecl_then [`cap`,`sa`] mp_tac exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule exprLoweringPropsTheory.ci_mono_compile_imm_copy_to_memory) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`]
      (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `b = w2n (w:bytes32)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_labels = s.vs_labels /\ u.vs_halted = s.vs_halted /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `exprSimCopy$copy_old_operand sm p.ptr_operand /\
   eval_operand p.ptr_operand u = SOME src /\
   op_taint tu p.ptr_operand = {} /\ op_prov Gu p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >> fs[exprSimCopyTheory.copy_old_operand_def,
       eval_operand_def,op_taint_def,op_prov_def]) >>
  `!region. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region ==>
     eval_operand region u = SOME 0w /\ exprSimCopy$copy_old_operand sm region /\
     op_taint tu region = {} /\ op_prov Gu region = NONE` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!r. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME r ==> _`
       (drule_all_then strip_assume_tac) >>
     Cases_on `region` >> fs[exprSimCopyTheory.copy_old_operand_def,eval_operand_def,
       op_taint_def,op_prov_def]) >>
  `?z Gz tz. (?orig. z = orig with vs_inst_idx := LENGTH sb.cs_current_insts /\
     exprSimCopy$copy_runtime_frame sm u sb orig /\
     orig.vs_memory = (immutable_transfers F ce.ce_is_ctor src w n 0 u).vs_memory) /\
     gas_origin_ptr_path (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz) /\
     ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
     tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
     (!x. not_fresh_at sm x ==> FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
     (!i. i IN tz.t_mem <=> if b <= i /\ i < b+cap
       then ce.ce_is_ctor /\ w2n src + (i-b) IN tu.t_mem else i IN tu.t_mem) /\
     ptr_covers Gz tz root z cap` by suspend "code_copy" >>
  suspend "code_finish"
QED

Resume raw_create_snapshot_code_path[code_copy]:
  `eval_operand (Var root) u = SOME w /\ exprSimCopy$copy_old_operand sm (Var root)` by
    simp[eval_operand_def,exprSimCopyTheory.copy_old_operand_def] >>
  `~u.vs_halted` by simp[] >>
  Cases_on `ce.ce_is_ctor`
  >- (`!region. ce.ce_imm_alloca = SOME region ==>
         eval_operand region u = SOME 0w /\ exprSimCopy$copy_old_operand sm region /\
         op_taint tu region = {} /\ op_prov Gu region = NONE` by simp[] >>
      `!region. ce.ce_imm_alloca = SOME region ==>
         eval_operand region u = SOME 0w /\ exprSimCopy$copy_old_operand sm region` by
        (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
      `w2n src + cap <= lo` by simp[] >>
      `w2n src + cap <= u.vs_alloca_next` by
        (qpat_assum `w2n src + cap <= lo` mp_tac >>
         qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >> numLib.ARITH_TAC) >>
      `compile_imm_copy_to_memory T ce.ce_imm_alloca p.ptr_operand (Var root) n 0 sm = ((),sb)` by gvs[] >>
      drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
        (Q.INST [`off` |-> `0`] bodyFullUnwrapCodeCtorRunTheory.code_copy_ctor_range_origin_ptr |> SRULE []) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `eval_operand p.ptr_operand u = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var root u = SOME _`)) >>
      disch_then (qspecl_then [`explicit`,`ctx`,`PG`,
        `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
      impl_tac >- (simp[Abbr `b`] >> gvs[]) >>
      disch_then (qx_choosel_then [`Gc`,`tc`,`r`] (map_every assume_tac o CONJUNCTS)) >>
      drule_all exprSimCopyTheory.copy_ctor_run >>
      disch_then (qx_choose_then `other` strip_assume_tac) >>
      `other = r` by fs[exprSimCopyTheory.copy_runtime_frame_def] >>
      qpat_x_assum `other = r` SUBST_ALL_TAC >>
      qexistsl [`r with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gc`,`tc`] >>
      simp[] >> qexists `r` >> simp[]) >>
  `w2n src + cap <= LENGTH u.vs_data_section /\ w2n src + cap < dimword (:256)` by gvs[] >>
  `compile_imm_copy_to_memory F ce.ce_imm_alloca p.ptr_operand (Var root) n 0 sm = ((),sb)` by gvs[] >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    (Q.INST [`off` |-> `0`] bodyFullUnwrapCodeRuntimeRunTheory.runtime_code_copy_range_origin |> SRULE []) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
  impl_tac >- (simp[Abbr `b`] >> gvs[]) >>
  disch_then (qx_choosel_then [`Gc`,`tc`,`r`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all exprSimCopyTheory.copy_runtime_run >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `other = r` by fs[exprSimCopyTheory.copy_runtime_frame_def] >>
  qpat_x_assum `other = r` SUBST_ALL_TAC >>
  qexistsl [`r with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gc`,`tc`] >>
  simp[pred_setTheory.IN_DIFF] >> conj_tac >- (qexists `r` >> simp[]) >>
  simp[CONJ_COMM]
QED

Resume raw_create_snapshot_code_path[code_finish]:
  rename1 `exprSimCopy$copy_runtime_frame sm u sb r` >>
  `z.vs_inst_idx = LENGTH sb.cs_current_insts /\ z.vs_memory = r.vs_memory` by simp[] >>
  `z with <|vs_vars := u.vs_vars;vs_memory := u.vs_memory;vs_prev_bb := u.vs_prev_bb;
            vs_current_bb := u.vs_current_bb;vs_inst_idx := u.vs_inst_idx|> = u` by
    (qpat_assum `exprSimCopy$copy_runtime_frame sm u sb r`
       (mp_tac o REWRITE_RULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
     strip_tac >>
     qpat_assum `copy_static r = copy_static u`
       (mp_tac o Q.AP_TERM `\t. t with <|vs_prev_bb := u.vs_prev_bb;vs_current_bb := u.vs_current_bb;
          vs_inst_idx := u.vs_inst_idx;vs_vars := u.vs_vars;vs_memory := u.vs_memory|>`) >>
     qpat_assum `z = r with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms,exprSimStorageCopyTheory.copy_static_def]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
   z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
   z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables` by
    (qpat_assum `z with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;vs_current_bb := _;vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u` by
    (qpat_assum `exprSimCopy$copy_runtime_frame sm u sb r`
       (mp_tac o REWRITE_RULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
     strip_tac >> qpat_assum `z = r with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x r = _` mp_tac >>
     simp[NoAsms,lookup_var_def]) >>
  `lookup_var root z = SOME (n2w b)` by simp[Abbr `b`] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by simp[] >>
  `z.vs_memory = (immutable_transfers F ce.ce_is_ctor src w n 0 u).vs_memory` by simp[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) b z.vs_memory /\
   LENGTH u.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= b \/ b+cap <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)` by suspend "code_content" >>
  `mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs` by
    fs[exprSimConvertFromBytesTheory.dynamic_bytes_memory_boundary,
       valueEncodingPropsTheory.mem_word_at_eq_mload,memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  `!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem` by suspend "code_clean" >>
  `!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `~(b <= i /\ i < b+cap)` by decide_tac >>
     qpat_assum `!i. i IN tz.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[NoAsms] >>
     asm_rewrite_tac[]) >>
  `typed_copy_state_frame sm b cap u z` by
    (rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def,typedMemoryCopyTheory.typed_copy_frame_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (gen_tac >> strip_tac >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce sm` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func z` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gz,tz)` (irule_at Any) >> simp[]) >>
  `lo <= z.vs_alloca_next /\ allocas_from lo z` by
    (conj_tac
     >- (qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >> simp[] >> numLib.ARITH_TAC)
     >> (rewrite_tac[allocas_from_def] >>
         qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
         qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
  `return_buf_frame d ce sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s` (irule_at Any) >>
     qpat_assum `ci_mono sa sm` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono sm sb` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     qpat_x_assum `z = r with vs_inst_idx := _` kall_tac >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s`
           (drule_then SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `sm.cs_next_var` >> asm_rewrite_tac[]) >>
  drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `other` (qx_choose_then `raw` strip_assume_tac)) >>
  `other = root` by metis_tac[operand_11] >> qpat_x_assum `other = root` SUBST_ALL_TAC >>
  `not_local_ptr ce ee.scopes root` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`)
       (cj 1 bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_frame_separation) >>
     disch_then irule >> simp[] >> qexists `sa` >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root]` by
    simp[Abbr `inst`,mk_inst_def] >>
  `MEM inst (fn_insts func)` by simp[Abbr `inst`] >>
  `!name a sz. local_region ce ee.scopes s name a sz ==> regions_disjoint b cap a sz` by
    (rpt gen_tac >> strip_tac >>
     `local_region ce ee.scopes u name a sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >>
        qpat_assum `local_region ce ee.scopes s _ _ _` (irule_at Any) >> simp[]) >>
     qpat_assum `!name a sz. local_region _ _ u name a sz ==> regions_disjoint b cap a sz`
       (drule_then ACCEPT_TAC)) >>
  `!a sz. a+sz <= b \/ b+cap <= a ==> mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)` by
    (rpt gen_tac >> strip_tac >> conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `wb_frame ce ee ee sa s z` by suspend "code_wb" >>
  `ghost_kept_at lo ce ee sa G tn s Gz tz` by suspend "code_kept" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by suspend "code_horizon" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `not_fresh_at sb root` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  qexistsl [`root`,`b`,`inst`,`z`,`Gz`,`tz`] >> simp[eval_operand_def] >>
  qpat_assum `lookup_var root z = SOME (n2w b)` mp_tac >> simp[NoAsms] >>
  qpat_assum `z = r with vs_inst_idx := _` SUBST1_TAC >> simp[]
QED

Resume raw_create_snapshot_code_path[code_content]:
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `immutable_holds _ _ _ _ _ _ s` (mp_tac o REWRITE_RULE [loweringPostsTheory.immutable_holds_def]) >>
     strip_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME _` mp_tac >>
     simp[NoAsms,vyperValueTheory.evaluate_type_def,AllCaseEqs()] >>
     disch_then (CONJUNCTS_THEN2 (assume_tac o CONJUNCT2) (SUBST1_TAC o SYM)) >>
     first_assum ACCEPT_TAC) >>
  `w2n w + type_memory_size (BaseTV (BytesT (Dynamic k))) < dimword (:256)` by gvs[Abbr `b`] >>
  Cases_on `ce.ce_is_ctor`
  >- (`immutable_holds ce cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) src ee u` by
        (qpat_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >> simp[NoAsms,loweringPostsTheory.immutable_holds_def]) >>
      `regions_disjoint (w2n src) (type_memory_size (BaseTV (BytesT (Dynamic k))))
         (w2n w) (type_memory_size (BaseTV (BytesT (Dynamic k))))` by
        (qpat_assum `ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
         qpat_assum `w2n src + cap <= lo` mp_tac >> qpat_assum `lo <= b` mp_tac >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def,Abbr `b`] >> numLib.ARITH_TAC) >>
      `z.vs_memory = (immutable_transfers F T src w (type_slot_size (BaseTV (BytesT (Dynamic k)))) 0 u).vs_memory` by simp[] >>
      drule_all exprSimCopyTheory.copy_ctor_contents >> simp[Abbr `b`] >> metis_tac[]) >>
  `z.vs_memory = (immutable_transfers F F src w (type_slot_size (BaseTV (BytesT (Dynamic k)))) 0 u).vs_memory` by simp[] >>
  drule_all exprSimCopyTheory.copy_runtime_contents >> simp[Abbr `b`] >> strip_tac >>
  `w2n src + type_memory_size (BaseTV (BytesT (Dynamic k))) < dimword (:256)` by gvs[] >>
  drule_all exprSimCopyTheory.runtime_code_copy_memory_frame >> simp[] >> metis_tac[]
QED

Resume raw_create_snapshot_code_path[code_clean]:
  gen_tac >> strip_tac >> strip_tac >>
  `i < b+cap` by intLib.COOPER_TAC >>
  qabbrev_tac `j = w2n src + (i-b)` >>
  `ce.ce_is_ctor /\ j IN tu.t_mem` by
    (qpat_assum `!j. j IN tz.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `i IN tz.t_mem` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `b <= i` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `i < b+cap` (fn th => pure_rewrite_tac [th]) >>
     simp[NoAsms,Abbr `j`]) >>
  qpat_assum `ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
  drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])
    representationCleanPtrTheory.robust_val_in_memory_bytes_clean >>
  `w2n src <= j /\ j < w2n src+32+LENGTH bs /\ j < s.vs_alloca_next` by
    (qpat_assum `b <= i` mp_tac >> qpat_assum `i < b+32+LENGTH bs` mp_tac >>
     qpat_assum `w2n src + cap <= lo` mp_tac >> qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     qpat_assum `32 + LENGTH bs <= cap` mp_tac >> simp[NoAsms,Abbr `j`] >> numLib.ARITH_TAC) >>
  `j IN tn.t_mem` by
    (qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `j` mp_tac) >>
     qpat_assum `j IN tu.t_mem` mp_tac >> qpat_assum `j < s.vs_alloca_next` mp_tac >>
     simp[NoAsms,arithmeticTheory.NOT_LESS_EQUAL]) >>
  Cases_on `j < w2n src+32`
  >- (qpat_assum `!i. w2n src <= i /\ i < w2n src+32 ==> i NOTIN tn.t_mem`
        (qspec_then `j` mp_tac) >>
      qpat_assum `j IN tn.t_mem` mp_tac >> qpat_assum `w2n src <= j` mp_tac >>
      qpat_assum `j < w2n src+32` mp_tac >> simp[NoAsms]) >>
  `w2n src+32 <= j` by intLib.COOPER_TAC >>
  qpat_assum `!i. w2n src+32 <= i /\ _ ==> i NOTIN tn.t_mem`
    (qspec_then `j` mp_tac) >>
  qpat_assum `j IN tn.t_mem` mp_tac >> qpat_assum `w2n src+32 <= j` mp_tac >>
  qpat_assum `j < w2n src+32+LENGTH bs` mp_tac >> simp[NoAsms]
QED

Resume raw_create_snapshot_code_path[code_wb]:
  irule raw_create_snapshot_wb >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`b`,`cap`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `u` >> conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume raw_create_snapshot_code_path[code_kept]:
  irule raw_create_snapshot_kept >>
  qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `ci_mono sa sm` (irule_at Any) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         qexistsl [`z`,`u`,`tu`,`cap`,`b`,`Gu`] >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Resume raw_create_snapshot_code_path[code_horizon]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee u` by simp[] >>
  `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by
    (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [``:'a`` |-> ``:256``] bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     disch_then irule >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            qexists `b+cap` >> first_assum ACCEPT_TAC,
            qexists `sa` >> rpt conj_tac >> first_assum ACCEPT_TAC,
            qexistsl [`H`,`ctx`,`func`] >> first_assum ACCEPT_TAC]) >>
  `stmt_state_rel H ctx func ce cx ee z /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z` by
    (irule raw_create_snapshot_copy_horizon >>
     qpat_assum `typed_copy_state_frame _ _ _ u z` (irule_at Any) >>
     qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl [`Gu`,`u`,`tu`] >> conj_tac >- simp[] >>
      irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
      first_assum ACCEPT_TAC)
QED

Finalise raw_create_snapshot_code_path

(* The memory branch copies the live header and payload, not the padded
   capacity. The source is already represented by a reached pointer. *)
Theorem raw_create_snapshot_memory_path:
  compile_create_snapshot ce vv (BaseT (BytesT (Dynamic k))) sa = (out,sb) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  vv_operand vv = Var src /\ not_fresh_at sa src /\
  eval_operand (Var src) s = SOME (n2w a) /\ ptr_covers G tn src s (32+LENGTH bs) /\
  a < dimword (:256) /\ a+32+LENGTH bs <= s.vs_alloca_next /\
  mload a s = n2w (LENGTH bs) /\ read_memory (a+32) (LENGTH bs) s = bs /\
  (!i. a <= i /\ i < a+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  cap = type_memory_bytes ce (BaseT (BytesT (Dynamic k))) /\
  32 + LENGTH bs <= cap /\ cap < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root b inst z Gz tz.
    out = Var root /\ MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root /\ not_fresh_at sb root /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (b,cap) /\
    eval_operand out z = SOME (n2w b) /\ ptr_covers Gz tz root z cap /\
    b+cap < dimword (:256) /\ b+cap <= z.vs_alloca_next /\
    mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem) /\
    wb_frame ce ee ee sa s z /\ ghost_kept_at lo ce ee sa G tn s Gz tz /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    return_buf_frame d ce sb z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_alloc_buffer cap sa` >>
  rename1 `compile_alloc_buffer cap sa = (buf,sm)` >>
  Cases_on `emit_op MLOAD [Var src] sm` >>
  rename1 `emit_op MLOAD [Var src] sm = (len,sl)` >>
  Cases_on `emit_op ADD [len;Lit 32w] sl` >>
  rename1 `emit_op ADD [len;Lit 32w] sl = (cnt,sc)` >>
  `out = buf.buf_operand /\ compile_copy_memory_dynamic out (Var src) cnt sc = ((),sb)` by
    (Cases_on `compile_copy_memory_dynamic buf.buf_operand (Var src) cnt sc` >>
     Cases_on `vv_location vv = NONE` >>
     gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,oneTheory.one]) >>
  `ci_mono sa sm /\ ci_mono sm sl /\ ci_mono sl sc /\ ci_mono sc sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,ci_mono_emit_op,
              exprLoweringPropsTheory.ci_mono_compile_copy_memory_dynamic,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sl func /\ fn_has_code sl sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `b = w2n (w:bytes32)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\ u.vs_halted = s.vs_halted /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> disch_then ACCEPT_TAC) >>
  `?z Gz tz.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
     z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ~z.vs_halted /\ lookup_var root z = SOME (n2w b) /\ ptr_covers Gz tz root z cap /\
     (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
        FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
     (z with <|vs_vars := u.vs_vars;vs_memory := u.vs_memory;vs_prev_bb := u.vs_prev_bb;
               vs_current_bb := u.vs_current_bb;vs_inst_idx := u.vs_inst_idx|>) = u /\
     tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
     LENGTH u.vs_memory <= LENGTH z.vs_memory /\
     (!off len. off+len <= b \/ b+cap <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
     (!i. (i < b \/ b+cap <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem) /\
     mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs /\
     (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tz.t_mem)` by suspend "memory_steps" >>
  suspend "memory_finish"
QED

Resume raw_create_snapshot_memory_path[memory_steps]:
  qabbrev_tac `n = 32 + LENGTH bs` >>
  `n < dimword (:256) /\ b < dimword (:256)` by
    (qpat_assum `cap < dimword (:256)` mp_tac >>
     qpat_assum `n <= cap` mp_tac >> qpat_assum `b+cap < dimword (:256)` mp_tac >>
     simp[NoAsms] >> numLib.ARITH_TAC) >>
  `not_fresh_at sm src` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `lookup_var src u = SOME (n2w a)` by fs[eval_operand_def] >>
  `ptr_covers Gu tu src u n` by
    (qpat_assum `ptr_covers G tn src s n`
       (mp_then Any irule appendStorageGhostPtrTheory.ptr_covers_old_transport) >>
     qexists `sa` >> conj_tac >- (rpt strip_tac >>
       qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` (drule_then strip_assume_tac) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `mload a u = n2w (LENGTH bs) /\ read_memory (a+32) (LENGTH bs) u = bs` by
    (qpat_assum `mload a s = _` mp_tac >> qpat_assum `read_memory (a+32) (LENGTH bs) s = _` mp_tac >>
     qpat_assum `u.vs_memory = s.vs_memory` (fn th => simp[NoAsms,mload_def,read_memory_def,th])) >>
  `!i. a <= i /\ i < a+n ==> i NOTIN tu.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
     `i < a+32+LENGTH bs` by fs[Abbr `n`] >>
     `i < s.vs_alloca_next` by
       (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists `a+32+LENGTH bs` >> simp[]) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `ptr_covers Gu tu src u 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `n` >> simp[Abbr `n`]) >>
  `eval_operand (Var src) u = SOME (n2w a)` by simp[eval_operand_def] >>
  `a+n <= u.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `s.vs_alloca_next` >> simp[Abbr `n`]) >>
  `a+32 <= u.vs_alloca_next` by
    (qpat_assum `a+n <= u.vs_alloca_next` mp_tac >> simp[NoAsms,Abbr `n`] >> numLib.ARITH_TAC) >>
  `w2n (n2w a:bytes32) = a` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `w2n (n2w a:bytes32)+32 <= u.vs_alloca_next /\
   (!i. w2n (n2w a:bytes32) <= i /\ i < w2n (n2w a:bytes32)+32 ==> i NOTIN tu.t_mem)` by
    (simp[] >> rpt gen_tac >> strip_tac >> qpat_assum `!i. a <= i /\ i < a+n ==> _` irule >>
     simp[Abbr `n`]) >>
  `~u.vs_halted` by simp[] >>
  drule_all create_clean_mload_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`l`,`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "memory_add"
QED

Resume raw_create_snapshot_memory_path[memory_add]:
  `v.vs_inst_idx = LENGTH sl.cs_current_insts /\ ~v.vs_halted /\
   allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (qpat_assum `v = _` SUBST1_TAC >> simp[update_var_def,allocas_from_def,allocas_below_fmp_def]) >>
  `eval_operand len v = SOME (n2w (LENGTH bs))` by
    (qpat_assum `eval_operand len v = SOME _` mp_tac >>
     qpat_assum `w2n (n2w a:bytes32) = a` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `mload a u = _` (fn th => pure_rewrite_tac [th]) >> simp[NoAsms]) >>
  qpat_x_assum `eval_operand len v = SOME (mload _ _)` kall_tac >>
  `eval_operand (Lit 32w) v = SOME 32w /\ op_taint tv (Lit 32w) = {} /\
   op_prov Gv (Lit 32w) = NONE` by simp[eval_operand_def,op_taint_def,op_prov_def] >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`q`,`t`,`Gadd`,`tt`] (map_every assume_tac o CONJUNCTS))) >>
  `eval_operand cnt t = SOME (n2w n)` by
    (qpat_assum `eval_operand cnt t = SOME _` mp_tac >>
     simp[NoAsms,wordsTheory.word_add_n2w,Abbr `n`] >> metis_tac[arithmeticTheory.ADD_SYM]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP Gadd x = FLOOKUP Gu x /\ op_taint tt (Var x) = op_taint tu (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sl x` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
     `x <> l /\ x <> q` by metis_tac[] >>
     qpat_assum `!p. p <> q ==> lookup_var p t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!p. p <> l ==> lookup_var p v = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `t with <|vs_vars := u.vs_vars;vs_inst_idx := u.vs_inst_idx|> = u /\
   t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted /\
   t.vs_memory = u.vs_memory /\ t.vs_alloca_next = u.vs_alloca_next /\
   allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `t = _` SUBST1_TAC >> qpat_assum `v = _` SUBST1_TAC >>
     simp[update_var_def,allocas_from_def,allocas_below_fmp_def,venom_state_component_equality]) >>
  `tt.t_mem = tu.t_mem /\ tt.t_stor = tu.t_stor /\
   tt.t_trans = tu.t_trans /\ tt.t_imm = tu.t_imm` by
    (qpat_assum `tv with t_var := _ = tu` (SUBST1_TAC o SYM) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gadd,tt)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gv`,`v`,`tv`] >> simp[]) >>
  suspend "memory_mcopy"
QED

Resume raw_create_snapshot_memory_path[memory_mcopy]:
  `lookup_var root u = SOME (n2w b)` by simp[Abbr `b`] >>
  `!x k'. not_fresh_at sm x /\ ptr_covers Gu tu x u k' ==> ptr_covers Gadd tt x t k'` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `ptr_covers Gu tu x u k'` (mp_then Any irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers Gadd tt src t n /\ ptr_covers Gadd tt root t cap` by simp[] >>
  `ptr_covers Gadd tt root t n` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `lookup_var root t = SOME (n2w b) /\ lookup_var src t = SOME (n2w a)` by
    metis_tac[] >>
  `b+n <= t.vs_alloca_next` by
    (qpat_assum `t.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
     qpat_assum `b+cap <= u.vs_alloca_next` mp_tac >> qpat_assum `n <= cap` mp_tac >>
     numLib.ARITH_TAC) >>
  `a+n <= t.vs_alloca_next /\ (!i. a <= i /\ i < a+n ==> i NOTIN tt.t_mem)` by simp[] >>
  `compile_copy_memory_dynamic (Var root) (Var src) cnt sc = ((),sb)` by metis_tac[] >>
  drule_all raw_create_static_mcopy_path >> strip_tac >>
  qabbrev_tac `z = mcopy b a n t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tz = tt with t_mem := tt.t_mem DIFF {i | b <= i /\ i < b+n}` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gadd,tt) [] (OK z,Gadd,tz)` by
    (simp[Abbr `z`,Abbr `tz`] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gadd,tz)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gadd`,`t`,`tt`] >> simp[]) >>
  suspend "memory_copy_content"
QED

Resume raw_create_snapshot_memory_path[memory_copy_content]:
  `lookup_var root z = lookup_var root t /\ op_taint tz (Var root) = op_taint tt (Var root)` by
    simp[NoAsms,Abbr `z`,Abbr `tz`,op_taint_def,lookup_var_def,
          mcopy_def,write_memory_with_expansion_def,write_memory_def] >>
  `lookup_var root z = SOME (n2w b)` by metis_tac[] >>
  `ptr_covers Gadd tz root z cap` by
    (qpat_assum `ptr_covers Gadd tt root t cap` (mp_then Any irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame) >>
     rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gadd x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _` (drule_then mp_tac) >>
     simp[NoAsms,Abbr `z`,Abbr `tz`,lookup_var_def,op_taint_def,
          mcopy_def,write_memory_with_expansion_def,write_memory_def]) >>
  `mload a t = n2w (LENGTH bs) /\ read_memory (a+32) (LENGTH bs) t = bs` by
    (qpat_assum `mload a u = _` mp_tac >> qpat_assum `read_memory (a+32) (LENGTH bs) u = _` mp_tac >>
     qpat_assum `t.vs_memory = u.vs_memory` (fn th => simp[NoAsms,mload_def,read_memory_def,th])) >>
  `mload b z = n2w (LENGTH bs) /\ read_memory (b+32) (LENGTH bs) z = bs` by
    (qspecl_then [`b`,`a`,`n`,`LENGTH bs`,`t`] mp_tac bytesSnapshotMemoryTheory.mcopy_live_bytestring_reads >>
     simp[Abbr `n`,Abbr `z`,mload_def,read_memory_def]) >>
  `LENGTH u.vs_memory <= LENGTH z.vs_memory` by
    (simp[NoAsms,Abbr `z`] >>
     qpat_assum `t.vs_memory = u.vs_memory` (SUBST1_TAC o SYM) >>
     irule exprSimAbiEncodeMemoryLengthTheory.abi_encode_mcopy_memory_length) >>
  `!off sz. off+sz <= b \/ b+cap <= off ==>
       mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory` by
    (rpt gen_tac >> disch_tac >> simp[NoAsms,Abbr `z`] >>
     qpat_assum `t.vs_memory = u.vs_memory` (SUBST1_TAC o SYM) >>
     irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >>
     qpat_assum `off+sz <= b \/ b+cap <= off` mp_tac >>
     qpat_assum `n <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
   z with <|vs_vars := u.vs_vars;vs_memory := u.vs_memory;vs_prev_bb := u.vs_prev_bb;
            vs_current_bb := u.vs_current_bb;vs_inst_idx := u.vs_inst_idx|> = u` by
    (simp[NoAsms,Abbr `z`,mcopy_def,write_memory_with_expansion_def,write_memory_def] >>
     qpat_assum `t with <|vs_vars := _;vs_inst_idx := _|> = u` (SUBST1_TAC o SYM) >>
     simp[venom_state_component_equality]) >>
  qexistsl [`z`,`Gadd`,`tz`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
   simp[Abbr `tz`,Abbr `n`,pred_setTheory.IN_DIFF,pred_setTheory.GSPECIFICATION])
QED

Resume raw_create_snapshot_memory_path[memory_finish]:
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
   z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
   z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables` by
    (qpat_assum `z with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;
                         vs_current_bb := _;vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `typed_copy_state_frame sm b cap u z` by
    (rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def,typedMemoryCopyTheory.typed_copy_frame_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (gen_tac >> strip_tac >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono sa sb /\ ci_mono sm sb` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved ce sm` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `alloca_inv u` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func z` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (u,Gu,tu) [] _` (irule_at Any) >> simp[]) >>
  `lo <= z.vs_alloca_next /\ allocas_from lo z` by
    (conj_tac
     >- (qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >> simp[] >> numLib.ARITH_TAC)
     >> (rewrite_tac[allocas_from_def] >>
         qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
         qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sm x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,ci_mono_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `return_buf_frame d ce sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s` (irule_at Any) >> fs[ci_mono_def]) >>
  drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `other` (qx_choose_then `raw` strip_assume_tac)) >>
  `other = root` by metis_tac[operand_11] >> qpat_x_assum `other = root` SUBST_ALL_TAC >>
  `not_local_ptr ce ee.scopes root` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`)
       (cj 1 bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_frame_separation) >>
     disch_then irule >> simp[] >> qexists `sa` >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root]` by
    simp[Abbr `inst`,mk_inst_def] >>
  `MEM inst (fn_insts func)` by simp[Abbr `inst`] >>
  `!name off sz. local_region ce ee.scopes s name off sz ==> regions_disjoint b cap off sz` by
    (rpt gen_tac >> strip_tac >>
     `local_region ce ee.scopes u name off sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >>
        qpat_assum `local_region ce ee.scopes s _ _ _` (irule_at Any) >> simp[]) >>
     qpat_assum `!name a sz. local_region _ _ u name a sz ==> regions_disjoint b cap a sz`
       (drule_then ACCEPT_TAC)) >>
  `!a sz. a+sz <= b \/ b+cap <= a ==> mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `wb_frame ce ee ee sa s z` by suspend "memory_wb" >>
  `ghost_kept_at lo ce ee sa G tn s Gz tz` by suspend "memory_kept" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by suspend "memory_horizon" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `not_fresh_at sb root` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  qexistsl [`root`,`b`,`inst`,`z`,`Gz`,`tz`] >> simp[eval_operand_def]
QED

Resume raw_create_snapshot_memory_path[memory_wb]:
  irule raw_create_snapshot_wb >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`b`,`cap`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `u` >> conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume raw_create_snapshot_memory_path[memory_kept]:
  irule raw_create_snapshot_kept >>
  qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `ci_mono sa sm` (irule_at Any) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         qexistsl [`z`,`u`,`tu`,`cap`,`b`,`Gu`] >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Resume raw_create_snapshot_memory_path[memory_horizon]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H ctx func ce cx ee u` by simp[] >>
  `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by
    (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [``:'a`` |-> ``:256``] bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists `b+cap` >> first_assum ACCEPT_TAC)
     >~ [`?h c f. stmt_state_rel h c f ce cx ee s`]
     >- (qexistsl [`H`,`ctx`,`func`] >> first_assum ACCEPT_TAC) >>
     qexists `sa` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,ci_mono_def] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> conj_tac
     >- (qpat_assum `ci_mono sa sm` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  `stmt_state_rel H ctx func ce cx ee z /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z` by
    (irule raw_create_snapshot_copy_horizon >>
     qpat_assum `typed_copy_state_frame _ _ _ u z` (irule_at Any) >>
     qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) lo d ce cx ee Gu tu u` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl [`Gu`,`u`,`tu`] >> simp[])
QED

Finalise raw_create_snapshot_memory_path

(* The encoder produces the length of its rows, not the length of the
   entire initcode. Only this last ADD changes the count at dispatch. *)
Theorem raw_create_total_path:
  emit_op ADD [Var root;len] sm = (Var dst,st) /\ fn_has_code sm st func /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\ emit_op ADD [len;alen] en = (total_op,sb) /\ fn_has_code en sb func /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (initial,Gi,ti) [] (OK z,Gz,tz)) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst (LENGTH bs) bs en z Gz tz /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\
  (!x. len = Var x ==> not_fresh_at se x) /\ (!l. len <> Label l) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  eval_operand alen z = SOME (n2w (LENGTH args_bytes)) /\ op_taint tz alen = {} /\
  LENGTH bs + LENGTH args_bytes <= capacity /\
  read_memory pbase (LENGTH (bs ++ args_bytes)) z = bs ++ args_bytes /\
  (!i. pbase <= i /\ i < pbase + LENGTH (bs ++ args_bytes) ==> i NOTIN tz.t_mem) ==>
  ?out t Gt tt. total_op = Var out /\ not_fresh_at sb out /\ not_fresh_at sb root /\
    shared < sb.cs_next_id /\ FLOOKUP t.vs_allocas shared = SOME (pbase,capacity) /\
    lookup_var root t = SOME (n2w pbase) /\ ptr_covers Gt tt root t capacity /\
    pbase + capacity <= t.vs_alloca_next /\ pbase + capacity < dimword (:256) /\
    LENGTH (bs ++ args_bytes) <= capacity /\ LENGTH (bs ++ args_bytes) < dimword (:256) /\
    eval_operand total_op t = SOME (n2w (LENGTH (bs ++ args_bytes))) /\
    op_taint tt total_op = {} /\ op_prov Gt total_op = NONE /\
    read_memory pbase (LENGTH (bs ++ args_bytes)) t = bs ++ args_bytes /\
    (!i. pbase <= i /\ i < pbase + LENGTH (bs ++ args_bytes) ==> i NOTIN tt.t_mem) /\
    wb_frame ce ee ee se s t /\ ghost_kept_at lo ce ee se G tn s Gt tt /\
    return_buf_frame d ce sb t /\ alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gt tt t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gt,tt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  drule bodyFullExtCallDirectStateTheory.abi_encode_saved_state_resources >>
  impl_tac
  >- (qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE
      [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  `op_prov Gz alen = NONE` by suspend "arg_length" >>
  `eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {}` by
    (irule (INST_TYPE [``:'a`` |-> ``:num # num``] create_operand_cut_frame) >>
     qpat_assum `wb_frame ce ee ee se s z` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gz tz` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `op_prov Gz len = NONE` by
    (qpat_assum `op_prov G len = NONE` (SUBST1_TAC o SYM) >>
     irule exprPtrCtorCodeLoadTheory.old_operand_prov_frame >> qexists `se` >>
     fs[exprSimCopyTheory.copy_old_operand_def,ghost_kept_at_def]) >>
  `pbase+capacity <= z.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `shared` >> first_assum ACCEPT_TAC) >>
  `pbase+capacity < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists `z.vs_alloca_next` >>
     conj_tac
     >- (qpat_assum `alloca_room ctx func z` (mp_then Any ACCEPT_TAC alloca_room_next_lt)) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH (bs ++ args_bytes) < dimword (:256)` by
    (qpat_assum `pbase+capacity < dimword (:256)` mp_tac >>
     qpat_assum `LENGTH bs + LENGTH args_bytes <= capacity` mp_tac >>
     rewrite_tac[LENGTH_APPEND] >> numLib.ARITH_TAC) >>
  drule_all create_blueprint_add_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`out`,`t`,`Gsum`,`tt`]
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "total_finish"
QED

Resume raw_create_total_path[arg_length]:
  qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (initial,Gi,ti) [] _`
    (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
  irule create_encoded_length_no_prov >>
  qpat_assum `emit_op ADD [Var root;len] sm = (Var dst,st)` (irule_at Any) >>
  qpat_assum `compile_abi_encode_values_to_buf _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ (initial,Gi,ti) [] (OK z,Gz,tz)` (irule_at Any) >>
  simp[]
QED

Resume raw_create_total_path[total_finish]:
  `ci_mono en sb` by metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `en.cs_next_var <= sb.cs_next_var /\ en.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `!x. not_fresh_at en x ==> lookup_var x t = lookup_var x z /\
       FLOOKUP Gsum x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >> qpat_assum `!p. p <> out ==> _` irule >> simp[]) >>
  `state_frame t = state_frame (z with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_assum `t = _` SUBST1_TAC >> simp[stateFrameTheory.state_frame_def,update_var_def]) >>
  `t.vs_memory = z.vs_memory /\ t.vs_allocas = z.vs_allocas /\
   t.vs_alloca_next = z.vs_alloca_next /\ t.vs_call_ctx = z.vs_call_ctx /\
   t.vs_accounts = z.vs_accounts /\ t.vs_transient = z.vs_transient /\
   t.vs_immutables = z.vs_immutables /\ ~t.vs_halted /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def,allocas_from_def,allocas_below_fmp_def]) >>
  `lookup_var root z = SOME (n2w pbase)` by fs[eval_operand_def] >>
  `lookup_var root t = SOME (n2w pbase) /\ ptr_covers Gsum tt root t capacity` by
    (qpat_assum `!x. not_fresh_at en x ==> lookup_var x t = _ /\ _`
       (qspec_then `root` (drule_then strip_assume_tac)) >>
     conj_tac >- simp[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gz tz root z capacity` (irule_at Any) >> simp[]) >>
  `eval_operand total_op t = SOME (n2w (LENGTH (bs ++ args_bytes)))` by
    (qpat_assum `eval_operand total_op t = SOME _` mp_tac >>
     simp[NoAsms,LENGTH_APPEND,wordsTheory.word_add_n2w]) >>
  `op_prov Gsum total_op = NONE` by simp[op_prov_def] >>
  `wb_frame ce ee ee se s t /\ ghost_kept_at lo ce ee se G tn s Gsum tt` by suspend "total_frames" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gsum tt t` by suspend "total_horizon" >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (z,Gz,tz) [] (OK t,Gsum,tt)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`explicit`] (irule_at Any)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `se.cs_next_var <= sb.cs_next_var` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `en.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d ce sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce se s` (irule_at Any) >> simp[IgnAsm `t = _`] >>
     rpt strip_tac >> irule exprSimWordArgsTheory.wb_frame_vars >>
     qpat_assum `wb_frame ce ee ee se s t` (irule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sb root` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `shared < sb.cs_next_id` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `LENGTH (bs ++ args_bytes) <= capacity` by simp[LENGTH_APPEND] >>
  `read_memory pbase (LENGTH (bs ++ args_bytes)) t = bs ++ args_bytes` by
    (qpat_assum `t.vs_memory = z.vs_memory` (fn th => rewrite_tac[read_memory_def,th]) >>
     qpat_assum `read_memory pbase (LENGTH (bs ++ args_bytes)) z = _`
       (ACCEPT_TAC o REWRITE_RULE [read_memory_def])) >>
  qexistsl [`out`,`t`,`Gsum`,`tt`] >>
  simp[IgnAsm `t = _`]
QED

Resume raw_create_total_path[total_frames]:
  conj_tac
  >- (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
      qpat_assum `wb_frame ce ee ee se s z` (irule_at Any) >>
      qexists `en` >> simp[IgnAsm `t = _`] >> metis_tac[]) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qpat_assum `ghost_kept_at lo ce ee se G tn s Gz tz` (irule_at Any) >>
  simp[IgnAsm `t = _`] >> gen_tac >> strip_tac >>
  `not_fresh_at en x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `!x. not_fresh_at en x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume raw_create_total_path[total_horizon]:
  `local_ptrs_reserved ce en` by metis_tac[local_ptrs_reserved_next_var] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
      qpat_assum `stmt_state_rel H ctx func ce cx ee z` (irule_at Any) >>
      qpat_assum `state_frame t = _` (irule_at Any) >>
      qexists `en` >> simp[IgnAsm `t = _`] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
  qpat_assum `ghost_inv_at (DF H) lo d ce cx ee Gz tz z` (irule_at Any) >>
  qexists `en` >> simp[IgnAsm `t = _`] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Finalise raw_create_total_path

(* The constructor cut owns its bytecode prefix before the first row is
   evaluated. The new owner is registered before the encoder starts. *)
Theorem raw_create_encoded_args_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  ctor <> [] /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget RawCreate salted rof ks) (code::amount::(ctor ++ salts)) dflt) entry /\
  expr_type code = BaseT (BytesT (Dynamic bd)) /\
  bd + abi_size_bound cenv.ce_struct_fields (TupleT (MAP expr_type ctor)) < 2**64 /\
  LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
  cap = bytelike_type_bound (lowered_value_type cenv code) +
    abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) ctor)) /\
  body_exprs_full_ok cx ctor /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  compile_create_ctor_args compile_expr cenv ctor sa = (vals,se) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr ctor) sh = (vals,she) /\
  compile_alloc_buffer cap se = (buf,a) /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) len a = ((),b) /\
  emit_op ADD [buf.buf_operand;len] b = (dst,c) /\
  compile_abi_encode_values_to_buf cenv dst (ZIP (vals,MAP (lowered_value_type cenv) ctor)) c = (alen,en) /\
  emit_op ADD [len;alen] en = (total_op,sb) /\
  fn_has_code sa se func /\ fn_has_code sh she shadow_func /\
  fn_has_code se a func /\ fn_has_code a b func /\ fn_has_code b c func /\
  fn_has_code c en func /\ fn_has_code en sb func /\
  gas_shadow_state sa sh /\ gas_shadow_state se she /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
  not_local_ptr cenv es.scopes owner /\ site.inst_id < sa.cs_next_id /\
  FLOOKUP s.vs_allocas site.inst_id = SOME (src_base,oldcap) /\
  src_base + oldcap <= s.vs_alloca_next /\ src_base + oldcap < dimword (:256) /\
  off + LENGTH bs <= oldcap /\ not_fresh_at sa src /\
  lookup_var src s = SOME (n2w (src_base+off)) /\ ptr_covers G tn src s (LENGTH bs) /\
  op_taint tn (Var src) = {} /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ (!l. len <> Label l) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  read_memory (src_base+off) (LENGTH bs) s = bs /\
  (!i. src_base+off <= i /\ i < src_base+off+LENGTH bs ==> i NOTIN tn.t_mem) /\
  (!vs. storage_trace_frame (next vs)) /\
  (!vs args_bytes ee Gz tz z marks.
    LENGTH vs = LENGTH ctor /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME args_bytes /\
    (!tail. eval_exprs cx ctor (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL vs,ee with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\ storage_trace_domain cx st0 ee.storage_trace /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= z.vs_alloca_next /\
    alloca_history func z /\ return_buf_frame d cenv sb z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    (!ef Gf tf f.
      wb_frame cenv ee ef sb z f /\ ghost_kept_at lo cenv ee sb Gz tz z Gf tf /\
      z.vs_alloca_next <= f.vs_alloca_next ==>
      ?p pbase. buf.buf_operand = Var p /\ lookup_var p f = SOME (n2w pbase) /\
        pbase < dimword (:256) /\ LENGTH (bs ++ args_bytes) < dimword (:256) /\
        ptr_covers Gf tf p f (LENGTH (bs ++ args_bytes)) /\ op_taint tf (Var p) = {} /\
        pbase + LENGTH (bs ++ args_bytes) <= f.vs_alloca_next /\
        eval_operand total_op f = SOME (n2w (LENGTH (bs ++ args_bytes))) /\
        op_taint tf total_op = {} /\ op_prov Gf total_op = NONE /\
        read_memory pbase (LENGTH (bs ++ args_bytes)) f = bs ++ args_bytes /\
        (!i. pbase <= i /\ i < pbase + LENGTH (bs ++ args_bytes) ==> i NOTIN tf.t_mem)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next vs) (ee,z,Gz,tz) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx ctor) next) (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!e u. MEM e ctor /\ expr_sim_inv cenv cx env u ==> expr_body_pre cenv cx env e u` by
    (rpt strip_tac >> irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ (CreateTarget RawCreate _ _ _) _ _) entry`
       (irule_at Any) >> simp[]) >>
  `ci_mono sa se` by
    (qpat_assum `compile_create_ctor_args _ _ ctor sa = _` mp_tac >>
     metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,pairTheory.SND]) >>
  `sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv se /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x. len = Var x ==> not_fresh_at se x) /\ not_fresh_at se src` by
    metis_tac[local_ptrs_reserved_next_var,freshWritesTheory.not_fresh_at_mono] >>
  `EVERY (\e. expr_body_pre cenv cx env e es) ctor` by simp[EVERY_MEM] >>
  `expr_body_pre cenv cx env code es` by
    (irule create_operand_pre >> qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) entry` (irule_at Any) >> simp[]) >>
  `bytelike_type_bound (lowered_value_type cenv code) <= bd` by
    (irule dallocaBlueprintArgsTheory.raw_create_bytecode_bound >>
     qpat_assum `expr_body_pre _ _ _ code es` (irule_at Any) >> first_assum ACCEPT_TAC) >>
  `abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) ctor)) <=
   abi_size_bound cenv.ce_struct_fields (TupleT (MAP expr_type ctor))` by
    (qpat_assum `EVERY (\e. expr_body_pre cenv cx env e es) ctor`
       (mp_then Any ACCEPT_TAC dallocaBlueprintArgsTheory.create_ctor_args_abi_bound)) >>
  `cap < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2**64` >> reverse conj_tac >- EVAL_TAC >>
     qpat_assum `cap = _` SUBST1_TAC >>
     map_every (fn q => qpat_assum q mp_tac)
       [`bytelike_type_bound (lowered_value_type cenv code) <= bd`,
        `abi_size_bound _ _ <= abi_size_bound _ _`, `bd + _ < 2**64`] >> numLib.ARITH_TAC) >>
  `LENGTH bs + abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) ctor)) <= cap` by
    (qpat_assum `cap = _` SUBST1_TAC >> simp[]) >>
  `LENGTH bs <= cap` by
    (qpat_assum `LENGTH bs + _ <= cap` mp_tac >> numLib.ARITH_TAC) >>
  irule create_ctor_rows_cut >>
  qpat_assum `compile_create_ctor_args _ _ ctor sa = _` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) sh = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "row_exit"
QED

Resume raw_create_encoded_args_cut[row_exit]:
  qx_genl_tac [`marks`,`vs`,`ee`,`Gr`,`tr`,`rs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `!tail. eval_exprs cx ctor _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value list``] valid_horizon_frame) >>
     qexistsl [`eval_exprs cx ctor`,`INL vs`,`ee with gas_obs := []`] >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee rs /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gr tr rs` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> LENGTH vals = LENGTH ctor /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. _ ==> LENGTH vals = LENGTH ctor /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >> simp[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings)) ctor /\
   EVERY (\e. expr_body_pre cenv cx env e ee) ctor` by
    (simp[EVERY_MEM] >> metis_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  qpat_assum `!tail. eval_exprs cx ctor _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `t` |-> `rs`, `G` |-> `Gr`, `tn` |-> `tr`,
      `entry` |-> `es with gas_obs := gas_explicit marks s.vs_gas_readings`,
      `fin` |-> `ee with gas_obs := []`] create_rows_encoder_inputs) >>
  impl_tac
  >- (simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. _ ==> LENGTH vals = LENGTH ctor /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocas_from lo rs /\ lo <= rs.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx ee Gr tr rs`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  suspend "recover_prefix"
QED

Resume raw_create_encoded_args_cut[recover_prefix]:
  `src_base+off < dimword (:256)` by
    (qpat_assum `off + LENGTH bs <= oldcap` mp_tac >>
     qpat_assum `src_base + oldcap < dimword (:256)` mp_tac >> numLib.ARITH_TAC) >>
  `w2n (n2w (src_base+off):bytes32) = src_base+off` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  drule_all raw_create_owned_window_frame >>
  disch_then (fn result =>
    qpat_assum `w2n (n2w (src_base+off):bytes32) = src_base+off`
      (fn th => map_every assume_tac (CONJUNCTS (REWRITE_RULE [th] result)))) >>
  drule_all raw_create_encoder_saved_prefix >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`root`,`payload`,`pbase`,`inst`,`u`,`Gu`,`tu`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "run_values_encoder"
QED

Resume raw_create_encoded_args_cut[run_values_encoder]:
  `compile_abi_encode_values_to_buf cenv (Var payload)
      (ZIP (vals,MAP (lowered_value_type cenv) ctor)) c = (alen,en)` by
    (qpat_assum `dst = Var payload` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee rs` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee rs /\ _`
       (drule_then strip_assume_tac)) >>
  mp_tac (Q.INST [`prefix` |-> `bs`, `capacity` |-> `cap`, `args` |-> `ctor`,
      `ce` |-> `cenv`, `s` |-> `rs`, `G` |-> `Gr`, `tn` |-> `tr`,
      `shared` |-> `se.cs_next_id`, `payload_var` |-> `payload`, `st` |-> `c`,
      `fin` |-> `en`, `disp` |-> `d`, `initial` |-> `u`, `Gi` |-> `Gu`, `ti` |-> `tu`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] create_encoded_rows_window) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`args_bytes`,`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "add_total"
QED

Resume raw_create_encoded_args_cut[add_total]:
  `emit_op ADD [Var root;len] b = (Var payload,c)` by
    (qpat_assum `buf.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     qpat_assum `dst = Var payload` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c u _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE
      [bodyFullExtCallDirectStateTheory.abi_encode_saved_state_def]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    raw_create_total_path) >>
  disch_then (qx_choosel_then [`out`,`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "join_paths"
QED

Resume raw_create_encoded_args_cut[join_paths]:
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (rs,Gr,tr) [] (OK z,Gz,tz)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gu`,`u`,`tu`] >> conj_tac
     >- (qpat_assum `!D explicit. gas_origin_ptr_path _ (rs,Gr,tr) [] (OK u,Gu,tu)`
           (qspecl_then [`D`,`gas_explicit_sites ctx shadow_ctx`] ACCEPT_TAC)) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gv`,`v`,`tv`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK rs,Gr,tr)`
       (drule_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`rs`,`Gr`,`tr`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  suspend "apply_next"
QED

Resume raw_create_encoded_args_cut[apply_next]:
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >>
     qpat_assum `wb_frame cenv ee ee se rs z` (irule_at Any) >> simp[] >>
     qexistsl [`tr`,`Gr`] >> simp[]) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `rs.vs_alloca_next` >> simp[]) >>
  `!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK z,Gz,tz)`
       (drule_then (irule_at Any)) >> qexists `fn` >>
     simp[] >> conj_tac
     >- (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
           qpat_assum `MEM func ctx.ctx_functions`
             (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
     first_assum ACCEPT_TAC) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gz`,`z`,`tz`] >> conj_tac
  >- (qx_gen_tac `H` >>
      qpat_assum `!D. gas_origin_ptr_path _ (rs,Gr,tr) [] (OK z,Gz,tz)`
        (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `!vs args_bytes ee Gz tz z marks. _ ==> gas_outcome_full _ _ _ _ (next vs) _ _ _`
    (qspecl_then [`vs`,`args_bytes`,`ee`,`Gz`,`tz`,`z`,`marks`] mp_tac) >>
  impl_tac >- suspend "suffix_window" >> simp[]
QED

Resume raw_create_encoded_args_cut[suffix_window]:
  `LENGTH vs = LENGTH ctor` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by (sym_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee z /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace` (drule_then assume_tac) >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path (DF H,_,_,_,_,_) (s,G,tn) marks (OK z,Gz,tz)`
        (drule_then assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`ef`,`Gf`,`tf`,`f`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pbase < dimword (:256)` by
    (qpat_assum `pbase + cap < dimword (:256)` mp_tac >> numLib.ARITH_TAC) >>
  `w2n (n2w pbase:bytes32) = pbase` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `inst.inst_id < sb.cs_next_id /\
   FLOOKUP z.vs_allocas inst.inst_id = SOME (pbase,cap)` by simp[] >>
  `ptr_covers Gz tz root z (LENGTH (bs ++ args_bytes))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tz (Var root) = {}` by
    (qpat_assum `ptr_covers Gz tz root z cap` (mp_tac o REWRITE_RULE [ptr_covers_def]) >> simp[]) >>
  `(!x. total_op = Var x ==> not_fresh_at sb x) /\ (!l. total_op <> Label l)` by
    simp[operand_11] >>
  drule_all (SIMP_RULE bool_ss [arithmeticTheory.ADD_CLAUSES]
    (Q.INST [`off` |-> `0`, `s` |-> `z`, `len` |-> `total_op`] raw_create_owned_window_frame)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`root`,`pbase`] >> asm_rewrite_tac[]
QED

Finalise raw_create_encoded_args_cut

(* The first bytecode read always uses the registered snapshot, even if
   the child was already represented by a pointer into ordinary memory. *)
Theorem raw_create_bytecode_cut:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env code es /\ body_expr_full_ok cx code /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_expr (gas_shadow_env T cenv) (expr_type code) (gas_shadow_expr code) sh = (vv,sha) /\
  compile_create_snapshot cenv vv (lowered_value_type cenv code) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap;Lit 32w] c = (data,sb) /\
  gas_shadow_state sa sh /\ gas_shadow_state a sha /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code sh sha shadow_func /\
  fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c sb func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!bs ee z Gz tz marks src owner pbase cap site.
    LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL (BytesV bs),ee with gas_obs := tail)) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    storage_trace_domain cx st0 ee.storage_trace /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\ return_buf_frame d cenv sb z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ site.inst_id < sb.cs_next_id /\
    FLOOKUP z.vs_allocas site.inst_id = SOME (pbase,cap) /\
    pbase + cap <= z.vs_alloca_next /\ pbase + cap < dimword (:256) /\ 32 + LENGTH bs <= cap /\
    data = Var src /\ not_fresh_at sb src /\ lookup_var src z = SOME (n2w (pbase + 32)) /\
    ptr_covers Gz tz src z (LENGTH bs) /\ op_taint tz (Var src) = {} /\
    (!x. len = Var x ==> not_fresh_at sb x) /\ (!l. len <> Label l) /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE /\
    read_memory (pbase + 32) (LENGTH bs) z = bs /\
    (!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tz.t_mem) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next (BytesV bs)) (ee,z,Gz,tz) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx code) (read_result cx)) next) (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (eval_expr cx code) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible,exprSimMemorySourceTheory.forced_expr_admissible_raw] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type code) code es` by
    (qpat_assum `body_expr_full_ok cx code` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_def] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodySimFullTheory.expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`a`,`sh`,`sha`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rewrite_tac[bind_assoc] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_expr cx code) _ childQ childR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl [`mid`,`t`,`v`] >> gvs[ignore_bind_def,bind_assoc])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >- (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists `\H res ee G1 tn1 t. childQ H res ee G1 tn1 t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[NoAsms,Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >> disj1_tac >>
  suspend "child_read"
QED

Resume raw_create_bytecode_cut[child_read]:
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr cx code) _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def]) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. _ ==> (?raw. res = INL raw /\ _) /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  rename1 `vv_post _ ctx func cenv cx code es sa a s ee raw vv t` >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    (drule_then ACCEPT_TAC exprSimAggregateSourceTheory.vv_post_materialises) >>
  `!tail. read_result cx raw (ee with gas_obs := tail) = (INL v,ee with gas_obs := tail)` by
    (drule_then ACCEPT_TAC exprSimMemorySourceTheory.read_result_gas_obs) >>
  qexists `raw` >> simp[] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_lands >> BETA_TAC >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t'`,`v'`] >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G1`,`ee`,`INL v`,`t`,`tn1`] >>
  simp[cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules,evaluation_state_component_equality] >>
  gen_tac >> disch_then kall_tac >> suspend "snapshot_inputs"
QED

Resume raw_create_bytecode_cut[snapshot_inputs]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[] >>
  `!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)` by (gen_tac >> simp[Once bind_def]) >>
  `expr_body_pre cenv cx env code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by
    simp[] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
    qpat_assum `!tail. monad_bind (eval_expr cx code) _ _ = _`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [eq]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (irule body_const_cells_agree_expr_read >>
     qexistsl [`code`, `INL v`, `es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []`] >>
     qpat_assum `expr_body_pre cenv cx env code es`
       (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >> simp[]) >>
  drule_all (REWRITE_RULE [exprSimPropsTheory.vv_post_initial_gas]
    (Q.INST [`es` |-> `es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []`,
             `s` |-> `t`, `s0` |-> `s`] raw_create_bytecode_physical_input)) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  rename1 `lowered_value_type cenv code = BaseT (BytesT (Dynamic k))` >>
  qabbrev_tac `cap = type_memory_bytes cenv (lowered_value_type cenv code)` >>
  `32 + LENGTH bs <= cap /\ cap < dimword (:256)` by
    (unabbrev_all_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     irule arithmeticTheory.LESS_TRANS >> qexists `2**64` >>
     conj_tac >- first_assum ACCEPT_TAC >> EVAL_TAC) >>
  `post_value_type cenv code = expr_type code` by
    simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ []).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:eval_result``] vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl [`eval_expr cx code`,`INL raw`,`ee`] >>
     simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c sb` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type code`,`code`,`sa`]
       (cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     mp_tac (Q.SPECL [`cenv`,`vv`,`lowered_value_type cenv code`,`a`]
       exprLoweringPropsTheory.ci_mono_compile_create_snapshot) >>
     mp_tac (Q.SPECL [`MLOAD`,`[snap]`,`b`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[snap;Lit 32w]`,`c`] ci_mono_emit_op) >>
     asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv a` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  suspend "child_facts"
QED

Resume raw_create_bytecode_cut[child_facts]:
  qpat_x_assum `MAP FDOM (es with gas_obs := _).scopes = MAP FDOM ee.scopes`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx ee G1 tn1 t`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `wb_frame cenv es ee sa s t` by
    (qpat_assum `vv_post _ ctx func cenv cx code es sa a s ee raw vv t`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
     rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv a t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     qpat_assum `wb_frame cenv es ee sa s t`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at a x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!l. vv_operand vv <> Label l` by
    (drule_all assignPlaceOperandFactsTheory.assign_place_operand_not_label >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> (?tv. INL raw = INL tv /\ _) /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [sumTheory.INL_11])) >>
     qpat_assum `vv_post H ctx func cenv cx code es sa a s ee _ vv t`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
     simp[]) >>
  qpat_x_assum `!H. _ ==> (?tv. INL raw = INL tv /\ _) /\ _` kall_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by simp[] >>
  `compile_create_snapshot cenv vv (BaseT (BytesT (Dynamic k))) a = (snap,b) /\
   cap = type_memory_bytes cenv (BaseT (BytesT (Dynamic k)))` by
    (qpat_assum `lowered_value_type cenv code = _` (SUBST1_TAC o SYM) >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[Abbr `cap`]) >>
  `?owner pbase site u Gu tu.
    snap = Var owner /\ MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
    site.inst_id = a.cs_next_id /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ not_fresh_at b owner /\
    FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
    eval_operand snap u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
    pbase+cap < dimword (:256) /\ pbase+cap <= u.vs_alloca_next /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
    wb_frame cenv ee ee a t u /\ ghost_kept_at lo cenv ee a G1 tn1 t Gu tu /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
    return_buf_frame d cenv b u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,Gu,tu))` by suspend "select_copy" >>
  suspend "header"
QED

Resume raw_create_bytecode_cut[select_copy]:
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- suspend "copy_memory" >>
  Cases_on `?tr. vv_location vv = SOME (slot_loc tr)`
  >- suspend "copy_slot" >>
  suspend "copy_code"
QED

Resume raw_create_bytecode_cut[copy_memory]:
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `vv_post H0 ctx func cenv cx code es sa a s ee (Value (BytesV bs)) vv t` by
    (irule exprSimUnwrapPropsTheory.vv_post_read_result >> first_assum (irule_at Any) >> simp[]) >>
  `expr_post H0 ctx func cenv cx code es sa a s ee (BytesV bs) (vv_operand vv) t /\
   ptr_val_ok cx (post_value_type cenv code) (BytesV bs) (vv_operand vv) G1 tn1 t` by
    (Cases_on `vv` >> fs[vv_location_def,vv_operand_def] >> conj_tac
     >- (first_assum (irule o MATCH_MP exprSimUnwrapTheory.expr_post_of_vv_post_stack))
     >- (fs[ptr_vv_ok_def] >> qpat_assum `expr_type code = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
     >- (irule exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >> simp[] >>
         qexists `t'` >> conj_tac
         >- (irule eventTopicValuePropsTheory.bytestring_type_not_word >>
             qpat_assum `vv_post H0 ctx func cenv cx code es sa a s ee (Value _) _ t`
               (mp_tac o MATCH_MP exprPtrUnwrapMarkedTheory.vv_post_located_type) >>
             qpat_assum `expr_type code = _` (fn th => simp[th]) >>
             strip_tac >> simp[is_bytestring_type_def]) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
         qpat_assum `expr_type code = _` (fn th => simp[th,ptr_val_ok_def,is_word_type_def]))) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic bound))) =
      SOME (BaseTV (BytesT (Dynamic bound)))` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     qpat_assum `expr_type code = _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic bound)))` >>
     simp[] >> metis_tac[abiValueEncodingTheory.evaluate_type_base_result]) >>
  qpat_assum `post_value_type cenv code = expr_type code` (fn post_eq =>
    qpat_assum `expr_type code = _` (fn ann_eq =>
      qpat_assum `expr_post H0 ctx func cenv cx code es sa a s ee _ _ t`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.expr_post_def,post_eq,ann_eq]) >>
      qpat_assum `ptr_val_ok cx (post_value_type cenv code) _ _ G1 tn1 t`
        (assume_tac o REWRITE_RULE [post_eq,ann_eq]))) >>
  drule_all blueprint_raw_header_input >>
  disch_then (qx_choosel_then [`src`,`w`] (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at a src` by (qpat_assum `!x. vv_operand vv = Var x ==> _` (drule_then ACCEPT_TAC)) >>
  `read_memory (w2n (w:bytes32) + 32) (LENGTH bs) t = bs` by
    (qpat_assum `mem_bytes_at _ _ t.vs_memory = bs` mp_tac >>
     pure_rewrite_tac[read_memory_def,valueEncodingDefsTheory.mem_bytes_at_def] >> simp[]) >>
  irule raw_create_snapshot_memory_path >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`w2n (w:bytes32)`,`k`,`src`,`vv`] >>
  simp[wordsTheory.n2w_w2n,wordsTheory.w2n_lt] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume raw_create_bytecode_cut[copy_slot]:
  qpat_x_assum `?tr. vv_location vv = SOME (slot_loc tr)` (qx_choose_then `tr` assume_tac) >>
  Cases_on `vv` >>
  qpat_x_assum `vv_location _ = SOME (slot_loc tr)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_location_def]) >>
  rename1 `p.ptr_location = slot_loc tr` >>
  qpat_assum `vv_post _ ctx func cenv cx code es sa a s ee raw _ t`
    (drule_then strip_assume_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       exprPtrUnwrapStorageTheory.vv_post_storage_source)) >>
  rename1 `storage_holds cx tr tag (Value v) key ee t` >>
  `tag = BaseT (BytesT (Dynamic k))` by
    (qpat_assum `!loc. _ ==> vv_type _ = _ /\ _` (qspec_then `slot_loc tr` mp_tac) >>
     qpat_assum `p.ptr_location = _` (fn loc_eq =>
       qpat_assum `lowered_value_type cenv code = _` (fn ty_eq =>
         simp[NoAsms,loc_eq,ty_eq,vv_location_def,vv_type_def])) >>
     Cases_on `tr` >> simp[NoAsms,loweringPostsTheory.slot_loc_def]) >>
  `v = BytesV bs` by
    (qpat_assum `read_result cx raw ee = (INL v,ee)` mp_tac >>
     qpat_assum `read_result cx raw ee = (INL (BytesV bs),ee)` (fn th => simp[NoAsms,th])) >>
  `ptr_vv_ok cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) (LocatedValue tag p) ee G1 tn1 t` by
    (qpat_assum `tag = post_value_type cenv code` (fn post_eq =>
       qpat_assum `tag = BaseT _` (fn phy_eq =>
         qpat_assum `ptr_vv_ok _ _ raw _ _ _ _ _`
           (mp_tac o REWRITE_RULE [GSYM post_eq,phy_eq,ptr_vv_ok_def]))) >>
     Cases_on `tr` >> simp[ptr_vv_ok_def,loweringPostsTheory.slot_loc_def]) >>
  `cap = 32 * type_slot_size (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `cap = type_memory_size _` mp_tac >> simp[NoAsms,valueEncodingPropsTheory.type_memory_size_slots]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at a x` by
    (qpat_assum `!x. vv_operand _ = Var x ==> _` (mp_tac o REWRITE_RULE [vv_operand_def]) >> simp[]) >>
  `storage_holds cx tr (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) key ee t` by
    (qpat_assum `storage_holds cx tr tag _ key ee t` mp_tac >>
     qpat_assum `tag = BaseT _` (fn ty_eq =>
       qpat_assum `v = BytesV bs` (fn val_eq => simp[NoAsms,ty_eq,val_eq]))) >>
  irule raw_create_snapshot_slot_path >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`k`,`key`,`p`,`tag`,`tr`,`Value (BytesV bs)`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[read_result_def,return_def]
QED

Resume raw_create_bytecode_cut[copy_code]:
  `vv_location vv = SOME LocCode` by
    (qpat_assum `~(?tr. vv_location vv = SOME (slot_loc tr))` mp_tac >>
     qpat_assum `~(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` mp_tac >>
     qpat_assum `vv_location vv <> SOME LocCalldata` mp_tac >>
     Cases_on `vv` >> simp[NoAsms,vv_location_def] >>
     rpt strip_tac >> rename1 `p.ptr_location <> LocMemory` >>
     qpat_assum `!tr. p.ptr_location <> slot_loc tr` (fn th =>
       qspec_then `T` mp_tac th >> qspec_then `F` mp_tac th) >>
     qpat_assum `p.ptr_location <> LocMemory` mp_tac >>
     qpat_assum `p.ptr_location <> LocCalldata` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     Cases_on `p.ptr_location` >> simp[loweringPostsTheory.slot_loc_def]) >>
  Cases_on `vv` >>
  qpat_x_assum `vv_location _ = SOME LocCode`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_location_def]) >>
  rename1 `p.ptr_location = LocCode` >>
  qpat_assum `vv_post _ ctx func cenv cx code es sa a s ee raw _ t`
    (drule_then strip_assume_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       exprPtrUnwrapCodeTheory.vv_post_code_source)) >>
  rename1 `immutable_holds cenv cx tag (Value v) src ee t` >>
  `tag = BaseT (BytesT (Dynamic k)) /\
   32 * ((type_memory_bytes cenv tag + 31) DIV 32) = cap` by
    (qpat_assum `!loc. _ ==> vv_type _ = _ /\ _` (qspec_then `LocCode` mp_tac) >>
     qpat_assum `p.ptr_location = _` (fn loc_eq =>
       qpat_assum `lowered_value_type cenv code = _` (fn ty_eq =>
         simp[NoAsms,loc_eq,ty_eq,vv_location_def,vv_type_def]))) >>
  `v = BytesV bs` by
    (qpat_assum `read_result cx raw ee = (INL v,ee)` mp_tac >>
     qpat_assum `read_result cx raw ee = (INL (BytesV bs),ee)` (fn th => simp[NoAsms,th])) >>
  `immutable_holds cenv cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) src ee t` by
    (qpat_assum `immutable_holds cenv cx tag _ src ee t` mp_tac >>
     qpat_assum `tag = BaseT _` (fn ty_eq =>
       qpat_assum `v = BytesV bs` (fn val_eq => simp[NoAsms,ty_eq,val_eq]))) >>
  `exprSimCopy$copy_old_operand a p.ptr_operand` by
    (qpat_assum `!x. vv_operand _ = Var x ==> _` (mp_tac o REWRITE_RULE [vv_operand_def]) >>
     simp[exprSimCopyTheory.copy_old_operand_def]) >>
  `op_taint tn1 p.ptr_operand = {} /\ op_prov G1 p.ptr_operand = NONE` by
    (qpat_assum `ptr_vv_ok _ _ raw _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
      SOME (BaseTV (BytesT (Dynamic k)))` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_evaluates >>
     qpat_assum `lowered_value_type cenv code = _` (fn th => pure_rewrite_tac[th]) >>
     strip_tac >> metis_tac[abiValueEncodingTheory.evaluate_type_base_result]) >>
  `post_value_type cenv code = BaseT (BytesT (Dynamic k))` by
    (qpat_assum `tag = post_value_type cenv code` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `(cenv.ce_is_ctor ==> w2n src + cap <= lo /\
    (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) (w2n src) mem))` by
    (disch_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location _ = SOME LocCode ==> _`
       (mp_tac o REWRITE_RULE [vv_location_def,vv_operand_def]) >>
     qpat_assum `post_value_type cenv code = BaseT _` (fn th => pure_rewrite_tac[th]) >>
     simp[] >> strip_tac >>
     qpat_assum `!rt w. _ ==> _` (drule_all_then strip_assume_tac) >> simp[]) >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region t = SOME 0w /\ exprSimCopy$copy_old_operand a region /\
    op_taint tn1 region = {} /\ op_prov G1 region = NONE` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand region t = SOME 0w` by
       (drule stateRelProjTheory.stmt_state_rel_immutable_base_zero >>
        simp[loweringStateRelDefsTheory.immutable_base_zero_def]) >>
     `lo <> 0` by
       (qpat_assum `cenv.ce_is_ctor ==> w2n _ + cap <= lo /\ _` (drule_then strip_assume_tac) >>
        qpat_assum `32 + LENGTH bs <= cap` mp_tac >>
        qpat_assum `w2n _ + cap <= lo` mp_tac >> numLib.ARITH_TAC) >>
     Cases_on `region` >> simp[exprSimCopyTheory.copy_old_operand_def,op_taint_def,op_prov_def] >>
     conj_tac >- metis_tac[local_ptrs_reserved_imm_base] >>
     qpat_assum `ghost_inv_at _ lo d cenv cx ee G1 tn1 t`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def,op_taint_def]) >> simp[]) >>
  `~cenv.ce_is_ctor ==> w2n src + cap <= LENGTH t.vs_data_section /\
      w2n src + cap < dimword (:256)` by
    (disch_tac >> qpat_assum `cap = type_memory_size _` SUBST1_TAC >>
     conj_tac >- (drule_all bodyImmutableUnwrapMemoryTheory.runtime_immutable_data_section >> simp[]) >>
     drule_all exprSimCopyTheory.immutable_holds_bounds >> simp[]) >>
  irule raw_create_snapshot_code_path >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`k`,`p`,`src`,`tag`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume raw_create_bytecode_cut[header]:
  qpat_x_assum `snap = Var owner` SUBST_ALL_TAC >>
  `ptr_covers Gu tu owner u (32 + LENGTH bs)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `pbase + 32 < dimword (:256) /\ pbase + 32 + LENGTH bs <= u.vs_alloca_next` by
    (qpat_assum `pbase + cap < dimword (:256)` mp_tac >>
     qpat_assum `pbase + cap <= u.vs_alloca_next` mp_tac >>
     qpat_assum `32 + LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `mem_bytes_at (pbase + 32) (LENGTH bs) u.vs_memory = bs` by
    (qpat_assum `read_memory (pbase + 32) (LENGTH bs) u = bs`
       (ACCEPT_TAC o REWRITE_RULE [memoryReadPropsTheory.read_memory_eq_mem_bytes_at])) >>
  drule_all blueprint_raw_header_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`l`,`src`,`z`,`Gz`,`tz`] strip_assume_tac)) >>
  qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = u`
    (mp_tac o Q.AP_TERM `\r. (r.vs_memory,r.vs_allocas,r.vs_alloca_next,
        r.vs_fmp,r.vs_initial_fmp,r.vs_call_ctx,r.vs_accounts,
        r.vs_transient,r.vs_immutables,r.vs_halted)`) >> simp[] >> strip_tac >>
  `state_frame z = state_frame (u with vs_inst_idx := z.vs_inst_idx)` by
    (qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = u`
      (mp_tac o Q.AP_TERM `\r:venom_state. r with <|vs_vars := FEMPTY; vs_inst_idx := z.vs_inst_idx|>`) >>
     simp[stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `tz with t_var := _ = tu`
    (mp_tac o Q.AP_TERM `\r. (r.t_mem,r.t_stor,r.t_trans,r.t_imm)`) >> simp[] >> strip_tac >>
  `ci_mono b sb` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved cenv b` by
    (irule local_ptrs_reserved_next_var >> qexists `a` >> simp[] >> fs[ci_mono_def]) >>
  `wb_frame cenv ee ee b u z` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl [`b`,`u`] >> simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
  `ghost_kept_at lo cenv ee b Gu tu u Gz tz` by simp[ghost_kept_at_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee u` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace`
       (drule_then assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx es s /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv ee ee a t z /\ ghost_kept_at lo cenv ee a G1 tn1 t Gz tz` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame cenv ee ee b u z` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx ee t` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee b Gu tu u Gz tz` (irule_at Any) >> simp[]) >>
  `wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] create_cut_frames_trans) >>
     qpat_assum `wb_frame cenv ee ee a t z` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee a G1 tn1 t Gz tz` (irule_at Any) >> simp[]) >>
  `!x. ((?k. cenv.ce_return_buf = SOME (PtrVar (Var x) k)) \/
         (?k. cenv.ce_return_pc = SOME (PtrVar (Var x) k))) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `a` >>
     (conj_tac >- fs[ci_mono_def] >>
      FIRST [qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x`
                (drule_then ACCEPT_TAC),
             qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x`
                (drule_then ACCEPT_TAC)])) >>
  `alloca_history func z` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gz,tz)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`gas_explicit_sites ctx shadow_ctx`]
         (irule_at Any)) >> simp[] >> metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `return_buf_frame d cenv sb z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv b u` (irule_at Any) >> simp[] >> fs[ci_mono_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (disch_tac >>
     `allocas_below_fmp u` by (first_assum (fn th => drule_then ACCEPT_TAC th)) >>
     pop_assum (fn th =>
       pure_rewrite_tac[allocas_below_fmp_def] >>
       map_every (fn sel => qpat_assum sel SUBST1_TAC)
         [`z.vs_initial_fmp = u.vs_initial_fmp`,`z.vs_fmp = u.vs_fmp`,`z.vs_allocas = u.vs_allocas`] >>
       ACCEPT_TAC (REWRITE_RULE[allocas_below_fmp_def] th))) >>
  suspend "header_paths"
QED

Resume raw_create_bytecode_cut[header_paths]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gu,tu)`
       (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> simp[] >>
     conj_tac
     >- (irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
         qpat_assum `state_frame z = _` (irule_at Any) >>
         qexists `b` >> simp[] >> rpt strip_tac >>
         qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
         qexistsl [`Gu`,`ee`,`u`,`b`,`tu`] >> simp[] >> metis_tac[]) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
       (drule_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  `!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u` by
    (rpt strip_tac >> irule bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK z,Gz,tz)` (irule_at Any) >>
     qexists `fn` >> simp[] >> metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]) >>
  suspend "header_cont"
QED

Resume raw_create_bytecode_cut[header_cont]:
  `LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code)` by
    simp[vyperTypeSystemTheory.bytelike_type_bound_def,bound_length_def] >>
  `site.inst_id < sb.cs_next_id` by
    (`a.cs_next_id <= b.cs_next_id /\ c.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
     qpat_assum `emit_op MLOAD _ b = _` (mp_tac o MATCH_MP entryDecodeStructureTheory.emit_op_next_id) >>
     qpat_assum `a.cs_next_id <= b.cs_next_id` mp_tac >>
     qpat_assum `c.cs_next_id <= sb.cs_next_id` mp_tac >> simp[] >> numLib.ARITH_TAC) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     qpat_assum `t.vs_alloca_next <= u.vs_alloca_next` mp_tac >> simp[] >> numLib.ARITH_TAC) >>
  `op_taint tz (Var src) = {}` by
    (qpat_assum `ptr_covers Gz tz src z (LENGTH bs)` mp_tac >>
     simp[NoAsms,ptr_covers_def]) >>
  `lookup_var src z = SOME (n2w (pbase + 32))` by
    (qpat_assum `data = Var src` SUBST_ALL_TAC >>
     qpat_assum `eval_operand (Var src) z = SOME _`
       (ACCEPT_TAC o REWRITE_RULE[eval_operand_def])) >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  conj_tac >- (qpat_assum `!v. storage_trace_frame (next v)` (irule)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gz`,`z`,`tz`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!bs ee z Gz tz marks src owner pbase cap site. _ ==> gas_outcome_full _ _ _ _ (next (BytesV bs)) _ _ _`
    irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[operand_11]
  >- simp[operand_11]
  >- (qexists `marks` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`cap`,`owner`,`pbase`,`site`,`src`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `z.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (pure_rewrite_tac[memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Finalise raw_create_bytecode_cut

Theorem raw_create_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx (create_operand_order RawCreate s es) ==>
    body_expr_full_ok cx (Call ty (CreateTarget RawCreate s r ks) es d)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`salted`,`rof`,`ks`,`args`,`dflt`] >>
  disch_tac >> rewrite_tac[Once body_expr_full_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_create_pre_args >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`code`,`amount`,`ctor`,`salts`,`bd`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  conj_asm1_tac
  >- (rewrite_tac[bodySimFullTheory.expr_sim_full_def,GSYM APPEND_ASSOC,APPEND] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all raw_create_compile_cuts >>
      strip_tac >>
      rename1 `compile_expr cenv (expr_type code) code sa = (vv,sa1)` >>
      rename1 `compile_expr _ _ (gas_shadow_expr code) shadow_sa = (vv,sha1)` >>
      rename1 `compile_create_snapshot cenv vv (lowered_value_type cenv code) sa1 = (root,sa2)` >>
      rename1 `emit_op MLOAD [root] sa2 = (len,sa3)` >>
      rename1 `emit_op ADD [root;Lit 32w] sa3 = (data,sc)` >>
      rename1 `emit_op ADD [root;Lit 32w] _ = (data,shc)` >>
      rename1 `lower_value _ _ _ amount se = (v,sf)` >>
      rename1 `lower_value _ _ _ (gas_shadow_expr amount) she = (v,shf)` >>
      rename1 `compile_create_salt _ _ _ sf = (sop,sg)` >>
      rename1 `compile_create_salt _ _ _ shf = (sop,shg)` >>
      rename1 `compile_create_dispatch init_op size_op v sop rof sg = (op,sb)` >>
      simp[create_eval_read,vyperASTTheory.expr_type_def,
           loweringPostsTheory.post_value_type_def,is_word_type_def] >>
      suspend "bytecode") >>
  irule bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
  simp[create_compile_stack,loweringPostsTheory.post_value_type_def,
       vyperASTTheory.expr_type_def,is_word_type_def] >>
  metis_tac[create_eval_value]
QED

Resume raw_create_expr_full_ok[bytecode]:
  `expr_body_pre cenv cx env code es` by fs[] >>
  qpat_assum `create_operand_order RawCreate _ _ = _` (fn order_th =>
    qpat_x_assum `body_exprs_full_ok _ (create_operand_order RawCreate _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def] o REWRITE_RULE [order_th])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `src_action = eval_create_operands cx RawCreate salted rof
    (BaseT (BytesT (Dynamic bd))::BaseT (UintT 256)::(MAP expr_type ctor ++ MAP expr_type salts))
    (blueprint_literal_offset cx salted (code::amount::(ctor ++ salts)))` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ postQ _` >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL raw_create_bytecode_cut) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
  qpat_assum `compile_expr cenv _ code sa = (vv,sa1)` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr code) shadow_sa = _` (irule_at Any) >>
  qpat_assum `compile_create_snapshot cenv vv _ sa1 = (root,sa2)` (irule_at Any) >>
  qpat_assum `emit_op MLOAD [root] sa2 = (len,sa3)` (irule_at Any) >>
  qpat_assum `emit_op ADD [root; Lit 32w] sa3 = (data,sc)` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `MEM shadow_func shadow_ctx.ctx_functions` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env code es` (irule_at Any) >>
  qpat_assum `expr_type code = BaseT (BytesT (Dynamic bd))` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_create_operands,
          vyperStorageTraceTheory.storage_trace_frame_read_result,Abbr `src_action`] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_full_ok cx (ctor ++ amount::salts)` by
    (first_assum irule >>
     qpat_assum `!tail. bind (eval_expr cx code) _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> metis_tac[]) >>
  `ci_mono sa sa1` by
    (qspecl_then [`cenv`,`expr_type code`,`code`,`sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono sa1 sa2` by
    (qspecl_then [`cenv`,`vv`,`lowered_value_type cenv code`,`sa1`]
       mp_tac ci_mono_compile_create_snapshot >> simp[]) >>
  `ci_mono sa2 sa3 /\ ci_mono sa3 sc` by
    (conj_tac
     >- (qspecl_then [`MLOAD`,`[root]`,`sa2`] mp_tac ci_mono_emit_op >> simp[]) >>
     qspecl_then [`ADD`,`[root; Lit 32w]`,`sa3`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `ci_mono se sf /\ ci_mono sf sg` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type amount`,`amount`,`se`]
           mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     qspecl_then [`compile_expr`,`cenv`,`if salted then SOME (HD salts) else NONE`,`sf`]
       mp_tac ci_mono_compile_create_salt >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono se sg` by metis_tac[ci_mono_trans] >>
  `!a. ci_mono sa a ==> local_ptrs_reserved cenv a /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x)` by
    (gen_tac >> rewrite_tac[ci_mono_def] >> strip_tac >>
     conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists `sa` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac
     >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
         qexists `sa` >> simp[] >>
         qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sa x`
           (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  `if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []` by (Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `!e u. MEM e (amount::salts) /\ expr_sim_inv cenv cx env u ==>
     expr_body_pre cenv cx env e u` by
    (rpt gen_tac >> strip_tac >> irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ (CreateTarget RawCreate _ _ _) _ _) es` (irule_at Any) >>
     fs[]) >>
  qabbrev_tac `cutQ = \e u Gu tu action.
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 action (e,u,Gu,tu) postQ
      (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` >>
  `!cvs enc eu u Gu tu.
    (if ctor = [] /\ cvs = [] then enc = []
     else encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) cvs = SOME enc) /\
    body_const_cells_agree [(NONE,tops)] cx env eu /\
    expr_sim_inv cenv cx env eu /\ body_exprs_full_ok cx (amount::salts) /\ ci_mono sa se /\
    wb_frame cenv es eu sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    return_buf_frame d cenv se u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = se.cs_current_bb /\ u.vs_inst_idx = LENGTH se.cs_current_insts /\
    (!H. valid_horizon cx st0 H eu.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx eu u /\
      storage_well_formed_on cx eu (FST H) /\ ghost_inv_at (DF H) lo d cenv cx eu Gu tu u) /\
    (!ef Gf tf f.
      wb_frame cenv eu ef se u f /\ ghost_kept_at lo cenv eu se Gu tu u Gf tf /\
      u.vs_alloca_next <= f.vs_alloca_next ==>
      ?p base. init_op = Var p /\ lookup_var p f = SOME (n2w base) /\
        base < dimword (:256) /\ LENGTH (bs ++ enc) < dimword (:256) /\
        ptr_covers Gf tf p f (LENGTH (bs ++ enc)) /\ op_taint tf (Var p) = {} /\
        base + LENGTH (bs ++ enc) <= f.vs_alloca_next /\
        eval_operand size_op f = SOME (n2w (LENGTH (bs ++ enc))) /\
        op_taint tf size_op = {} /\ op_prov Gf size_op = NONE /\
        read_memory base (LENGTH (bs ++ enc)) f = bs ++ enc /\
        (!i. base <= i /\ i < base + LENGTH (bs ++ enc) ==> i NOTIN tf.t_mem)) ==>
    cutQ eu u Gu tu (bind (eval_exprs cx (amount::salts))
      (\ws. bind (src_action (BytesV bs::(cvs ++ ws))) (read_result cx)))` by
      (qx_genl_tac [`cvs`,`ctor_bytes`,`eu`,`u`,`Gu`,`tu`] >>
       disch_then (map_every assume_tac o CONJUNCTS) >> suspend "scalar") >>
  Cases_on `ctor = []`
  >- suspend "no_ctor" >>
  suspend "ctor"
QED

Resume raw_create_expr_full_ok[scalar]:
  qabbrev_tac `raw_action = \av sv.
    bind (src_action (BytesV bs::(cvs ++ av::(case sv of NONE => [] | SOME salt_val => [salt_val]))))
         (read_result cx)` >>
  `bind (eval_exprs cx (amount::salts))
      (\ws. bind (src_action (BytesV bs::(cvs ++ ws))) (read_result cx)) =
    bind (eval_exprs cx (amount::salts))
      (\ws. raw_action (HD ws) (if salted then SOME (EL 1 ws) else NONE))` by
    (irule vyperInterpreterTheory.bind_cong_implicit >> simp[] >>
     rpt strip_tac >> drule vyperInterpreterTheory.eval_exprs_length >>
     Cases_on `salted` >> fs[LENGTH_EQ_NUM_compute] >> rpt strip_tac >>
     gvs[Abbr `raw_action`]) >>
  simp[Abbr `cutQ`] >>
  ho_match_mp_tac (GEN_ALL raw_create_scalar_suffix_cut) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env eu` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ amount se = (v,sf)` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) she = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ sf = (sop,sg)` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ shf = (sop,shg)` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `MEM shadow_func shadow_ctx.ctx_functions` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv se u` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env eu`
    (fn th => `expr_body_pre cenv cx env amount eu` by
      (first_assum irule >> simp[th])) >>
  qpat_assum `expr_body_pre cenv cx env amount eu` (irule_at Any) >>
  qpat_assum `!a. ci_mono sa a ==> _` (drule_then strip_assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!e u. MEM e (amount::salts) /\ _ ==> _` irule >> simp[])
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H eu.storage_trace ==> _` (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- simp[NoAsms,Abbr `raw_action`,Abbr `src_action`,
       vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.storage_trace_frame_create_operands,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qx_genl_tac [`av`,`sv`,`yw`,`sw`,`ef`,`Gf`,`tf`,`f`,`gs`,`scalar_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ef.storage_trace) ef.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx st0 H eu.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `wb_frame cenv es ef sa s0 f /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (qpat_assum `wb_frame cenv eu ef se u f`
      (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sa sg` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= sg.cs_next_var /\ s0.vs_alloca_next <= f.vs_alloca_next` by
    (qpat_assum `ci_mono sa sg` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  qpat_assum `!a. ci_mono sa a ==> _`
    (qspec_then `sg` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!ef Gf tf f. wb_frame cenv eu ef se u f /\ _ ==> ?p base. _`
    (qspecl_then [`ef`,`Gf`,`tf`,`f`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `init_op = Var final_ptr` >>
  rename1 `lookup_var final_ptr f = SOME (n2w final_base)` >>
  `eval_operand init_op f = SOME (n2w final_base)` by simp[eval_operand_def] >>
  `outcomes_accounts_typed ef.outcomes /\ IS_SOME ef.outcomes` by
    (qpat_assum `expr_sim_inv cenv cx env ef` (mp_tac o REWRITE_RULE[expr_sim_inv_def]) >> simp[]) >>
  simp[NoAsms,Abbr `postQ`] >> irule create_dispatch_outcome_full >>
  qpat_assum `compile_create_dispatch init_op size_op v sop rof sg = (op,sb)` (irule_at Any) >>
  qpat_assum `eval_operand init_op f = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand size_op f = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand v f = SOME yw` (irule_at Any) >>
  qexistsl [`sw`,`bs ++ ctor_bytes`] >>
  simp[wordsTheory.w2n_n2w,loweringPostsTheory.post_value_type_def,vyperASTTheory.expr_type_def,
       supportedExprTraverseTheory.expr_has_effect_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_effect_root_def] >>
  conj_tac
  >- (gen_tac >> simp[NoAsms,Abbr `raw_action`,Abbr `src_action`] >>
      qpat_assum `IS_SOME sv <=> salted` (pure_once_rewrite_tac o single o GSYM) >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [Q.INST [`ctor_tys` |-> `MAP expr_type ctor`, `encoded` |-> `ctor_bytes`,
                 `value` |-> `w2n (yw:256 word)`, `sw` |-> `sw`] raw_create_read_prepared] >>
      simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `IS_SOME sv <=> salted` (pure_once_rewrite_tac o single) >>
      first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- (PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >> first_assum ACCEPT_TAC)
  >- (disch_tac >> PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >> first_assum ACCEPT_TAC)
  >- (disch_tac >> disj1_tac >> PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `OPTREL _ sop sw` mp_tac >>
  Cases_on `sop` >> Cases_on `sw` >> simp[NoAsms,optionTheory.OPTREL_def]
QED

Resume raw_create_expr_full_ok[no_ctor]:
  qpat_x_assum `if ctor = [] then _ else _`
    (fn th => qpat_assum `ctor = []` (fn eq =>
      mp_tac (SIMP_RULE bool_ss [eq] th))) >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  qpat_assum `ctor = []` SUBST_ALL_TAC >>
  qpat_assum `data = Var src` SUBST_ALL_TAC >>
  qpat_assum `!cvs enc eu u Gu tu. _ ==> cutQ eu u Gu tu _`
    (qspecl_then [`[]`,`[]`,`ee`,`z`,`Gz`,`tz`] mp_tac) >>
  simp[NoAsms,Abbr `cutQ`] >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- fs[APPEND]
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qx_genl_tac [`ef`,`Gf`,`tf`,`f`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
      by fs[storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    `pbase + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)` by
      (qpat_assum `cap + pbase < _` mp_tac >> qpat_assum `LENGTH bs + 32 <= cap` mp_tac >>
       simp[wordsTheory.dimword_def] >> numLib.ARITH_TAC) >>
    `w2n (n2w (pbase + 32) :bytes32) = pbase + 32` by simp[wordsTheory.w2n_n2w] >>
    `pbase + cap <= z.vs_alloca_next /\ 32 + LENGTH bs <= cap` by decide_tac >>
    `!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tz.t_mem` by
      (gen_tac >> strip_tac >>
       qpat_assum `!i. pbase + 32 <= i /\ i < pbase + (LENGTH bs + 32) ==> _` irule >>
       decide_tac) >>
    qpat_assum `wb_frame cenv ee ef sc z f`
      (mp_then Any (drule_all_then (fn th =>
        qpat_assum `w2n (n2w (pbase + 32) :bytes32) = _`
          (fn eq => map_every assume_tac (CONJUNCTS (REWRITE_RULE[eq] th)))))
        (Q.INST [`off` |-> `32`] raw_create_owned_window_frame)) >>
    qexists `pbase + 32` >> fs[wordsTheory.dimword_def]) >>
  simp[NoAsms]
QED

Resume raw_create_expr_full_ok[ctor]:
  qpat_x_assum `if ctor = [] then _ else _`
    (fn th => qpat_assum `ctor <> []` (fn ne =>
      mp_tac (SIMP_RULE bool_ss [ne,LET_THM] th))) >>
  strip_tac >>
  qpat_assum `data = Var src` SUBST_ALL_TAC >>
  qpat_assum `init_op = _` SUBST_ALL_TAC >>
  qpat_assum `body_exprs_full_ok cx (ctor ++ amount::salts)`
    (mp_then Any (map_every assume_tac o CONJUNCTS) create_body_exprs_split) >>
  once_rewrite_tac[create_eval_exprs_append] >>
  simp[NoAsms,bind_assoc,bind_return] >>
  ho_match_mp_tac (GEN_ALL (Q.INST [`off` |-> `32`] raw_create_encoded_args_cut)) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env ee` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env (Call _ (CreateTarget RawCreate _ _ _) _ _) es`
    (irule_at Any) >>
  qpat_assum `expr_type code = BaseT (BytesT (Dynamic bd))` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ cenv ctor sc = _` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) shc = _` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sc z` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
  qpat_assum `compile_copy_memory_dynamic _ (Var src) len _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD [_;len] _ = _` (irule_at Any) >>
  qpat_assum `compile_abi_encode_values_to_buf cenv _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD [len;_] _ = (size_op,se)` (irule_at Any) >>
  qpat_assum `lookup_var src z = SOME (n2w (pbase+32))` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas site.inst_id = SOME (pbase,cap)` (irule_at Any) >>
  qpat_assum `site.inst_outputs = [owner]` (irule_at Any) >>
  qpat_assum `ptr_covers Gz tz src z (LENGTH bs)` (irule_at Any) >>
  qpat_assum `read_memory (pbase+32) (LENGTH bs) z = bs` (irule_at Any) >>
  qexists `shadow_func` >>
  qpat_assum `!a. ci_mono sa a ==> _`
    (qspec_then `sc` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[]
  >- REFL_TAC
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (PURE_ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)
  >- (PURE_ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >> simp[wordsTheory.dimword_def])
  >- (PURE_ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!i. pbase + 32 <= i /\ i < pbase + (LENGTH bs + 32) ==> _` irule >>
      decide_tac)
  >- simp[NoAsms,Abbr `src_action`,
       vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_create_operands,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qx_genl_tac [`cvs`,`ctor_bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_exprs env ctor` by
    (simp[constSubstCorrectTheory.frame_well_typed_exprs_every,EVERY_MEM] >>
     qx_gen_tac `arg` >> strip_tac >>
     `expr_body_pre cenv cx env arg ee` by
       (irule create_operand_pre >>
        qpat_assum `expr_body_pre cenv cx env (Call _ (CreateTarget RawCreate _ _ _) _ _) es`
          (irule_at Any) >>
        simp[MEM_APPEND]) >>
     drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env eu` by
    (qpat_assum `!tail. eval_exprs cx ctor _ = (INL cvs,_)` (qspec_then `[]` assume_tac) >>
     `body_const_cells_agree [(NONE,tops)] cx env (eu with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_exprs >>
     qexistsl [`ctor`,`INL cvs`,
       `ee with gas_obs := gas_explicit ctor_marks z.vs_gas_readings`] >> fs[]) >>
  `body_exprs_full_ok cx (amount::salts)` by
    (qpat_assum `!st vs en. eval_exprs cx ctor st = (INL vs,en) ==> _` irule >>
     qpat_assum `!tail. eval_exprs cx ctor _ = _` (qspec_then `[]` (irule_at Any))) >>
  `valid_horizon cx st0 (storage_trace_horizon eu.storage_trace) eu.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H eu.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `wb_frame cenv es eu sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` by
    (qpat_assum `wb_frame cenv ee eu sc z u`
      (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sc r /\ ci_mono r i /\ ci_mono i j /\ ci_mono j k /\ ci_mono k m /\ ci_mono m se` by
    (conj_tac >- metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_copy_memory_dynamic,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
     metis_tac[ci_mono_emit_op,pairTheory.SND]) >>
  `ci_mono sa se` by metis_tac[ci_mono_trans] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  qpat_assum `!cvs enc eu u Gu tu. _ ==> cutQ eu u Gu tu _`
    (qspecl_then [`cvs`,`ctor_bytes`,`eu`,`u`,`Gu`,`tu`] mp_tac) >>
  qpat_assum `ctor <> []` (fn ne => simp[NoAsms,ne,Abbr `cutQ`]) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (qx_gen_tac `HH` >> disch_tac >>
        qpat_assum `!H. valid_horizon cx st0 H eu.storage_trace ==> _`
          (qspec_then `HH` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
          (qspec_then `HH` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_assum `!ef Gf tf f. wb_frame cenv eu ef se u f /\ _ ==> ?p base. _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  simp[NoAsms]
QED

Finalise raw_create_expr_full_ok
