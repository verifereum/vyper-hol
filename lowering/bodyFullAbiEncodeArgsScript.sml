Theory bodyFullAbiEncodeArgs
Ancestors
  bodyFullShadowBodyInv bodyFullExtCallPosList
  bodyFullPreds bodySimFull bodyFullEmptyLeafData exprSimFullBundleProps
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimAbiEncodeRuntimeInputs abiEncodeArgsCase abiEncodeEndpointMetadata abiEncodeSnapshotOperandProps
  stmtSimProps[qualified,ignore_grammar]
  abiBuiltinEncodeCode abiBuiltinEncodeMethod abiBuiltinEncodeAllocate bodyFullAbiEncodeSetupTail
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeFinish bodyFullAbiEncodeResultResources
  bodyFullAllocaFresh bodyFullExtCallDirectWindows allocaSiteResource
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeSiteResources exprSimHash fragGasOriginPtrLoop
  gasOutcomeFullCompose gasShadowCompileHelpers gasShadowCompile gasShadowState
  exprLowering exprLoweringProps exprSimHyps exprSimHypsDefs exprSimSource exprSimDefs
  emitHelperProps loweringHalt localPtrsProps abiEncoderProps supportedExprTraverse
  eventTopicValueProps vyperTypeABI
  vyperTypeSystem vyperInterpreter vyperContext vyperState vyperAST
  vyperStorageTrace vyperStorageFootprint exprSimProps
  stateRelProj loweringStateRelDefs loweringPosts bodyPtrDefs freshWrites fragExec venomInst
  bodyPtrMakeArrayCopyStateFrame bodyFullExtCallDirectLayout
  wordArgsPtr exprSimWordArgs exprSimStorageCopy bodyMemoryDefs memoryReadProps
  gasExemptCert fragGasMode abiBuiltinAllocation freshWrites
  logStoreDataOriginPtr exprSimAlloc reasonCopySourcePtr
  bodyFullExtCallDirectEncode bodyFullExtCallDirectRow bodyFullExtCallDirectState
  bodyFullExtCallDirectPhase
  bodyFullExtCallDirectSaved bodyFullExtCallDirectUnwrap bodyFullAbiEncodeNonwordWindow abiEncoderWindowJoint
  abiEncoderAdmissible abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderWindowSource
  assignPlaceOperandFacts exprSafeOperand loweringShapeRules aggregateEvaluatedLayout
  entryDecodeStaticProps entryDecodeStructure allocLimits
  valueEncodingDefs valueEncodingProps valueEncodingProofs abiEncoderMemory abiBuiltinEncodeRun abiBuiltinEncodeSource
  abiEncodeValuesMetadata abiEncodeValuesSource contractABI vyperABI vyperABIValid
  exprSimAbiEncodeCapacity exprSimAbiEncodeSourceMetadata
  exprSimAbiEncodeArgsPhysicalCapacity vyperTypeDefaults
  vyperEvalScopesProgress abiDecoderMembers vyperABIRoundtrip vyperTypeArgFits
  typedMemoryCopy venomMemDefs ptrDiscipline fragGasOriginPtr
  compileEnv context words arithmetic pair list pred_set finite_map
Libs pairLib horizonTypeLib

Theorem abi_encode_snapshot_not_label[local]:
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm =
    (sv,ss) ==> !l. vv_operand sv <> Label l
Proof
  strip_tac >> irule abi_snapshot_operand_not_label >>
  metis_tac[assign_place_operand_not_label]
QED

(* A phase law is the ordinary producer's exact premise and result packet,
   with a side fact in that packet.  Make the statement templates from the
   producer terms so the frame and resource interfaces stay single-sourced. *)
local
  val side_ty = ``:compile_state -> compile_state -> venom_state -> venom_state -> bool``
  fun named vars name =
    case List.filter (fn v => #1 (dest_var v) = name) vars of
        [v] => v
      | _ => raise Fail ("ABI packaging phase variable: " ^ name)
  fun annotated side args tm =
    let
      val (prem,post) = dest_imp tm
      val (vs,body) = strip_exists post
      val side = list_mk_comb (side, map (named (vs @ free_vars tm)) args)
    in
      mk_imp (prem, list_mk_exists (vs, mk_conj (side,body)))
    end
  fun close fixed tm =
    list_mk_forall (List.filter (fn v =>
      not (List.exists (fn s => #1 (dest_var v) = s) fixed)) (free_vars tm), tm)
  val common = ["ctx","func","explicit","PG","lo"]
  val saved = ["ce","cx","st0","DF"]
  fun law side (rule,fixed,args) =
    close (side :: common @ fixed)
      (annotated (mk_var (side,side_ty)) args (#2 (strip_forall (concl rule))))
  fun equation name params rhs =
    let
      val args = map (named (free_vars rhs)) params
      val ty = List.foldr (fn (x,t) => type_of x --> t) bool args
    in
      mk_eq (list_mk_comb (mk_var (name,ty),args), rhs)
    end
  fun phase rel name (rule,fixed,args) =
    equation name (rel :: common @ fixed) (law rel (rule,fixed,args))
  fun is_row_callback tm =
    let val (vs,body) = strip_forall tm in
      not (null vs) andalso is_imp body andalso
      can (find_term (fn c => is_const c andalso
        #Name (dest_thy_const c) = "compile_abi_encode_value_rows")) body
    end
  fun annotate_row_callback side tm =
    if is_row_callback tm then
      let
        val (outer,p) = strip_forall tm
        val (site,rows) = dest_imp p
        val (inner,row) = strip_forall rows
      in
        list_mk_forall (outer,mk_imp (site,
          list_mk_forall (inner,annotated side ["a","c","v","z"] row)))
      end
    else tm
  fun fold_phase fixed =
    let
      val row = mk_var ("RowSide",side_ty)
      val seg = mk_var ("Seg",side_ty)
      val (pre,post) = dest_imp (#2 (strip_forall (concl abi_encode_saved_values_execute_pure)))
      val premises = strip_conj pre
      val [_] = List.filter is_row_callback premises
      val rule = mk_imp (list_mk_conj (map (annotate_row_callback row) premises), post)
      val params = "Seg" :: "RowSide" :: common @ fixed
    in
      equation "abi_packaging_fold_law" params
        (close params (annotated seg ["st","en","u","z"] rule))
    end
in
  val packaging_alloc_tm = phase "Seg" "abi_packaging_alloc_law"
    (INST_TYPE [Type.beta |-> ``:256``] abi_encode_alloc_origin_exact,
     ["sa","sb","n","buf","H"], ["sa","sb","s","t"])
  val packaging_setup_tm = phase "Seg" "abi_packaging_setup_law"
    (abi_encode_setup_tail_origin,
     ["a","method_st","ready","mid","data","k","N","maxlen"], ["a","ready","s","t"])
  val packaging_finish_tm = phase "Seg" "abi_packaging_finish_law"
    (abi_encode_finish_origin, ["a","b","lenop","k"], ["a","b","s","t"])
  val packaging_restore_tm = phase "Seg" "abi_packaging_restore_law"
    (extcall_direct_restore_saved_pure,
     saved @ ["d","front","su","sb","e","saved","src"], ["su","sb","u","z"])
  val packaging_window_tm = phase "Seg" "abi_packaging_window_law"
    (compile_abi_encode_to_buf_window_joint,
     ["st","en","dst","src","ei","out"], ["st","en","s","t"])
  val packaging_row_tm = phase "RowSide" "abi_packaging_row_law"
    (abi_encode_saved_row_open_pure,
     saved @ ["d","se","loc","shared","capacity","dst_offset","dst"], ["su","en","u","z"])
  val packaging_fold_tm = fold_phase
    (saved @ ["disp","se","st","en","shared","capacity","dst_offset","alen","rows","payload_var"])
end

Definition abi_packaging_alloc_law_def:
  ^packaging_alloc_tm
End

Definition abi_packaging_setup_law_def:
  ^packaging_setup_tm
End

Definition abi_packaging_finish_law_def:
  ^packaging_finish_tm
End

Definition abi_packaging_restore_law_def:
  ^packaging_restore_tm
End

Definition abi_packaging_window_law_def:
  ^packaging_window_tm
End

Definition abi_packaging_row_law_def:
  ^packaging_row_tm
End

Definition abi_packaging_fold_law_def:
  ^packaging_fold_tm
End

(* This quantification is over the cuts of this compilation, not over
   arbitrary intervals in the function.  Both payload suppliers are guarded. *)
Definition abi_packaging_phases_def:
  abi_packaging_phases Seg RowSide ctx func explicit PG lo ce cx st0 DF d hz
      single tys args svs meth maxlen k N out st sb <=>
  !buf allocated method_st data_ptr ready len body_end.
    compile_alloc_buffer N st = (buf,allocated) /\
    buf.buf_operand = out /\
    abi_builtin_encode_method_id meth out allocated = ((),method_st) /\
    emit_op ADD [out; Lit (n2w (32+k))] method_st = (data_ptr,ready) /\
    compile_abi_encode_payload ce single svs tys data_ptr ready = (len,body_end) /\
    abi_builtin_encode_finish out len k body_end = ((),sb) ==>
    abi_packaging_alloc_law Seg ctx func explicit PG lo st allocated N buf hz /\
    abi_packaging_setup_law Seg ctx func explicit PG lo allocated method_st ready meth data_ptr k N maxlen /\
    abi_packaging_finish_law Seg ctx func explicit PG lo body_end sb len k /\
    (single ==> !src unwrap_end.
      unwrap_value ce (HD svs) ready = (src,unwrap_end) ==>
      abi_packaging_restore_law Seg ctx func explicit PG lo ce cx st0 DF d st
        ready unwrap_end (HD args) (HD svs) src /\
      abi_packaging_window_law Seg ctx func explicit PG lo unwrap_end body_end data_ptr src
        (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce (HD args))) len /\
      (!pre z q. Seg ready unwrap_end pre z /\ Seg unwrap_end body_end z q ==>
        Seg ready body_end pre q)) /\
    (~single ==> !dp. data_ptr = Var dp ==>
      abi_packaging_row_law RowSide ctx func explicit PG lo ce cx st0 DF d st
        ready.cs_next_id st.cs_next_id N (32+k) dp /\
      abi_packaging_fold_law Seg RowSide ctx func explicit PG lo ce cx st0 DF d st
        ready body_end st.cs_next_id N (32+k) len (ZIP (svs,tys)) dp) /\
    (!t u pre q actual. Seg st allocated t u /\ Seg allocated ready u pre /\
      Seg ready body_end pre q /\ Seg body_end sb q actual ==> Seg st sb t actual)
End

Theorem abi_packaging_phases_trivial[local]:
  abi_packaging_phases (\a b s t. T) (\a b s t. T) ctx func explicit PG lo ce cx st0 DF d hz
    single tys args svs meth maxlen k N out st sb
Proof
  pure_rewrite_tac [abi_packaging_phases_def, abi_packaging_alloc_law_def,
    abi_packaging_setup_law_def, abi_packaging_finish_law_def,
    abi_packaging_restore_law_def, abi_packaging_window_law_def,
    abi_packaging_row_law_def, abi_packaging_fold_law_def] >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP] >>
  rpt (FIRST (map MATCH_ACCEPT_TAC
    [abi_encode_alloc_origin_exact, abi_encode_setup_tail_origin,
     abi_encode_finish_origin, extcall_direct_restore_saved_pure,
     compile_abi_encode_to_buf_window_joint, abi_encode_saved_row_open_pure,
     abi_encode_saved_values_execute_pure]) ORELSE
    gen_tac ORELSE conj_tac ORELSE disch_tac)
QED

(* The list has already returned at this site.  Keep its selected source
   equation and ghosts as inputs to the physical packaging continuation. *)
Theorem abi_encode_normal_packaging_side:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  (LENGTH args = 1 /\ ~ensure ==> ~is_word_type (lowered_value_type ce (HD args))) /\
  1 <= LENGTH args /\
  compile_abi_encode_args compile_expr ce args sa = (svs,st) /\
  lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
       else TupleT (MAP (lowered_value_type ce) args)))
    (compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) svs
      (MAP (lowered_value_type ce) args)) st = (out,sb) /\
  LocatedValue ann (mk_ptr out LocMemory) = vv /\
  LENGTH svs = LENGTH args /\ ci_mono sa st /\ ci_mono st sb /\
  fn_has_code sa st func /\ fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  storage_trace_domain cx st0 mid'.storage_trace /\
  (!tail. eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,mid' with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H mid'.storage_trace ==>
       extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s0 G0 tn0
         H res mid' G1 tn1 t) /\
  (!H. valid_horizon cx st0 H mid'.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) marks (OK t,G1,tn1)) /\
  (let single = (LENGTH args = 1 /\ ~ensure);
       tys = MAP (lowered_value_type ce) args;
       meth = OPTION_MAP bytes_method_id_word mid;
       k = (case meth of NONE => 0 | SOME _ => 4);
       maxlen = abi_size_bound ce.ce_struct_fields
         (if single then lowered_value_type ce (HD args) else TupleT tys);
       N = 32 + 32 * word_size (maxlen+k)
   in abi_packaging_phases Seg RowSide ctx func (gas_explicit_sites ctx shadow_ctx) PG lo
        ce cx st0 DF d (storage_trace_horizon mid'.storage_trace)
        single tys args svs meth maxlen k N out st sb) ==>
  ?vs payload actual Gf tf.
    Seg st sb t actual /\
    res = INL vs /\
    evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
      INL (BytesV payload) /\
    ~t.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK actual,Gf,tf)) /\
    (!H. valid_horizon cx st0 H mid'.storage_trace ==>
       expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx
         (TypeBuiltin ann (AbiEncode ensure mid) target args) (es,sa,sb,s0,vv,G0,tn0)
         H (INL (Value (BytesV payload)) : eval_result + exception)
         (mid' with gas_obs := []) Gf tf actual)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  qabbrev_tac `H0 = storage_trace_horizon mid'.storage_trace` >>
  `valid_horizon cx st0 H0 mid'.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s0 G0 tn0 H _ _ _ _ _`
    (qspec_then `H0` (drule_then (strip_assume_tac o SIMP_RULE bool_ss
      [extcall_positional_post_def]))) >>
  `eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid'.gas_obs) =
      (INL vs,mid')` by
    (qpat_assum `!tail. eval_exprs cx args _ = _` (qspec_then `mid'.gas_obs` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid'.gas_obs)` by
    (simp_tac bool_ss [expr_body_pre_gas_obs] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `meth = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `k = case meth of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `single = (LENGTH args = 1 /\ ~ensure)` >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `maxlen = abi_size_bound ce.ce_struct_fields
    (if single then lowered_value_type ce (HD args) else TupleT tys)` >>
  qabbrev_tac `N = 32 + 32 * word_size (maxlen+k)` >>
  `N < dimword(:256)` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es`
       (mp_tac o MATCH_MP abi_encode_endpoint_output_size) >>
     simp[Abbr `N`, Abbr `k`, Abbr `meth`, Abbr `maxlen`, Abbr `single`, Abbr `tys`] >>
     Cases_on `mid` >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `lower_abi_encode meth maxlen _ st = (out,sb)`
    (strip_assume_tac o MATCH_MP lower_abi_encode_trace) >>
  drule abi_builtin_encode_setup_trace >> strip_tac >>
  `ci_mono allocated method_st` by
    metis_tac[ci_mono_abi_builtin_encode_method_id, pairTheory.SND] >>
  `cs_extends allocated method_st` by fs[ci_mono_def] >>
  `cs_extends st allocated /\ cs_extends method_st ready /\
    cs_extends ready body_end /\ cs_extends body_end sb` by
    (drule abi_builtin_encode_finish_shape >> strip_tac >>
     metis_tac[ci_mono_def, ci_mono_compile_abi_encode_payload,
       ci_mono_emit_op, compile_alloc_buffer_extends, cs_extends_same_block,
       inst_extends_def, pairTheory.SND]) >>
  `fn_has_code st allocated func /\ fn_has_code allocated ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `compile_alloc_buffer N st = (buf,allocated) /\
   buf.buf_operand = out /\
   abi_builtin_encode_method_id meth out allocated = ((),method_st) /\
   emit_op ADD [out; Lit (n2w (32+k))] method_st = (data_ptr,ready) /\
   compile_abi_encode_payload ce single svs tys data_ptr ready = (len,body_end) /\
   abi_builtin_encode_finish out len k body_end = ((),sb)` by
    fs[Abbr `N`, Abbr `k`] >>
  qhdtm_x_assum `abi_packaging_phases`
    (mp_tac o PURE_REWRITE_RULE [abi_packaging_phases_def]) >>
  disch_then (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_assum `abi_packaging_alloc_law _ _ _ _ _ _ st allocated N buf H0`
    (fn th => mp_tac (Q.INST [`s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
          `cenv` |-> `ce`, `es` |-> `mid'`]
       (SPEC_ALL (PURE_REWRITE_RULE [abi_packaging_alloc_law_def] th)))) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`] strip_assume_tac) >>
  qabbrev_tac `p = w2n (w:bytes32)` >>
  `w = n2w p` by simp[Abbr `p`] >>
  `lo <= p` by metis_tac[allocas_from_def] >>
  `alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `~u.vs_halted` by
    (qpat_assum `~t.vs_halted` mp_tac >>
     qpat_assum `u with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H0 ctx func ce cx mid' u` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx mid' u`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `local_ptrs_rel func ce mid'.scopes u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ci_mono st allocated /\ ci_mono method_st ready` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_op, SND] >>
  `allocated.cs_next_var <= ready.cs_next_var /\ allocated.cs_next_id <= ready.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `sa.cs_next_var <= allocated.cs_next_var /\ sa.cs_next_id <= allocated.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce allocated /\ local_ptrs_reserved ce ready` by
    metis_tac[local_ptrs_reserved_next_var, LESS_EQ_TRANS] >>
  `not_fresh_at ready root` by metis_tac[not_fresh_at_mono] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
    (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x)` by
    metis_tac[ci_mono_def, not_fresh_at_mono, local_ptrs_reserved_imm_base] >>
  `ghost_inv_at (DF H0) lo d ce cx mid' Gu tu u` by
    (irule (horizonTypeLib.at_horizon_named "H" alloc_buffer_ghost_inv_at) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G1`,`H0`,`ctx`,`p+N`,`func`,`t`,`st`,`tn1`] >> simp[]) >>
  `lookup_var root u = SOME (n2w p)` by metis_tac[] >>
  `out = Var root /\
    abi_builtin_encode_method_id meth (Var root) allocated = ((),method_st) /\
    emit_op ADD [Var root;Lit (n2w (32+k))] method_st = (data_ptr,ready) /\
    compile_abi_encode_payload ce single svs tys data_ptr ready = (len,body_end) /\
    abi_builtin_encode_finish (Var root) len k body_end = ((),sb)` by fs[Abbr `k`] >>
  qabbrev_tac `write_len = case meth of NONE => 0 | SOME _ => 32` >>
  qpat_assum `abi_packaging_setup_law _ _ _ _ _ _ allocated method_st ready meth data_ptr k N maxlen`
    (fn th => mp_tac (Q.INST [`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`]
      (SPEC_ALL (PURE_REWRITE_RULE [abi_packaging_setup_law_def] th)))) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr `k`, Abbr `N`, Abbr `write_len`] >>
  disch_then (qx_choosel_then [`dp`,`pre`,`Gpre`,`tnpre`] strip_assume_tac) >>
  `32+write_len <= N` by
    (Cases_on `meth` >> simp[Abbr `write_len`, Abbr `N`, Abbr `k`] >>
     mp_tac abi_builtin_rounded_selector_store >> decide_tac) >>
  `!name base size. local_region ce mid'.scopes u name base size ==>
    regions_disjoint (p+32) write_len base size` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region ce mid'.scopes u name b len ==> _`
       (drule_then mp_tac) >>
     simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at allocated x` by
    (rpt strip_tac >>
     qpat_assum `local_ptrs_reserved ce allocated`
       (qspecl_then [`name`, `name`, `x`, `sz`, `sz`] (drule_then (ACCEPT_TAC o cj 1)) o
        cj 2 o REWRITE_RULE [local_ptrs_reserved_def])) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at allocated x) /\
   (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at allocated x)` by
    (qpat_assum `ci_mono st allocated`
       (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     rpt conj_tac >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists_tac `st` >> asm_rewrite_tac[] >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  `ghost_inv_at (DF H0) lo d ce cx mid' Gpre tnpre pre` by
    (qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es Gpre tnpre pre` irule >>
     asm_rewrite_tac[]) >>
  suspend "setup_frame"
QED

Resume abi_encode_normal_packaging_side[setup_frame]:
  `cs_extends allocated ready /\ allocated.cs_next_var <= ready.cs_next_var` by
    metis_tac[cs_extends_trans] >>
  `emit_op ALLOCA [Lit (n2w N)] st = (Var root,allocated)` by
    (qpat_assum `compile_alloc_buffer N st = _`
       (mp_then Any mp_tac abi_builtin_alloc_buffer_shape) >> simp[]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = st.cs_next_id /\ inst.inst_outputs = [root] /\
     not_local_ptr ce mid'.scopes root` by
    (mp_tac (Q.INST [`cut` |-> `st`, `en` |-> `allocated`, `n` |-> `n2w N`,
      `out` |-> `Var root`, `scopes` |-> `mid'.scopes`] extcall_direct_alloca_site) >>
     asm_simp_tac (srw_ss()) [] >>
     disch_then (qx_choose_then `inst` strip_assume_tac) >>
     qexists_tac `inst` >> asm_rewrite_tac[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func)` by
    (qpat_assum `emit_op ALLOCA _ st = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `root = STRING #"%" (toString st.cs_next_var)` by
       (qpat_assum `Var root = Var (STRING _ _)` (ACCEPT_TAC o SRULE [])) >>
     qpat_assum `compile_alloc_buffer N st = _`
       (mp_then Any mp_tac buffer_alloc_code) >> asm_rewrite_tac[] >>
     disch_then (qspec_then `func` (fn code =>
       qpat_assum `fn_has_code st allocated func` (ACCEPT_TAC o MP code)))) >>
  `p+32+write_len <= p+N /\ 32+k <= N` by
    (`k <= write_len` by (Cases_on `meth` >> simp[Abbr `write_len`, Abbr `k`]) >>
     decide_tac) >>
  `typed_copy_state_frame allocated p N u pre` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`p+32`,`write_len`] >> simp[]) >>
  `copy_static pre = copy_static u /\ LENGTH u.vs_memory <= LENGTH pre.vs_memory /\
    (!a n. a+n <= p \/ p+N <= a ==>
      mem_bytes_at a n pre.vs_memory = mem_bytes_at a n u.vs_memory)` by
    (qpat_assum `typed_copy_state_frame allocated p N u pre`
      (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `pre with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = u` (SUBST1_TAC o SYM) >>
     simp[copy_static_def]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' pre /\ storage_well_formed_on cx mid' (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid' Gpre tnpre pre` by suspend "setup_horizons" >>
  `FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,N) /\ p+N <= pre.vs_alloca_next /\
    t.vs_alloca_next <= pre.vs_alloca_next /\ alloca_history func pre` by metis_tac[] >>
  `wb_frame ce mid' mid' st t pre /\ ghost_kept_at lo ce mid' st G1 tn1 t Gpre tnpre`
    by suspend "setup_caller_frame" >>
  `pure_frame ce func mid' st t pre` by suspend "setup_pure_frame" >>
  `st.cs_next_id < ready.cs_next_id` by
    (drule emit_op_next_id >> fs[ci_mono_def] >> decide_tac) >>
  qabbrev_tac `prefix = abi_builtin_encode_prefix meth` >>
  `LENGTH prefix = k /\ prefix = abi_encode_method_id_bytes mid` by
    suspend "selector_source" >>
  `read_memory (p+32) k pre = prefix /\
   (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem)` by suspend "selector_memory" >>
  `env.type_defs = get_tenv cx /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv ce cx env es` mp_tac >>
     simp[NoAsms, expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `LENGTH args = LENGTH vs /\ LENGTH args = LENGTH svs` by
    (qpat_assum `LENGTH svs = LENGTH args` (fn th => REWRITE_TAC [SYM th]) >>
     qpat_assum `eval_exprs cx args _ = (INL vs,mid')`
       (mp_then Any mp_tac eval_exprs_length) >> simp[]) >>
  qabbrev_tac `declared = MAP expr_type args` >>
  qabbrev_tac `rows = ZIP (svs,tys)` >>
  `LENGTH declared = LENGTH args /\ LENGTH tys = LENGTH args /\
   LENGTH rows = LENGTH args` by
    (qpat_assum `LENGTH svs = LENGTH args` (fn th =>
       simp[NoAsms, Abbr `declared`, Abbr `tys`, Abbr `rows`, LENGTH_ZIP, th])) >>
  `arg_types_fit tys declared` by
    (simp_tac bool_ss [Abbr `declared`, Abbr `tys`] >>
     qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es`
       (ACCEPT_TAC o MATCH_MP abi_encode_body_arg_types_fit)) >>
  `well_typed_type_builtin_args (AbiEncode ensure mid) target declared /\
     type_builtin_result_ok (get_tenv cx) (AbiEncode ensure mid) ann target declared` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` (fn th =>
       simp[NoAsms, expr_body_pre_def, Once well_typed_expr_def, th, Abbr `declared`])) >>
  `target = TupleT declared` by
    (qpat_assum `well_typed_type_builtin_args (AbiEncode ensure mid) target declared`
       mp_tac >> simp[NoAsms, well_typed_type_builtin_args_def]) >>
  `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix ready pre Gpre tnpre` by
    (simp_tac bool_ss [abi_encode_saved_state_def] >>
     `p+(32+k) = p+32+k` by ACCEPT_TAC (Q.SPECL [`p`,`32`,`k`] ADD_ASSOC) >>
     `eval_operand (Var dp) pre = SOME (n2w (p+32+k))` by
       (qpat_assum `data_ptr = Var dp` (fn eq =>
          qpat_assum `eval_operand data_ptr pre = SOME _`
            (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
     `st.cs_next_var <= ready.cs_next_var` by
       (fs[ci_mono_def] >> decide_tac) >>
     `LENGTH prefix <= 32+k` by
       (qpat_assum `LENGTH prefix = k` SUBST1_TAC >>
        simp_tac (srw_ss() ++ ARITH_ss) []) >>
     asm_rewrite_tac[LESS_EQ_REFL, ADD_SUB] >>
     qpat_assum `tnpre.t_mem = _` (fn eq =>
       qpat_assum `!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem`
          (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==> stmt_state_rel H ctx func ce cx mid' t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post T DF lo d ctx
       func ce cx env [] args svs sa st es s0 G0 tn0 H _ _ _ _ _`
       (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE bool_ss
         [extcall_positional_post_def]))) >>
     first_assum ACCEPT_TAC) >>
  `?bytes limit q Gq tq.
    ann = BaseT (BytesT (Dynamic limit)) /\ LENGTH (prefix ++ bytes) <= limit /\
    LENGTH bytes <= maxlen /\
    evaluate_type_builtin cx (AbiEncode ensure mid) target declared vs =
      INL (BytesV (prefix ++ bytes)) /\
    abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
      st.cs_next_id p N root dp (32+k) prefix body_end q Gq tq /\
    eval_operand len q = SOME (n2w (LENGTH bytes)) /\ op_taint tq len = {} /\
    (!x. len = Var x ==> not_fresh_at body_end x) /\
    mem_bytes_at (p+32+k) (LENGTH bytes) q.vs_memory = bytes /\
    (!j. p+32+k <= j /\ j < p+32+k + LENGTH bytes ==> j NOTIN tq.t_mem) /\
    pure_frame ce func mid' st t q /\ Seg ready body_end pre q /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (pre,Gpre,tnpre) [] (OK q,Gq,tq))` by
    (Cases_on `single` >- suspend "standalone_payload" >> suspend "wrapped_payload") >>
  suspend "finish_payload"
QED

Resume abi_encode_normal_packaging_side[setup_horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post T DF lo d ctx
    func ce cx env [] args svs sa st es s0 G0 tn0 H _ _ _ _ _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp_tac bool_ss [extcall_positional_post_def] >> strip_tac >>
  `stmt_state_rel H ctx func ce cx mid' u` by metis_tac[] >>
  `ghost_inv_at (DF H) lo d ce cx mid' Gu tu u` by
    (irule (horizonTypeLib.at_horizon_named "H" alloc_buffer_ghost_inv_at) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G1`,`H`,`ctx`,`p+N`,`func`,`t`,`st`,`tn1`] >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule literal_copy_window_stmt_state_rel >>
      qexistsl_tac [`st.cs_next_id`,`p`,`N`,`root`,`st`,`allocated`,`u`] >>
      asm_rewrite_tac[] >> rpt conj_tac
      >- metis_tac[not_fresh_at_mono, ci_mono_def]
      >> qpat_assum `typed_copy_state_frame allocated p N u pre`
           (ACCEPT_TAC o cj 2 o MATCH_MP (iffLR typed_copy_state_frame_def))) >>
  qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es Gpre tnpre pre` irule >>
  asm_rewrite_tac[]
QED

Resume abi_encode_normal_packaging_side[setup_caller_frame]:
  `u.vs_memory = t.vs_memory` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
         vs_inst_idx := _|> = t` (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x t` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at allocated x` by
       (irule not_fresh_at_mono >> qexists_tac `st` >>
        qpat_assum `ci_mono st allocated`
          (strip_assume_tac o PURE_REWRITE_RULE [ci_mono_def]) >>
        asm_rewrite_tac[]) >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t /\ _`
       (qspec_then `x` (drule_then (SUBST1_TAC o SYM o cj 1))) >>
     qpat_assum `typed_copy_state_frame allocated p N u pre`
       (fn th => MATCH_MP (iffLR typed_copy_state_frame_def) th |> cj 2 |>
          Q.SPEC `x` |> drule_then ACCEPT_TAC)) >>
  `!name b sz. local_region ce mid'.scopes t name b sz ==>
     regions_disjoint p N b sz /\ b+sz <= t.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!name b len. local_region ce mid'.scopes u name b len ==>
            loweringStateRelDefs$regions_disjoint p N b len` irule >>
         qexists_tac `name` >> irule local_region_frame_fwd >>
         qexistsl_tac [`t`,`st`,`mid'.scopes`] >> simp[]) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx mid' t`
       (mp_then Any irule body_local_region_frontier) >> qexists_tac `name` >> asm_rewrite_tac[]) >>
  `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < st.cs_next_id ==>
    b+sz <= t.vs_alloca_next` by
    (`alloca_inv t` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  conj_tac
  >- (match_mp_tac (Q.INST [`cenv` |-> `ce`, `es` |-> `mid'`, `es'` |-> `mid'`,
        `sa` |-> `st`, `sm` |-> `st`, `scopes` |-> `mid'.scopes`,
        `s` |-> `t`, `s0` |-> `t`, `t` |-> `pre`] wb_frame_allocating_tail) >>
      asm_rewrite_tac[LESS_EQ_REFL] >> rpt conj_tac
      >- simp_tac (srw_ss()) [wb_frame_refl]
      >- gvs[]
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `u.vs_memory = t.vs_memory` (SUBST1_TAC o SYM) >>
          qpat_assum `!a n. a+n <= p \/ p+N <= a ==> _ = mem_bytes_at a n u.vs_memory` irule >>
          qpat_assum `!aid b n. aid < st.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==> _`
            (qspecl_then [`aid`,`b`,`sz`] mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >>
          simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM])
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `u.vs_memory = t.vs_memory` (SUBST1_TAC o SYM) >>
          qpat_assum `!a n. a+n <= p \/ p+N <= a ==> _ = mem_bytes_at a n u.vs_memory` irule >>
          qpat_assum `!name b n. local_region ce mid'.scopes t name b n ==> _`
            (qspecl_then [`n`,`b`,`sz`] (drule_then mp_tac)) >>
          simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM])) >>
  `ghost_kept_at lo ce mid' st G1 tn1 t Gu tu` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G1`,`p+N`,`t`,`tn1`] >>
     asm_simp_tac bool_ss [ghost_kept_at_refl] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> first_assum drule >> simp[]) >>
  qpat_assum `!ce es origin G0 tn0 s0. _ ==> ghost_kept_at lo ce es origin G0 tn0 s0 Gpre tnpre`
    irule >> simp[] >> metis_tac[ci_mono_def, not_fresh_at_mono]
QED

Resume abi_encode_normal_packaging_side[setup_pure_frame]:
  `u.vs_memory = t.vs_memory` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (SUBST1_TAC o SYM) >> simp[]) >>
  match_mp_tac (Q.SPECL [`ce`,`func`,`mid'`,`st`,`t`,`pre`,`st.cs_next_id`,
    `[Lit (n2w N)]`,`[root]`,`p`,`N`] pure_frame_fresh_alloca) >>
  asm_rewrite_tac[LESS_EQ_REFL] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `local_region ce mid'.scopes u n lb lsz` by
        (irule local_region_frame_fwd >> qexistsl_tac [`t`,`st`,`mid'.scopes`] >> simp[]) >>
      qpat_assum `u.vs_memory = t.vs_memory` (SUBST1_TAC o SYM) >>
      qpat_assum `!a n. a+n <= p \/ p+N <= a ==> _ = mem_bytes_at a n u.vs_memory` irule >>
      qpat_assum `!name b n. local_region ce mid'.scopes u name b n ==>
          loweringStateRelDefs$regions_disjoint p N b n`
        (qspecl_then [`n`,`lb`,`lsz`] (drule_then mp_tac)) >>
      simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  qpat_assum `u.vs_memory = t.vs_memory` (SUBST1_TAC o SYM) >>
  rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC
QED

Resume abi_encode_normal_packaging_side[selector_source]:
  conj_tac
  >- (Cases_on `meth` >> simp[Abbr `prefix`,Abbr `k`,abi_builtin_encode_prefix_def,
        abi_builtin_encode_method_bytes_length]) >>
  qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es`
    (mp_tac o cj 2 o REWRITE_RULE [expr_body_pre_def]) >>
  simp_tac bool_ss [Once well_typed_expr_def] >> strip_tac >>
  drule abi_builtin_encode_checked_prefix >>
  simp_tac bool_ss [Abbr `prefix`, Abbr `meth`]
QED

Resume abi_encode_normal_packaging_side[selector_memory]:
  namedCases_on `meth` ["", "selector"]
  >- simp[NoAsms, Abbr `k`, Abbr `prefix`, abi_builtin_encode_prefix_def,
          read_memory_eq_mem_bytes_at, mem_bytes_at_def, ADD_CLAUSES] >>
  conj_tac
  >- (simp[NoAsms, Abbr `k`, Abbr `prefix`, abi_builtin_encode_prefix_def,
          read_memory_eq_mem_bytes_at] >>
      irule abi_builtin_encode_method_window >> rewrite_tac[GSYM mem_word_at_eq_mload] >>
      qpat_assum `(case SOME selector of NONE => T | SOME w => !mem. _ ==> _)`
        (irule o SIMP_RULE bool_ss [optionTheory.option_case_def]) >>
      simp[mem_agree_outside_def]) >>
  qpat_assum `tnpre.t_mem = _` (fn th => PURE_REWRITE_TAC [th]) >>
  simp[NoAsms, Abbr `k`, Abbr `write_len`, IN_DIFF] >> decide_tac
QED

Resume abi_encode_normal_packaging_side[wrapped_payload]:
  `compile_abi_encode_values_to_buf ce (Var dp) rows ready = (len,body_end)` by
    (simp[NoAsms, Abbr `rows`] >>
     qpat_assum `data_ptr = Var dp` (fn eq =>
       qpat_assum `compile_abi_encode_payload ce F svs tys data_ptr ready = _`
         (ACCEPT_TAC o SIMP_RULE bool_ss [compile_abi_encode_payload_def, eq]))) >>
  `?avs ats bytes.
    vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) tys /\
    bytes = enc (Tuple ats) (ListV avs) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats` by suspend "wrapped_layout" >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  `LENGTH ats = LENGTH args /\ LENGTH avs = LENGTH args` by
    (qpat_assum `LIST_REL abi_encoder_layout_valid ats avs`
       (assume_tac o MATCH_MP LIST_REL_LENGTH) >>
     `LENGTH ats = LENGTH tys` by
       (qpat_assum `ats = vyper_to_abi_types _ tys` SUBST1_TAC >>
        simp[NoAsms, abiDecoderMembersTheory.vyper_to_abi_types_MAP]) >>
     metis_tac[]) >>
  `LENGTH bytes <= maxlen /\ 32+k+LENGTH bytes <= N` by
    (conj_asm1_tac
     >- (simp[NoAsms, Abbr `maxlen`] >> first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `N`] >> irule abi_encode_payload_capacity >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `dtvs = MAP (THE o evaluate_type (get_tenv cx)) declared` >>
  qabbrev_tac `ptvs = MAP (THE o evaluate_type (get_tenv cx)) tys` >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) declared dtvs /\
   LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys ptvs /\
   values_have_types dtvs vs` by
    (drule_all abi_encode_body_args_indexed_types >> strip_tac >>
     drule_all abi_encode_body_args_indexed_physical_types >> strip_tac >>
     simp[NoAsms, LIST_REL_EL_EQN, values_have_types_LIST_REL,
       Abbr `dtvs`, Abbr `ptvs`, Abbr `declared`, Abbr `tys`, EL_MAP] >>
     rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!k. k < LENGTH args ==> ?tv.
       evaluate_type _ (expr_type _) = SOME tv /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!k. k < LENGTH args ==> ?tv.
       evaluate_type _ (lowered_value_type _ _) = SOME tv /\ _`
       (drule_then strip_assume_tac) >>
     simp[]) >>
  `vyper_to_abi_types (get_tenv cx) declared = ats /\
   vyper_to_abi_list (get_tenv cx) declared vs = SOME avs` by
    metis_tac[cj 2 abi_args_fits_abi_type, cj 2 abi_args_fits_conversion] >>
  `~(~ensure /\ LENGTH declared <= 1)` by
    (qpat_assum `Abbrev (F <=> LENGTH args = 1 /\ ~ensure)`
       (assume_tac o SIMP_RULE bool_ss [markerTheory.Abbrev_def]) >>
     strip_tac >> `LENGTH args = 1` by decide_tac >> simp[] >> metis_tac[]) >>
  `evaluate_type_builtin cx (AbiEncode ensure mid) target declared vs =
    INL (BytesV (prefix ++ bytes))` by
    (qpat_assum `target = TupleT declared` SUBST1_TAC >>
     qpat_assum `prefix = abi_encode_method_id_bytes mid`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `bytes = enc _ _` SUBST1_TAC >>
     qpat_assum `vyper_to_abi_types (get_tenv cx) declared = ats`
       (SUBST1_TAC o SYM) >>
     match_mp_tac (PURE_REWRITE_RULE [vyper_to_abi_type_def]
       abi_builtin_encode_source_tuple) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `vyper_to_abi_list _ declared vs = SOME avs` (fn th =>
       simp[NoAsms, Once vyper_to_abi_def, th])) >>
  `?limit. ann = BaseT (BytesT (Dynamic limit)) /\
     LENGTH (prefix ++ bytes) <= limit` by
    (`(case declared of [elem_ty] => (if ensure then TupleT declared else elem_ty)
          | _ => TupleT declared) = TupleT declared` by
       (namedCases_on `declared` ["", "elm rest"] >- simp[] >>
        namedCases_on `rest` ["", "elm2 rest2"] >- fs[] >> simp[]) >>
     qpat_assum `type_builtin_result_ok _ _ _ _ _` mp_tac >>
     qpat_assum `target = TupleT declared` SUBST1_TAC >>
     simp[NoAsms, type_builtin_result_ok_def, abi_encode_size_ok_def] >>
     qpat_assum `(case declared of _ => _) = TupleT declared`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     strip_tac >> qexists_tac `n` >> simp[NoAsms, LENGTH_APPEND] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `LENGTH bytes <= vyper_abi_size_bound (get_tenv cx) (TupleT declared)` by
       (qpat_assum `bytes = enc _ _` SUBST1_TAC >>
        qpat_assum `vyper_to_abi_types (get_tenv cx) declared = ats`
          (SUBST1_TAC o SYM) >>
        irule (cj 2 vyper_to_abi_enc_le_size_bound) >>
        qexistsl_tac [`dtvs`,`vs`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `abi_encode_method_id_size mid = LENGTH prefix` by
       (simp[NoAsms, abi_encode_method_id_size_def] >> AP_TERM_TAC >>
        sym_tac >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  qpat_assum `~F ==> !dp. data_ptr = Var dp ==> _`
    (mp_tac o SIMP_RULE bool_ss []) >>
  disch_then (qspec_then `dp` (drule_then strip_assume_tac)) >>
  qpat_assum `Abbrev (rows = _)` (fn ab =>
    qhdtm_assum `abi_packaging_fold_law`
      (mp_tac o PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab),
        abi_packaging_fold_law_def])) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pat `LIST_REL abi_encoder_layout_valid ats avs`)) >>
  disch_then (qspecl_then [`bytes`,`hl`,`inst`] mp_tac) >>
  impl_tac >- suspend "wrapped_rows" >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`]
    (strip_assume_tac o PURE_REWRITE_RULE [ADD_ASSOC])) >>
  qexistsl_tac [`bytes`,`limit`,`q`,`Gq`,`tq`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`H` |-> `H0`,`ee` |-> `mid'`,`se` |-> `st`,
    `a` |-> `st`,`u` |-> `t`,`v` |-> `pre`,`z` |-> `q`]
    abi_encode_saved_frames_trans) >>
  asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Resume abi_encode_normal_packaging_side[wrapped_rows]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp_tac bool_ss [Abbr `hl`] >> NO_TAC) >>
  TRY (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`ci`,`cursor_var`] >> strip_tac >>
  qx_genl_tac [`i`,`a`,`c`,`vstate`,`Gv`,`tvstate`,`cursor`,`slot`] >>
  strip_tac >>
  `i < LENGTH args /\ i < LENGTH svs /\ i < LENGTH tys /\
   i < LENGTH vs /\ i < LENGTH ats /\ i < LENGTH avs` by decide_tac >>
  qabbrev_tac `e = EL i args` >>
  qabbrev_tac `sv = EL i svs` >>
  qabbrev_tac `v = EL i vs` >>
  qabbrev_tac `at = EL i ats` >>
  qabbrev_tac `av = EL i avs` >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `EL i tys = lowered_value_type ce e` by
    (qpat_assum `i < LENGTH args` (fn lt =>
       simp[NoAsms, Abbr `tys`, Abbr `e`, EL_MAP, lt])) >>
  `EL i rows = (sv,lowered_value_type ce e) /\
    at = vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    (`LENGTH svs = LENGTH tys` by decide_tac >>
     conj_tac
     >- (qpat_assum `LENGTH svs = LENGTH tys` (fn eq =>
           qpat_assum `i < LENGTH svs` (fn lt =>
             simp[NoAsms, Abbr `rows`, Abbr `sv`, EL_ZIP, eq, lt])) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `ats = vyper_to_abi_types _ tys` (fn eq =>
       qpat_assum `i < LENGTH tys` (fn lt =>
         simp[NoAsms, Abbr `at`, eq,
           abiDecoderMembersTheory.vyper_to_abi_types_MAP, EL_MAP, lt])) >>
     AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
  `vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av` by
    (qpat_assum `vyper_to_abi_list _ tys vs = SOME avs`
       (qspec_then `i` (drule_then mp_tac) o cj 3 o
        MATCH_MP vyperABIRoundtripTheory.vyper_to_abi_list_EL) >>
     qpat_assum `EL i tys = _` (fn eq =>
       simp[NoAsms, Abbr `av`, Abbr `v`, eq])) >>
  `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
   hl <= off /\ off <= LENGTH bytes /\ h + abi_member_head_size at <= hl /\
   (is_dynamic at ==> off + LENGTH (enc at av) <= LENGTH bytes) /\
   (~is_dynamic at ==> LENGTH (enc at av) = abi_member_head_size at) /\
   abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp_tac bool_ss [Abbr `at`, Abbr `av`, Abbr `off`, Abbr `hl`] >> NO_TAC) >>
     TRY (qpat_assum `bytes = enc _ _` (fn th => simp[NoAsms, th]) >> NO_TAC) >>
     qexistsl_tac [`rows`,`ce.ce_struct_fields`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms, Abbr `h`]) >>
  `off <= N-(32+k) /\
   (is_dynamic at ==> off + LENGTH (enc at av) <= N-(32+k))` by
    (conj_tac >- decide_tac >> strip_tac >>
     qpat_assum `is_dynamic at ==> off + LENGTH (enc at av) <= LENGTH bytes`
       (drule_then assume_tac) >> decide_tac) >>
  `compile_abi_encode_value_rows ce (Var dp) cursor h [(sv,lowered_value_type ce e)] a =
    ((),c)` by
    (qpat_assum `EL i rows = _` (fn th => rewrite_tac [GSYM th]) >>
     simp_tac bool_ss [Abbr `h`] >> first_assum ACCEPT_TAC) >>
  `(!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' t /\ vv_storage_live H cx sv mid' t)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!H. valid_horizon cx st0 H _ ==> stmt_state_rel H ctx func ce cx mid' t`
           (qspec_then `H` (drule_then ACCEPT_TAC))) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post T DF lo d ctx
       func ce cx env [] args svs sa st es s0 G0 tn0 H _ _ _ _ _`
       (qspec_then `H` (drule_then
          (qx_choose_then `vsH` (mp_tac o cj 3) o
           SIMP_RULE bool_ss [extcall_positional_post_def]))) >>
     `LENGTH args = LENGTH svs` by decide_tac >>
     simp[NoAsms, LIST_REL_EL_EQN, LENGTH_ZIP] >>
     disch_then (qspec_then `i` mp_tac o cj 2) >>
     qpat_assum `LENGTH args = LENGTH svs` (fn eq =>
       qpat_assum `i < LENGTH args` (fn lt =>
         simp[NoAsms, EL_ZIP, Abbr `sv`, eq, lt]))) >>
  `?si sm ss vv raw copy.
      compile_expr ce (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm =
        (sv,ss) /\
      local_ptrs_reserved ce si /\ sm.cs_next_var <= st.cs_next_var /\
      sm.cs_next_id <= st.cs_next_id /\ ss.cs_next_var <= st.cs_next_var /\
      ss.cs_next_id <= st.cs_next_id /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?pp. sv = LocatedValue (lowered_value_type ce e) pp /\
          ~is_word_type (lowered_value_type ce e) /\ pp.ptr_location = LocMemory) \/
       (?pp. sv = LocatedValue (lowered_value_type ce e) pp /\
          ~is_word_type (lowered_value_type ce e) /\ pp.ptr_location <> LocMemory /\
          lowered_value_type ce e = expr_type e /\ sv = vv)) /\
      read_result cx raw mid' = (INL v,mid') /\
      vv_holds ce cx (lowered_value_type ce e) raw sv mid' t /\
      vv_at ce cx (lowered_value_type ce e) si ss mid' raw sv t /\
      ptr_vv_ok cx (lowered_value_type ce e) raw sv mid' G1 tn1 t /\
      vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) mid' raw sv t /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type ce e)
        | LocatedValue tag pp => pp.ptr_location = LocMemory) ==>
         ptr_buf_ok ce e (vv_operand sv) G1 t)` suffices_by
    (disch_then (qx_choosel_then [`si`,`sm`,`ss`,`row_vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS)) >>
    suspend "wrapped_row_execute") >>
  suspend "saved_row"
QED

Resume abi_encode_normal_packaging_side[wrapped_row_execute]:
  `expr_body_pre ce cx env e es` by
    metis_tac[EL_MEM, Abbr `e`, abi_encode_body_arg_pre] >>
  `!l. vv_operand sv <> Label l` by metis_tac[abi_encode_snapshot_not_label] >>
  `~is_word_type (lowered_value_type ce e) ==> ~is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  `?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ value_has_type tv v` by suspend "physical_row" >>
  `st.cs_next_id < ready.cs_next_id` by first_assum ACCEPT_TAC >>
  qhdtm_assum `abi_packaging_row_law`
    (fn th => mp_tac (Q.INST [`ee` |-> `mid'`,`pbase` |-> `p`,
       `s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`,`prefix` |-> `prefix`,
       `saved` |-> `sv`,`ty` |-> `lowered_value_type ce e`,`su` |-> `a`,
       `u` |-> `vstate`,`Gu` |-> `Gv`,`tu` |-> `tvstate`,`en` |-> `c`,
       `cursor_inst` |-> `ci`,`vv` |-> `row_vv`]
       (SPEC_ALL (PURE_REWRITE_RULE [abi_packaging_row_law_def] th)))) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
    TRY (rename1 `LENGTH ats = LENGTH avs` >> decide_tac) >>
    simp_tac bool_ss [Abbr `at`, Abbr `av`, Abbr `off`] >>
    first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [Abbr `at`, Abbr `av`, Abbr `off`])) >>
  disch_then ACCEPT_TAC
QED

Resume abi_encode_normal_packaging_side[wrapped_layout]:
  `LENGTH tys = LENGTH declared /\ LENGTH tys = LENGTH vs /\
   LENGTH tys = LENGTH svs /\
   sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!i. i < LENGTH tys ==>
     ?tv ftv. evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
       evaluate_type (get_tenv cx) (EL i declared) = SOME ftv /\
       arg_type_fits (EL i tys) (EL i declared) /\
       value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs))`
  suffices_by
    (disch_then (mp_tac o MATCH_MP extcall_direct_args_layout) >>
     simp_tac bool_ss [Abbr `rows`] >>
     disch_then (qx_choose_then `avs` strip_assume_tac) >>
     qexists_tac `avs` >> asm_rewrite_tac[]) >>
  rpt conj_tac >> TRY decide_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  `i < LENGTH args` by decide_tac >>
  `arg_type_fits (EL i tys) (EL i declared)` by
    (qpat_assum `arg_types_fit tys declared`
       (strip_assume_tac o REWRITE_RULE [arg_types_fit_LIST_REL, LIST_REL_EL_EQN]) >>
     first_x_assum (irule o SPEC_ALL) >> first_assum ACCEPT_TAC) >>
  drule_all abi_encode_body_args_indexed_types >>
  disch_then (qspec_then `i` (drule_then (qx_choose_then `ftv` strip_assume_tac)) o CONJUNCT2) >>
  drule_all abi_encode_body_args_indexed_physical_types >>
  disch_then (qspec_then `i` (drule_then (qx_choose_then `tv` strip_assume_tac)) o CONJUNCT2) >>
  qexistsl_tac [`tv`,`ftv`] >>
  conj_tac >- (simp_tac bool_ss [Abbr `tys`] >>
     qpat_assum `i < LENGTH args` (fn th => simp_tac bool_ss [EL_MAP, th]) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- (simp_tac bool_ss [Abbr `declared`] >>
     qpat_assum `i < LENGTH args` (fn th => simp_tac bool_ss [EL_MAP, th]) >>
     first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_normal_packaging_side[saved_row]:
  `LENGTH args = LENGTH svs` by decide_tac >>
  qpat_assum `LIST_REL _ (ZIP (args,svs)) vs` mp_tac >>
  qpat_assum `LENGTH args = LENGTH svs` (fn eq =>
    simp_tac bool_ss [LIST_REL_EL_EQN, LENGTH_ZIP, GSYM eq, arithmeticTheory.MIN_IDEM]) >>
  disch_then (qspec_then `i` mp_tac o CONJUNCT2) >>
  qpat_assum `LENGTH args = LENGTH svs` (fn eq =>
    qpat_assum `i < LENGTH args` (fn lt =>
      simp_tac (srw_ss()) [EL_ZIP, lt, GSYM eq, LET_THM])) >>
  qpat_assum `Abbrev (e = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (sv = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (v = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`row_vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`si`,`sm`,`ss`,`row_vv`,`raw`,`copy`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `sv` >> simp[NoAsms, vv_operand_def] >>
  strip_tac >> first_x_assum irule >>
  simp[NoAsms, SF CONJ_ss] >> TRY (first_assum ACCEPT_TAC)
QED

Resume abi_encode_normal_packaging_side[physical_row]:
  Cases_on `is_word_type (expr_type e)`
  >- (drule_all abi_encode_body_args_indexed_physical_types >>
      disch_then (qspec_then `i` (drule_then (qx_choose_then `tv` strip_assume_tac)) o CONJUNCT2) >>
      `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ value_has_type tv v` by
        (simp_tac bool_ss [Abbr `e`, Abbr `v`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
        (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >> metis_tac[]) >>
      `is_word_type (lowered_value_type ce e)` by metis_tac[] >>
      qexists_tac `tv` >> asm_rewrite_tac[] >>
      `type_memory_bytes ce (lowered_value_type ce e) = 32` by
        (irule (cj 3 word_type_dec_sizes) >> first_assum ACCEPT_TAC) >>
      qpat_assum `type_memory_bytes ce _ = type_memory_size tv`
        (fn th => once_rewrite_tac [GSYM th]) >>
      qpat_assum `type_memory_bytes ce _ = 32` (fn th => rewrite_tac [th]) >> EVAL_TAC) >>
  `~is_word_type (expr_type (EL i args))` by
    (qpat_assum `Abbrev (e = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all abi_encode_body_arg_physical_copy_bound >>
  disch_then (qx_choose_then `tv` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists_tac `tv` >> simp_tac bool_ss [Abbr `e`, Abbr `v`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_normal_packaging_side[standalone_payload]:
  `LENGTH args = 1 /\ ~ensure` by
    (qpat_assum `Abbrev (T = (LENGTH args = 1 /\ ~ensure))` mp_tac >>
     simp_tac bool_ss [markerTheory.Abbrev_def]) >>
  `?e. args = [e]` by (rewrite_tac [GSYM LENGTH_EQ_1] >> first_assum ACCEPT_TAC) >>
  `?sv v. svs = [sv] /\ vs = [v]` by
    (`LENGTH svs = 1` by
       (qpat_assum `LENGTH svs = LENGTH args` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     `LENGTH vs = 1` by
       (drule LIST_REL_LENGTH >>
        asm_simp_tac (srw_ss()) [LENGTH_ZIP]) >>
     qpat_assum `LENGTH svs = 1` (strip_assume_tac o REWRITE_RULE [LENGTH_EQ_1]) >>
     qpat_assum `LENGTH vs = 1` (strip_assume_tac o REWRITE_RULE [LENGTH_EQ_1]) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qabbrev_tac `ty = lowered_value_type ce e` >>
  `expr_body_pre ce cx env e es` by metis_tac[abi_encode_body_arg_pre, MEM] >>
  `~is_word_type ty /\ ~is_word_type (expr_type e)` by
    (`~is_word_type (lowered_value_type ce e)` by
       (qpat_assum `T ==> ~is_word_type _` mp_tac >> simp[]) >>
     qpat_assum `expr_body_pre ce cx env e es`
       (mp_tac o MATCH_MP arg_type_fits_word_type o MATCH_MP expr_body_pre_lowered_fits) >>
     simp[Abbr `ty`]) >>
  `maxlen = abi_size_bound ce.ce_struct_fields ty` by simp[Abbr `maxlen`, Abbr `ty`] >>
  `declared = [expr_type e] /\ tys = [ty] /\ target = TupleT [expr_type e]` by
    simp[Abbr `declared`, Abbr `tys`, Abbr `ty`] >>
  qpat_assum `LIST_REL _ (ZIP (args,svs)) vs` (fn th =>
    qpat_assum `args = [e]` (fn ae =>
    qpat_assum `svs = [sv]` (fn se =>
    qpat_assum `vs = [v]` (fn ve =>
      mp_tac (SIMP_RULE (srw_ss()) [ae,se,ve,ZIP,LIST_REL_CONS1] th))))) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`evv`,`raw`,`copy`]
       (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' t /\ vv_storage_live H cx sv mid' t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post T DF lo d ctx
       func ce cx env [] args svs sa st es s0 G0 tn0 H _ _ _ _ _`
       (qspec_then `H` (drule_then mp_tac)) >>
     qpat_assum `res = INL vs` (fn re =>
     qpat_assum `args = [e]` (fn ae =>
     qpat_assum `svs = [sv]` (fn se =>
     qpat_assum `vs = [v]` (fn ve =>
       simp_tac (srw_ss()) [extcall_positional_post_def,re,ae,se,ve,ZIP,LIST_REL_CONS1])))) >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    (`0 < LENGTH args /\ ~is_word_type (expr_type (EL 0 args))` by simp[] >>
     drule_all (Q.INST [`k` |-> `0`] abi_encode_body_arg_physical_copy_bound) >>
     qpat_assum `args = [e]` (fn ae =>
     qpat_assum `vs = [v]` (fn ve => simp_tac (srw_ss()) [ae,ve,Abbr `ty`]))) >>
  `?av. vyper_to_abi (get_tenv cx) ty v = SOME av` by metis_tac[cj 1 vyper_to_abi_total] >>
  `vyper_to_abi_type (get_tenv cx) ty = vyper_to_abi_type (get_tenv cx) (expr_type e) /\
    vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    (mp_tac (Q.INST [`es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid'.gas_obs`,
                     `es'` |-> `mid'`] abi_encode_body_args_physical_conversion) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `0` mp_tac) >>
     simp[Abbr `ty`] >> metis_tac[]) >>
  qabbrev_tac `bytes = enc (vyper_to_abi_type (get_tenv cx) ty) av` >>
  `?limit. ann = BaseT (BytesT (Dynamic limit)) /\ LENGTH (prefix ++ bytes) <= limit` by
    (`expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) target [e]) es` by
       (qpat_assum `args = [e]` (fn ae =>
        qpat_assum `~ensure` (fn ne =>
        qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es`
          (ACCEPT_TAC o REWRITE_RULE [ae,ne])))) >>
     mp_tac (Q.INST [`ty` |-> `target`,`tv` |-> `tv`,`av` |-> `av`]
       abi_encode_nonword_result_bound) >>
     `LENGTH (abi_encode_method_id_bytes mid) = k` by
       (qpat_assum `prefix = abi_encode_method_id_bytes mid` (once_rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC) >>
     simp[Abbr `ty`, Abbr `bytes`, expr_type_def]) >>
  `LENGTH bytes <= maxlen` by
    (mp_tac (Q.INST [`tv` |-> `tv`,`av` |-> `av`] abi_encode_nonword_length_bound) >>
     simp[Abbr `ty`, Abbr `bytes`]) >>
  `evaluate_type_builtin cx (AbiEncode ensure mid) target declared vs =
    INL (BytesV (prefix ++ bytes))` by
    (simp[Abbr `bytes`] >> irule abi_builtin_encode_source_single >> first_assum ACCEPT_TAC) >>
  Cases_on `unwrap_value ce sv ready` >>
  rename1 `unwrap_value ce sv ready = (src,unwrap_end)` >>
  `compile_abi_encode_to_buf (Var dp) src
    (type_to_abi_enc_info ce.ce_struct_fields ce ty) unwrap_end = (len,body_end)` by
    (qpat_assum `data_ptr = Var dp` (fn de =>
     qpat_assum `unwrap_value ce sv ready = (src,unwrap_end)` (fn ue =>
     qpat_assum `svs = [sv]` (fn se =>
     qpat_assum `tys = [ty]` (fn te =>
     qpat_assum `compile_abi_encode_payload ce T svs tys data_ptr ready = _`
       (mp_tac o SIMP_RULE (srw_ss()) [compile_abi_encode_payload_def, comp_bind_def,de,ue,se,te]))))) >>
     simp[]) >>
  `ci_mono ready unwrap_end /\ ci_mono unwrap_end body_end /\ ci_mono st body_end` by
    (`ci_mono ready unwrap_end` by
       (qpat_assum `unwrap_value ce sv ready = (src,unwrap_end)` (fn eq =>
          ACCEPT_TAC (REWRITE_RULE [eq, SND]
            (Q.SPECL [`ce`, `sv`, `ready`] ci_mono_unwrap_value)))) >>
     `ci_mono unwrap_end body_end` by
       (qpat_assum `compile_abi_encode_to_buf (Var dp) src _ unwrap_end = (len,body_end)`
          (fn eq => ACCEPT_TAC (REWRITE_RULE [eq, SND]
            (Q.SPECL [`Var dp`, `src`, `type_to_abi_enc_info ce.ce_struct_fields ce ty`,
                      `unwrap_end`] (cj 2 ci_mono_compile_abi_encode))))) >>
     asm_rewrite_tac[] >>
     irule ci_mono_trans >> qexists_tac `unwrap_end` >> asm_rewrite_tac[] >>
     irule ci_mono_trans >> qexists_tac `ready` >> asm_rewrite_tac[] >>
     irule ci_mono_trans >> qexists_tac `allocated` >> asm_rewrite_tac[] >>
     irule ci_mono_trans >> qexists_tac `method_st` >> asm_rewrite_tac[]) >>
  `fn_has_code ready unwrap_end func /\ fn_has_code unwrap_end body_end func` by
    (match_mp_tac (Q.SPECL [`ready`, `unwrap_end`, `body_end`, `func`] fn_has_code_split) >>
     asm_rewrite_tac[] >> conj_tac
     >- qpat_assum `ci_mono ready unwrap_end`
          (ACCEPT_TAC o cj 1 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono unwrap_end body_end`
       (ACCEPT_TAC o cj 1 o REWRITE_RULE [ci_mono_def])) >>
  `!l. vv_operand sv <> Label l` by
    (match_mp_tac (Q.INST [`si` |-> `si`, `sm` |-> `sm`,
       `ss` |-> `ss`, `vv` |-> `evv`, `copy` |-> `copy`]
       abi_encode_snapshot_not_label) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `T ==> !src unwrap_end. unwrap_value ce (HD svs) ready = _ ==> _`
    (qspecl_then [`src`,`unwrap_end`] mp_tac o REWRITE_RULE [IMP_CLAUSES]) >>
  impl_tac >- asm_rewrite_tac[HD] >>
  qpat_assum `args = [e]` (fn args_eq =>
    qpat_assum `svs = [sv]` (fn svs_eq =>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS o
        SIMP_RULE bool_ss [args_eq,svs_eq,HD]))) >>
  qhdtm_assum `abi_packaging_restore_law`
    (fn th => mp_tac (Q.INST [`ee` |-> `mid'`,`s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`,
       `u` |-> `pre`,`Gu` |-> `Gpre`,`tu` |-> `tnpre`,`vv` |-> `evv`]
       (SPEC_ALL (PURE_REWRITE_RULE [abi_packaging_restore_law_def] th)))) >>
  impl_tac >- suspend "standalone_restore_premises" >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  `!name b n. local_region ce mid'.scopes pre name b n ==> p+N <= b \/ b+n <= p` by
    suspend "standalone_separation" >>
  `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix unwrap_end z Gz tz` by
    (irule abi_encode_saved_state_unwrap >>
     rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC,
       qexists_tac `H0` >> first_assum ACCEPT_TAC,
       rpt strip_tac >> first_x_assum drule >> simp[]]) >>
     qexistsl_tac [`Gpre`,`ready`,`tnpre`,`pre`] >> asm_rewrite_tac[]) >>
  Q.SUBGOAL_THEN `?first last. expr_val_at ce cx ty first last mid' v src z /\
    last.cs_next_id <= unwrap_end.cs_next_id /\
    (st.cs_next_id < first.cs_next_id \/ last.cs_next_id <= st.cs_next_id)`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS))
  >- suspend "source_cut" >>
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix unwrap_end z Gz tz`
    (mp_then Any mp_tac abi_encode_saved_state_resources) >>
  (impl_tac >- (qexists_tac `H0` >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix unwrap_end z Gz tz`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `stmt_state_rel H0 ctx func ce cx mid' z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func ce cx mid' z /\ _`
       (qspec_then `H0` (drule_then (ACCEPT_TAC o cj 1)))) >>
  `p+N <= z.vs_alloca_next /\ 32+k+LENGTH bytes <= N` by
    (conj_tac
     >- (irule alloca_site_registered_below >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `st.cs_next_id` >> first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `N`] >> irule abi_encode_payload_capacity >>
     first_assum ACCEPT_TAC) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = st.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce mid'.scopes root` by
    (qexists_tac `inst` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`H` |-> `H0`,`s` |-> `z`,`G` |-> `Gz`,`tn` |-> `tz`,
    `ee` |-> `mid'`,`sa` |-> `first`,`sb` |-> `last`,`x` |-> `root`,`b` |-> `p`,
    `n` |-> `N`,`d` |-> `p+32+k`,`len` |-> `LENGTH (bytes:word8 list)`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_memory_source)) >>
  (impl_tac >- suspend "standalone_source_premises") >>
  disch_then (qx_choose_then `src_addr` strip_assume_tac) >>
  `eval_operand src z = SOME (n2w (w2n src_addr))` by simp[] >>
  mp_tac (Q.INST [`H` |-> `H0`,`s` |-> `z`,`st` |-> `unwrap_end`,`en` |-> `body_end`,
    `ee` |-> `mid'`,`dst` |-> `Var dp`,`out` |-> `len`,
    `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce ty`,
    `sa` |-> `first`,`sb` |-> `last`,
    `parent` |-> `st.cs_next_id`,`b` |-> `p`,`sz` |-> `N`,
    `d` |-> `p+32+k`,`n` |-> `LENGTH (bytes:word8 list)`,`q` |-> `w2n (src_addr:bytes32)`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_scratch_separation)) >>
  (impl_tac >- suspend "standalone_scratch") >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?at rv. enc at rv = bytes /\
    !mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        at rv (w2n src_addr) (val_footprint tv v) mem` by suspend "standalone_open_input" >>
  `lowered_value_type ce e = ty` by simp[Abbr `ty`] >>
  qpat_assum `lowered_value_type ce e = ty` (fn ty_eq =>
    qpat_assum `data_ptr = Var dp` (fn data_eq =>
      qhdtm_assum `abi_packaging_window_law` (fn th =>
        mp_tac (Q.INST [`at` |-> `at`,`av` |-> `rv`,`s` |-> `z`,`G` |-> `Gz`,`tn` |-> `tz`,
          `sb` |-> `w2n (src_addr:bytes32)`,`d` |-> `p+32+k`,`cap` |-> `val_footprint tv v`]
          (SPEC_ALL (PURE_REWRITE_RULE [abi_packaging_window_law_def,ty_eq,data_eq] th)))))) >>
  (impl_tac >- suspend "standalone_window_premises") >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac) >>
  `Seg ready body_end pre q` by
    (qpat_assum `!p1 p2 p3. Seg ready unwrap_end p1 p2 /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  drule window_phase_strong_result >> strip_tac >>
  drule window_strong_result_public >>
  disch_then (fn th => mp_tac (MATCH_MP abi_encoder_window_result_output th)) >>
  strip_tac >>
  suspend "standalone_result"
QED

Resume abi_encode_normal_packaging_side[standalone_separation]:
  rpt strip_tac >>
  `stmt_state_rel H0 ctx func ce cx mid' pre` by metis_tac[] >>
  `regions_disjoint p N b n` suffices_by
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  irule local_ptrs_rel_alloca_disjoint >>
  qexistsl_tac [`ce`,`func`,`inst`,`name`,`root`,`mid'.scopes`,`pre`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `inst.inst_id = st.cs_next_id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule stmt_state_rel_local_ptrs_alloca >> simp[]
QED

Resume abi_encode_normal_packaging_side[source_cut]:
  qpat_assum `~is_word_type ty ==> _ \/ _` (drule_then strip_assume_tac)
  >- (qexistsl_tac [`si`,`ss`] >> asm_rewrite_tac[] >>
      qpat_assum `ci_mono ready unwrap_end` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
      qpat_assum `ss.cs_next_id <= st.cs_next_id` mp_tac >>
      qpat_assum `st.cs_next_id < ready.cs_next_id` mp_tac >> decide_tac) >>
  qexistsl_tac [`ready`,`unwrap_end`] >> asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Resume abi_encode_normal_packaging_side[standalone_source_premises]:
  qpat_assum `inst.inst_id = st.cs_next_id` (fn id_eq =>
    asm_rewrite_tac [id_eq]) >>
  rpt conj_tac >> decide_tac
QED

Resume abi_encode_normal_packaging_side[standalone_scratch]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `ready` >>
      asm_rewrite_tac[] >>
      qpat_assum `ci_mono ready unwrap_end` (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def])) >>
  strip_tac >>
  qpat_assum `0 < val_footprint tv v ==> _ /\ _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Resume abi_encode_normal_packaging_side[standalone_open_input]:
  simp_tac bool_ss [Abbr `bytes`] >>
  `!t value_type. evaluate_type (get_tenv cx) t = SOME value_type ==>
    type_memory_bytes ce t = type_memory_size value_type` by
    (rpt strip_tac >>
     rename1 `type_memory_bytes ce input_ty = type_memory_size runtime_ty` >>
     qpat_assum `evaluate_type (get_tenv cx) input_ty = SOME runtime_ty` (fn eval_ty =>
       qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es`
         (fn pre => ACCEPT_TAC (CONJUNCT1
           (MATCH_MP abi_encode_body_evaluated_metadata (CONJ pre eval_ty)))))) >>
  irule abi_encode_uniform_translated_footprint_window >>
  simp[] >> qexists_tac `get_tenv cx` >> simp[]
QED

Resume abi_encode_normal_packaging_side[standalone_window_premises]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp z /\
    z.vs_alloca_next + pending_alloca_size func z <= w2n z.vs_initial_fmp` by
    (strip_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel H0 ctx func ce cx mid' z`
           (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
         qpat_assum `ctx_has_dalloca ctx` (rewrite_tac o single))
     >> qpat_assum `stmt_state_rel H0 ctx func ce cx mid' z`
          (mp_tac o REWRITE_RULE [fmp_room_def] o MATCH_MP stmt_state_rel_fmp_room) >>
     qpat_assum `ctx_has_dalloca ctx` (rewrite_tac o single) >>
     disch_then (mp_tac o CONJUNCT1) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_assum `enc at rv = bytes` SUBST1_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  TRY (simp_tac bool_ss [abi_encoder_translation_admissible] >> NO_TAC)
  >- (rewrite_tac[GSYM ADD_ASSOC] >> first_assum ACCEPT_TAC)
  >- (qpat_assum `ptr_covers Gz tz dp z _` (ACCEPT_TAC o cj 1 o REWRITE_RULE [ptr_covers_def]))
  >- (rpt strip_tac
      >- (qpat_assum `!x. src = Var x ==> not_fresh_at unwrap_end x`
           (drule_then ACCEPT_TAC)) >>
      qpat_assum `Var dp = Var x` mp_tac >> simp[NoAsms] >>
      disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `dp` >> rewrite_tac[] >>
  irule reasonCopySourcePtrTheory.ptr_covers_mono >>
  qexists_tac `N - (32+k)` >> asm_rewrite_tac[] >>
  qpat_assum `32+k+LENGTH bytes <= N` mp_tac >> decide_tac
QED

Resume abi_encode_normal_packaging_side[standalone_result]:
  qpat_assum `enc at rv = bytes` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`ee` |-> `mid'`,`se` |-> `st`,`s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`,
       `shared` |-> `st.cs_next_id`,`pbase` |-> `p`,`capacity` |-> `N`,
       `dst` |-> `dp`,`dst_offset` |-> `32+k`,
       `a` |-> `unwrap_end`,`u` |-> `z`,`Gu` |-> `Gz`,`tu` |-> `tz`,
       `c` |-> `body_end`,`v` |-> `q`,`Gv` |-> `Gq`,`tv` |-> `tq`,
       `ids` |-> `window_alloca_sites func (frag_ids unwrap_end body_end)`,
       `outs` |-> `[(p+32+k,LENGTH (bytes:word8 list))]`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] abi_encode_saved_state_phase_pure) >>
  (impl_tac >- suspend "standalone_phase_premises") >> strip_tac >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (pre,Gpre,tnpre) [] (OK q,Gq,tq)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gz`,`z`,`tz`] >> asm_rewrite_tac[]) >>
  `pure_frame ce func mid' st t z /\ wb_frame ce mid' mid' st t z` by
    (irule abi_encode_saved_frames_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qexistsl_tac [`ready`,`pre`] >> asm_rewrite_tac[] >>
        qpat_assum `ci_mono st allocated` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
        qpat_assum `allocated.cs_next_var <= ready.cs_next_var` mp_tac >>
        qpat_assum `st.cs_next_id < ready.cs_next_id` mp_tac >> decide_tac) >>
     qexistsl_tac [`H0`,`ctx`,`cx`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bytes`,`limit`,`q`,`Gq`,`tq`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule (cj 1 abi_encode_saved_frames_trans) >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`st`,`z`] >> asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  qexistsl_tac [`H0`,`ctx`,`cx`] >> first_assum ACCEPT_TAC
QED

Resume abi_encode_normal_packaging_side[standalone_phase_premises]:
  `32+k+LENGTH bytes <= N` by first_assum ACCEPT_TAC >>
  `!aid. aid IN window_alloca_sites func (frag_ids unwrap_end body_end) ==>
    unwrap_end.cs_next_id <= aid` by simp[NoAsms, window_alloca_sites_def, frag_ids_def] >>
  `st.cs_next_id NOTIN window_alloca_sites func (frag_ids unwrap_end body_end)` by
    (strip_tac >> res_tac >> decide_tac) >>
  `local_ptrs_reserved ce unwrap_end` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `ready` >>
     asm_rewrite_tac[] >>
     qpat_assum `ci_mono ready unwrap_end`
       (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
  TRY (simp_tac (srw_ss()) [EVERY_DEF] >> decide_tac >> NO_TAC) >>
  TRY (rpt strip_tac >> first_x_assum drule >> decide_tac >> NO_TAC)
  >- (simp_tac (srw_ss()) [IN_INSERT, window_alloca_sites_def] >>
      gen_tac >> strip_tac
      >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
      rename1 `scratch.inst_id = aid` >>
      `?x. scratch.inst_operands = [Lit 32w] /\ scratch.inst_outputs = [x] /\
        not_local_ptr ce mid'.scopes x` by
        (irule (cj 2 abi_encode_compiled_scratch_site) >>
         qpat_assum `compile_abi_encode_to_buf (Var dp) src _ unwrap_end = (len,body_end)`
            (irule_at Any) >>
         qexistsl_tac [`func`,`func`,`unwrap_end`] >>
         asm_simp_tac (srw_ss()) [LESS_EQ_REFL]) >>
      rename1 `scratch.inst_outputs = [scratch_var]` >>
      qexistsl_tac [`scratch`,`scratch_var`] >> asm_rewrite_tac[]) >>
  simp_tac (srw_ss()) [EVERY_DEF] >> gen_tac >> disch_tac >>
  qpat_assum `!i. _ ==> (i IN tq.t_mem <=> i IN tz.t_mem)`
    (qspec_then `i` mp_tac) >>
  pop_assum mp_tac >> tautLib.TAUT_TAC
QED

Resume abi_encode_normal_packaging_side[standalone_restore_premises]:
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (qpat_assum `ci_mono st allocated` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `allocated.cs_next_var <= ready.cs_next_var` mp_tac >>
     qpat_assum `st.cs_next_id < ready.cs_next_id` mp_tac >> decide_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
  TRY (simp_tac bool_ss [Abbr `ty`] >> first_assum ACCEPT_TAC) >>
  TRY (rename1 `sm.cs_next_var <= ready.cs_next_var` >> decide_tac >> NO_TAC) >>
  TRY (rename1 `sm.cs_next_id <= ready.cs_next_id` >> decide_tac >> NO_TAC) >>
  TRY (rename1 `_ ==> ~is_word_type (expr_type e)` >>
       disch_tac >> first_assum ACCEPT_TAC) >>
  namedCases_on `sv` ["tag op0", "tag pp"] >>
  simp_tac (srw_ss()) [vv_operand_def, Abbr `ty`] >>
  disch_tac
  >- (qpat_assum `!tag op. _ ==> ptr_buf_ok ce e op G1 t`
        (qspecl_then [`tag`,`op0`] mp_tac) >> asm_simp_tac (srw_ss()) []) >>
  qpat_assum `!tag pp. _ ==> ptr_buf_ok ce e pp.ptr_operand G1 t`
    (qspecl_then [`tag`,`pp`] mp_tac) >> asm_simp_tac (srw_ss()) []
QED

Resume abi_encode_normal_packaging_side[finish_payload]:
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix body_end q Gq tq`
    (mp_then Any mp_tac abi_encode_saved_state_resources) >>
  (impl_tac >- (qexists_tac `H0` >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 mid' DF lo d st t G1 tn1
    st.cs_next_id p N root dp (32+k) prefix body_end q Gq tq`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `stmt_state_rel H0 ctx func ce cx mid' q` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func ce cx mid' q /\ _`
       (qspec_then `H0` (drule_then (ACCEPT_TAC o cj 1)))) >>
  `local_ptrs_rel func ce mid'.scopes q` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `p+N <= q.vs_alloca_next /\ 32+LENGTH (prefix ++ bytes) <= N` by
    (conj_tac >- metis_tac[alloca_site_registered_below] >>
     simp[LENGTH_APPEND] >>
     mp_tac (Q.SPECL [`maxlen+k`] le_word_size_mul) >> simp[Abbr `N`] >> decide_tac) >>
  `p < dimword(:256) /\ LENGTH bytes+k < dimword(:256)` by
    (qpat_assum `32 + LENGTH (prefix ++ bytes) <= N` (mp_tac o REWRITE_RULE [LENGTH_APPEND]) >>
     decide_tac) >>
  `lookup_var root q = SOME (n2w p) /\ ptr_covers Gq tq root q 32` by
    (conj_tac >-
       (qpat_assum `eval_operand (Var root) q = SOME (n2w p)`
         (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.eval_operand_def])) >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `N` >>
     conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  `!name b sz. local_region ce mid'.scopes q name b sz ==> regions_disjoint p N b sz`
    by suspend "finish_local_separation" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx mid' q`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `p+32 <= q.vs_alloca_next` by decide_tac >>
  qhdtm_assum `abi_packaging_finish_law`
    (mp_tac o PURE_REWRITE_RULE [abi_packaging_finish_law_def]) >>
  disch_then (drule_all_then
    (qx_choosel_then [`actual`,`Gf`,`tf`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `Seg st sb t actual` by
    (qpat_assum `!s1 s2 s3 s4 s5. Seg st allocated s1 s2 /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `ptr_covers Gf tf root actual N` by metis_tac[] >>
  `typed_copy_state_frame body_end p N q actual` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`p`,`32`] >> simp[] >>
     decide_tac) >>
  `copy_static actual = copy_static q /\ LENGTH q.vs_memory <= LENGTH actual.vs_memory /\
    (!a n. a+n <= p \/ p+N <= a ==>
      mem_bytes_at a n actual.vs_memory = mem_bytes_at a n q.vs_memory)` by
    (qpat_assum `typed_copy_state_frame body_end p N q actual`
      (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `actual with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = q` (SUBST1_TAC o SYM) >>
     simp[copy_static_def]) >>
  `local_ptrs_reserved ce body_end /\
   (!x. not_fresh_at st x ==> not_fresh_at body_end x) /\
   (!x. not_fresh_at sa x ==> not_fresh_at body_end x)` by
    (conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
         asm_rewrite_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >>
         asm_rewrite_tac[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     asm_rewrite_tac[] >>
     irule LESS_EQ_TRANS >> qexists_tac `st.cs_next_var` >>
     qpat_assum `ci_mono sa st` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx mid' Gf tf actual /\
    ghost_kept_at lo ce mid' st G1 tn1 t Gf tf` by suspend "finish_ghost" >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' actual /\ storage_well_formed_on cx mid' (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid' Gf tf actual` by suspend "finish_horizons" >>
  `!name b sz. local_region ce mid'.scopes actual name b sz ==> p+N <= b \/ b+sz <= p`
    by suspend "finish_result_separation" >>
  `wb_frame ce es mid' sa s0 actual /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf`
    by suspend "finish_caller_frame" >>
  `~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 actual`
    by suspend "finish_pure_frame" >>
  `!mem. mem_agree_outside tf.t_mem actual.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV (prefix ++ bytes)) p mem`
    by suspend "finish_bytes" >>
  `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) =
    N` by
    (once_rewrite_tac[lowered_value_type_def] >> Cases_on `mid` >>
     simp[NoAsms, Abbr `N`, Abbr `maxlen`, Abbr `tys`, Abbr `single`, Abbr `meth`,
       Abbr `k`, type_memory_bytes_def, vfmConstantsTheory.word_size_def, MULT_COMM]) >>
  `val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV (prefix ++ bytes)) <= N` by
    (`word_size (LENGTH (prefix ++ bytes)) <= word_size (maxlen+k)` by
       (irule word_size_monotone >> simp[LENGTH_APPEND] >> decide_tac) >>
     qpat_assum `word_size (LENGTH (prefix ++ bytes)) <= word_size (maxlen+k)` mp_tac >>
     simp[NoAsms, val_store_size_def, Abbr `N`]) >>
  `w2n (n2w p : bytes32) = p` by simp[w2n_n2w] >>
  `p+N <= actual.vs_alloca_next` by simp[] >>
  mp_tac (Q.INST [`s` |-> `actual`,`q` |-> `root`,`capacity` |-> `N`,
    `w` |-> `n2w p:bytes32`,`G` |-> `Gf`,`tn` |-> `tf`,`N` |-> `limit`,
    `ann` |-> `ann`, `ensure` |-> `ensure`, `target` |-> `target`,
    `args` |-> `args`, `mid` |-> `mid`, `ce` |-> `ce`, `cx` |-> `cx`,
    `ee` |-> `mid' with gas_obs := []`,`payload` |-> `prefix ++ bytes`]
    abi_encode_bytes_full_resources) >>
  (impl_tac >-
    (rewrite_tac[expr_type_def] >>
     qpat_assum `w2n (n2w p : bytes32) = p` (pure_rewrite_tac o single) >>
     qpat_assum `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann _ _ _)) = N`
       (fn th => rewrite_tac[th, LESS_EQ_REFL]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (OK actual,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> asm_rewrite_tac[] >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gpre`,`pre`,`tnpre`] >>
     asm_rewrite_tac[] >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gq`,`q`,`tq`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`vs`,`prefix ++ bytes`,`actual`,`Gf`,`tf`] >>
  simp[NoAsms,Abbr `declared`,expr_vv_sim_full_post_def,expr_sim_full_endpoint_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "finish_post"
QED

Resume abi_encode_normal_packaging_side[finish_local_separation]:
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`,`ce`,`mid'.scopes`,`q`,`inst`,`root`,`p`,`N`,`name`,`b`,`sz`]
    local_ptrs_rel_alloca_disjoint) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_normal_packaging_side[finish_bytes]:
  `p+32+k-LENGTH prefix = p+32` by decide_tac >>
  `mem_bytes_at (p+32) k q.vs_memory = prefix` by
    (qpat_assum `read_memory _ (LENGTH prefix) q = prefix`
       (mp_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     qpat_assum `p+32+k-LENGTH prefix = p+32` (pure_rewrite_tac o single) >>
     qpat_assum `LENGTH prefix = k` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  rpt strip_tac >>
  `!a n. p+32 <= a ==> mem_bytes_at a n actual.vs_memory = mem_bytes_at a n q.vs_memory` by
    (qpat_assum `typed_copy_state_frame body_end p 32 q actual`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
     rpt strip_tac >> first_assum irule >> simp[]) >>
  `mem_bytes_at (p+32) k mem = prefix /\
    mem_bytes_at (p+32+k) (LENGTH bytes) mem = bytes` by
    (conj_tac
     >- (TRANS_TAC EQ_TRANS ``mem_bytes_at (p+32) k actual.vs_memory`` >>
         reverse conj_tac >- simp[] >>
         irule (GSYM (SPEC_ALL logStoreDataOriginPtrTheory.mem_agree_outside_window)) >>
         qexists_tac `tf.t_mem` >> simp[] >> fs[IN_DIFF] >> decide_tac) >>
     TRANS_TAC EQ_TRANS ``mem_bytes_at (p+32+k) (LENGTH (bytes:word8 list)) actual.vs_memory`` >>
     reverse conj_tac >- simp[] >>
     irule (GSYM (SPEC_ALL logStoreDataOriginPtrTheory.mem_agree_outside_window)) >>
     qexists_tac `tf.t_mem` >> simp[IN_DIFF]) >>
  simp_tac (srw_ss()) [val_in_memory_def, LENGTH_APPEND] >>
  conj_tac >-
    (qpat_assum `LENGTH prefix = k` (pure_once_rewrite_tac o single) >>
     qpat_assum `!m. mem_agree_outside tf.t_mem actual.vs_memory m ==> mem_word_at p m = _`
       (qspec_then `mem` (drule_then mp_tac)) >> simp[NoAsms, ADD_COMM]) >>
  once_rewrite_tac[mem_bytes_at_split_padded] >>
  qpat_assum `LENGTH prefix = k` (pure_rewrite_tac o single) >>
  qpat_assum `mem_bytes_at (p+32) k mem = _` (pure_rewrite_tac o single) >>
  qpat_assum `mem_bytes_at (p+32+k) _ mem = _` (pure_rewrite_tac o single) >>
  REFL_TAC
QED

Resume abi_encode_normal_packaging_side[finish_ghost]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' q /\ _` (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!D d ce cx es origin G0 tn0 s0.
    _ ==> ghost_inv_at D lo d ce cx es Gf tf actual /\ _`
    (qspecl_then [`DF H`,`d`,`ce`,`cx`,`mid'`,`st`,`G1`,`tn1`,`t`] mp_tac) >>
  impl_tac >-
    (asm_rewrite_tac[] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `FLOOKUP ce.ce_vars _ = SOME (PtrVar (Var _) _)` (fn lookup =>
           qpat_assum `local_ptrs_reserved ce body_end` (fn reserved =>
             POP_ASSUM_LIST (K (metis_tac[lookup, reserved, local_ptrs_reserved_def])))))
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at body_end x` irule >>
         qpat_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at sa x` (drule_then ACCEPT_TAC))
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at body_end x` irule >>
         qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sa x` (drule_then ACCEPT_TAC))
     >- (rpt strip_tac >> irule local_ptrs_reserved_imm_base >> qexists_tac `ce` >> asm_rewrite_tac[])
     >> rpt strip_tac >>
     qpat_assum `!name b sz. local_region ce mid'.scopes q name b sz ==> regions_disjoint p N b sz`
       (drule_then mp_tac) >>
     simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[NoAsms]
QED

Resume abi_encode_normal_packaging_side[finish_horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' q /\ _` (qspec_then `H` (drule_then strip_assume_tac)) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer N st = _`
      (mp_then Any mp_tac buffer_alloc_code) >> simp[]) >>
  rpt conj_tac
  >- (irule literal_copy_window_stmt_state_rel >>
      qexistsl_tac [`st.cs_next_id`,`p`,`N`,`root`,`body_end`,`body_end`,`q`] >>
      asm_rewrite_tac[] >> simp[])
  >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. _ ==> ghost_inv_at (DF H) lo d ce cx mid' Gf tf actual /\ _`
    (qspec_then `H` (drule_then (ACCEPT_TAC o cj 1)))
QED

Resume abi_encode_normal_packaging_side[finish_result_separation]:
  rpt strip_tac >>
  `local_region ce mid'.scopes q name b sz` by
    (irule local_region_frame_fwd >> qexistsl_tac [`actual`,`st`,`mid'.scopes`] >>
     simp[] >> fs[ci_mono_def] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume abi_encode_normal_packaging_side[finish_caller_frame]:
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `eval_exprs cx args _ = (INL vs,mid')`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 6 evaluate_storage_trace_frame]) >>
  `stmt_state_rel H0 ctx func ce cx es s0` by metis_tac[] >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
    fs[ci_mono_def] >>
  `wb_frame ce es mid' sa s0 q` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx es s0`
       (mp_then Any assume_tac exprSimWordArgsTheory.wb_frame_trans) >>
     first_x_assum irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mid'`,`st`,`t`] >> simp[]) >>
  conj_tac
  >- (irule exprSimHashTheory.wb_frame_allocating_tail >>
      qpat_assum `wb_frame ce es mid' sa s0 q` (irule_at Any) >>
      qexistsl_tac [`st`,`mid'.scopes`] >> asm_rewrite_tac[] >>
      rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!a n. _ ==> mem_bytes_at a n actual.vs_memory = _` irule >>
          qpat_assum `!name b sz. local_region ce mid'.scopes q name b sz ==> _`
            (drule_then mp_tac) >>
          simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
      >- (rpt strip_tac >>
          qpat_assum `!x. not_fresh_at st x ==> not_fresh_at body_end x`
            (drule_then assume_tac) >> simp[]) >>
      rpt strip_tac >>
      `alloca_inv q` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func ce cx mid' q /\ _`
           (qspec_then `H0` (drule_then (mp_tac o cj 1))) >>
         metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
      `venomMemDefs$regions_disjoint (p,N) (b,sz)` by
        (irule alloca_site_registered_disjoint >>
         qexistsl_tac [`st.cs_next_id`,`aid`,`q`] >> asm_rewrite_tac[] >> decide_tac) >>
      Cases_on `sz = 0` >- simp[mem_bytes_at_def] >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n actual.vs_memory = _` irule >>
      qpat_x_assum `venomMemDefs$regions_disjoint (p,N) (b,sz)` mp_tac >>
      `N <> 0` by decide_tac >>
      simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ghost_kept_at lo ce mid' st G1 tn1 t Gf tf` by
    (qpat_assum `!H. _ ==> ghost_inv_at (DF H) lo d ce cx mid' Gf tf actual /\ _`
      (qspec_then `H0` (drule_then (ACCEPT_TAC o cj 2)))) >>
  qpat_assum `stmt_state_rel H0 ctx func ce cx es s0`
    (mp_then Any irule ghost_kept_at_wb_trans) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G1`,`mid'`,`mid'`,`t`,`st`,`tn1`] >>
  asm_rewrite_tac[]
QED

Resume abi_encode_normal_packaging_side[finish_pure_frame]:
  strip_tac >>
  `pure_frame ce func es sa s0 q` by
    (match_mp_tac (Q.SPECL [`ce`,`func`,`es`,`mid'`,`sa`,`st`,`s0`,`t`,`q`]
       pure_frame_trans) >>
     qpat_assum `ci_mono sa st` (assume_tac o cj 3 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `wb_frame ce mid' mid' st t q`
       (assume_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `wb_frame ce es mid' sa s0 t`
       (assume_tac o cj 1 o REWRITE_RULE [wb_frame_def]) >>
     asm_rewrite_tac[] >>
     first_assum (drule_then ACCEPT_TAC)) >>
  match_mp_tac (Q.SPECL [`ce`,`func`,`es`,`sa`,`s0`,`q`,`actual`,`inst`,`p`,`N`]
    pure_frame_buffer_tail) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (qpat_assum `inst.inst_id = st.cs_next_id` SUBST1_TAC >>
      qpat_assum `ci_mono sa st` (ACCEPT_TAC o cj 3 o REWRITE_RULE [ci_mono_def]))
  >- (rpt strip_tac >>
      `local_region ce mid'.scopes actual n lb lsz` by
        (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
         asm_rewrite_tac[] >>
         qpat_assum `wb_frame ce es mid' sa s0 actual`
           (ACCEPT_TAC o cj 1 o REWRITE_RULE [wb_frame_def])) >>
      qpat_assum `!name b sz. local_region ce mid'.scopes actual name b sz ==> _`
        (drule_then mp_tac) >>
      simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def] >>
      decide_tac) >>
  rpt gen_tac >> simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def] >>
  disch_tac >>
  qpat_assum `!a n. _ ==> mem_bytes_at a n actual.vs_memory = _` irule >>
  decide_tac
QED

Resume abi_encode_normal_packaging_side[finish_post]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func ce cx mid' actual /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp actual` by
    (qpat_assum `stmt_state_rel H ctx func ce cx mid' actual`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `stmt_state_rel H ctx func ce cx (mid' with gas_obs := []) actual /\
    storage_well_formed_on cx (mid' with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d ce cx (mid' with gas_obs := []) Gf tf actual` by
    (conj_tac >- simp[stmt_state_rel_start_gas_obs] >>
     conj_tac
     >- (qpat_assum `storage_well_formed_on cx mid' _` mp_tac >>
         simp[NoAsms, storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def,
              boolTheory.FORALL_BOOL]) >>
     `ghost_inv_at (DF H) lo d ce cx (mid' with gas_obs := []) Gf tf actual =
      ghost_inv_at (DF H) lo d ce cx mid' Gf tf actual` suffices_by
        (disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `is_bytestring_type (expr_type (TypeBuiltin ann (AbiEncode ensure mid) target args))` by
    (qpat_assum `ann = BaseT (BytesT (Dynamic limit))` (fn th =>
       simp[NoAsms, th, expr_type_def, is_bytestring_type_def])) >>
  qpat_assum `LocatedValue ann (mk_ptr out LocMemory) = vv` (SUBST1_TAC o SYM) >>
  qpat_assum `out = Var root` SUBST1_TAC >>
  simp[NoAsms, vv_location_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule (REWRITE_RULE [expr_type_def]
        (Q.INST [`e` |-> `TypeBuiltin ann (AbiEncode ensure mid) target args`,
                 `result` |-> `Value (BytesV (prefix ++ bytes))`,
                 `payload` |-> `prefix ++ bytes`]
          abi_encode_bytes_vv_post)) >>
      `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,N)` by simp[] >>
      pop_assum (irule_at Any) >>
      `val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV (prefix ++ bytes)) p actual.vs_memory` by
        (qpat_assum `!mem. _ ==> val_in_memory _ _ p mem` irule >>
         simp[NoAsms, mem_agree_outside_def]) >>
      pop_assum (irule_at Any) >>
      `st.cs_next_id < sb.cs_next_id` by
        (qpat_assum `abi_builtin_encode_finish _ _ _ body_end = ((),sb)`
           (mp_then Any (mp_tac o cj 1) abi_builtin_encode_finish_shape) >>
         qpat_assum `st.cs_next_id < body_end.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
      `sa.cs_next_id <= st.cs_next_id` by
        (qpat_assum `ci_mono sa st` (ACCEPT_TAC o cj 3 o REWRITE_RULE [ci_mono_def])) >>
      simp_tac (srw_ss()) [expr_type_def, read_result_def, return_def,
        expr_has_effect_def, wb_frame_gas_obs] >>
      (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
      >- (disch_tac >>
          qpat_assum `~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 actual` irule >>
          qpat_x_assum `EVERY _ args` mp_tac >>
          pure_once_rewrite_tac[EVERY_NOT_EXISTS] >>
          simp[NoAsms, combinTheory.o_DEF, ETA_AX]) >>
      (qpat_assum `32 + LENGTH (prefix ++ bytes) <= N`
          (assume_tac o REWRITE_RULE [LENGTH_APPEND]) >>
       qpat_assum `LENGTH (prefix ++ bytes) <= limit`
          (assume_tac o REWRITE_RULE [LENGTH_APPEND]) >>
       first_assum ACCEPT_TAC))
  >- (qpat_assum `is_bytestring_type _`
        (mp_then Any (fn th => qpat_assum `vv_store_bound cx (post_value_type _ _) _ _ _ _ _`
          (ACCEPT_TAC o REWRITE_RULE [th])) post_value_type_bytestring))
  >- (qpat_assum `_ ==> alloca_history func actual` irule >> asm_rewrite_tac[])
  >- (qpat_assum `actual.vs_alloca_next = q.vs_alloca_next` SUBST1_TAC >>
      irule LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >> asm_rewrite_tac[])
  >- (qpat_assum `is_bytestring_type _`
        (mp_then Any (fn th => qpat_assum `ptr_vv_ok cx (post_value_type _ _) _ _ _ _ _ _`
          (ACCEPT_TAC o REWRITE_RULE [th])) post_value_type_bytestring)) >>
  (simp[NoAsms, mk_ptr_def, vv_location_def])
  >- (qpat_assum `is_bytestring_type _` (fn th => simp[NoAsms, th])) >>
  first_assum ACCEPT_TAC
QED

Finalise abi_encode_normal_packaging_side

(* Project the normal continuation back into the ordinary full list bind. *)
Theorem abi_encode_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  (LENGTH args = 1 /\ ~ensure ==> ~is_word_type (lowered_value_type ce (HD args))) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  (!s x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s = (INL x,t) ==> body_exprs_full_ok cx args) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode ensure mid) target args) es
Proof
  strip_tac >>
  `1 <= LENGTH args` by
    (Cases_on `args` >> simp[] >>
     `well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target [])`
       by fs[expr_body_pre_def] >>
     pop_assum mp_tac >> simp[Once well_typed_expr_def,
       well_typed_type_builtin_args_def]) >>
  `body_exprs_full_ok cx args` by
    (qpat_x_assum `!s x t. _` (qspecl_then [`es`, `()`, `es`] mp_tac) >>
     simp[type_check_def, type_builtin_args_length_ok_def, assert_def, return_def]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_abi_encode_body_layout >>
  disch_then (qx_choosel_then [`svs`,`st`,`out`] strip_assume_tac) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ shadow_sa = _`) compile_abi_encode_body_layout >>
  disch_then drule_all >> strip_tac >>
  rename1 `compile_abi_encode_args compile_expr _ (MAP gas_shadow_expr args) shadow_sa =
    (shadow_svs,shadow_st)` >>
  `gas_shadow_compiles (compile_abi_encode_args compile_expr ce args)
     (compile_abi_encode_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr args))` by
    (irule (SIMP_RULE bool_ss []
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_abi_encode_args_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  `shadow_svs = svs /\ gas_shadow_state st shadow_st` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_svs = svs` SUBST_ALL_TAC >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `!e q. MEM e args /\ expr_sim_inv ce cx env q ==> expr_body_pre ce cx env e q`
    by metis_tac[abi_args_body_pre_arg] >>
  qpat_assum `compile_abi_encode_args _ _ args sa = _`
    (assume_tac o REWRITE_RULE [compile_abi_encode_args_def]) >>
  qpat_assum `compile_abi_encode_args _ _ (MAP _ args) shadow_sa = _`
    (assume_tac o REWRITE_RULE [compile_abi_encode_args_def, gasShadowCompileBaseTheory.lowered_value_type_gas_shadow_env]) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `kw_es` |-> `[]:expr list`, `xs` |-> `args`,
    `sb` |-> `st`, `shadow_sb` |-> `shadow_st`]
    (Q.SPEC `T` extcall_request_positional_packing_outcome_named)) >>
  simp[NoAsms] >> impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  dep_rewrite.DEP_REWRITE_TAC [eval_expr_abi_encode_action] >> simp[] >>
  irule gas_outcome_full_bind_all_path >>
  conj_tac >- simp[storage_trace_frame_def] >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[cj 6 evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >>
      first_assum ACCEPT_TAC) >>
  qexists_tac `extcall_positional_post T DF lo d ctx func ce cx env
    [] args svs sa st es s0 G0 tn0` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      rpt strip_tac >> Cases_on `res` >> gvs[] >>
      conj_tac
      >- (qpat_x_assum `expr_exit _ _` mp_tac >>
          once_rewrite_tac[stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
      fs[halt_exit_def]) >>
  suspend "normal_packaging"
QED

Resume abi_encode_vv_full_from_packaging[normal_packaging]:
  rpt gen_tac >> strip_tac >>
  `out' = out` by
    (qpat_assum `LocatedValue ann (mk_ptr out LocMemory) = LocatedValue ann (mk_ptr out' LocMemory)`
      mp_tac >> simp[mk_ptr_def]) >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all (Q.INST [`vv` |-> `LocatedValue ann (mk_ptr out LocMemory)`,
                    `Seg` |-> `\a b s t. T`, `RowSide` |-> `\a b s t. T`]
             abi_encode_normal_packaging_side
             |> PURE_REWRITE_RULE [LET_THM] |> BETA_RULE
             |> REWRITE_RULE [abi_packaging_phases_trivial]) >>
  strip_tac >>
  disj1_tac >> qexists_tac `vs` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_full_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`mid'`,`INL (Value (BytesV payload))`,`actual`,`tf`] >>
  conj_tac >- simp[] >>
  rpt strip_tac >> res_tac >>
  fs[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def]
QED

Finalise abi_encode_vv_full_from_packaging
