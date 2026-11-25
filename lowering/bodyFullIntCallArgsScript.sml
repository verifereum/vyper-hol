(*
 * The internal call full case's argument stage over the finite-horizon
 * joint judgment.
 *
 * TOP-LEVEL:
 *   intcall_args_full
 *)
Theory bodyFullIntCallArgs
Ancestors bodyCallSupport bodyFullShadowBodyInv vyperCallOutcome[qualified,ignore_grammar] fragGasPath compileVyper[qualified,ignore_grammar] pair[qualified,ignore_grammar] vyperStorageBackend[qualified,ignore_grammar] vyperStorageFootprint[qualified,ignore_grammar] freshWrites[qualified,ignore_grammar] bodyFullAllocaFresh[qualified,ignore_grammar] bodyIntCallSource[qualified,ignore_grammar] bodySim[qualified,ignore_grammar] supportedProgram[qualified,ignore_grammar] supportedNames[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar]
  compileExprAllocaFresh[qualified,ignore_grammar]
  compilerInstructionSuffix[qualified,ignore_grammar]
  abiEncoderProps[qualified,ignore_grammar]
  bodyFullIntCallDefs bodyFullIntCallByteFrame[qualified,ignore_grammar]
  bodyInvIntCallPinsProps
  bodyIntCallSeams bodyFullPreds bodySimFull bodyFullUnwrap
  constSubst constSubstStmtsPreserve
  gasOutcomeFull bodyPtrDefs gasShadow gasShadowShape gasContext exprSimHypsDefs
  exprSimIfExpWidenedAdapter exprSimSliceCompose
  loweringPosts exprSimVVFrame valueEncodingProofs bodyPtrBytestringBuiltinsWindowGhost
  exprReasonOperand haltExitProj typedMemoryCopy
  logStoreDataOriginPtr annassignRelayoutSource bodyFullPathHistory
  wideningZeroLayout exprSimHyps exprSimSend aggregateEvaluatedLayout vyperTypeSystem context compileEnv
  exprLowering emitHelper vyperInterpreter vyperTypeEvalProofs vyperState vyperAST
  vyperStorageTrace bodyFullIntCallArgsTrace fragExec list
  ctorDeployLoweringFrameSupport[qualified]
  exprLoweringProps[qualified,ignore_grammar]
  exprSimDefs[qualified,ignore_grammar]
  loweringStateRelDefs[qualified,ignore_grammar]
  vyperTypeInvariants[qualified,ignore_grammar]
  nonreentrantEquiv[qualified,ignore_grammar] nonreentrantEntryPath[qualified,ignore_grammar]
  transientLockProps transientLockPtr[qualified,ignore_grammar] fragGasCopyLoop[qualified,ignore_grammar]
  instSeqPtrLo[qualified,ignore_grammar] fragExecMem fragGasSeqPtr
  unitTransformDefs[qualified,ignore_grammar] memSafeRun[qualified,ignore_grammar]
  fragGasOriginPtrInvoke bodyFullShadowInternalRun[qualified,ignore_grammar]
  intCallMaterializeFull bodyFullAllocGeneric[qualified,ignore_grammar]
  internalReturnMemoryInputs[qualified,ignore_grammar]
  abiBufferAllocationCode[qualified,ignore_grammar]
  bodyPtrPrecompileBuiltinsAllocationFrame[qualified,ignore_grammar]
  bodyExprPreFacts[qualified] exprOracleStorageInterfaces[qualified]
  bodyInvSplit[qualified] bodyInvCodeProps[qualified]
  bodyInvExecutionProps[qualified] bodyInvMetadataProps[qualified]
  exprBodyPreProps[qualified]
  compileUnit intCallAllocationProps[qualified]

  venomInst[qualified,ignore_grammar]
  bodyFullIfExpReach[qualified,ignore_grammar]
  contextCodegenRel[qualified,ignore_grammar]
  contextRawReachable[qualified,ignore_grammar]
  venomState[qualified,ignore_grammar]
  venomExecProofs[qualified,ignore_grammar]
  vyperCompiler[qualified,ignore_grammar]
  vyperLoweringCorrect[qualified,ignore_grammar]
  deployUnitProducers[qualified,ignore_grammar]
  venomFnInstsProofs[qualified,ignore_grammar]
  fragGasOriginPtr[qualified,ignore_grammar]
  fragGasOrigin[qualified,ignore_grammar]
  fragGasMode[qualified,ignore_grammar]
  ctorDeployLoweringSource[qualified,ignore_grammar] fragGasPathMem[qualified,ignore_grammar]

val _ = Parse.hide "body";

Theorem intcall_args_body_inv_struct_fields[local]:
  body_inv tops ctx cenv cx ==>
  cenv.ce_struct_fields = make_struct_fields_map tops
Proof
  disch_then (mp_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
  disch_then (mp_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_struct_fields) >>
  simp[compileUnitTheory.make_struct_fields_map_mods_singleton]
QED

Theorem intcall_args_body_inv_constructor[local]:
  body_inv tops ctx cenv cx ==> cx.in_deploy = cenv.ce_is_ctor
Proof
  disch_then (mp_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
  disch_then (mp_tac o MATCH_MP bodyInvMetadataPropsTheory.contract_inv_constructor) >>
  simp[EQ_SYM_EQ]
QED

Theorem intcall_args_body_inv_function_tables[local]:
  body_inv tops ctx cenv cx ==>
  cenv.ce_func_ids = build_func_ids 0 tops /\
  cenv.ce_func_param_types = build_func_param_types tops /\
  cenv.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
  (!name. ~MEM (NONE,name) cx.stk ==>
    ALOOKUP cenv.ce_func_defaults name = ALOOKUP (build_func_defaults tops) name)
Proof
  disch_then (mp_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
  simp[bodyInvSplitTheory.contract_inv_def,
       compileUnitTheory.build_func_ids_mods_singleton,
       compileUnitTheory.build_func_param_types_mods_singleton,
       compileUnitTheory.build_func_info_mods_singleton,
       compileUnitTheory.make_struct_fields_map_mods_singleton,
       compileUnitTheory.build_func_defaults_mods_singleton, nsid_to_string_def]
QED

Theorem intcall_args_body_inv_lowering[local]:
  body_inv tops ctx cenv cx ==>
  ?rpolicy unit.
    (if cx.in_deploy then
      ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
     else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
    ctx = unit.cu_context
Proof
  disch_then (mp_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
  simp[bodyInvSplitTheory.contract_inv_def,
       lower_vyper_deploy_unit_mods_singleton,
       lower_vyper_runtime_unit_mods_singleton] >>
  strip_tac >>
  rename1 `cenv.ce_target = rpolicy.rpol_target` >>
  rename1 `ctx = unit.cu_context` >>
  qexistsl_tac [`rpolicy`,`unit`] >> simp[]
QED

Theorem intcall_args_pre_state[local]:
  expr_body_pre cenv cx tenv e es /\
  expr_sim_inv cenv cx tenv ee ==>
  expr_body_pre cenv cx tenv e ee
Proof
  simp[expr_body_pre_split_def, expr_body_pre_mods_def, expr_sim_inv_split_def] >>
  rpt strip_tac >> res_tac
QED

(* The allocation made between the two unwrap ownership intervals cannot
   own the source.  A local source is separated by the allocation's local
   frame instead.  Both alternatives describe this very same state. *)
Theorem intcall_args_aggregate_source_disjoint[local]:
  ~is_bytestring_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  read_result cx raw es = (INL v,es) /\
  type_memory_size stv <> 0 /\
  eval_operand op s = SOME sw /\
  (vv_at ce cx sty sa sm es raw (LocatedValue sty (mk_ptr op LocMemory)) s \/
   vv_at ce cx sty sb sc es raw (LocatedValue sty (mk_ptr op LocMemory)) s) /\
  sm.cs_next_id <= did /\ did < sb.cs_next_id /\
  alloca_inv s /\ FLOOKUP s.vs_allocas did = SOME (w2n dw,cap) /\
  n <= cap /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    w2n dw + cap <= b \/ b + sz <= w2n dw) ==>
  w2n sw + type_memory_size stv <= w2n dw \/
  w2n dw + n <= w2n sw
Proof
  rpt strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  gvs[loweringPostsTheory.vv_at_def, contextTheory.mk_ptr_def] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + cap <= w2n sw` suffices_by (strip_tac >> decide_tac) >>
  FIRST [
    (qpat_x_assum `!name b sz. local_region ce es.scopes s name b sz ==> _` drule >>
     strip_tac >> decide_tac),
    (rename1 `FLOOKUP s.vs_allocas sid = SOME (b,sz)` >>
     `sid <> did` by decide_tac >>
     `b + sz <= w2n dw \/ w2n dw + cap <= b` by
       (fs[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.allocas_non_overlapping_def] >>
        metis_tac[arithmeticTheory.ADD_COMM]) >>
     decide_tac)]
QED


(* A nonzero aggregate store uses the same unwrap landing for ownership,
   representation and ghosts, and chooses its endpoint before the horizon. *)
Theorem intcall_args_aggregate_store_nonzero:
  compile_store_memory cenv (Var src) (Var dst) dty sty cu = ((),cs) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ ~is_bytestring_type sty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  type_memory_size stv <> 0 /\
  not_fresh_at cu src /\ not_fresh_at cu dst /\
  lookup_var src z = SOME sw /\ lookup_var dst z = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv <= z.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next /\
  z.vs_alloca_next < dimword (:256) /\
  ptr_covers G tn src z (type_memory_size stv) /\
  ptr_covers G tn dst z (MAX 32 (type_memory_bytes cenv dty)) /\
  read_result cx raw es = (INL v,es) /\
  (vv_at cenv cx sty sa sm es raw
     (LocatedValue sty (mk_ptr (Var src) LocMemory)) z \/
   vv_at cenv cx sty sb cu es raw
     (LocatedValue sty (mk_ptr (Var src) LocMemory)) z) /\
  sm.cs_next_id <= did /\ did < sb.cs_next_id /\
  FLOOKUP z.vs_allocas did = SOME (w2n dw,MAX 32 (type_memory_bytes cenv dty)) /\
  (!name b sz. local_region cenv es.scopes z name b sz ==>
     w2n dw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + sz <= w2n dw) /\
  alloca_inv z /\ alloca_history func z /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code cu cs func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = cu.cs_current_bb /\
  z.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (t,G1,tn1) [] (OK z,G,tn)) ==>
  ?wt wG wtn nw.
    nw <= MAX 32 (type_memory_bytes cenv dty) /\
    typed_copy_state_frame cu (w2n dw) nw z wt /\
    ~wt.vs_halted /\ wt.vs_current_bb = cs.cs_current_bb /\
    wt.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func wt /\
    wtn.t_stor = tn.t_stor /\ wtn.t_trans = tn.t_trans /\ wtn.t_imm = tn.t_imm /\
    (!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G p /\
      op_taint wtn (Var p) = op_taint tn (Var p)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + nw) ==>
      (i IN wtn.t_mem <=> i IN tn.t_mem)) /\
    (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
      value_has_type rt v /\ val_wf rt v /\
      type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
      (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
        val_in_memory rt v (w2n dw) mem)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK wt,wG,wtn))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `type_memory_size dtv <= MAX 32 (type_memory_bytes cenv dty)` by simp[] >>
  `eval_operand (Var src) z = SOME sw` by simp[venomStateTheory.eval_operand_def] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (drule_all intcall_args_aggregate_source_disjoint >> simp[]) >>
  `ptr_covers G tn dst z (type_memory_size dtv)` by
    (qpat_x_assum `ptr_covers G tn dst z (MAX 32 _)` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   w2n dw + type_memory_size dtv < dimword (:256) /\
   w2n dw + type_memory_size dtv <= z.vs_alloca_next` by decide_tac >>
  drule compile_store_memory_origin_ptr_path >>
  disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
  disch_then (drule_at (Pat `lookup_var src _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ src _ _`)) >>
  disch_then (qspecl_then [`v`,`sw`,`stv`] mp_tac) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `alloca_history func t'` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `ARB` assume_tac) >>
     irule body_full_path_alloca_history >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl [`t'`,`Gf`,`tnf`,`type_memory_size dtv`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
  disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[]
QED

(* The staging traversal never reads metadata past its expression prefix. *)
Theorem intcall_args_stage_take:
  !es flags dtys.
    LENGTH es <= LENGTH flags /\ LENGTH es <= LENGTH dtys ==>
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
    compile_stage_intcall_args compile_expr cenv es
      (TAKE (LENGTH es) flags) (TAKE (LENGTH es) dtys) si
Proof
  `!es flags dtys.
    LENGTH es <= LENGTH flags /\ LENGTH es <= LENGTH dtys ==>
    compile_stage_intcall_args compile_expr cenv es flags dtys =
    compile_stage_intcall_args compile_expr cenv es
      (TAKE (LENGTH es) flags) (TAKE (LENGTH es) dtys)` suffices_by metis_tac[] >>
  Induct_on `es` >- simp[compile_stage_intcall_args_def] >>
  namedCases_on `flags` ["", "flag flags'"] >- simp[] >>
  namedCases_on `dtys` ["", "dty dtys'"] >- simp[] >>
  Cases_on `flag` >> simp[compile_stage_intcall_args_def]
QED

Theorem intcall_args_allocation_bounds_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  MEM (src,(mut,nr,rr,name,args,dflts,ret,ss))
    (FST (SND (classify_functions_unit mods exps))) ==>
  EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) (MAP SND args) /\
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >>
  drule_all_then assume_tac intCallAllocationPropsTheory.contract_inv_internal_allocs >>
  drule_then assume_tac bodyInvCodePropsTheory.contract_inv_struct_fields >>
  rename1 `cenv.ce_struct_fields = make_struct_fields_map_mods mods` >>
  qabbrev_tac `fn_env = build_compile_env_unit mods src Internal mut name args ret ss F` >>
  `fn_env.ce_struct_fields = cenv.ce_struct_fields` by
    (simp[Abbr `fn_env`, compileUnitTheory.build_compile_env_unit_def] >>
     rpt (pairarg_tac >> simp[])) >>
  `type_memory_bytes fn_env = type_memory_bytes cenv` by
    simp[compileEnvTheory.type_memory_bytes_frame] >>
  fs[compileUnitTheory.fn_allocs_ok_unit_def, GSYM markerTheory.Abbrev_def, EVERY_MAP,
     combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem intcall_args_classified_singleton[local]:
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  MEM (NONE,subst_consts_fn (module_consts_env tops [])
       (mut,nr,rr,name,args,dflts,ret,ss))
    (FST (SND (classify_functions_unit [(NONE,tops)] [])))
Proof
  strip_tac >>
  `MEM (subst_consts_fn (module_consts_env tops [])
     (mut,nr,rr,name,args,dflts,ret,ss))
     (FST (SND (classify_functions tops)))` by
    (simp[constSubstTheory.subst_consts_fn_def,
          loweringShapePropsTheory.MEM_classify_internal] >>
     qexistsl [`dflts`,`ss`] >> simp[]) >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = (exts,rest)` >> PairCases_on `rest` >>
  fs[classify_functions_unit_singleton, MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_args_allocation_bounds[local]:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) (MAP SND args) /\
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_then assume_tac intcall_args_classified_singleton >>
  pop_assum (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def]) >>
  drule_all intcall_args_allocation_bounds_mods >> simp[]
QED

(* The compiler table selects the omitted suffix after constant substitution. *)
Theorem intcall_args_omitted_defaults[local]:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\ ~MEM (NONE,name) cx.stk ==>
  omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) =
    DROP (LENGTH dflts - (LENGTH args - LENGTH es))
      (subst_consts_exprs (module_consts_env tops []) dflts) /\
  LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) =
    LENGTH args - LENGTH es /\
  cenv.ce_func_param_types name =
    TAKE (LENGTH es) (MAP SND args) ++ DROP (LENGTH es) (MAP SND args) /\
  LENGTH (TAKE (LENGTH es) (cenv.ce_func_param_types name)) = LENGTH es /\
  LENGTH (DROP (LENGTH es) (cenv.ce_func_param_types name)) =
    LENGTH args - LENGTH es
Proof
  strip_tac >>
  drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
  drule_then strip_assume_tac intcall_args_body_inv_function_tables >>
  `ALL_DISTINCT (supported_function_names tops) /\
   EVERY (supported_declaration_header tops) tops` by
    gvs[supportedProgramTheory.supported_program_def,
        supportedNamesTheory.supported_declaration_names_def,
        supportedDeclsTheory.supported_declaration_headers_def] >>
  `cenv.ce_func_param_types name = MAP SND args` by
    (gvs[] >> irule intCallLookupTheory.build_func_param_types_distinct >>
     conj_tac >- simp[] >>
     first_assum (irule_at Any) >> simp[]) >>
  qabbrev_tac `compiled_defaults = subst_consts_exprs (module_consts_env tops []) dflts` >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) ss` >>
  `MEM (mut,nr,rr,name,args,compiled_defaults,ret,compiled_body)
      (FST (SND (classify_functions tops)))` by
    (simp[loweringShapePropsTheory.MEM_classify_internal] >>
     qexistsl [`dflts`,`ss`] >>
     simp[Abbr `compiled_defaults`, Abbr `compiled_body`, constSubstTheory.subst_consts_fn_def]) >>
  `ALOOKUP (build_func_defaults tops) name = SOME compiled_defaults` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     conj_tac
     >- (drule loweringShapeSourceTheory.supported_names_internal_names_distinct >>
         simp[compileVyperTheory.build_func_defaults_def, MAP_MAP_o,
              combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
     simp[compileVyperTheory.build_func_defaults_def, MEM_MAP,
          pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  gvs[omitted_defaults_def, nsid_to_string_def, TAKE_DROP,
      Abbr `compiled_defaults`, loweringShapePropsTheory.subst_consts_exprs_length] >>
  decide_tac
QED

(* The concrete emitted word store preserves the execution's allocation history. *)
Theorem intcall_args_word_store_history:
  !cenv op aq dty sty cu cs func z w aw.
    compile_store_memory cenv op (Var aq) dty sty cu = ((),cs) /\
    is_word_type dty /\
    fn_has_code cu cs func /\ fn_inst_ids_distinct func /\
    eval_operand op z = SOME w /\ lookup_var aq z = SOME aw /\
    alloca_history func z /\ alloca_inv z /\ ~z.vs_halted /\
    z.vs_current_bb = cu.cs_current_bb /\
    z.vs_inst_idx = LENGTH cu.cs_current_insts ==>
    alloca_history func
      ((mstore (w2n aw) w z) with vs_inst_idx := LENGTH cs.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `emit_inst MSTORE [Var aq;op] [] cu = ((),cs)` by
    gvs[contextTheory.compile_store_memory_def,
        emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`[mk_inst cu.cs_next_id MSTORE [Var aq;op] []]`,`z`,`cu`] >>
  `eval_operand (Var aq) z = SOME aw` by simp[venomStateTheory.eval_operand_def] >>
  `step_inst_base (mk_inst cu.cs_next_id MSTORE [Var aq;op] []) z =
     OK (mstore (w2n aw) w z)` by
    (irule emitHelperPropsTheory.step_MSTORE >> simp[]) >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

(* Empty local typing maps can be weakened without changing static maps. *)
Theorem intcall_args_defaults_typing_mutual[local]:
  (!env e. well_typed_expr env e ==>
    !tenv. env = defaults_env tenv ==> well_typed_expr tenv e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
    !tenv. env = defaults_env tenv ==> type_place_expr tenv e = SOME vt) /\
  (!env tgt vt. type_place_target env tgt = SOME vt ==>
    !tenv. env = defaults_env tenv ==> type_place_target tenv tgt = SOME vt) /\
  (!env es. well_typed_exprs env es ==>
    !tenv. env = defaults_env tenv ==> well_typed_exprs tenv es) /\
  (!env opt. well_typed_opt env opt ==>
    !tenv. env = defaults_env tenv ==> well_typed_opt tenv opt) /\
  (!env fs. well_typed_named_exprs env fs ==>
    !tenv. env = defaults_env tenv ==> well_typed_named_exprs tenv fs)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[defaults_env_def, well_typed_expr_def]
  >- (disj1_tac >> irule subscript_base_type_exact_transfer >>
      first_assum (irule_at Any) >> simp[]) >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

(* Nonlocal places cannot observe the caller's scope stack. *)
Theorem intcall_args_read_place_scope_action[local]:
  (!id path. p <> MemoryPlace id path) ==>
  !cx s scopes. read_place cx p (s with scopes := scopes) =
    (FST (read_place cx p s),SND (read_place cx p s) with scopes := scopes)
Proof
  Cases_on `p` >> simp[read_place_def]
  >- simp[vyperLookupStorageScopesTheory.read_storage_slot_scopes,
          pairTheory.UNCURRY, read_storage_slot_state_snd] >>
  rpt strip_tac >>
  simp[get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, lift_option_type_def, lift_sum_def,
                            return_def, raise_def])
QED

Theorem intcall_args_scope_bind[local]:
  (!s sc. a (s with scopes := sc) =
    (FST (a s),SND (a s) with scopes := sc)) /\
  (!s0 v t. a s0 = (INL v,t) ==>
    !s sc. k v (s with scopes := sc) =
      (FST (k v s),SND (k v s) with scopes := sc)) ==>
  !s sc. bind a k (s with scopes := sc) =
    (FST (bind a k s),SND (bind a k s) with scopes := sc)
Proof
  rpt strip_tac >> simp[bind_def] >>
  namedCases_on `a s` ["res mid"] >>
  namedCases_on `res` ["v", "err"] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem intcall_args_call_outcome_scope[local]:
  (!g a d v s sc. vyperCallOutcome$take_call_outcome g a d v
      (s with scopes := sc) =
    (FST (vyperCallOutcome$take_call_outcome g a d v s),
     SND (vyperCallOutcome$take_call_outcome g a d v s) with scopes := sc)) /\
  (!g a d v s sc. vyperCallOutcome$take_delegate_outcome g a d v
      (s with scopes := sc) =
    (FST (vyperCallOutcome$take_delegate_outcome g a d v s),
     SND (vyperCallOutcome$take_delegate_outcome g a d v s) with scopes := sc)) /\
  (!req out s sc. vyperCallOutcome$adopt_call_outcome req out
      (s with scopes := sc) =
    (FST (vyperCallOutcome$adopt_call_outcome req out s),
     SND (vyperCallOutcome$adopt_call_outcome req out s) with scopes := sc))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (simp[vyperCallOutcomeTheory.take_call_outcome_def,
           vyperCallOutcomeTheory.call_outcome_request_def,
           vyperCallOutcomeTheory.take_request_outcome_def,
           pairTheory.UNCURRY, evaluation_state_fupdcanon] >>
      Cases_on `s.outcomes` >> simp[] >>
      Cases_on `x` >> simp[] >>
      IF_CASES_TAC >> simp[evaluation_state_fupdcanon])
  >- (simp[vyperCallOutcomeTheory.take_delegate_outcome_def,
           vyperCallOutcomeTheory.delegate_outcome_request_def,
           vyperCallOutcomeTheory.call_outcome_request_def,
           vyperCallOutcomeTheory.take_request_outcome_def,
           pairTheory.UNCURRY, evaluation_state_fupdcanon] >>
      Cases_on `s.outcomes` >> simp[] >>
      Cases_on `x` >> simp[] >>
      IF_CASES_TAC >> simp[evaluation_state_fupdcanon]) >>
  simp[vyperCallOutcomeTheory.adopt_call_outcome_def, pairTheory.UNCURRY] >>
  IF_CASES_TAC >> simp[record_storage_backend_def, record_storage_event_def,
                      return_def, evaluation_state_fupdcanon]
QED

Theorem intcall_args_scope_bind_all[local]:
  (!s sc. a (s with scopes := sc) =
    (FST (a s),SND (a s) with scopes := sc)) /\
  (!v s sc. k v (s with scopes := sc) =
    (FST (k v s),SND (k v s) with scopes := sc)) ==>
  bind a k (s with scopes := sc) =
    (FST (bind a k s),SND (bind a k s) with scopes := sc)
Proof
  rpt strip_tac >> irule intcall_args_scope_bind >> simp[]
QED

val intcall_args_call_leaf_simps =
  [type_check_def, check_def, assert_def, check_not_static_def,
   lift_option_def, lift_option_type_def, lift_sum_runtime_def,
   return_def, raise_def, get_accounts_def, get_transient_storage_def,
   get_pending_deletions_def, update_accounts_def, update_transient_def,
   update_pending_deletions_def, record_storage_backend_def,
   record_storage_event_def, append_logs_def, evaluation_state_fupdcanon];

fun intcall_args_scope_steps facts =
  rpt (FIRST
    [CHANGED_TAC BETA_TAC,
     irule intcall_args_scope_bind_all >> conj_tac,
     gen_tac,
     CHANGED_TAC (simp (facts @ intcall_args_call_leaf_simps)),
     BasicProvers.TOP_CASE_TAC]);

Theorem intcall_args_frame_value_scope[local]:
  !cx v s sc. frame_call_value cx v (s with scopes := sc) =
    (FST (frame_call_value cx v s),SND (frame_call_value cx v s) with scopes := sc)
Proof
  rpt gen_tac >> Cases_on `cx.txn.is_static` >>
  simp[frame_call_value_def, ignore_bind_def, bind_def, check_def, assert_def,
       COND_RATOR, return_def, raise_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem intcall_args_eval_raw_call_scope[local]:
  !cx fl a d v g s sc. eval_raw_call cx fl a d v g (s with scopes := sc) =
    (FST (eval_raw_call cx fl a d v g s),SND (eval_raw_call cx fl a d v g s)
       with scopes := sc)
Proof
  simp_tac bool_ss [eval_raw_call_def, ignore_bind_def, LET_THM, pairTheory.ELIM_UNCURRY] >>
  intcall_args_scope_steps [intcall_args_frame_value_scope, intcall_args_call_outcome_scope]
QED

Theorem intcall_args_eval_send_scope[local]:
  !cx g vs s sc. eval_send cx g vs (s with scopes := sc) =
    (FST (eval_send cx g vs s),SND (eval_send cx g vs s) with scopes := sc)
Proof
  rpt gen_tac >> Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  Cases_on `t` >>
  simp_tac bool_ss [eval_send_def, ignore_bind_def, LET_THM, pairTheory.ELIM_UNCURRY] >>
  intcall_args_scope_steps [intcall_args_frame_value_scope, intcall_args_call_outcome_scope]
QED

Theorem intcall_args_ext_call_effects_scope[local]:
  !cx a d v g ac s sc. eval_ext_call_effects cx a d v g ac (s with scopes := sc) =
    (FST (eval_ext_call_effects cx a d v g ac s),
     SND (eval_ext_call_effects cx a d v g ac s) with scopes := sc)
Proof
  simp_tac bool_ss
    [eval_ext_call_effects_def, ignore_bind_def, LET_THM, pairTheory.ELIM_UNCURRY] >>
  intcall_args_scope_steps [intcall_args_call_outcome_scope]
QED

Theorem intcall_args_eval_ext_call_scope[local]:
  !cx a b sig opts vs s sc. eval_ext_call cx a b sig opts vs (s with scopes := sc) =
    (FST (eval_ext_call cx a b sig opts vs s),
     SND (eval_ext_call cx a b sig opts vs s) with scopes := sc)
Proof
  rpt gen_tac >> PairCases_on `sig` >> Cases_on `vs` >>
  simp_tac bool_ss [eval_ext_call_def, ignore_bind_def, LET_THM] >>
  intcall_args_scope_steps [intcall_args_frame_value_scope, intcall_args_ext_call_effects_scope]
QED

Theorem intcall_args_take_create_scope[local]:
  !kind v code s sc. vyperCallOutcome$take_create_outcome kind v code
      (s with scopes := sc) =
    (FST (vyperCallOutcome$take_create_outcome kind v code s),
     SND (vyperCallOutcome$take_create_outcome kind v code s) with scopes := sc)
Proof
  rpt gen_tac >> Cases_on `s.outcomes` >>
  simp[vyperCallOutcomeTheory.take_create_outcome_def,
       vyperCallOutcomeTheory.create_outcome_request_def,
       pairTheory.UNCURRY, evaluation_state_fupdcanon] >>
  Cases_on `x` >> simp[] >>
  IF_CASES_TAC >> simp[evaluation_state_fupdcanon]
QED

Theorem intcall_args_create_oracle_scope[local]:
  !salt v code rof s sc. create_oracle_result salt v code rof (s with scopes := sc) =
    (FST (create_oracle_result salt v code rof s),
     SND (create_oracle_result salt v code rof s) with scopes := sc)
Proof
  rpt gen_tac >>
  simp_tac bool_ss [vyperCreateTheory.create_oracle_result_def,
                    intcall_args_take_create_scope] >>
  qabbrev_tac `result = vyperCallOutcome$take_create_outcome
     (case salt of NONE => extCallOracle$CreateCall | SOME ss => extCallOracle$Create2Call ss)
     v code s` >>
  namedCases_on `result` ["res st"] >> namedCases_on `res` ["out", "ex"] >>
  simp[] >>
  PairCases_on `out` >> simp[intcall_args_call_outcome_scope] >>
  rpt (IF_CASES_TAC >> simp[])
QED

Theorem intcall_args_eval_create_scope[local]:
  !cx kind hs rof tys vs size s sc. eval_create cx kind hs rof tys vs size
      (s with scopes := sc) =
    (FST (eval_create cx kind hs rof tys vs size s),
     SND (eval_create cx kind hs rof tys vs size s) with scopes := sc)
Proof
  simp_tac bool_ss [vyperCreateTheory.eval_create_def, ignore_bind_def, LET_THM,
                    pairTheory.ELIM_UNCURRY] >>
  intcall_args_scope_steps
    [vyperCreateTheory.create_soft_failure_def, intcall_args_create_oracle_scope]
QED

Theorem intcall_args_create_operands_scope[local]:
  !cx kind hs rof tys offset vs s sc.
    eval_create_operands cx kind hs rof tys offset vs (s with scopes := sc) =
    (FST (eval_create_operands cx kind hs rof tys offset vs s),
     SND (eval_create_operands cx kind hs rof tys offset vs s) with scopes := sc)
Proof
  rpt gen_tac >> Cases_on `kind` >>
  simp_tac bool_ss
    [vyperCreateTheory.eval_create_operands_def, LET_THM, vyperCreateTheory.create_kind_CASE_rator,
     vyperCreateTheory.check_create_blueprint_def] >>
  intcall_args_scope_steps [intcall_args_eval_create_scope]
QED

Theorem intcall_args_read_result_scope_action[local]:
  (!id path. r <> PlaceR (MemoryPlace id path)) ==>
  !cx s sc. read_result cx r (s with scopes := sc) =
    (FST (read_result cx r s),SND (read_result cx r s) with scopes := sc)
Proof
  Cases_on `r` >> simp[read_result_def, return_def, raise_def] >>
  strip_tac >> drule intcall_args_read_place_scope_action >>
  simp[pairTheory.UNCURRY]
QED

Theorem intcall_args_place_type_scope_action[local]:
  (!id path. p <> MemoryPlace id path) ==>
  !cx s sc. place_type_value cx p (s with scopes := sc) =
    (FST (place_type_value cx p s),SND (place_type_value cx p s) with scopes := sc)
Proof
  Cases_on `p` >> simp[place_type_value_def, return_def] >>
  rpt strip_tac >>
  simp[get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, lift_option_type_def, return_def, raise_def])
QED

Theorem intcall_args_conditional_result_scope_action:
  (!id path. r <> PlaceR (MemoryPlace id path)) ==>
  !cx s sc. conditional_result cx r (s with scopes := sc) =
    (FST (conditional_result cx r s),
     SND (conditional_result cx r s) with scopes := sc)
Proof
  Cases_on `r` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def] >>
  (gen_tac >> irule intcall_args_scope_bind >> reverse conj_tac
   >- (irule intcall_args_place_type_scope_action >> simp[]) >>
   rpt gen_tac >> disch_tac >> BETA_TAC >>
   irule intcall_args_scope_bind >> reverse conj_tac
   >- simp[intcall_args_read_place_scope_action, pairTheory.UNCURRY] >>
   simp[return_def])
QED

Theorem intcall_args_conditional_result_nonlocal:
  (!id path. r <> PlaceR (MemoryPlace id path)) /\
  conditional_result cx r s = (INL r',t) ==>
  (!id path. r' <> PlaceR (MemoryPlace id path))
Proof
  rpt strip_tac >> Cases_on `r` >>
  gvs[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  gvs[conditional_result_def, bind_def, return_def, AllCaseEqs()]
QED

Theorem intcall_args_result_array_length_scope_action:
  (!id path. r <> PlaceR (MemoryPlace id path)) ==>
  !cx s sc. result_array_length cx r (s with scopes := sc) =
    (FST (result_array_length cx r s),
     SND (result_array_length cx r s) with scopes := sc)
Proof
  strip_tac >> gen_tac >>
  qabbrev_tac `k = \v. case v of
      ArrayV (DynArrayV vs) => return (LENGTH vs)
    | ArrayV (SArrayV vs) => return (LENGTH vs)
    | ArrayV (TupleV vs) => return (LENGTH vs)
    | BytesV bs => return (LENGTH bs)
    | StringV bs => return (LENGTH bs)
    | _ => raise (Error (TypeError "result_array_length"))` >>
  `!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !s sc. bind (read_result cx r) k (s with scopes := sc) =
      (FST (bind (read_result cx r) k s),
       SND (bind (read_result cx r) k s) with scopes := sc)` by
    (gen_tac >> strip_tac >> irule intcall_args_scope_bind >> reverse conj_tac
     >- (irule intcall_args_read_result_scope_action >> simp[]) >>
     rpt gen_tac >> disch_tac >> simp[Abbr `k`] >>
     Cases_on `v` >> simp[return_def, raise_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[return_def]) >>
  fs[Abbr `k`] >>
  Cases_on `r` >> simp[result_array_length_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >> gvs[result_array_length_def] >>
  rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
  simp[result_array_length_def] >> rename1 `ArrayTV etv bd` >> Cases_on `bd` >>
  simp[result_array_length_def, return_def] >> Cases_on `tr` >>
  simp[get_storage_backend_def, get_accounts_def, get_transient_storage_def,
       bind_def, return_def]
QED

Theorem intcall_args_extend_storage_scope_action[local]:
  !cx tr slot tv sb s sc.
    extend_storage_place cx tr slot tv sb (s with scopes := sc) =
      (FST (extend_storage_place cx tr slot tv sb s),
       SND (extend_storage_place cx tr slot tv sb s) with scopes := sc)
Proof
  recInduct extend_storage_place_ind >> rpt strip_tac >>
  simp[extend_storage_place_def, raise_def]
  >- (simp[bind_def, lift_option_type_def] >>
      Cases_on `struct_field_slot fields id` >>
      simp[return_def, raise_def] >> Cases_on `x` >> simp[return_def])
  >- (Cases_on `bd` >> Cases_on `tr` >>
      simp[resolve_array_element_def,
           vyperStoragePlaceProvenanceTheory.resolve_array_element_empty,
           get_storage_backend_def,
           get_accounts_def, get_transient_storage_def, check_def,
           assert_def, ignore_bind_def, bind_def, return_def, raise_def] >>
      rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def]) >>
  simp[check_def, assert_def, ignore_bind_def, bind_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt IF_CASES_TAC >> simp[] >> Cases_on `oEL (Num i) tvs` >>
  simp[return_def, raise_def]
QED

Theorem intcall_args_extend_place_scope_action:
  (!id path. r <> PlaceR (MemoryPlace id path)) ==>
  !cx sb s sc. extend_place cx r sb (s with scopes := sc) =
    (FST (extend_place cx r sb s),
     SND (extend_place cx r sb s) with scopes := sc)
Proof
  Cases_on `r` >> simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >> simp[extend_place_def]
      >- (rpt gen_tac >> irule intcall_args_scope_bind >> reverse conj_tac
          >- simp[intcall_args_extend_storage_scope_action] >>
          simp[return_def]) >>
      rpt gen_tac >> irule intcall_args_scope_bind >> reverse conj_tac
      >- (irule intcall_args_place_type_scope_action >> simp[]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- simp[intcall_args_read_place_scope_action, pairTheory.UNCURRY] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      simp[ignore_bind_def, lift_sum_def, bind_def, return_def, raise_def] >>
      Cases_on `evaluate_subscripts v v' [sb]` >> simp[return_def, raise_def]) >>
  rpt gen_tac >> Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `v` >> simp[return_def, lift_option_type_def, bind_def,
    ignore_bind_def, record_storage_event_def] >>
  Cases_on `evaluate_type (get_tenv cx) t'` >> simp[return_def, raise_def]
QED

Theorem intcall_args_select_result_scope_action:
  (!id path. r <> PlaceR (MemoryPlace id path)) ==>
  !cx ty sb s sc. select_result cx ty r sb (s with scopes := sc) =
    (FST (select_result cx ty r sb s),
     SND (select_result cx ty r sb s) with scopes := sc)
Proof
  Cases_on `r` >> simp[select_result_def,
    intcall_args_extend_place_scope_action] >>
  rpt gen_tac >> simp[lift_option_type_def, bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty` >>
  simp[return_def, raise_def, lift_sum_def, bind_def] >>
  Cases_on `evaluate_subscripts x v [sb]` >> simp[return_def, raise_def]
QED

Theorem intcall_args_select_result_nonlocal:
  (!id path. r <> PlaceR (MemoryPlace id path)) /\
  select_result cx ty r sb s = (INL r',t) ==>
  (!id path. r' <> PlaceR (MemoryPlace id path))
Proof
  metis_tac[exprSimPropsTheory.select_result_memory_place]
QED

(* The support induction keeps success nonlocality alongside scope action. *)
Theorem intcall_args_nonlocal_base_scope[local]:
  !bt cx. (!id. base_target_root bt <> NameTarget id) /\
  (!e. MEM e (target_indices bt) ==>
    (!s sc. eval_expr cx e (s with scopes := sc) =
       (FST (eval_expr cx e s),SND (eval_expr cx e s) with scopes := sc)) /\
    (!s r t. eval_expr cx e s = (INL r,t) ==>
       !id path. r <> PlaceR (MemoryPlace id path))) ==>
  (!s sc. eval_base_place cx bt (s with scopes := sc) =
     (FST (eval_base_place cx bt s),SND (eval_base_place cx bt s) with scopes := sc)) /\
  (!s r t. eval_base_place cx bt s = (INL r,t) ==>
     !id path. r <> PlaceR (MemoryPlace id path))
Proof
  recInduct constSubstCorrectTheory.base_target_root_ind >>
  simp[constSubstCorrectTheory.base_target_root_def,
       supportedExprsTheory.target_indices_def] >>
  rpt conj_tac >> rpt gen_tac
  >~ [`eval_base_place _ (TopLevelNameTarget _)`]
  >- (rename1 `TopLevelNameTarget key` >> PairCases_on `key` >>
      simp[evaluate_def, vyperLookupStorageScopesTheory.lookup_global_with_scopes] >>
      conj_tac >- (rpt gen_tac >> Cases_on `lookup_global cx key0 key1 s` >> simp[]) >>
      metis_tac[vyperLocalAccessFrameTheory.lookup_global_not_memory]) >>
  disch_tac >> gen_tac >> disch_then (CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_assum `!cx. _ ==> (!s sc. eval_base_place _ _ _ = _) /\ _`
    (qspec_then `cx` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rpt conj_tac
  >- (pure_rewrite_tac[evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_extend_place_scope_action >> metis_tac[])
  >- (gvs[evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      drule vyperLocalAccessFrameTheory.extend_place_memory_origin >> metis_tac[])
  >- (qpat_assum `!e'. MEM e' _ \/ e' = e ==> _` (qspec_then `e` mp_tac) >>
      simp[NoAsms] >> disch_then (CONJUNCTS_THEN ASSUME_TAC) >>
      pure_rewrite_tac[evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_extend_place_scope_action >> metis_tac[]) >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      drule vyperLocalAccessFrameTheory.extend_place_memory_origin >> metis_tac[]
QED

Theorem intcall_args_nonlocal_pop_scope[local]:
  !place. (!id path. place <> MemoryPlace id path) ==>
  (!s sc. pop_place cx place (s with scopes := sc) =
     (FST (pop_place cx place s),SND (pop_place cx place s) with scopes := sc)) /\
  (!s r t. pop_place cx place s = (INL r,t) ==>
     !id path. r <> PlaceR (MemoryPlace id path))
Proof
  gen_tac >> Cases_on `place` >> simp[]
  >- (rename1 `StoragePlace tr slot tv` >>
      Cases_on `tv` >> simp[pop_place_def, raise_def] >>
      rename1 `ArrayTV _ bound` >> Cases_on `bound` >>
      Cases_on `tr` >> Cases_on `cx.txn.is_static` >>
      simp[pop_place_def, get_storage_backend_def, get_transient_storage_def,
           get_accounts_def, write_storage_slot_def, set_storage_backend_def,
           update_transient_def, update_accounts_def, check_def, assert_def,
           lift_option_type_def, bind_def, ignore_bind_def, return_def, raise_def,
           vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator] >>
      rpt conj_tac >> rpt gen_tac >>
      rpt (BasicProvers.FULL_CASE_TAC >>
           gvs[bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
               evaluation_state_fupdcanon]) >> rpt strip_tac >> gvs[]) >>
  simp[pop_place_def, bind_def, get_immutables_def, get_address_immutables_def,
       set_immutable_def, set_address_immutables_def, lift_option_type_def, lift_sum_def,
       ignore_bind_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
           evaluation_state_fupdcanon]) >> rpt strip_tac >> gvs[]
QED

Theorem intcall_args_target_indices_typed[local]:
  !bt env. IS_SOME (type_place_target env bt) ==>
    !e. MEM e (target_indices bt) ==> well_typed_expr env e
Proof
  recInduct constSubstCorrectTheory.base_target_root_ind >>
  simp[optionTheory.IS_SOME_EXISTS, supportedExprsTheory.target_indices_def,
       vyperTypeEnvTheory.type_place_target_AttributeTarget,
       vyperTypeEnvTheory.type_place_target_SubscriptTarget] >>
  metis_tac[]
QED

Theorem intcall_args_scope_eval_exprs[local]:
  !es. (!e. MEM e es ==>
    (!s sc. eval_expr cx e (s with scopes := sc) =
      (FST (eval_expr cx e s),SND (eval_expr cx e s) with scopes := sc)) /\
    (!s r t. eval_expr cx e s = (INL r,t) ==>
      !id path. r <> PlaceR (MemoryPlace id path))) ==>
  !s sc. eval_exprs cx es (s with scopes := sc) =
    (FST (eval_exprs cx es s),SND (eval_exprs cx es s) with scopes := sc)
Proof
  Induct >> simp[evaluate_def, return_def] >>
  strip_tac >> strip_tac >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (irule intcall_args_read_result_scope_action >>
      qpat_x_assum `!e. _ ==> _` (qspec_then `h` mp_tac) >>
      simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (first_x_assum irule >> gen_tac >> disch_tac >>
      qpat_assum `!e. e = h \/ MEM e es ==> _` (qspec_then `e` mp_tac) >>
      simp[]) >>
  simp[return_def]
QED

Theorem intcall_args_lock_scope[local]:
  (!s sc. lock_if_nr cx nr is_view (s with scopes := sc) =
    (FST (lock_if_nr cx nr is_view s),SND (lock_if_nr cx nr is_view s) with scopes := sc)) /\
  (!s sc. unlock_if_nr cx nr is_view (s with scopes := sc) =
    (FST (unlock_if_nr cx nr is_view s),SND (unlock_if_nr cx nr is_view s) with scopes := sc))
Proof
  Cases_on `nr` >> Cases_on `is_view` >> simp[lock_if_nr_def, unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def, raise_def] >>
  simp[acquire_nonreentrant_lock_def, release_nonreentrant_lock_def,
       ignore_bind_def, bind_def, get_transient_storage_def, update_transient_def,
       record_storage_event_def, return_def, raise_def,
       check_not_static_def, check_def, assert_def, COND_RATOR] >>
  rpt gen_tac >> rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, update_transient_def,
       assert_def, evaluation_state_fupdcanon] >> gvs[]
QED

Theorem intcall_args_defaults_scope_reset[local]:
  !a s sc. finally (ignore_bind (set_scopes [FEMPTY]) a) (set_scopes sc)
        s =
    (FST (a (s with scopes := [FEMPTY])),
     SND (a (s with scopes := [FEMPTY])) with scopes := sc)
Proof
  rpt gen_tac >> simp[ignore_bind_def, bind_def, set_scopes_def, finally_def, return_def] >>
  namedCases_on `a (s with scopes := [FEMPTY])` ["res st"] >> Cases_on `res` >>
  simp[ignore_bind_def, bind_def, set_scopes_def, return_def, raise_def]
QED

Theorem intcall_args_scope_cleanup[local]:
  (!s sc. cleanup (s with scopes := sc) =
    (FST (cleanup s),SND (cleanup s) with scopes := sc)) ==>
  !act s from to.
    finally_unless_halt (finally act (set_scopes to)) cleanup s =
    (FST (finally_unless_halt (finally act (set_scopes from)) cleanup s),
     SND (finally_unless_halt (finally act (set_scopes from)) cleanup s)
         with scopes := to)
Proof
  strip_tac >> rpt gen_tac >>
  simp[finally_unless_halt_def, finally_def, set_scopes_def,
       ignore_bind_def, bind_def, return_def, raise_def] >>
  namedCases_on `act s` ["res st"] >> Cases_on `res` >> simp[] >>
  simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  namedCases_on `cleanup st` ["ans endst"] >> Cases_on `ans` >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def])
QED

Theorem intcall_args_internal_scope[local]:
  (!s sc. eval_exprs cx es (s with scopes := sc) =
    (FST (eval_exprs cx es s),SND (eval_exprs cx es s) with scopes := sc)) ==>
  (!s sc. eval_expr cx (Call ty (IntCall (src,nm)) es dflt) (s with scopes := sc) =
    (FST (eval_expr cx (Call ty (IntCall (src,nm)) es dflt) s),
     SND (eval_expr cx (Call ty (IntCall (src,nm)) es dflt) s) with scopes := sc)) /\
  (!s r t. eval_expr cx (Call ty (IntCall (src,nm)) es dflt) s = (INL r,t) ==>
    !id path. r <> PlaceR (MemoryPlace id path))
Proof
  strip_tac >> simp_tac bool_ss [evaluate_def, LET_THM, ignore_bind_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[bind_def, return_def, AllCaseEqs()]) >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- simp[type_check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (Cases_on `get_module_code cx src` >> simp[lift_option_type_def,return_def,raise_def]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (Cases_on `lookup_callable_function cx.in_deploy nm v'` >>
      simp[lift_option_type_def,return_def,raise_def]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- simp[type_check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  rename1 `lift_option_type (lookup_callable_function _ _ _) _ _ = (INL info,_)` >>
  rename1 `eval_exprs cx es _ = (INL actuals,_)` >>
  PairCases_on `info` >>
  rpt gen_tac >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
       get_scopes_def, bind_def, return_def,
       REWRITE_RULE [ignore_bind_def] intcall_args_defaults_scope_reset] >>
  qabbrev_tac `dv = eval_exprs (cx with stk updated_by CONS (src,nm))
    (DROP (LENGTH info3 - (LENGTH info2 - LENGTH es)) info3)
    (s with scopes := [FEMPTY])` >>
  namedCases_on `dv` ["dres dst"] >>
  Cases_on `dres` >> simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  Cases_on `bind_arguments (get_tenv cx) info2 (actuals ++ x)` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
       lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) info4` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", return_def, raise_def,
       cj 1 intcall_args_lock_scope] >>
  namedCases_on `lock_if_nr cx info1 (info0 = View \/ info0 = Pure) dst`
    ["lres locked"] >>
  Cases_on `lres` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", push_function_def,
       return_def, pop_function_def] >>
  qabbrev_tac `act = try
    (bind (eval_stmts (cx with stk updated_by CONS (src,nm)) info5)
          (\x. return NoneV)) handle_function` >>
  qabbrev_tac `unlock = unlock_if_nr cx info1 (info0 = View \/ info0 = Pure)` >>
  `!s sc. unlock (s with scopes := sc) =
    (FST (unlock s),SND (unlock s) with scopes := sc)` by
    simp[Abbr `unlock`, Excl "unlock_if_nr_def", cj 2 intcall_args_lock_scope] >>
  drule_then
    (qspecl_then [`act`, `locked with scopes := [x']`, `s.scopes`, `sc`] mp_tac)
    intcall_args_scope_cleanup >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  disch_then (fn th => PURE_REWRITE_TAC[th]) >>
  namedCases_on `finally_unless_halt (finally act (set_scopes s.scopes))
    unlock (locked with scopes := [x'])` ["res st"] >>
  Cases_on `res` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  rename1 `finally_unless_halt _ _ _ = (INL returned,st)` >>
  Cases_on `safe_cast x'' returned` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"]
QED

Theorem intcall_args_defaults_scope_with_code_addr[local]:
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx s sc. conditional_result cx r (s with scopes := sc) =
      (FST (conditional_result cx r s),
       SND (conditional_result cx r s) with scopes := sc)) /\
  (!r cx s r' t. (!id path. r <> PlaceR (MemoryPlace id path)) /\
    conditional_result cx r s = (INL r',t) ==>
    !id path. r' <> PlaceR (MemoryPlace id path)) /\
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx s sc. result_array_length cx r (s with scopes := sc) =
      (FST (result_array_length cx r s),
       SND (result_array_length cx r s) with scopes := sc)) /\
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx ty sb s sc. select_result cx ty r sb (s with scopes := sc) =
      (FST (select_result cx ty r sb s),
       SND (select_result cx ty r sb s) with scopes := sc)) /\
  (!r cx ty sb s r' t. (!id path. r <> PlaceR (MemoryPlace id path)) /\
    select_result cx ty r sb s = (INL r',t) ==>
    !id path. r' <> PlaceR (MemoryPlace id path)) ==>
  (!tops e. supported_pure_expr tops e ==>
    !tenv. well_typed_expr (defaults_env tenv) e ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path)) /\
      (!ct addr. e = Builtin ct (Acc Code) [addr] ==>
        (!s sc. eval_expr cx addr (s with scopes := sc) =
          (FST (eval_expr cx addr s),SND (eval_expr cx addr s) with scopes := sc)) /\
        (!s r t. eval_expr cx addr s = (INL r,t) ==>
          !id path. r <> PlaceR (MemoryPlace id path)))) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!tenv. well_typed_exprs (defaults_env tenv) es ==> !cx s sc.
      eval_exprs cx es (s with scopes := sc) =
        (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with scopes := sc)) /\
    (!e. MEM e es ==> !tenv. well_typed_expr (defaults_env tenv) e ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path)) /\
      (!ct addr. e = Builtin ct (Acc Code) [addr] ==>
        (!s sc. eval_expr cx addr (s with scopes := sc) =
          (FST (eval_expr cx addr s),SND (eval_expr cx addr s) with scopes := sc)) /\
        (!s r t. eval_expr cx addr s = (INL r,t) ==>
          !id path. r <> PlaceR (MemoryPlace id path))))) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !tenv. well_typed_named_exprs (defaults_env tenv) fields ==> !cx s sc.
      eval_exprs cx (MAP SND fields) (s with scopes := sc) =
        (FST (eval_exprs cx (MAP SND fields) s),
         SND (eval_exprs cx (MAP SND fields) s) with scopes := sc)) /\
  (!tops e. supported_place_expr tops e ==>
    !tenv. (well_typed_expr (defaults_env tenv) e \/
      ?vt. type_place_expr (defaults_env tenv) e = SOME vt) ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path)))
Proof
  strip_tac >> ho_match_mp_tac supportedExprsTheory.supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[supportedExprsTheory.supported_pure_expr_def]
  >- simp[cj 1 well_typed_expr_def, defaults_env_def]
  >- simp[cj 33 evaluate_def, return_def]
  >- suspend "global"
  >- (PairCases_on `id` >>
      simp[cj 31 evaluate_def, lookup_flag_mem_def] >> rpt strip_tac >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >- suspend "ifexp"
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "pop"
  >- suspend "call"
  >- simp[cj 30 well_typed_expr_def, cj 49 evaluate_def, return_def]
  >- suspend "cons"
  >- simp[cj 34 well_typed_expr_def, cj 49 evaluate_def, return_def]
  >- suspend "fields_cons"
  >- simp[cj 1 well_typed_expr_def, defaults_env_def, well_typed_expr_def]
  >- suspend "place_global"
  >- suspend "place_subscript"
  >> suspend "place_rest"
QED

Resume intcall_args_defaults_scope_with_code_addr[global]:
  PairCases_on `id` >> disch_tac >> gen_tac >> disch_tac >> gen_tac >>
  conj_tac
  >- (rpt gen_tac >> simp[cj 30 evaluate_def,
        vyperLookupStorageScopesTheory.lookup_global_with_scopes] >>
      Cases_on `lookup_global cx id0 id1 s` >> simp[]) >>
  simp[cj 30 evaluate_def] >>
  metis_tac[vyperLocalAccessFrameTheory.lookup_global_not_memory]
QED
Resume intcall_args_defaults_scope_with_code_addr[ifexp]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 4 well_typed_expr_def] >> strip_tac >> gen_tac >> gvs[] >>
  ntac 3 (first_x_assum
    (drule_all_then (qspec_then `cx` strip_assume_tac))) >>
  conj_tac
  >- (pure_rewrite_tac[cj 32 evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (rewrite_tac[switch_BoolV_def] >>
          irule intcall_args_scope_bind >> reverse conj_tac
          >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
          rpt gen_tac >> disch_tac >> BETA_TAC >>
          rpt IF_CASES_TAC >> simp[raise_def]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      gvs[switch_BoolV_def, bind_def, AllCaseEqs(), COND_RATOR, raise_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  gvs[cj 32 evaluate_def, switch_BoolV_def, bind_def, AllCaseEqs(),
      COND_RATOR, raise_def] >> metis_tac[]
QED
Resume intcall_args_defaults_scope_with_code_addr[structlit]:
  PairCases_on `id` >> strip_tac >> strip_tac >> gen_tac >>
  simp[cj 6 well_typed_expr_def] >> strip_tac >> gen_tac >> gvs[] >>
  first_x_assum (drule_all_then assume_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      gvs[cj 34 evaluate_def, bind_def, return_def, AllCaseEqs()]) >>
  pure_rewrite_tac[cj 34 evaluate_def, LET_THM] >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  simp[return_def]
QED
Resume intcall_args_defaults_scope_with_code_addr[subscript]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 7 well_typed_expr_def] >> strip_tac >> gen_tac >> gvs[] >>
  qpat_x_assum `!tenv. _ \/ _ ==> _` (qspec_then `tenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  first_x_assum (drule_all_then (qspec_then `cx` strip_assume_tac)) >>
  (conj_tac
  >- (pure_rewrite_tac[cj 35 evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (IF_CASES_TAC >> simp[return_def] >>
          irule intcall_args_scope_bind >> reverse conj_tac
          >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
          simp[return_def]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      gvs[bind_def, AllCaseEqs(), COND_RATOR, return_def] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[cj 35 evaluate_def, bind_def, AllCaseEqs(), COND_RATOR, return_def]
  >- (qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `select_result _ _ ibaser _ _` >>
      `!j p. ibaser <> PlaceR (MemoryPlace j p)` by simp[Abbr `ibaser`] >>
      qpat_x_assum `!j p. ibaser <> _` mp_tac >>
      qpat_x_assum `!r cx ty sb s r' t.
        _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (`!j p. res <> PlaceR (MemoryPlace j p)` by metis_tac[] >>
      qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
      qpat_x_assum `!j p. res <> _` mp_tac >>
      qpat_x_assum `!r cx ty sb s r' t.
        _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]))
QED
Resume intcall_args_defaults_scope_with_code_addr[attribute]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 8 well_typed_expr_def] >> strip_tac >> gen_tac >> gvs[] >>
  qpat_x_assum `!tenv. _ \/ _ ==> _` (qspec_then `tenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  (conj_tac
   >- (pure_rewrite_tac[cj 36 evaluate_def] >>
       irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
       rpt gen_tac >> disch_tac >> BETA_TAC >> metis_tac[]) >>
   rpt strip_tac >>
   gvs[cj 36 evaluate_def, bind_def, AllCaseEqs()] >>
   `!j p. res <> PlaceR (MemoryPlace j p)` by metis_tac[] >>
   qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
   qpat_x_assum `!j p. res <> _` mp_tac >>
   qpat_x_assum `!r cx ty sb s r' t.
     _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
QED
Resume intcall_args_defaults_scope_with_code_addr[pop]:
  strip_tac >> strip_tac >> gen_tac >> disch_tac >> gen_tac >>
  sg `IS_SOME (type_place_target (defaults_env tenv) target)`
  >- (irule constSubstCorrectTheory.typed_pop_target >>
      first_assum (irule_at Any)) >>
  sg `!id. base_target_root target <> NameTarget id`
  >- (drule constSubstCorrectTheory.type_place_target_root >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `IS_SOME (type_place_target _ (NameTarget _))` mp_tac >>
      simp[Once well_typed_expr_def, defaults_env_def]) >>
  sg `(!s sc. eval_base_place cx target (s with scopes := sc) =
     (FST (eval_base_place cx target s),SND (eval_base_place cx target s) with scopes := sc)) /\
    (!s r t. eval_base_place cx target s = (INL r,t) ==>
     !id path. r <> PlaceR (MemoryPlace id path))`
  >- (irule intcall_args_nonlocal_base_scope >>
      rpt strip_tac >> gvs[EVERY_MEM] >>
      metis_tac[intcall_args_target_indices_typed]) >>
  simp_tac bool_ss [evaluate_def, bind_assoc] >>
  conj_tac
  >- (irule intcall_args_scope_bind >> reverse conj_tac
      >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      Cases_on `v` >> simp[get_place_def, bind_def, return_def, raise_def] >>
      mp_tac (Q.SPEC `p` intcall_args_nonlocal_pop_scope) >>
      impl_tac >- (first_x_assum drule >> simp[]) >>
      simp[]) >>
  rpt gen_tac >> simp[bind_def] >>
  namedCases_on `eval_base_place cx target s` ["res st"] >>
  namedCases_on `res` ["v", "err"] >> simp[] >>
  Cases_on `v` >> simp[get_place_def, bind_def, return_def, raise_def] >>
  mp_tac (Q.SPEC `p` intcall_args_nonlocal_pop_scope) >>
  impl_tac >- (first_x_assum drule >> simp[]) >>
  strip_tac >> disch_tac >> first_x_assum drule >> simp[]
QED

Resume intcall_args_defaults_scope_with_code_addr[builtin]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 9 well_typed_expr_def] >> strip_tac >> gen_tac >>
  CONV_TAC (REWR_CONV CONJ_ASSOC) >>
  reverse conj_tac
  >- (gen_tac >> strip_tac >> gvs[supportedExprsTheory.supported_pure_expr_def,
                                 Once well_typed_expr_def] >>
      sg `well_typed_expr (defaults_env tenv) addr`
      >- metis_tac[exprSimSourceTheory.well_typed_exprs_member, MEM] >>
      qpat_x_assum `!tenv'. well_typed_expr (defaults_env tenv') addr ==> _`
        (qspec_then `tenv` mp_tac) >> simp[] >>
      disch_then (qspec_then `cx` strip_assume_tac) >> simp[]) >>
  qpat_x_assum `supported_pure_exprs _ es ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!tenv. well_typed_exprs _ es ==> _`
    (drule_then (qspec_then `cx` assume_tac)) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      gvs[cj 37 evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()]) >>
  pure_rewrite_tac[cj 37 evaluate_def, ignore_bind_def] >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- simp[type_check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (Cases_on `blt = Len` >> simp[]
      >- (gvs[well_typed_builtin_app_def] >>
          `MEM (HD es) es` by (Cases_on `es` >> gvs[]) >>
          `well_typed_expr (defaults_env tenv) (HD es)` by
            metis_tac[exprSimSourceTheory.well_typed_exprs_member] >>
          qpat_x_assum `!e. MEM e es ==> _` drule >>
          disch_then (drule_all_then (qspec_then `cx` strip_assume_tac)) >>
          irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
          rpt gen_tac >> disch_tac >> BETA_TAC >>
          irule intcall_args_scope_bind >> reverse conj_tac
          >- metis_tac[] >> simp[return_def]) >>
      Cases_on `blt = Env MsgGas` >> simp[]
      >- (rpt gen_tac >> simp[next_gas_reading_def] >>
          Cases_on `s.gas_obs` >> simp[return_def, raise_def]) >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (Cases_on `code_slice_source blt es` >- simp[] >>
          PairCases_on `x` >> simp[] >>
          qpat_x_assum `code_slice_source _ _ = SOME _` mp_tac >>
          rw[code_slice_source_SOME] >> suspend "code_slice_args") >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      simp[get_accounts_def, lift_sum_def, bind_def, return_def] >>
      rpt gen_tac >> Cases_on `is_self_codesize blt es`
      >- (Cases_on `v'`
          >| [ALL_TAC, Cases_on `h` >> Cases_on `t''`] >>
          (simp[vyperContextTheory.is_self_codesize_def,
                   vyperContextTheory.evaluate_self_codesize_def,
                   bind_def, return_def, raise_def, get_accounts_def,
                   lift_sum_def, precompile_call_success_def, check_def,
                   assert_def, evaluation_state_component_equality] >>
              rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def] >>
              Cases_on `s.outcomes` >> simp[bind_def, return_def, raise_def] >>
              TRY (Cases_on `x`) >> simp[bind_def, return_def, raise_def] >>
              TRY (Cases_on `x'`) >> simp[bind_def, return_def, raise_def] >>
              rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def] >>
              simp[vyperCallOutcomeTheory.take_call_outcome_def,
                   vyperCallOutcomeTheory.take_request_outcome_def,
                   vyperCallOutcomeTheory.call_outcome_request_def] >>
              rpt (pairarg_tac >> gs[]) >>
              Cases_on `outcome.co_success` >>
              simp[assert_def, return_def, raise_def,
                   evaluation_state_component_equality]))
      >- (Cases_on `evaluate_builtin cx s.accounts ty blt (MAP expr_type es) v'` >>
          simp[return_def, raise_def] >>
          simp[precompile_call_success_def, check_def, assert_def,
               bind_def, return_def, raise_def] >>
          rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def] >>
          Cases_on `s.outcomes` >> simp[bind_def, return_def, raise_def] >>
          TRY (Cases_on `x'`) >> simp[bind_def, return_def, raise_def] >>
          rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def] >>
          simp[vyperCallOutcomeTheory.take_call_outcome_def,
               vyperCallOutcomeTheory.take_request_outcome_def,
               vyperCallOutcomeTheory.call_outcome_request_def] >>
          rpt (pairarg_tac >> gs[]) >>
          Cases_on `outcome.co_success` >>
          simp[assert_def, return_def, raise_def,
               evaluation_state_component_equality])) >>
  simp[return_def]
QED

Resume intcall_args_defaults_scope_with_code_addr[typebuiltin]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 10 well_typed_expr_def] >> strip_tac >> gen_tac >> gvs[] >>
  first_x_assum (drule_all_then assume_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      gvs[cj 39 evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()]) >>
  pure_rewrite_tac[cj 39 evaluate_def, ignore_bind_def] >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- simp[type_check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  simp[lift_sum_def, bind_def, return_def] >>
  Cases_on `evaluate_type_builtin cx blt target (MAP expr_type es) v'` >>
  simp[return_def, raise_def]
QED
Resume intcall_args_defaults_scope_with_code_addr[cons]:
  strip_tac >> strip_tac >> gvs[] >> reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[Once well_typed_expr_def] >> strip_tac >> gen_tac >>
  qpat_x_assum `!tenv. well_typed_expr _ e ==> _`
    (drule_all_then (qspec_then `cx` strip_assume_tac)) >>
  first_x_assum (drule_all_then assume_tac) >>
  pure_rewrite_tac[cj 50 evaluate_def] >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  simp[return_def]
QED
Resume intcall_args_defaults_scope_with_code_addr[fields_cons]:
  strip_tac >> strip_tac >> gvs[] >>
  gen_tac >> simp[Once well_typed_expr_def] >> strip_tac >> gen_tac >>
  qpat_x_assum `!tenv. well_typed_expr _ e ==> _`
    (drule_all_then (qspec_then `cx` strip_assume_tac)) >>
  first_x_assum (drule_all_then assume_tac) >>
  pure_rewrite_tac[cj 50 evaluate_def] >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
  simp[return_def]
QED
Resume intcall_args_defaults_scope_with_code_addr[place_global]:
  PairCases_on `id` >> disch_tac >> gen_tac >> disch_tac >> gen_tac >>
  conj_tac
  >- (rpt gen_tac >> simp[cj 30 evaluate_def,
        vyperLookupStorageScopesTheory.lookup_global_with_scopes] >>
      Cases_on `lookup_global cx id0 id1 s` >> simp[]) >>
  simp[cj 30 evaluate_def] >>
  metis_tac[vyperLocalAccessFrameTheory.lookup_global_not_memory]
QED
Resume intcall_args_defaults_scope_with_code_addr[place_subscript]:
  strip_tac >> strip_tac >> gen_tac >>
  simp[cj 7 well_typed_expr_def] >>
  simp[Once well_typed_expr_def] >> strip_tac >> gen_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `!tenv. _ \/ _ ==> _` (qspec_then `tenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  first_x_assum (drule_all_then (qspec_then `cx` strip_assume_tac)) >>
  (conj_tac
  >- (pure_rewrite_tac[cj 35 evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (IF_CASES_TAC >> simp[return_def] >>
          irule intcall_args_scope_bind >> reverse conj_tac
          >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
          simp[return_def]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      irule intcall_args_scope_bind >> reverse conj_tac
      >- (irule intcall_args_read_result_scope_action >> metis_tac[]) >>
      rpt gen_tac >> disch_tac >> BETA_TAC >>
      gvs[bind_def, AllCaseEqs(), COND_RATOR, return_def] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[cj 35 evaluate_def, bind_def, AllCaseEqs(), COND_RATOR, return_def]
  >- (qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `select_result _ _ ibaser _ _` >>
      `!j p. ibaser <> PlaceR (MemoryPlace j p)` by simp[Abbr `ibaser`] >>
      qpat_x_assum `!j p. ibaser <> _` mp_tac >>
      qpat_x_assum `!r cx ty sb s r' t.
        _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (`!j p. res <> PlaceR (MemoryPlace j p)` by metis_tac[] >>
      qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
      qpat_x_assum `!j p. res <> _` mp_tac >>
      qpat_x_assum `!r cx ty sb s r' t.
        _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]))
QED
Resume intcall_args_defaults_scope_with_code_addr[place_rest]:
  markerLib.RESUME_TAC >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  fs[] >>
  TRY (qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
    simp[Once well_typed_expr_def] >> NO_TAC) >>
  TRY (qpat_x_assum `!tenv. well_typed_expr _ _ ==> _`
    (drule_all_then (qspec_then `cx` ACCEPT_TAC)) >> NO_TAC)
  >>~- ([`eval_expr cx (Builtin _ _ _)`],
    qpat_x_assum `!tenv. well_typed_expr _ (Builtin _ _ _) ==> _`
      (drule_all_then (qspec_then `cx` (fn th =>
        ACCEPT_TAC (CONJ (cj 1 th) (cj 2 th))))) )
  >>~- ([`eval_expr cx (Call _ _ _ _)`],
    qpat_x_assum `!tenv. well_typed_expr _ (Call _ _ _ _) ==> _`
      (drule_all_then (qspec_then `cx` ACCEPT_TAC))) >>
  gvs[cj 8 well_typed_expr_def] >>
  qpat_x_assum `!tenv. _ \/ _ ==> _` (qspec_then `tenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  conj_tac
  >- (pure_rewrite_tac[cj 36 evaluate_def] >>
      irule intcall_args_scope_bind >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> BETA_TAC >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[cj 36 evaluate_def, bind_def, AllCaseEqs()] >>
  `!j p. res <> PlaceR (MemoryPlace j p)` by metis_tac[] >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `!j p. res <> _` mp_tac >>
  qpat_x_assum `!r cx ty sb s r' t.
    _ /\ select_result cx ty r sb s = (INL r',t) ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED
Resume intcall_args_defaults_scope_with_code_addr[code_slice_args]:
  simp_tac bool_ss [TL] >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (irule intcall_args_scope_eval_exprs >>
      gen_tac >> strip_tac >>
      qpat_assum `!e. MEM e _ ==> !tenv. _` (qspec_then `e` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `tenv` mp_tac) >>
      impl_tac >- metis_tac[exprSimSourceTheory.well_typed_exprs_member, MEM] >>
      disch_then (qspec_then `cx` (fn th => ACCEPT_TAC (CONJ (cj 1 th) (cj 2 th))))) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- (irule intcall_args_scope_eval_exprs >> simp[] >>
      qpat_assum `!e. MEM e _ ==> !tenv. _`
        (qspec_then `Builtin x0 (Acc Code) [x1]` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `tenv` mp_tac) >>
      impl_tac >- metis_tac[exprSimSourceTheory.well_typed_exprs_member, MEM] >>
      disch_then (qspec_then `cx` (fn th => ACCEPT_TAC (CONJ (cj 3 th) (cj 4 th))))) >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule intcall_args_scope_bind >> reverse conj_tac
  >- simp[get_accounts_def, return_def] >>
  rpt gen_tac >> disch_tac >> BETA_TAC >>
  rpt gen_tac >> simp[lift_sum_def, bind_def, return_def, vyperMiscTheory.sum_CASE_rator] >>
  BasicProvers.FULL_CASE_TAC >> simp[bind_def, return_def, raise_def]
QED

Resume intcall_args_defaults_scope_with_code_addr[call]:
  strip_tac >> strip_tac >> gen_tac >> disch_tac >> gen_tac >>
  sg `well_typed_exprs (defaults_env tenv) es`
  >- (qpat_x_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
      Cases_on `target` >> simp[Once well_typed_expr_def]
      >- (rename1 `IntCall key` >> PairCases_on `key` >>
          simp[Once well_typed_expr_def])
      >> rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >>
      simp[Once well_typed_expr_def]) >>
  qpat_x_assum `supported_pure_exprs _ es ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!tenv. well_typed_exprs _ es ==> _`
    (drule_then (qspec_then `cx` assume_tac)) >>
  `!ds. (!e. MEM e ds ==> MEM e es) ==>
    !s sc. eval_exprs cx ds (s with scopes := sc) =
      (FST (eval_exprs cx ds s),SND (eval_exprs cx ds s) with scopes := sc)` by
    (gen_tac >> strip_tac >> irule intcall_args_scope_eval_exprs >>
     gen_tac >> strip_tac >>
     qpat_assum `!e. MEM e es ==> !tenv. _` (qspec_then `e` mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (qspec_then `tenv` mp_tac) >>
     (impl_tac >- metis_tac[exprSimSourceTheory.well_typed_exprs_member]) >>
     disch_then (qspec_then `cx` (fn th => ACCEPT_TAC (CONJ (cj 1 th) (cj 2 th))))) >>
  Cases_on `target`
  >>~- ([`eval_expr cx (Call _ RawLog _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def, LET_THM] >>
    reverse conj_tac >- (rpt strip_tac >> gvs[bind_def, return_def, AllCaseEqs()]) >>
    irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> disch_tac >> BETA_TAC >>
    rpt gen_tac >> Cases_on `LENGTH v = 2` >>
    simp[type_check_def, assert_def, bind_def, return_def, raise_def] >>
    Cases_on `dest_ArrayV (HD v)` >>
    simp[lift_option_type_def, bind_def, return_def, raise_def] >>
    Cases_on `dest_BytesV (EL 1 v)` >>
    simp[lift_option_type_def, bind_def, return_def, raise_def] >>
    Cases_on `x` >> Cases_on `cx.txn.is_static` >>
    simp[type_check_def, assert_def, bind_def, push_log_def, return_def, raise_def,
         evaluation_state_fupdcanon] >>
    IF_CASES_TAC >> simp[return_def, raise_def, bind_def, push_log_def,
                        evaluation_state_fupdcanon])
  >>~- ([`eval_expr cx (Call _ RawRevert _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def] >>
    reverse conj_tac >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()]) >>
    irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> disch_tac >> BETA_TAC >>
    simp[type_check_def, assert_def, lift_option_type_def, bind_def,
         vyperMiscTheory.option_CASE_rator, COND_RATOR, return_def, raise_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def]))
  >>~- ([`eval_expr cx (Call _ SelfDestructTarget _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def, LET_THM] >>
    reverse conj_tac >-
      (rpt strip_tac >>
       gvs[bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()]) >>
    irule intcall_args_scope_bind >> reverse conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> disch_tac >> BETA_TAC >>
    rpt gen_tac >>
    Cases_on `LENGTH v = 1` >>
    simp[type_check_def, assert_def, bind_def, return_def, raise_def] >>
    Cases_on `dest_AddressV (HD v)` >>
    simp[lift_option_type_def, bind_def, check_not_static_def, check_def,
         assert_def, return_def, raise_def] >>
    Cases_on `cx.txn.is_static` >>
    simp[check_def, assert_def, bind_def, return_def, raise_def, get_accounts_def,
         transfer_value_def, ignore_bind_def] >>
    Cases_on `cx.txn.created_in_tx` >>
    simp[COND_RATOR, bind_def, return_def, raise_def, check_def, assert_def,
         get_accounts_def, update_accounts_def, update_pending_deletions_def,
         evaluation_state_fupdcanon] >>
    rpt (IF_CASES_TAC >> simp[]))
  >>~- ([`eval_expr cx (Call _ (RawCallTarget _) _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def] >>
    reverse conj_tac
    >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
        drule vyperCallFrameTheory.eval_raw_call_success_value >> simp[]) >>
    intcall_args_scope_steps [intcall_args_eval_raw_call_scope])
  >>~- ([`eval_expr cx (Call _ (RawCallCalldataTarget _) _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def] >>
    reverse conj_tac
    >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
        drule vyperCallFrameTheory.eval_raw_call_success_value >> simp[]) >>
    intcall_args_scope_steps [intcall_args_eval_raw_call_scope])
  >>~- ([`eval_expr cx (Call _ (IntCall _) _ _)`],
    rename1 `IntCall key` >> PairCases_on `key` >>
    irule intcall_args_internal_scope >> first_assum ACCEPT_TAC)
  >>~- ([`eval_expr cx (Call _ (Send _) _ _)`],
    simp_tac bool_ss [evaluate_def, ignore_bind_def] >>
    reverse conj_tac
    >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
        drule vyperCallFrameTheory.eval_send_success_value >> simp[]) >>
    intcall_args_scope_steps [intcall_args_eval_send_scope])
  >>~- ([`eval_expr cx (Call _ (ExtCall _ _ _ _) _ _)`],
    simp_tac bool_ss [evaluate_def, LET_THM] >>
    reverse conj_tac
    >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
        drule vyperCallFrameTheory.eval_ext_call_success_value >> simp[]) >>
    ntac 3
      (ho_match_mp_tac intcall_args_scope_bind >> conj_tac
       >- (first_assum irule >> metis_tac[rich_listTheory.MEM_TAKE, rich_listTheory.MEM_DROP_IMP]) >>
       rpt gen_tac >> disch_tac >> BETA_TAC) >>
    simp[intcall_args_eval_ext_call_scope])
  >>~- ([`eval_expr cx (Call _ (CreateTarget _ _ _ _) _ _)`],
    simp_tac bool_ss [evaluate_def] >>
    reverse conj_tac
    >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
        drule vyperLocalAccessFrameTheory.eval_create_operands_success_value >> simp[]) >>
    rename1 `CreateTarget kind hs rof arg_tys` >>
    irule intcall_args_scope_bind >> reverse conj_tac
    >- (first_assum irule >> POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `es` >- simp[vyperCreateTheory.create_operand_order_def] >>
        rename1 `create_operand_order _ _ (operand::operands)` >>
        Cases_on `operands` >> Cases_on `kind` >>
        gvs[vyperCreateTheory.create_operand_order_def, MEM_APPEND] >>
        metis_tac[rich_listTheory.MEM_TAKE, rich_listTheory.MEM_DROP_IMP, MEM]) >>
    simp[intcall_args_create_operands_scope])
QED

Finalise intcall_args_defaults_scope_with_code_addr

Theorem intcall_args_defaults_scope_mutual_from_actions:
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx s sc. conditional_result cx r (s with scopes := sc) =
      (FST (conditional_result cx r s),
       SND (conditional_result cx r s) with scopes := sc)) /\
  (!r cx s r' t. (!id path. r <> PlaceR (MemoryPlace id path)) /\
    conditional_result cx r s = (INL r',t) ==>
    !id path. r' <> PlaceR (MemoryPlace id path)) /\
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx s sc. result_array_length cx r (s with scopes := sc) =
      (FST (result_array_length cx r s),
       SND (result_array_length cx r s) with scopes := sc)) /\
  (!r. (!id path. r <> PlaceR (MemoryPlace id path)) ==>
    !cx ty sb s sc. select_result cx ty r sb (s with scopes := sc) =
      (FST (select_result cx ty r sb s),
       SND (select_result cx ty r sb s) with scopes := sc)) /\
  (!r cx ty sb s r' t. (!id path. r <> PlaceR (MemoryPlace id path)) /\
    select_result cx ty r sb s = (INL r',t) ==>
    !id path. r' <> PlaceR (MemoryPlace id path)) ==>
  (!tops e. supported_pure_expr tops e ==>
    !tenv. well_typed_expr (defaults_env tenv) e ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path))) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!tenv. well_typed_exprs (defaults_env tenv) es ==> !cx s sc.
      eval_exprs cx es (s with scopes := sc) =
        (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with scopes := sc)) /\
    (!e. MEM e es ==> !tenv. well_typed_expr (defaults_env tenv) e ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path)))) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !tenv. well_typed_named_exprs (defaults_env tenv) fields ==> !cx s sc.
      eval_exprs cx (MAP SND fields) (s with scopes := sc) =
        (FST (eval_exprs cx (MAP SND fields) s),
         SND (eval_exprs cx (MAP SND fields) s) with scopes := sc)) /\
  (!tops e. supported_place_expr tops e ==>
    !tenv. (well_typed_expr (defaults_env tenv) e \/
      ?vt. type_place_expr (defaults_env tenv) e = SOME vt) ==> !cx.
      (!s sc. eval_expr cx e (s with scopes := sc) =
        (FST (eval_expr cx e s), SND (eval_expr cx e s) with scopes := sc)) /\
      (!s r t. eval_expr cx e s = (INL r,t) ==>
        !id path. r <> PlaceR (MemoryPlace id path)))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac intcall_args_defaults_scope_with_code_addr >>
  rpt conj_tac
  >- (rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >> gen_tac >>
      qpat_assum `!tops e. supported_pure_expr tops e ==> _`
        (drule_then (qspec_then `tenv` mp_tac)) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qspec_then `cx` (fn th => ACCEPT_TAC (CONJ (cj 1 th) (cj 2 th)))))
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!tops es. supported_pure_exprs tops es ==> _`
        (drule_then strip_assume_tac) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> disch_tac >> gen_tac >> disch_tac >> gen_tac >>
      qpat_assum `!e. MEM e es ==> _`
        (drule_then (qspec_then `tenv` mp_tac)) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qspec_then `cx` (fn th => ACCEPT_TAC (CONJ (cj 1 th) (cj 2 th))))) >>
  first_assum ACCEPT_TAC
QED

Theorem intcall_args_defaults_scope_action[local]:
  supported_pure_exprs tops ds /\ well_typed_exprs (defaults_env tenv) ds ==>
  !cx s scopes. eval_exprs cx ds (s with scopes := scopes) =
    (FST (eval_exprs cx ds s),SND (eval_exprs cx ds s) with scopes := scopes)
Proof
  strip_tac >> mp_tac (cj 2 intcall_args_defaults_scope_mutual_from_actions) >>
  simp[intcall_args_conditional_result_scope_action,
       intcall_args_conditional_result_nonlocal,
       intcall_args_result_array_length_scope_action,
       intcall_args_select_result_scope_action,
       intcall_args_select_result_nonlocal] >>
  (impl_tac >- (conj_tac
    >- metis_tac[intcall_args_conditional_result_nonlocal] >>
    metis_tac[intcall_args_select_result_nonlocal])) >>
  disch_then (qspecl_then [`tops`,`ds`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!tenv. well_typed_exprs _ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED

(* Lock acquisition precedes push_function.  Only its successful endpoint
   commutes with the scope update; failures retain the original scopes. *)
Theorem intcall_args_lock_push_success:
  lock_if_nr cx nr (is_view_mut mut) st = (INL (),locked) ==>
  bind (lock_if_nr cx nr (is_view_mut mut))
    (\u. bind (push_function (NONE,name) penv cx)
      (\cxf. bind
        (finally_unless_halt
          (finally
            (try (bind (eval_stmts cxf ss) (\u. return NoneV))
                 handle_function)
            (pop_function prev))
          (unlock_if_nr cx nr (is_view_mut mut)))
        (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                   (\crv. return (Value crv))))) st =
  intcall_rest cx name mut nr ss prev rtv (st with scopes := [penv])
Proof
  strip_tac >>
  `lock_if_nr cx nr (is_view_mut mut) (st with scopes := [penv]) =
   (INL (), locked with scopes := [penv])` by
    (qpat_x_assum `lock_if_nr _ _ _ st = _` mp_tac >>
     Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
     simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
       get_transient_storage_def, update_transient_def,
       record_storage_event_def, return_def, raise_def,
       check_not_static_def, check_def, assert_def, COND_RATOR] >>
     rpt IF_CASES_TAC >>
     simp[bind_def, return_def, raise_def, update_transient_def,
          assert_def] >>
     Cases_on `is_view_mut mut` >> simp[] >> rpt strip_tac >> gvs[]) >>
  pure_rewrite_tac[intcall_rest_def, ignore_bind_def] >>
  pure_asm_rewrite_tac[bind_def] >>
  simp[bind_def, push_function_def, return_def]
QED

Theorem intcall_args_aggregate_physical_type_mods[local]:
  expr_body_pre_mods mods cenv cx tenv e esi /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) (expr_type e) dty ==>
  vv_type vv = lowered_value_type cenv e
Proof
  strip_tac >>
  `well_typed_expr tenv e /\
   (!id t. FLOOKUP tenv.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
    (fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
     rpt strip_tac >> first_assum (irule_at Any) >> simp[]) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type cenv e` by
    (drule_all compile_expr_reason_uniform >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum (qspec_then `expr_type e` strip_assume_tac) >>
     first_x_assum drule >> Cases_on `vv` >>
     gvs[reason_result_shape_def, vv_type_def] >> metis_tac[]) >>
  Cases_on `lowered_value_type cenv e = expr_type e` >- gvs[] >>
  `~is_bytestring_type (expr_type e)` by metis_tac[type_widens_from_bytestring] >>
  `(?n s. e = Literal (BaseT (StringT n)) (StringL s)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) \/
   (?ty n args. e = Builtin ty (Concat n) args) \/
   (?ann ensure method_id tys args.
      e = TypeBuiltin ann (AbiEncode ensure method_id) tys args) \/
   (?ann fid args dret. e = Call ann (IntCall fid) args dret)` by
    (qpat_x_assum `lowered_value_type cenv e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def]
     >~ [`Literal t l`]
     >- (Cases_on `t` >> simp[lowered_value_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         Cases_on `l` >> simp[lowered_value_type_def] >>
         rename1 `BytesT bound` >> Cases_on `bound` >>
         simp[lowered_value_type_def])
     >~ [`Builtin t b l`]
     >- (Cases_on `b = NamedConst`
         >- (gvs[] >>
             qpat_x_assum `~is_bytestring_type (expr_type (Builtin _ NamedConst _))`
               mp_tac >>
             Cases_on `t` >> simp[expr_type_def, is_bytestring_type_def] >>
             TRY (rename1 `~is_bytestring_type (BaseT bt) ==> _` >>
                  Cases_on `bt` >> simp[is_bytestring_type_def]) >>
             TRY (rename1 `~is_bytestring_type (BaseT (BytesT bound)) ==> _` >>
                  Cases_on `bound` >> simp[is_bytestring_type_def]) >>
             simp[Once (oneline lowered_value_type_def), expr_type_def] >>
             rpt (BasicProvers.TOP_CASE_TAC >> simp[expr_type_def])) >>
         Cases_on `b` >> fs[lowered_value_type_def])
     >~ [`TypeBuiltin ann tb tys args`]
     >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
     rename1 `Call ann target args dret` >> Cases_on `target` >>
     simp[lowered_value_type_def]) >>
  pop_assum mp_tac >> strip_tac >> gvs[expr_type_def, is_bytestring_type_def]
  >- gvs[well_typed_expr_def, well_typed_builtin_app_def, is_bytestring_type_def]
  >- gvs[well_typed_expr_def, type_builtin_result_ok_def, is_bytestring_type_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[compile_expr_call] >> strip_tac >>
  drule reason_compile_call >> Cases_on `vv` >>
  gvs[reason_result_shape_def, vv_type_def]
QED

(* Defaults retain the caller frame and erase only their recursive table entry. *)
Theorem intcall_args_defaults_body_inv[local]:
  body_inv tops ctx ce cx ==>
  body_inv tops ctx (cenv_without_defaults ce name)
    (cx with stk updated_by CONS (NONE,name))
Proof
  simp[bodySimTheory.body_inv_split_def,
       bodyInvSplitTheory.contract_inv_def, bodyInvSplitTheory.module_body_inv_def,
       bodySimTheory.cenv_module_pins_split_def, bodyInvSplitTheory.cenv_module_pins_mods_def,
       bodyInvSplitTheory.immutable_section_layout_mods_def,
       cenv_without_defaults_def, vyperContextTheory.get_tenv_def,
       alistTheory.ALOOKUP_def, alistTheory.ALOOKUP_FILTER, nsid_to_string_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> fs[]
QED

Theorem intcall_args_defaults_inv[local]:
  expr_sim_inv ce cx env st ==>
  expr_sim_inv (cenv_without_defaults ce name)
    (cx with stk updated_by CONS (NONE,name)) (env with current_src := NONE) st
Proof
  `functions_well_typed (cx with stk updated_by CONS (NONE,name)) =
   functions_well_typed cx` by
    simp[vyperTypeInvariantsTheory.functions_well_typed_def,
         vyperTypeInvariantsTheory.fn_sigs_consistent_def,
         vyperTypeInvariantsTheory.fn_sigs_declared_complete_def,
         vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
         vyperTypeInvariantsTheory.bare_globals_complete_def,
         vyperTypeInvariantsTheory.bare_global_assignable_complete_def,
         vyperTypeInvariantsTheory.flag_members_complete_def,
         vyperContextTheory.get_module_code_def,
         vyperContextTheory.get_tenv_def] >>
  `env_consistent env cx st ==>
   env_consistent (env with current_src := NONE)
      (cx with stk updated_by CONS (NONE,name)) st` by
    (simp[vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_context_consistent_def,
         vyperTypeInvariantsTheory.env_scopes_consistent_def,
         vyperTypeInvariantsTheory.env_immutables_consistent_def,
         vyperTypeInvariantsTheory.fn_sigs_consistent_def,
         vyperTypeInvariantsTheory.fn_sigs_declared_complete_def,
         vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
         vyperTypeInvariantsTheory.bare_globals_complete_def,
         vyperTypeInvariantsTheory.bare_global_assignable_complete_def,
         vyperTypeInvariantsTheory.flag_members_complete_def,
         vyperContextTheory.get_module_code_def,
         vyperContextTheory.get_tenv_def,
         vyperContextTheory.current_module_def] >>
     strip_tac >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!src. get_module_code (cx with stk updated_by CONS (NONE,name)) src =
         get_module_code cx src` by simp[vyperContextTheory.get_module_code_def] >>
  `get_tenv (cx with stk updated_by CONS (NONE,name)) = get_tenv cx` by
    simp[vyperContextTheory.get_tenv_def] >>
  `context_well_typed (cx with stk updated_by CONS (NONE,name)) =
   context_well_typed cx` by simp[vyperTypeInvariantsTheory.context_well_typed_def] >>
  `place_map_tables_agree_on_defined (cenv_without_defaults ce name)
      (env with current_src := NONE) = place_map_tables_agree_on_defined ce env` by
    (match_mp_tac placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >>
     simp[cenv_without_defaults_def]) >>
  pure_rewrite_tac[expr_sim_inv_def] >> strip_tac >> rpt conj_tac >>
  TRY (simp[cenv_without_defaults_def] >> first_assum ACCEPT_TAC) >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (first_assum irule >> first_assum ACCEPT_TAC)
  >- (`cx_tops (cx with stk updated_by CONS (NONE,name)) = cx_tops cx` by
        simp[gasContextTheory.cx_tops_def] >>
      qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
        mp_tac >> simp[cenv_without_defaults_def, cx_const_name_def] >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_x_assum `bare_globals_layout _ _ _ _ cx _ _` mp_tac >>
  simp[cenv_without_defaults_def, bare_globals_layout_def] >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED

val local_default_pop =
  ``\e. ?ty bt id. e = Pop ty bt /\ base_target_root bt = NameTarget id``;

Theorem intcall_args_typed_no_local_pop[local]:
  (!env e. well_typed_expr env e ==> env.var_types = FEMPTY ==>
     ~supported_expr_exists ^local_default_pop e) /\
  (!env e vt. type_place_expr env e = SOME vt ==> env.var_types = FEMPTY ==>
     ~supported_expr_exists ^local_default_pop e) /\
  (!env bt vt. type_place_target env bt = SOME vt ==> env.var_types = FEMPTY ==>
     ~supported_target_exists ^local_default_pop bt) /\
  (!env es. well_typed_exprs env es ==> env.var_types = FEMPTY ==>
     ~supported_exprs_exists ^local_default_pop es) /\
  (!env opt. well_typed_opt env opt ==> env.var_types = FEMPTY ==>
     ~supported_opt_exists ^local_default_pop opt) /\
  (!env kes. well_typed_named_exprs env kes ==> env.var_types = FEMPTY ==>
     ~supported_fields_exists ^local_default_pop kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, supportedExprTraverseTheory.supported_expr_exists_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> gvs[] >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule constSubstCorrectTheory.type_place_target_root >>
  gvs[optionTheory.IS_SOME_EXISTS, Once well_typed_expr_def]
QED

Theorem intcall_args_target_overlap_frame[local]:
  c'.ce_struct_fields = c.ce_struct_fields /\
  c'.ce_modules = c.ce_modules /\
  c'.ce_hashmap_info = c.ce_hashmap_info /\
  c'.ce_module_var_type = c.ce_module_var_type ==>
  !bt idx. (!id. base_target_root bt <> NameTarget id) ==>
      target_subscript_overlap c' bt idx = target_subscript_overlap c bt idx
Proof
  strip_tac >>
  `!bt. (!id. base_target_root bt <> NameTarget id) ==>
      target_place_type c' bt = target_place_type c bt` by
    (recInduct constSubstCorrectTheory.base_target_root_ind >>
     simp[constSubstCorrectTheory.base_target_root_def,
                    allocLimitsTheory.target_place_type_def]) >>
  `!bt. (!id. base_target_root bt <> NameTarget id) ==>
      target_through_dynarray c' bt = target_through_dynarray c bt` by
    (recInduct constSubstCorrectTheory.base_target_root_ind >>
     simp[constSubstCorrectTheory.base_target_root_def,
                    allocLimitsTheory.target_through_dynarray_def]) >>
  simp[allocLimitsTheory.target_subscript_overlap_def]
QED

Theorem intcall_args_extcode_no_local_pop[local]:
  !es. es <> [] /\ is_extcode (HD es) /\
       ~supported_exprs_exists ^local_default_pop es ==>
       ~supported_exprs_exists ^local_default_pop (extcode_addr_expr (HD es) :: TL es)
Proof
  Cases >> simp[] >> rename1 `is_extcode h` >>
  Cases_on `h` >> simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `Builtin _ b l` >> Cases_on `b` >>
  simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >>
  simp[exprLoweringTheory.is_extcode_def] >>
  Cases_on `l` >> simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `_ :: tl` >> Cases_on `tl` >>
  simp[exprLoweringTheory.is_extcode_def, exprLoweringTheory.extcode_addr_expr_def,
       supportedExprTraverseTheory.supported_expr_exists_def]
QED

val default_alloc_fields =
  ``c'.ce_struct_fields = c.ce_struct_fields /\
    c'.ce_func_return_type = c.ce_func_return_type /\
    c'.ce_modules = c.ce_modules /\
    c'.ce_hashmap_info = c.ce_hashmap_info /\
    c'.ce_module_var_type = c.ce_module_var_type /\
    c'.ce_module_vars = c.ce_module_vars``;

Theorem intcall_args_pure_alloc_mutual[local]:
  (!c e c'. ^default_alloc_fields ==>
         ~supported_expr_exists ^local_default_pop e ==>
         alloc_limits_expr c' e = alloc_limits_expr c e) /\
  (!c bt c'. ^default_alloc_fields ==>
         (!id. base_target_root bt <> NameTarget id) /\
         ~supported_target_exists ^local_default_pop bt ==>
         alloc_limits_target c' bt = alloc_limits_target c bt) /\
  (!c es c'. ^default_alloc_fields ==>
         ~supported_exprs_exists ^local_default_pop es ==>
         alloc_limits_exprs c' es = alloc_limits_exprs c es) /\
  (!c de c'. ^default_alloc_fields ==>
         ~supported_opt_exists ^local_default_pop de ==>
         alloc_limits_opt c' de = alloc_limits_opt c de) /\
  (!c kes c'. ^default_alloc_fields ==>
         ~supported_fields_exists ^local_default_pop kes ==>
         alloc_limits_named_exprs c' kes = alloc_limits_named_exprs c kes)
Proof
  ho_match_mp_tac allocLimitsTheory.alloc_limits_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  drule compileEnvTheory.type_memory_bytes_frame >> strip_tac >>
  drule allocLimitsPropsTheory.ext_call_alloc_ok_struct_fields >> strip_tac >>
  qmatch_asmsub_rename_tac `updated.ce_struct_fields = original.ce_struct_fields` >>
  mp_tac (Q.INST [`c'` |-> `updated`, `c` |-> `original`]
             intcall_args_target_overlap_frame) >>
  simp[] >> strip_tac >>
  `lowered_value_type updated = lowered_value_type original` by
    (simp[FUN_EQ_THM] >> metis_tac[allocLimitsPropsTheory.lowered_value_type_struct_fields]) >>
  `type_alloc_ok updated = type_alloc_ok original` by
    simp[FUN_EQ_THM, allocLimitsTheory.type_alloc_ok_def] >>
  `array_slot_base updated = array_slot_base original` by
    metis_tac[allocLimitsPropsTheory.array_slot_base_frame] >>
  gvs[allocLimitsTheory.alloc_limits_expr_def, allocLimitsTheory.type_alloc_ok_def,
       exprLoweringTheory.copies_subscript_base_def,
       supportedExprTraverseTheory.supported_expr_exists_def, constSubstCorrectTheory.base_target_root_def] >>
  TRY COND_CASES_TAC >> gvs[] >>
  metis_tac[intcall_args_extcode_no_local_pop]
QED

Theorem intcall_args_pure_allocs_frame:
  ^default_alloc_fields /\ well_typed_exprs (defaults_env env) ds ==>
  alloc_limits_exprs c' ds = alloc_limits_exprs c ds
Proof
  strip_tac >>
  drule (cj 4 intcall_args_typed_no_local_pop) >>
  simp[defaults_env_def] >> strip_tac >>
  irule (cj 3 intcall_args_pure_alloc_mutual) >> simp[]
QED

Theorem intcall_args_defaults_alloc_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  MEM (src,(mut,nr,rr,name,args,defaults,ret,ss))
    (FST (SND (classify_functions_unit mods exps))) /\
  well_typed_exprs (defaults_env env) (DROP k defaults) ==>
  alloc_limits_exprs (cenv_without_defaults cenv key) (DROP k defaults)
Proof
  strip_tac >>
  drule_all_then assume_tac intCallAllocationPropsTheory.contract_inv_internal_allocs >>
  qabbrev_tac `fn_env = build_compile_env_unit mods src Internal mut name args ret ss F` >>
  `alloc_limits_exprs fn_env defaults` by
    fs[fn_allocs_ok_unit_def, GSYM markerTheory.Abbrev_def] >>
  `!ds skipped. alloc_limits_exprs fn_env ds ==> alloc_limits_exprs fn_env (DROP skipped ds)` by
    (Induct >> simp[allocLimitsTheory.alloc_limits_expr_def] >>
     gen_tac >> qx_gen_tac `skipped` >> Cases_on `skipped` >>
     fs[allocLimitsTheory.alloc_limits_expr_def]) >>
  `alloc_limits_exprs (cenv_without_defaults cenv key) (DROP k defaults) =
   alloc_limits_exprs fn_env (DROP k defaults)` suffices_by
    (disch_then SUBST1_TAC >> simp[]) >>
  irule intcall_args_pure_allocs_frame >>
  fs[bodyInvSplitTheory.contract_inv_def, bodyInvSplitTheory.cenv_module_pins_mods_def,
     cenv_without_defaults_def, Abbr `fn_env`, build_compile_env_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_assum (irule_at Any)
QED

Theorem intcall_args_defaults_alloc[local]:
  body_inv tops ctx cenv cx /\
  well_typed_exprs (defaults_env env) (subst_consts_exprs (module_consts_env tops []) dflts) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  alloc_limits_exprs (cenv_without_defaults cenv name)
    (DROP k (subst_consts_exprs (module_consts_env tops []) dflts))
Proof
  strip_tac >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_then (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def])
    intcall_args_classified_singleton >>
  irule intcall_args_defaults_alloc_mods >>
  qpat_assum `MEM (NONE,_) (FST (SND (classify_functions_unit _ _)))` (irule_at Any) >>
  qpat_assum `contract_inv [(NONE,tops)] [] ctx cenv cx` (irule_at Any) >>
  qexists_tac `env` >> simp[vyperTypeEvalProofsTheory.well_typed_exprs_DROP]
QED

(* Prepare defaults in caller scopes at the supplied-argument endpoint. *)
Theorem intcall_args_defaults_pre[local]:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx tenv ee /\
  well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt) /\
  call_evaluation_safe cx
    (int_calls_expr (Call ann (IntCall (NONE,name)) es dflt)) /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  dflts' = subst_consts_exprs (module_consts_env tops []) dflts /\
  well_typed_exprs (defaults_env (tenv with current_src := NONE)) dflts' /\
  supported_pure_exprs tops dflts' /\
  int_calls_exprs (DROP k dflts') = int_calls_exprs (DROP k dflts) /\
  ~supported_exprs_exists (const_name_root cx) (DROP k dflts') /\
  (!target. supported_exprs_exists (expr_abi_decode_target_root target) dflts' ==>
    supported_exprs_exists (expr_abi_decode_target_root target) dflts) ==>
  EVERY (\e. expr_body_pre (cenv_without_defaults cenv name)
      (cx with stk updated_by CONS (NONE,name))
      (tenv with current_src := NONE) e ee) (DROP k dflts')
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  `well_typed_exprs (tenv with current_src := NONE) dflts'` by
    (irule (cj 4 intcall_args_defaults_typing_mutual) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `alloc_limits_exprs (cenv_without_defaults cenv name) (DROP k dflts')` by
    (gvs[] >>
     irule intcall_args_defaults_alloc >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `MEM (FunctionDecl Internal _ _ _ _ _ _ _ _) tops` (irule_at Any) >>
     qexists_tac `tenv with current_src := NONE` >> simp[]) >>
  `expr_sim_inv (cenv_without_defaults cenv name)
     (cx with stk updated_by CONS (NONE,name))
     (tenv with current_src := NONE) ee` by
    metis_tac[intcall_args_defaults_inv] >>
  `call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
     (int_calls_exprs (DROP k dflts'))` by
    metis_tac[vyperTypeEvalProofsTheory.intcall_call_evaluation_safe_needed_defaults] >>
  simp[EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
  `MEM e dflts'` by metis_tac[rich_listTheory.MEM_DROP_IMP] >>
  `well_typed_expr (tenv with current_src := NONE) e` by
    metis_tac[exprSimSourceTheory.well_typed_exprs_member] >>
  `alloc_limits_expr (cenv_without_defaults cenv name) e` by
    metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem] >>
  `call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
     (int_calls_expr e)` by
    metis_tac[exprSimSourceTheory.call_evaluation_safe_exprs_mem] >>
  `supported_expr tops e` by
    (fs[supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[supportedExprsTheory.supported_expr_def]) >>
  `body_inv tops ctx (cenv_without_defaults cenv name)
     (cx with stk updated_by CONS (NONE,name))` by
    metis_tac[intcall_args_defaults_body_inv] >>
  `byte_widths_expr e` by
    (irule externalBodyWidthsTheory.well_typed_expr_byte_widths >>
     qexists `tenv with current_src := NONE` >> simp[] >>
     `env_consistent tenv cx ee` by gvs[expr_sim_inv_def] >>
     conj_tac
     >- metis_tac[logArgumentTypeEvalTheory.consistent_variable_type_well_formed] >>
     gvs[vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  drule_all_then strip_assume_tac bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  `~supported_expr_exists
      (const_name_root (cx with stk updated_by CONS (NONE,name))) e` by
    (`cx_tops (cx with stk updated_by CONS (NONE,name)) = cx_tops cx` by
       simp[NoAsms, cx_tops_def, vyperContextTheory.get_module_code_def] >>
     `const_name_root (cx with stk updated_by CONS (NONE,name)) = const_name_root cx` by
       (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `x` >>
        simp[const_name_root_def, pairTheory.FORALL_PROD] >>
        rename1 `cx_const_name _ nsid` >> PairCases_on `nsid` >>
        simp[cx_const_name_def]) >>
     gvs[supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  `cx_tops (cx with stk updated_by CONS (NONE,name)) = tops` by
    (drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >> simp[]) >>
  `expr_sim_inv_mods [(NONE,tops)] (cenv_without_defaults cenv name)
       (cx with stk updated_by CONS (NONE,name))
       (tenv with current_src := NONE) ee` by
    fs[expr_sim_inv_split_def] >>
  `~supported_expr_exists (unallocated_bare_global_root
       (cenv_without_defaults cenv name) (tenv with current_src := NONE)) e` by
    (irule expr_sim_inv_no_unallocated_bare_globals >>
     qexistsl_tac [`cx with stk updated_by CONS (NONE,name)`, `ee`] >>
     simp[]) >>
  `!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
       occurs_abi_decode_target target tops` by
    (simp[supportedProgramTheory.occurs_abi_decode_target_def, EXISTS_MEM] >>
     rpt strip_tac >>
     `supported_exprs_exists (expr_abi_decode_target_root target) dflts'` by
       (simp[supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
        metis_tac[]) >>
     qexists `FunctionDecl Internal mut nr rr name args dflts ret ss` >>
     simp[supportedProgramTheory.declaration_abi_decode_target_def,
          supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  `get_tenv (cx with stk updated_by CONS (NONE,name)) = get_tenv cx` by
    simp[vyperContextTheory.get_tenv_def] >>
  `get_tenv cx = type_env_all_modules [(NONE,tops)]` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP bodyInvMetadataPropsTheory.contract_inv_type_env o
        MATCH_MP bodySimTheory.body_inv_contract)) >>
  `get_module_code (cx with stk updated_by CONS (NONE,name)) NONE =
     get_module_code cx NONE` by
    simp[NoAsms, vyperContextTheory.get_module_code_def] >>
  `EVERY (\c. FST c = NONE /\
              ?ts. supported_program ts /\
                   get_module_code (cx with stk updated_by CONS (NONE,name)) NONE = SOME ts /\
                   IS_SOME (supported_function_decl ts c Internal))
     (int_calls_expr e)` by
    (simp[EVERY_MEM] >> qx_gen_tac `call` >> strip_tac >> conj_tac >>
     fs[EVERY_MEM]) >>
  fs[expr_body_pre_split_def, expr_body_pre_mods_def, GSYM source_body_calls_main,
     GSYM const_name_root_mods_singleton,
     vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def,
     finite_mapTheory.FUNION_FEMPTY_2]
QED

Theorem intcall_args_defaults_ih:
  (!s1 vs t1. ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
  ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,ee) ==>
  body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
Proof
  metis_tac[]
QED

(* A completed memory argument is protected by its full allocation, not by
   an arbitrary fixed-low memory frame.  Restrict both byte and taint frames
   to its value footprint before applying the canonical robust transport. *)
Theorem intcall_args_old_site_robust[local]:
  wb_frame cenv es ee si s t /\
  ghost_kept_at lo cenv es si G tn s G' tn' /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < si.cs_next_id /\
  (!n lb sz. local_region cenv es.scopes s n lb sz ==>
     b+cap <= lb \/ lb+sz <= b) /\
  b <= a /\ a + val_footprint rt v <= b+cap /\ val_wf rt v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt v a mem) ==>
  !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
     val_in_memory rt v a mem
Proof
  strip_tac >>
  `mem_bytes_at b cap t.vs_memory = mem_bytes_at b cap s.vs_memory` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  `mem_bytes_at a (val_footprint rt v) t.vs_memory =
   mem_bytes_at a (val_footprint rt v) s.vs_memory` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`a-b`,`val_footprint rt v`] mp_tac) >>
     simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_window_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`,`tn'.t_mem`,`val_footprint rt v`,
                `s.vs_memory`,`t.vs_memory`] >>
  simp[] >> rpt strip_tac >>
  `b <= i /\ i < b+cap` by decide_tac >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED

Theorem intcall_args_prefix_frame:
  LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
  LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
  eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
  (!j rt. j < LENGTH ops /\
     evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
     value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
     val_footprint rt (EL j vals) <= type_memory_size rt /\
     (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
       (clean_words ==> op_prov G (EL j ops) = NONE)) /\
     (~EL j pflags ==> ?b cap aid.
       op_prov G (EL j ops) = SOME (b,cap) /\
       FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
       lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
       w2n (EL j ws) + type_memory_size rt <= b+cap /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+cap <= lb \/ lb+sz <= b) /\
       (case pin of NONE => T | SOME (rb,pb,pk) =>
         b+cap <= pb \/ pb+pk <= b))) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
     lookup_var rb s = SOME (n2w b) /\
     FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
     not_fresh_at si rb /\
     (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
       b+k <= lb \/ lb+sz <= b)) /\
  wb_frame cenv esi ee si s t /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!n b k. local_region cenv esi.scopes s n b k <=>
           local_region cenv ee.scopes t n b k) /\
  (!lbl. FLOOKUP t.vs_labels lbl = FLOOKUP s.vs_labels lbl) ==>
  LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
  LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
  eval_operands ops t = SOME ws /\ EVERY (\op. op_taint tn1 op = {}) ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at sj x) /\
  (!j rt. j < LENGTH ops /\
     evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
     value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
     val_footprint rt (EL j vals) <= type_memory_size rt /\
     (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
       (clean_words ==> op_prov G1 (EL j ops) = NONE)) /\
     (~EL j pflags ==> ?b cap aid.
       op_prov G1 (EL j ops) = SOME (b,cap) /\
       FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < sj.cs_next_id /\
       lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws) /\
       w2n (EL j ws) + type_memory_size rt <= b+cap /\
       (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
       (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
         b+cap <= lb \/ lb+sz <= b) /\
       (case pin of NONE => T | SOME (rb,pb,pk) =>
         b+cap <= pb \/ pb+pk <= b))) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
     lookup_var rb t = SOME (n2w b) /\
     FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < sj.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
     not_fresh_at sj rb /\
     (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
       b+k <= lb \/ lb+sz <= b))
Proof
  strip_tac >>
  `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w` by metis_tac[wb_frame_def] >>
  `!x. not_fresh_at si x ==>
      FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
    metis_tac[ghost_kept_at_def] >>
  `!a w. MEM a ops /\ eval_operand a s = SOME w ==>
      eval_operand a t = SOME w` by
    (rpt strip_tac >> Cases_on `a` >>
     gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operands ops t = SOME ws` by
    (qpat_x_assum `eval_operands ops s = SOME ws` mp_tac >>
     qpat_x_assum `!a w. MEM a ops /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `ws` >>
     Induct_on `ops` >> simp[venomStateTheory.eval_operands_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `EVERY (\op. op_taint tn1 op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def] >>
     metis_tac[ptrDisciplineTheory.op_taint_def]) >>
  simp[] >> conj_tac
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!j rt. _` (qspecl_then [`j`,`rt`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `op_prov G1 (EL j ops) = op_prov G (EL j ops)` by
        (Cases_on `EL j ops` >>
         gvs[ptrDisciplineTheory.op_prov_def] >> metis_tac[MEM_EL]) >>
      simp[] >> strip_tac >>
      qpat_x_assum `~EL j pflags ==> _` (drule_then strip_assume_tac) >>
      `op_prov G1 (EL j ops) = SOME (b,cap)` by
        (Cases_on `EL j ops` >>
         gvs[ptrDisciplineTheory.op_prov_def] >>
         metis_tac[MEM_EL]) >>
      `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem` by
        (`w2n (EL j ws) + val_footprint rt (EL j vals) <= b+cap`
           by decide_tac >>
         metis_tac[intcall_args_old_site_robust]) >>
      qexistsl_tac [`b`,`cap`,`aid`] >>
      fs[wb_frame_def] >> metis_tac[]) >>
  Cases_on `pin` >> simp[] >>
  PairCases_on `x` >> gvs[] >>
  fs[wb_frame_def] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

(* The completed prefix and the pinned return allocation are proof data only.
   The source continuation receives just the values read by the remaining list. *)
Theorem intcall_args_locals_compose[local]:
  !cenv es es1 es2 s0 s1 s2.
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
               local_region cenv es1.scopes s1 n b sz) /\
    locals_kept cenv es es1 s0 s1 /\
    locals_kept cenv es1 es2 s1 s2 ==>
    locals_kept cenv es es2 s0 s2
Proof
  rpt gen_tac >> strip_tac >>
  fs[loweringPostsTheory.locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[vyperEvalScopesProgressTheory.scopes_progress_trans]
  >- (rpt strip_tac >>
      `?entry entry1. lookup_scopes n es.scopes = SOME entry /\
                      lookup_scopes n es1.scopes = SOME entry1` by
        (gvs[loweringStateRelDefsTheory.local_region_def] >>
         metis_tac[optionTheory.option_CASES]) >>
      `entry1 = entry` by
        (qpat_x_assum `scopes_progress es.scopes _`
           (qspecl_then [`n`, `entry`, `entry1`] mp_tac o
             SIMP_RULE std_ss [vyperEvalScopesProgressTheory.scopes_progress_def]) >>
         qpat_x_assum `scopes_progress es1.scopes _`
           (qspecl_then [`n`, `entry1`, `entry`] mp_tac o
             SIMP_RULE std_ss [vyperEvalScopesProgressTheory.scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[loweringPostsTheory.popped_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!n b sz entry' h. local_region _ es1.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz entry' h. local_region _ es.scopes _ _ _ _ /\ _ ==> _`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `n` >> fs[])
  >- simp[] >>
  metis_tac[]
QED

(* Compose the original caller frame once, for both staging branches. *)
Theorem intcall_args_frame_compose[local]:
  wb_frame cenv es0 esi sa s0 s /\
  wb_frame cenv esi mid si s t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  sa.cs_next_id <= si.cs_next_id /\
  sa.cs_next_var <= si.cs_next_var /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv esi.scopes s n b sz) ==>
  wb_frame cenv es0 mid sa s0 t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  conj_tac >-
    (fs[loweringPostsTheory.wb_frame_def] >>
     conj_tac >-
       (rpt strip_tac >> `aid < si.cs_next_id` by decide_tac >> metis_tac[]) >>
     irule intcall_args_locals_compose >>
     qexistsl [`esi`, `s`] >> simp[]) >>
  fs[bodyPtrDefsTheory.ghost_kept_at_def, loweringPostsTheory.wb_frame_def] >>
  conj_tac >-
    (rpt strip_tac >>
     `aid < si.cs_next_id` by decide_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `i IN tn.t_mem` by
       (qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
        simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
     simp[] >> disch_then irule >> rpt strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem intcall_args_read_result_prefix[local]:
  ~s.vs_halted /\
  read_result cx tv es = (INL v,es) /\
  (!x. storage_trace_frame (k x)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 (k v)
    (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (read_result cx tv) k) (es,s,G,tn) Q R
Proof
  strip_tac >>
  irule (gasOutcomeFullComposeTheory.gas_outcome_full_bind_all
    |> Q.INST [`Q1` |-> `\H res ee G1 tn1 t.
       res = INL v /\ ee = (es with gas_obs := []) /\
       G1 = G /\ tn1 = tn /\ t = s`]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`gas_outcome_full _ _ _ _ (read_result cx tv) _ _ _`]
  >- (qexists_tac `v` >> reverse conj_tac
      >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
          conj_tac >- (qexistsl_tac [`G`,`es`,`INL v`,`s`,`tn`] >>
            simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
            metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
          simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
          metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >> disj1_tac >> simp[])
  >~ [`storage_trace_frame (read_result cx tv)`]
  >- simp[storage_trace_frame_read_result]
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      metis_tac[]) >>
  rpt strip_tac >>
  irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED

(* Zero physical layout is rigid under widening.  Consequently this is the
   actual empty-copy compiler branch, with the unwrap endpoint and all of its
   allocation history and taints retained, not an independent execution. *)
Theorem intcall_args_aggregate_store_zero:
  compile_store_memory cenv op (Var aq) dty sty cu = ((),cs) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME rty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_size rty = 0 /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type dtv v /\ val_wf dtv v /\ alloca_history func z /\
  ~z.vs_halted /\ z.vs_current_bb = cu.cs_current_bb /\
  z.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK z,G',tn')) ==>
  ?wt wG wtn nw.
    nw <= MAX 32 (type_memory_bytes cenv dty) /\
    typed_copy_state_frame cu (w2n aw) nw z wt /\
    ~wt.vs_halted /\ wt.vs_current_bb = cs.cs_current_bb /\
    wt.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func wt /\
    wtn.t_stor = tn'.t_stor /\ wtn.t_trans = tn'.t_trans /\ wtn.t_imm = tn'.t_imm /\
    (!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\
      op_taint wtn (Var p) = op_taint tn' (Var p)) /\
    (!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==>
      (i IN wtn.t_mem <=> i IN tn'.t_mem)) /\
    (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
      value_has_type rt v /\ val_wf rt v /\
      type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
      (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
        val_in_memory rt v (w2n aw) mem)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK wt,wG,wtn))
Proof
  strip_tac >>
  `sty = dty` by metis_tac[wideningZeroLayoutTheory.type_widens_to_zero_layout] >>
  gvs[] >>
  `cs = cu` by
    gvs[contextTheory.compile_store_memory_def, contextPropsTheory.compile_copy_memory_zero,
        compileEnvTheory.comp_return_def] >>
  gvs[] >> qexistsl_tac [`z`, `G'`, `tn'`, `0`] >>
  simp[typedMemoryCopyTheory.typed_copy_state_frame_refl,
       valueEncodingProofsTheory.return_zero_wf_memory]
QED

(* Widen only the interpreted bytestring representation, at the same address. *)
Theorem intcall_args_bytestring_widen:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\ value_has_type stv v /\
  val_in_memory stv v a mem ==>
  value_has_type dtv v /\ val_wf dtv v /\
  type_memory_size dtv <= MAX 32 (type_memory_bytes cenv dty) /\
  val_in_memory dtv v a mem
Proof
  strip_tac >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  reverse conj_tac
  >- (irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `is_bytestring_type dty` mp_tac >>
  simp[exprSimConvertBytesTheory.bytestring_type_cases] >>
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def,
    valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
    vfmConstantsTheory.word_size_def]
QED

(* Keep the actual allocation site when the prefix moves to a later cut. *)
Theorem intcall_args_sites_snoc[local]:
  LENGTH pflags = LENGTH ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  wb_frame cenv esi ee si s t /\
  si.cs_next_id <= sj.cs_next_id /\
  (!j. j < LENGTH ops /\ ~EL j pflags ==>
    ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
      FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
      sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
      32 <= cap /\
      ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) /\
  (~flag ==> ?b cap aid. op_prov G1 op = SOME (b,cap) /\
      FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
      sa.cs_next_id <= aid /\ aid < sj.cs_next_id /\
      32 <= cap /\
      ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) ==>
  !j. j < LENGTH (ops ++ [op]) /\ ~EL j (pflags ++ [flag]) ==>
    ?b cap aid. op_prov G1 (EL j (ops ++ [op])) = SOME (b,cap) /\
      FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
      sa.cs_next_id <= aid /\ aid < sj.cs_next_id /\
      32 <= cap /\
      ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid
Proof
  strip_tac >> gen_tac >> strip_tac >> Cases_on `j < LENGTH ops`
  >- (`op_prov G1 (EL j ops) = op_prov G (EL j ops)` by
        (Cases_on `EL j ops` >> simp[ptrDisciplineTheory.op_prov_def] >>
         fs[ghost_kept_at_def] >> metis_tac[MEM_EL]) >>
      `j < LENGTH pflags` by metis_tac[] >>
      `~EL j pflags` by fs[EL_APPEND_EQN] >>
      qpat_assum `!j. j < LENGTH ops /\ ~EL j pflags ==> _`
        (drule_all_then strip_assume_tac) >>
      simp[EL_APPEND_EQN] >> qexists `aid` >>
      fs[wb_frame_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `j = LENGTH ops` by fs[] >>
  gvs[EL_APPEND_EQN] >> qexists `inst.inst_id` >> simp[] >>
  qexists `inst` >> simp[]
QED

(* Compare buffers only at ordered, distinct memory indices.  The new
   operand is the last index, so a mixed pair always has the new one second. *)
Theorem intcall_args_separate_snoc[local]:
  LENGTH pflags = LENGTH ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  (!i j b k c l. i < j /\ j < LENGTH ops /\ ~EL i pflags /\ ~EL j pflags /\
     op_prov G (EL i ops) = SOME (b,k) /\ op_prov G (EL j ops) = SOME (c,l) ==>
     regions_disjoint b k c l) /\
  (~flag ==> !i b k c l. i < LENGTH ops /\ ~EL i pflags /\
     op_prov G (EL i ops) = SOME (b,k) /\ op_prov G1 op = SOME (c,l) ==>
     regions_disjoint b k c l) ==>
  !i j b k c l. i < j /\ j < LENGTH (ops ++ [op]) /\
     ~EL i (pflags ++ [flag]) /\ ~EL j (pflags ++ [flag]) /\
     op_prov G1 (EL i (ops ++ [op])) = SOME (b,k) /\
     op_prov G1 (EL j (ops ++ [op])) = SOME (c,l) ==>
     regions_disjoint b k c l
Proof
  strip_tac >>
  `!a. a < LENGTH ops ==> op_prov G1 (EL a ops) = op_prov G (EL a ops)` by
    (rpt strip_tac >> Cases_on `EL a ops` >>
     simp[ptrDisciplineTheory.op_prov_def] >>
     fs[ghost_kept_at_def] >> metis_tac[MEM_EL]) >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH ops` by fs[] >> `i < LENGTH pflags` by metis_tac[] >>
  Cases_on `j < LENGTH ops`
  >- (`j < LENGTH pflags` by metis_tac[] >> fs[EL_APPEND_EQN] >>
      qpat_assum `!i j b k c l. _ ==> regions_disjoint b k c l`
        (qspecl_then [`i`,`j`,`b`,`k`,`c`,`l`] mp_tac) >> simp[] >>
      metis_tac[]) >>
  `j = LENGTH ops /\ j = LENGTH pflags` by fs[] >> gvs[EL_APPEND_EQN] >>
  first_x_assum irule >> simp[] >> qexists_tac `i` >> simp[] >> metis_tac[]
QED

Theorem intcall_args_stage_full_p2_with_path[local]:
  !es DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
   st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin f P Q R.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv esi /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (vyperState$bind (eval_exprs cx es) f) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (keep_sites ==> !j. j < LENGTH ops /\ ~EL j pflags ==>
       ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
         sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
         32 <= cap /\
         ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
           inst.inst_id = aid) /\
    (keep_sites ==> !i j b k c l.
       i < j /\ j < LENGTH ops /\ ~EL i pflags /\ ~EL j pflags /\
       op_prov G (EL i ops) = SOME (b,k) /\ op_prov G (EL j ops) = SOME (c,l) ==>
       regions_disjoint b k c l) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
         (clean_words ==> op_prov G (EL j ops) = NONE)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) /\
    (!marks xs ee t G1 tn1.
       (!tail. eval_exprs cx es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs, ee with gas_obs := tail)) /\
       gas_path ctx func s (LENGTH marks) (OK t) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       LENGTH xs = LENGTH es /\ expr_sim_inv cenv cx tenv ee /\
       (?ws1.
         LENGTH ws1 = LENGTH (ops ++ newops) /\
         LENGTH (vals ++ xs) = LENGTH (ops ++ newops) /\
         LENGTH (ptys ++ dtys) = LENGTH (ops ++ newops) /\
         LENGTH (pflags ++ flags) = LENGTH (ops ++ newops) /\
         eval_operands (ops ++ newops) t = SOME ws1 /\
         EVERY (\op. op_taint tn1 op = {}) (ops ++ newops) /\
         (!x. MEM (Var x) (ops ++ newops) ==> not_fresh_at sf x) /\
         (keep_sites ==> !j. j < LENGTH (ops ++ newops) /\ ~EL j (pflags ++ flags) ==>
           ?b cap aid. op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
             FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
             sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
             32 <= cap /\
             ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
               inst.inst_id = aid) /\
         (keep_sites ==> !i j b k c l.
           i < j /\ j < LENGTH (ops ++ newops) /\
           ~EL i (pflags ++ flags) /\ ~EL j (pflags ++ flags) /\
           op_prov G1 (EL i (ops ++ newops)) = SOME (b,k) /\
           op_prov G1 (EL j (ops ++ newops)) = SOME (c,l) ==>
           regions_disjoint b k c l) /\
         (!j rt. j < LENGTH (ops ++ newops) /\
           evaluate_type (get_tenv cx) (EL j (ptys ++ dtys)) = SOME rt ==>
           value_has_type rt (EL j (vals ++ xs)) /\
           val_wf rt (EL j (vals ++ xs)) /\
           val_footprint rt (EL j (vals ++ xs)) <= type_memory_size rt /\
           (EL j (pflags ++ flags) ==>
             EL j ws1 = typed_val_to_w256 rt (EL j (vals ++ xs)) /\
             (clean_words ==> op_prov G1 (EL j (ops ++ newops)) = NONE)) /\
           (~EL j (pflags ++ flags) ==>
             ?b cap aid.
               op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
               FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
               sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
               lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws1) /\
               w2n (EL j ws1) + type_memory_size rt <= b+cap /\
               (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
                 val_in_memory rt (EL j (vals ++ xs)) (w2n (EL j ws1)) mem) /\
               (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
                 b+cap <= lb \/ lb+sz <= b) /\
               (case pin of NONE => T | SOME (rb,pb,pk) =>
                 b+cap <= pb \/ pb+pk <= b)))) /\
       (case pin of NONE => T | SOME (rb,b,k) =>
         FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
         lookup_var rb t = SOME (n2w b) /\
         FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
         sa.cs_next_id < sf.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
         not_fresh_at sf rb /\
         (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
           b+k <= lb \/ lb+sz <= b)) /\
       wb_frame cenv es0 ee sa s0 t /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
       alloca_history func t /\ sa.cs_next_id <= sf.cs_next_id /\
       sa.cs_next_var <= sf.cs_next_var /\
       (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
          local_region cenv ee.scopes t n b sz) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       MAP FDOM es0.scopes = MAP FDOM ee.scopes /\
       return_buf_frame d cenv sf t /\ ~t.vs_halted /\
       t.vs_current_bb = sf.cs_current_bb /\
       t.vs_inst_idx = LENGTH sf.cs_current_insts /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
       gas_admissible (f xs) P ee ==>
       gas_outcome_full
         (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (f xs) (ee,t,G1,tn1) Q R) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (vyperState$bind (eval_exprs cx es) f) (esi,s,G,tn) Q R
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `vyperState$bind (eval_exprs cx []) f = f []` by
        (simp[FUN_EQ_THM, Once evaluate_def, bind_def, return_def]) >>
      gvs[compile_stage_intcall_args_def, comp_return_def] >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
      simp[] >> strip_tac >>
      qpat_x_assum `!marks ee t G1 tn1. _`
        (qspecl_then [`[]`,`esi`,`s`,`G`,`tn`] mp_tac) >>
      simp[Once evaluate_def, return_def, gasSummaryTheory.gas_explicit_def,
           cj 1 fragGasPathTheory.gas_path_rules] >>
      disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `ws` >> simp[])
  >> rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok cx (e::es)` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
           (CONJ inv member))))) >>
  `!res ee.
     vyperState$bind (eval_expr cx e) (\tv. read_result cx tv) esi = (res,ee) ==>
     expr_sim_inv cenv cx tenv ee /\
     EVERY (\arg. expr_body_pre cenv cx tenv arg ee) es` by
    (rpt gen_tac >> disch_tac >>
     `expr_body_pre cenv cx tenv e esi` by fs[] >>
     drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
     conj_tac >- simp[] >>
     fs[EVERY_MEM] >>
     qx_gen_tac `arg` >> strip_tac >>
     irule intcall_args_pre_state >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `esi` >> simp[] >> res_tac) >>
  namedCases_on `flags` ["", "flag flags1"] >- fs[] >>
  namedCases_on `dtys` ["", "dty dtys1"] >- fs[] >>
  Cases_on `flag`
  >- (Cases_on `compile_expr cenv (expr_type e) e si` >>
      rename1 `compile_expr cenv (expr_type e) e si = (vv,ci)` >>
      Cases_on `unwrap_value cenv vv ci` >>
      rename1 `unwrap_value cenv vv ci = (op,cu)` >>
      qpat_x_assum `compile_stage_intcall_args _ _ (e::es) _ _ si = _` mp_tac >>
      simp[Once compile_stage_intcall_args_def, comp_bind_def,
           comp_return_def] >>
      Cases_on `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cu` >>
      rename1 `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cu =
        (rest,cf)` >>
      simp[] >> strip_tac >>
      Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_si` >>
      rename1 `compile_expr _ (expr_type e) (gas_shadow_expr e) shadow_si =
        (shadow_vv,shadow_ci)` >>
      `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
         (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
        irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
      `vv = shadow_vv /\ gas_shadow_state ci shadow_ci` by
        (drule_all bodyFullSharedTheory.gas_shadow_step >>
         disch_then strip_assume_tac >> simp[]) >>
      Cases_on `unwrap_value cenv vv shadow_ci` >>
      rename1 `unwrap_value cenv vv shadow_ci = (shadow_op,shadow_cu)` >>
      `op = shadow_op /\ gas_shadow_state cu shadow_cu` by
        (qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
         mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
         simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`ci`,`shadow_ci`] mp_tac) >> simp[]) >>
      qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `compile_stage_intcall_args _ _ _ _ _ shadow_si = _` mp_tac >>
      simp[Once compile_stage_intcall_args_def, comp_bind_def,
           comp_return_def] >>
      Cases_on `compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
        (MAP gas_shadow_expr es) flags1 dtys1 shadow_cu` >>
      simp[] >> strip_tac >>
      `lower_value compile_expr cenv (expr_type e) e si = (op,cu)` by
        simp[lower_value_def, comp_bind_def] >>
      `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
         shadow_si = (op,shadow_cu)` by
        simp[lower_value_def, comp_bind_def] >>
      `cs_extends si cu` by
        (qpat_assum `lower_value _ _ _ _ si = _`
           (mp_then Any mp_tac (CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows)) >> simp[]) >>
      `cs_extends cu cf` by
        (`ci_mono cu (SND (compile_stage_intcall_args compile_expr cenv
            es flags1 dtys1 cu))` by
           (irule exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args >>
            simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
         gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      `cs_extends shadow_si shadow_cu` by
        (qpat_assum `lower_value _ _ _ _ shadow_si = _`
           (mp_then Any mp_tac (CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows)) >> simp[]) >>
      `cs_extends shadow_cu shadow_sf` by
        (`ci_mono shadow_cu (SND (compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
            (MAP gas_shadow_expr es) flags1 dtys1 shadow_cu))` by
           (irule exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args >>
            simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
         gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      `fn_has_code si cu func /\ fn_has_code shadow_si shadow_cu shadow_func` by
        (qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` kall_tac >>
         conj_tac
         >- (mp_tac (Q.SPECL [`si`,`cu`,`cf`,`func`] fn_has_code_split) >> simp[]) >>
         mp_tac (Q.SPECL [`shadow_si`,`shadow_cu`,`shadow_sf`,`shadow_func`]
           fn_has_code_split) >> simp[]) >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx))
         expr_res_ok esi` by
        (`bind (eval_exprs cx (e::es)) f =
            bind (bind (eval_expr cx e) (read_result cx))
              (\v. bind (eval_exprs cx es) (\xs. f (v::xs)))` by
           simp[vyperInterpreterTheory.evaluate_def,
                vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
         qpat_x_assum `gas_admissible _ P esi` mp_tac >>
         pop_assum SUBST1_TAC >> strip_tac >>
         irule exprSimSliceComposeTheory.slice_gas_admissible_bind_head >>
         conj_tac >- simp[exprSimDefsTheory.expr_res_ok_def] >>
         qexistsl_tac [`P`, `\v. bind (eval_exprs cx es) (\xs. f (v::xs))`] >>
         simp[] >>
         qpat_x_assum `!err. P (INR err) ==> expr_vv_res_ok (INR err)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprSimDefsTheory.expr_res_ok_def,
              exprSimDefsTheory.expr_vv_res_ok_def]) >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e esi` by
        (`body_expr_full_ok cx e` by fs[Once body_exprs_full_ok_def] >>
         `expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_x_assum `body_expr_full_ok cx e`
           (mp_tac o CONJUNCT1 o
             ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
         disch_then drule_all >> simp[]) >>
      qpat_x_assum `expr_sim_full _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspec_then `st0` mp_tac) >>
      disch_then drule >> disch_then drule >>
      simp[] >>
      disch_then (qspecl_then [`s`,`G`,`tn`] mp_tac) >>
      simp[] >> disch_then assume_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
      qpat_x_assum `_ ==> gas_outcome_full _ _ _ _ _ _ childQ childR` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `bind (eval_exprs cx (e::es)) f =
         bind (bind (eval_expr cx e) (read_result cx))
           (\v. bind (eval_exprs cx es) (\xs. f (v::xs)))` by
        simp[vyperInterpreterTheory.evaluate_def,
             vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
      pop_assum SUBST1_TAC >>
      match_mp_tac (GEN_ALL
        gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path) >>
      qexists_tac `childQ` >> BETA_TAC >>
      conj_tac
      >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR`
            (irule_at Any) >> simp[Abbr `childR`] >>
          rpt strip_tac >> namedCases_on `res` ["v", "exc"] >- fs[] >>
          qexists_tac `exc` >> simp[] >>
          qpat_assum `!H res ee gt r. expr_exit res r /\ _ /\ _ ==> R H res ee gt r`
            irule >> simp[] >>
          conj_tac
          >- (irule (iffLR (INST_TYPE [``:'a`` |-> ``:value``]
                (SPEC_ALL stmtSimPropsTheory.expr_exit_INR_type))) >> simp[]) >>
          irule (iffLR (INST_TYPE [``:'a`` |-> ``:value``]
            haltExitProjTheory.halt_exit_INR_type)) >> simp[]) >>
      reverse (rpt conj_tac)
      >- (rpt strip_tac >>
          irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
          goal_assum (drule_at Any) >> simp[])
      >- (rpt strip_tac >>
          irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
      >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame])
      >- (irule vyperStorageTraceTheory.storage_trace_frame_bind >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H _ _ _ _ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp[Abbr `childQ`, NoAsms] >> strip_tac >>
      disj1_tac >> qexists_tac `v` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      `wb_frame cenv esi mid si s t` by
        (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, wb_frame_def] >> metis_tac[]) >>
      `MAP FDOM esi.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
         imp_res_tac vyperStateTheory.read_result_state >> gvs[] >>
         drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
         simp[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         esi.storage_trace` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `valid_horizon cx st0 _ mid.storage_trace` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         drule_at Any vyperStorageFootprintTheory.valid_horizon_frame >>
         simp[vyperStorageTraceTheory.storage_trace_frame_bind,
              vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `local_ptrs_rel func cenv esi.scopes s` by
        (qpat_x_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _`
           drule >> strip_tac >>
         drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
      `!n b sz. local_region cenv esi.scopes s n b sz <=>
                  local_region cenv mid.scopes t n b sz` by
        (qpat_assum `local_ptrs_rel func cenv esi.scopes s` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s t` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[wb_frame_def] >> rpt strip_tac >> eq_tac
         >- (rw[loweringStateRelDefsTheory.local_region_def] >>
             `lookup_scopes n mid.scopes <> NONE` by
               metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                         optionTheory.NOT_SOME_NONE] >>
             `not_fresh_at si p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
         rw[loweringStateRelDefsTheory.local_region_def] >>
         `lookup_scopes n esi.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         Cases_on `lookup_scopes n esi.scopes` >> fs[] >>
         rename1 `lookup_scopes n esi.scopes = SOME entry0` >>
         `?w0. lookup_var p s = SOME w0` by
           (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
            qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         `lookup_var p t = SOME w0` by metis_tac[] >> gvs[]) >>
      `t.vs_labels = s.vs_labels` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_labels]) >>
      `ci_mono si cu` by
        (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`si`]
           exprLoweringPropsTheory.ci_mono_lower_value_compile_expr) >> simp[]) >>
      mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cu`]
        intcall_args_prefix_frame) >>
      (impl_tac >- fs[exprLoweringPropsTheory.ci_mono_def]) >>
      strip_tac >>
      `is_word_type dty /\ expr_type e = dty` by
        (`is_word_type dty` by
           (qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
              (qspec_then `0` mp_tac) >> simp[]) >>
         fs[] >> irule compileEnvTheory.type_widens_to_word >>
         simp[] >> qexists_tac `get_tenv cx` >> simp[]) >>
      `post_value_type cenv e = dty` by simp[post_value_type_word] >>
      `?w. eval_operand op t = SOME w /\
           (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
              w = typed_val_to_w256 rt v)` by
        (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         qpat_assum `post_value_type cenv e = dty` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tn1 op = {} /\ op_prov G1 op = NONE` by fs[ptr_val_ok_def] >>
      `!x. op = Var x ==> not_fresh_at cu x` by
        (`expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_assum `lower_value compile_expr cenv (expr_type e) e si = (op,cu)`
           (mp_then Any mp_tac
             exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
         disch_then (qspecl_then [`cx`,`tenv`,`esi`] mp_tac) >> simp[]) >>
      `expr_result_typed tenv e (Value v)` by
        (`expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         `expr_body_pre cenv cx tenv e
            (esi with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
         drule_at (Pos hd) exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
         simp[] >> metis_tac[]) >>
      `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
             value_has_type rt v` by
        (qpat_assum `expr_result_typed tenv e (Value v)` mp_tac >>
         qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
         qpat_assum `expr_type e = dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[vyperTypeExprResultTheory.expr_result_typed_def,
              vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
              vyperTypeInvariantsTheory.value_result_typed_def,
              exprSimHypsDefsTheory.expr_sim_inv_def,
              vyperTypeInvariantsTheory.env_consistent_def,
              vyperTypeInvariantsTheory.env_context_consistent_def] >>
         rpt strip_tac >> gvs[]) >>
      `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
             value_has_type rt v /\ val_wf rt v /\
             val_footprint rt v <= type_memory_size rt` by
        (qpat_assum `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
                        value_has_type rt v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
                   exprSimPropsTheory.val_footprint_le]) >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)` by
        (conj_tac
         >- first_assum ACCEPT_TAC >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                      gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
             qpat_assum `!fn i z. frag_reachable ctx func s fn i z ==> _`
               (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
                CONJ path o CONJ no_phi)))) >>
      qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` irule >>
      BETA_TAC >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_normal]) >>
      ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `body_exprs_full_ok cx (e::es)` mp_tac >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[Once body_exprs_full_ok_def, bind_def, AllCaseEqs()] >>
         metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G0`,`P`,`cenv`,`d`,`dtys1`,`es0`,`flags1`,`rest`,
        `ops ++ [op]`,`pflags ++ [T]`,`pin`,`ptys ++ [dty]`,`s0`,`sa`,`cf`,
        `shadow_func`,`shadow_sf`,`shadow_cu`,`cu`,`tenv`,`tn0`,`tops`,
        `vals ++ [v]`,`ws ++ [w]`] >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!marks xs ee t G1 tn1. _`
           (qspecl_then [`marks ++ marks'`,`v::xs`,`ee`,`t'`,`G1'`,`tn1'`] mp_tac) >>
         (impl_tac >- (
           `gas_path ctx func s (LENGTH marks) (OK t)` by
             (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
                (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
              (impl_tac >- first_assum ACCEPT_TAC) >>
              POP_ASSUM_LIST (K all_tac) >> strip_tac >>
              metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                fragGasOriginTheory.gas_origin_path_erase,
                fragGasModeTheory.gas_marked_path_exec]) >>
           conj_tac >-
             (drule gasSummaryComposeTheory.gas_explicit_append_path >>
              disch_then (qspec_then `marks'` assume_tac) >>
              qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` mp_tac >>
              qpat_assum `!tail. eval_exprs cx es _ = _` mp_tac >>
              qpat_assum `res = INL v` mp_tac >>
              pop_assum mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
              simp[Once evaluate_def, GSYM bind_assoc, APPEND_ASSOC] >>
              qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
                (qspec_then `gas_explicit marks' t.vs_gas_readings ++ tail` assume_tac) >>
              gvs[bind_def, AllCaseEqs(), return_def, APPEND_ASSOC] >>
              metis_tac[]) >>
           conj_tac >-
             (simp[NoAsms,LENGTH_APPEND] >>
              irule fragGasPathTheory.gas_path_then >>
              qexists_tac `t` >> conj_tac
              >- (first_assum ACCEPT_TAC)
              >> first_assum ACCEPT_TAC) >>
           qpat_x_assum `op::rest = newops` (SUBST_ALL_TAC o SYM) >>
           qpat_x_assum `cf = sf` (SUBST_ALL_TAC o SYM) >>
           rule_assum_tac (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
           rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- simp[] >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- (qexists_tac `ws1` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[]) >>
      conj_tac >-
        (qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz <=> _` mp_tac >>
         qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      ntac 2 (conj_tac >-
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[] >>
         gvs[exprLoweringPropsTheory.ci_mono_def])) >>
      conj_tac >- (simp[] >> metis_tac[]) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >> Cases_on `j < LENGTH ops`
         >- (`j < LENGTH ptys /\ j < LENGTH vals /\
              j < LENGTH pflags /\ j < LENGTH ws` by metis_tac[] >>
             simp[EL_APPEND_EQN] >>
             qpat_x_assum `!j rt. j < LENGTH ops /\ _ ==> _`
               (qspecl_then [`j`,`rt`] mp_tac) >>
             fs[EL_APPEND_EQN, arithmeticTheory.ADD_SYM]) >>
         `j = LENGTH ops` by gvs[] >>
         gvs[EL_APPEND_EQN]) >>
      conj_tac >-
        (rpt strip_tac >>
         qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
           (qspec_then `SUC j` mp_tac) >> simp[]) >>
      conj_tac >-
        (gen_tac >> strip_tac >>
         qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> (\H res ee G' tn' t. _) H res mid G1 tn1 t`
           drule >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def] >> metis_tac[]) >>
      simp[] >>
      ntac 2 (conj_tac >-
        (qpat_assum `ci_mono si cu` mp_tac >>
         qpat_assum `sa.cs_next_id <= si.cs_next_id` mp_tac >>
         qpat_assum `sa.cs_next_var <= si.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def])) >>
      ntac 2 (conj_tac >- gvs[]) >>
      conj_tac >-
        (qpat_assum `eval_operands ops t = SOME ws` mp_tac >>
         qpat_assum `eval_operand op t = SOME w` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         qid_spec_tac `ws` >> Induct_on `ops` >>
         simp[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
         rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[] >>
      conj_tac >- metis_tac[listTheory.CONS_11] >>
      `body_const_cells_agree [(NONE,tops)] cx tenv mid` by
        (`well_typed_expr tenv e` by
           (qpat_assum `EVERY (\arg. expr_body_pre cenv cx tenv arg esi) (e::es)` mp_tac >>
            simp[NoAsms] >>
            disch_then (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts o cj 1)) >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` assume_tac) >>
         `body_const_cells_agree [(NONE,tops)] cx tenv (mid with gas_obs := [])`
           suffices_by simp[] >>
         irule body_const_cells_agree_expr_read >>
         goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
      `expr_sim_inv cenv cx tenv mid` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         `expr_body_pre cenv cx tenv e esi` by fs[] >>
         pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         `expr_body_pre cenv cx tenv e
           (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
         dxrule exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`res`,`mid with gas_obs := []`] mp_tac) >>
         gvs[bind_def]) >>
      conj_tac >-
        (disch_tac >>
         mp_tac (Q.INST [`flag` |-> `T`] intcall_args_separate_snoc) >>
         (impl_tac >-
           (simp[] >>
            qpat_assum `keep_sites ==> !i j b k c l. _ ==> regions_disjoint b k c l`
              (drule_then ACCEPT_TAC))) >> simp[]) >>
      conj_tac >-
        (disch_tac >>
         mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cu`, `flag` |-> `T`]
           intcall_args_sites_snoc) >>
         (impl_tac >-
           (`si.cs_next_id <= cu.cs_next_id` by fs[exprLoweringPropsTheory.ci_mono_def] >>
            simp[] >>
            qpat_assum `keep_sites ==> !j. _ ==> ?b cap aid. _`
              (drule_then ACCEPT_TAC))) >> simp[]) >>
      conj_tac >-
        (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
         qpat_assum `expr_sim_inv cenv cx tenv mid` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[EVERY_MEM] >> rpt strip_tac >>
         irule intcall_args_pre_state >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `esi` >> simp[] >> res_tac) >>
      conj_tac >- fs[] >>
      conj_tac >-
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `si` >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      conj_tac >- fs[] >>
      ntac 2 (conj_tac >- metis_tac[fragExecTheory.fn_has_code_split]) >>
      conj_tac >-
        (qpat_assum `gas_admissible _ P esi` mp_tac >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` mp_tac >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[gas_admissible_def, vyperInterpreterTheory.evaluate_def,
              vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
         rpt strip_tac >>
         first_x_assum (qspec_then
           `gas_explicit marks s.vs_gas_readings ++ gs` mp_tac) >>
         qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >>
         Cases_on `eval_expr cx e (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ gs)` >>
         Cases_on `q` >> gvs[bind_def] >>
         Cases_on `read_result cx x r` >> Cases_on `q` >> gvs[bind_def] >>
         metis_tac[]) >>
      simp[] >>
      conj_tac >-
        (qpat_assum `return_buf_frame d cenv si s` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s t` mp_tac >>
         qpat_assum `ci_mono si cu` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def,
              loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >>
         simp[]) >>
      irule intcall_args_frame_compose >>
      qexistsl [`G`, `esi`, `s`, `si`, `tn`] >> simp[]) >>
  Cases_on `compile_expr cenv (expr_type e) e si` >>
  rename1 `compile_expr cenv (expr_type e) e si = (vv,ci)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci` >>
  rename1 `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci = (buf,ca)` >>
  Cases_on `unwrap_value cenv vv ca` >>
  rename1 `unwrap_value cenv vv ca = (op,cu)` >>
  qpat_x_assum `compile_stage_intcall_args _ _ (e::es) _ _ si = _` mp_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  qpat_abbrev_tac `store_step = if is_word_type dty then _ else _` >>
  Cases_on `store_step cu` >> rename1 `store_step cu = (u,cs)` >>
  Cases_on `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cs` >>
  rename1 `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cs = (rest,cf)` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >> strip_tac >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_si` >>
  rename1 `compile_expr _ (expr_type e) (gas_shadow_expr e) shadow_si =
    (shadow_vv,shadow_ci)` >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
     (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
  `vv = shadow_vv /\ gas_shadow_state ci shadow_ci` by
    (drule_all bodyFullSharedTheory.gas_shadow_step >>
     disch_then strip_assume_tac >> simp[]) >>
  qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) shadow_ci` >>
  rename1 `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) shadow_ci =
    (shadow_buf,shadow_ca)` >>
  `buf = shadow_buf /\ gas_shadow_state ca shadow_ca` by
    (mp_tac (Q.INST [`nbytes` |-> `MAX 32 (type_memory_bytes cenv dty)`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`ci`,`shadow_ci`] mp_tac) >> simp[]) >>
  qpat_x_assum `buf = shadow_buf` (SUBST_ALL_TAC o SYM) >>
  Cases_on `unwrap_value cenv vv shadow_ca` >>
  rename1 `unwrap_value cenv vv shadow_ca = (shadow_op,shadow_cu)` >>
  `op = shadow_op /\ gas_shadow_state cu shadow_cu` by
    (mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`ca`,`shadow_ca`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  `gas_shadow_compiles store_step store_step` by
    (simp[Abbr `store_step`] >>
     rpt IF_CASES_TAC >>
     simp[gasShadowCompileBaseTheory.gas_shadow_compiles_ignore_bind,
          gasShadowCompileContextTheory.gas_shadow_compiles_ptr_store,
          gasShadowCompileContextTheory.gas_shadow_compiles_store_bytestring,
          gasShadowCompileContextTheory.gas_shadow_compiles_store_memory,
          gasShadowStateTheory.gas_shadow_compiles_return,
          gasShadowStateTheory.gas_shadow_compiles_emit_void]) >>
  Cases_on `store_step shadow_cu` >>
  rename1 `store_step shadow_cu = (shadow_u,shadow_cs)` >>
  `u = shadow_u /\ gas_shadow_state cs shadow_cs` by
    (qpat_assum `gas_shadow_compiles store_step store_step` mp_tac >>
     pure_rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`cu`,`shadow_cu`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_stage_intcall_args _ _ _ _ _ shadow_si = _` mp_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  qpat_assum `Abbrev (store_step = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr es) flags1 dtys1 shadow_cs` >>
  rename1 `compile_stage_intcall_args compile_expr _
    (MAP gas_shadow_expr es) flags1 dtys1 shadow_cs = (shadow_rest,shadow_cf)` >>
  simp[] >> strip_tac >>
  `!a. ci_mono a (SND (store_step a))` by
    (gen_tac >> simp[Abbr `store_step`] >> rpt IF_CASES_TAC >>
     simp[contextTheory.compile_ptr_store_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def,
          exprLoweringPropsTheory.ci_mono_compile_store_bytestring,
          exprLoweringPropsTheory.ci_mono_compile_store_memory,
          exprLoweringPropsTheory.ci_mono_emit_void] >>
     pairarg_tac >> simp[] >>
     qspecl_then [`op`,`buf.buf_operand`,`a`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring >> simp[]) >>
  `ci_mono ci ca /\ ci_mono ca cu /\ ci_mono cu cs /\ ci_mono cs cf /\
   ci_mono shadow_ci shadow_ca /\ ci_mono shadow_ca shadow_cu /\
   ci_mono shadow_cu shadow_cs /\ ci_mono shadow_cs shadow_cf` by
    (conj_tac >-
       (qspecl_then [`MAX 32 (type_memory_bytes cenv dty)`,`ci`] mp_tac
          exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
     conj_tac >-
       (qspecl_then [`cenv`,`vv`,`ca`] mp_tac
          exprLoweringPropsTheory.ci_mono_unwrap_value >> simp[]) >>
     conj_tac >-
       (qpat_assum `!a. ci_mono a (SND (store_step a))`
          (qspec_then `cu` mp_tac) >>
        qpat_assum `store_step cu = _`
          (fn th => pure_rewrite_tac[th, pairTheory.SND]) >>
        simp[NoAsms]) >>
     conj_tac >-
       (mp_tac (Q.SPECL [`compile_expr`,`cenv`,`es`,`flags1`,`dtys1`,`cs`]
          exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args) >>
        simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
     conj_tac >-
       (qspecl_then [`MAX 32 (type_memory_bytes cenv dty)`,`shadow_ci`] mp_tac
          exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
     conj_tac >-
       (qspecl_then [`cenv`,`vv`,`shadow_ca`] mp_tac
          exprLoweringPropsTheory.ci_mono_unwrap_value >> simp[]) >>
     conj_tac >-
       (qpat_assum `!a. ci_mono a (SND (store_step a))`
          (qspec_then `shadow_cu` mp_tac) >>
        qpat_assum `store_step shadow_cu = _`
          (fn th => pure_rewrite_tac[th, pairTheory.SND]) >>
        simp[NoAsms]) >>
     mp_tac (Q.SPECL [`compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr es`,`flags1`,`dtys1`,`shadow_cs`]
          exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args) >>
     simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
  `ci_mono si ci /\ ci_mono shadow_si shadow_ci` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`si`] mp_tac
           (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono) >> simp[]) >>
     qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_si`] mp_tac
       (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono) >> simp[]) >>
  qpat_x_assum `cf = sf` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `shadow_cf = shadow_sf` (SUBST_ALL_TAC o SYM) >>
  `ci_mono ci cf /\ ci_mono shadow_ci shadow_cf` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `ca` >>
         simp[] >> irule exprLoweringPropsTheory.ci_mono_trans >>
         qexists_tac `cu` >> simp[] >>
         irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `cs` >> simp[]) >>
     irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `shadow_ca` >>
     simp[] >> irule exprLoweringPropsTheory.ci_mono_trans >>
     qexists_tac `shadow_cu` >> simp[] >>
     irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `shadow_cs` >> simp[]) >>
  `cs_extends si ci /\ cs_extends ci cf /\
   cs_extends shadow_si shadow_ci /\ cs_extends shadow_ci shadow_cf` by
    (fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code si ci func /\ fn_has_code shadow_si shadow_ci shadow_func` by
    (qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` kall_tac >>
     conj_tac
     >- (mp_tac (Q.SPECL [`si`,`ci`,`cf`,`func`] fn_has_code_split) >> simp[]) >>
     mp_tac (Q.SPECL [`shadow_si`,`shadow_ci`,`shadow_cf`,`shadow_func`]
       fn_has_code_split) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok esi` by
    (`bind (eval_exprs cx (e::es)) f =
        bind (eval_expr cx e)
          (\tv. bind (read_result cx tv)
            (\v. bind (eval_exprs cx es) (\xs. f (v::xs))))` by
       simp[vyperInterpreterTheory.evaluate_def,
            vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
     qpat_x_assum `gas_admissible _ P esi` mp_tac >>
     pop_assum SUBST1_TAC >> strip_tac >>
     rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
     qpat_x_assum `gas_admissible _ P esi`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[bind_def] >> Cases_on `res`
     >- (rename1 `eval_expr _ _ _ = (INL tv,ee)` >>
         Cases_on `tv` >> simp[exprSimDefsTheory.expr_vv_res_ok_def] >>
         simp[read_result_def, raise_def, bind_def] >>
         qpat_x_assum `!err. P (INR err) ==> _`
           (qspec_then `Error (TypeError "read_result mapping")` mp_tac) >>
         simp[exprSimDefsTheory.expr_vv_res_ok_def]) >>
     rename1 `INR exc` >>
     disch_then (qspecl_then [`INR exc`, `ee`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!err. P (INR err) ==> _` irule >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e esi` by
    (`body_expr_full_ok cx e` by fs[Once body_exprs_full_ok_def] >>
     `expr_body_pre cenv cx tenv e esi` by fs[] >>
     qpat_x_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o
         ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspec_then `st0` mp_tac) >>
  disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s`,`G`,`tn`] mp_tac) >>
  simp[] >> disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
      qpat_x_assum `_ ==> gas_outcome_full _ _ _ _ _ _ childQ childR` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `bind (eval_exprs cx (e::es)) f =
     bind (eval_expr cx e) (\tv. bind (read_result cx tv)
       (\v. bind (eval_exprs cx es) (\xs. f (v::xs))))` by
    simp[vyperInterpreterTheory.evaluate_def,
         vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac (GEN_ALL
    gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path) >>
  qexists_tac `childQ` >> BETA_TAC >>
  conj_tac
  >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR`
        (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> namedCases_on `res` ["tv", "exc"] >- fs[] >>
      qexists_tac `exc` >> simp[] >>
      qpat_assum `!H res ee gt r. expr_exit res r /\ _ /\ _ ==> R H res ee gt r`
        irule >> simp[] >>
      conj_tac
      >- (irule (iffLR (INST_TYPE [``:'a`` |-> ``:eval_result``]
            (SPEC_ALL stmtSimPropsTheory.expr_exit_INR_type))) >> simp[]) >>
      irule (iffLR (INST_TYPE [``:'a`` |-> ``:eval_result``]
        haltExitProjTheory.halt_exit_INR_type)) >> simp[]) >>
  reverse (rpt conj_tac)
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[])
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_bind]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >>
  disj1_tac >> qexists_tac `tv` >> conj_tac
  >- first_assum ACCEPT_TAC >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
      ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST (storage_trace_horizon mid.storage_trace))` by
    fs[loweringPostsTheory.vv_post_def] >>
  `MAX 32 (type_memory_bytes cenv dty) < dimword (:256)` by
    (qpat_assum `EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.dimword_def, arithmeticTheory.MAX_DEF] >>
     rpt strip_tac >> decide_tac) >>
  `fn_has_code ci ca func` by
    (qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends ci cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `local_ptrs_reserved cenv ci` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `si` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `~t.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
     simp[]) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn1`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`]
    (qx_choose_then `aq` (qx_choose_then `aw` (qx_choose_then `at`
      (qx_choose_then `aG` (qx_choose_then `atn` strip_assume_tac)))))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid aG atn at` by
    (rpt strip_tac >>
     irule (INST_TYPE [``:'a`` |-> ``:256``]
       bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G1`,`H`,`ctx`,
       `w2n aw + MAX 32 (type_memory_bytes cenv dty)`,
       `func`,`t`,`ci`,`tn1`] >>
     simp[] >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ H res mid G1 tn1 t`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[loweringPostsTheory.vv_post_def, NoAsms] >>
     rpt strip_tac >>
     `si.cs_next_var <= ci.cs_next_var` by
       (qpat_assum `ci_mono si ci` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[exprLoweringPropsTheory.ci_mono_def]) >>
     (first_assum ACCEPT_TAC ORELSE
      (irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `si` >> conj_tac >- first_assum ACCEPT_TAC >>
       (qpat_assum `cenv.ce_return_buf = SOME _` mp_tac ORELSE
        qpat_assum `cenv.ce_return_pc = SOME _` mp_tac) >>
       qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` mp_tac >>
       qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> metis_tac[]))) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at ci x` by
    (qpat_assum `compile_expr cenv (expr_type e) e si = (vv,ci)` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var]) >>
  `at.vs_labels = t.vs_labels` by
    (qpat_assum `at with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >> simp[]) >>
  `eval_operand (vv_operand vv) at = eval_operand (vv_operand vv) t /\
   op_prov aG (vv_operand vv) = op_prov G1 (vv_operand vv) /\
   op_taint atn (vv_operand vv) = op_taint tn1 (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid tv vv at` by
    (irule exprSimMemDefsTheory.vv_store_bound_frame_mem_src >>
     qexists_tac `t` >> simp[]) >>
  `ptr_buf_ok cenv e (vv_operand vv) G1 t ==>
   ptr_buf_ok cenv e (vv_operand vv) aG at` by
    (qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >>
     qexistsl_tac [`x`,`b`,`sz`] >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `(!t' op. vv = StackValue t' op /\
       ~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op aG at) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand aG at)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_buf_ok cenv e (vv_operand vv) G1 t ==>
         ptr_buf_ok cenv e (vv_operand vv) aG at`,
        `!t' op. vv = StackValue t' op /\
           ~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G1 t`,
        `!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv e p.ptr_operand G1 t`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `vv` >> simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
  `at.vs_memory = t.vs_memory /\ at.vs_accounts = t.vs_accounts /\
   at.vs_transient = t.vs_transient /\ at.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `at with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!rt v b len.
     val_wf rt v /\ val_footprint rt v <= len /\
     b + len <= t.vs_alloca_next /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory rt v b mem) ==>
     !mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
        val_in_memory rt v b mem` by
    (rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
     irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tn1.t_mem`,`atn.t_mem`,`len`,`t.vs_memory`,`at.vs_memory`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `b + len <= t.vs_alloca_next` mp_tac >>
     qpat_assum `i < b + len` mp_tac >>
     qpat_assum `t.vs_alloca_next <= i` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     esi.storage_trace` by
    (qpat_assum `!tail. eval_expr cx e _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `valid_horizon cx st0 _ mid.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at Any vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx esi s` by
    (qpat_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _` drule >>
     simp[]) >>
  `ghost_kept_at lo cenv esi si G tn s aG atn` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G1`,`w2n aw + MAX 32 (type_memory_bytes cenv dty)`,`t`,`tn1`] >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at ci x` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >>
            fs[exprLoweringPropsTheory.ci_mono_def]) >>
         qpat_assum `!x. not_fresh_at ci x ==> _` drule >> simp[])
     >- (rpt strip_tac >>
         `b + sz <= s.vs_alloca_next` by
           (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
         qpat_assum `b + sz <= s.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     (rpt strip_tac >>
      `off + sz <= s.vs_alloca_next` by
        (qpat_assum `stmt_state_rel _ ctx func cenv cx esi s` mp_tac >>
         qpat_assum `FLOOKUP s.vs_allocas aid = SOME (off,sz)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
         simp[venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      qpat_assum `off + sz <= s.vs_alloca_next` mp_tac >>
      qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
  `!v rt w.
     read_result cx tv mid = (INL v,mid) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) t = SOME w /\
     ((?ty op. vv = StackValue ty op /\
         ~is_word_type (post_value_type cenv e)) \/
      (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory)) ==>
     val_wf rt v /\
     (val_footprint rt v = 0 \/
      w2n w + val_footprint rt v <= t.vs_alloca_next)` by
    (rpt gen_tac >> disch_tac >>
     `vv_at cenv cx (post_value_type cenv e) si ci mid tv vv t` by
       fs[loweringPostsTheory.vv_post_def] >>
     qpat_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx mid t` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL v,mid) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     gvs[loweringPostsTheory.vv_at_def, contextTheory.vv_operand_def,
         loweringPostsTheory.expr_val_at_def] >>
     `b + sz <= t.vs_alloca_next` by
       ((drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) ORELSE
        (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
         simp[venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[])) >>
     decide_tac) >>
  `!rt v b.
     val_wf rt v /\
     (val_footprint rt v = 0 \/ b + val_footprint rt v <= t.vs_alloca_next) /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory rt v b mem) ==>
     !mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
        val_in_memory rt v b mem` by
    (rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >>
     irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
     conj_tac >- fs[] >>
     qexistsl_tac [`tn1.t_mem`,`atn.t_mem`,`val_footprint rt v`,
                    `t.vs_memory`,`at.vs_memory`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `val_wf rt v /\ _` mp_tac >>
     qpat_assum `b <= i` mp_tac >>
     qpat_assum `i < b + val_footprint rt v` mp_tac >>
     qpat_assum `t.vs_alloca_next <= i` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> decide_tac) >>
  `!v. read_result cx tv mid = (INL v,mid) /\
     ((?ty op. vv = StackValue ty op /\
         ~is_word_type (post_value_type cenv e)) \/
      (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory)) /\
     ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) G1 tn1 t ==>
     ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) aG atn at` by
    (gen_tac >> disch_tac >>
     qpat_assum `!rt v b. val_wf rt v /\ _ ==> _` mp_tac >>
     qpat_assum `!v rt w. read_result cx tv mid = _ /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL v,mid) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> rpt strip_tac
     >- metis_tac[] >>
     Cases_on `vv_operand vv` >>> NTH_GOAL (gvs[ptrDisciplineTheory.op_prov_def]) 1 >>
     qpat_x_assum `op_prov aG _ = _` mp_tac >>
     simp[ptrDisciplineTheory.op_prov_def] >>
     qpat_x_assum `!tv w. _ ==> (!mem. _ ==> _) /\ _`
       (qspecl_then [`tv'`,`w`] mp_tac) >> simp[] >> metis_tac[]) >>
  `ptr_vv_ok cx (post_value_type cenv e) tv vv mid aG atn at` by
    (qpat_assum `ptr_vv_ok cx _ tv vv mid G1 tn1 t` mp_tac >>
     qpat_assum `!v. read_result cx tv mid = _ /\ _ ==> ptr_mem_ok _ _ _ _ aG atn at` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     qpat_assum `op_taint atn (vv_operand vv) = _` mp_tac >>
     qpat_assum `at.vs_accounts = t.vs_accounts` mp_tac >>
     qpat_assum `at.vs_transient = t.vs_transient` mp_tac >>
     qpat_assum `at.vs_call_ctx = t.vs_call_ctx` mp_tac >>
     qpat_assum `atn.t_stor = tn1.t_stor` mp_tac >>
     qpat_assum `atn.t_trans = tn1.t_trans` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     gvs[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
         contextTheory.vv_operand_def] >> metis_tac[]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     !v rt. read_result cx tv mid = (INL v,mid) /\
       evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt ==>
       val_wf rt v /\ val_footprint rt v <= type_memory_size rt` by
    (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `vv` >>
     simp[contextTheory.vv_location_def, loweringPostsTheory.vv_post_def] >>
     rpt strip_tac >>
     fs[loweringPostsTheory.vv_holds_def, loweringPostsTheory.immutable_holds_def] >>
     metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
               exprSimPropsTheory.val_footprint_le]) >>
  `(cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx tv mid = (INL v,mid) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
         eval_operand (vv_operand vv) at = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))` by
    (qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?v. _` mp_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> !v rt. _` mp_tac >>
     qpat_assum `!rt v b len. val_wf rt v /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `lo <= t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> fs[] >>
     rpt strip_tac >>
     `w2n w + type_memory_size rt <= lo` by metis_tac[arithmeticTheory.ADD_COMM] >>
     simp[] >>
     `w2n w + type_memory_size rt <= t.vs_alloca_next` by decide_tac >>
     metis_tac[]) >>
  `!n b sz. local_region cenv mid.scopes at n b sz <=>
             local_region cenv mid.scopes t n b sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >>
     rpt gen_tac >> eq_tac >> strip_tac >>
     qexistsl_tac [`entry`,`p`,`w`] >> simp[] >>
     `not_fresh_at ci p` by
       (qpat_assum `local_ptrs_reserved cenv ci`
          (qspecl_then [`n`,`n`,`p`,`sz`,`sz`] mp_tac o hd o tl o CONJUNCTS o
           REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        simp[]) >>
     qpat_assum `!x. not_fresh_at ci x ==> lookup_var x at = lookup_var x t /\ _`
       drule >> simp[]) >>
  `!sn H. ci.cs_next_id <= sn.cs_next_id /\
     valid_horizon cx st0 H mid.storage_trace ==>
     vv_post H ctx func cenv cx e esi si sn s mid tv vv at` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e esi si ci s mid tv vv t` by
       (qpat_assum `!h. valid_horizon cx st0 h mid.storage_trace ==>
           (\h r ee g tn tt. ?v. r = INL v /\
             vv_post h ctx func cenv cx e esi si ci s ee v vv tt /\ _) h res mid G1 tn1 t`
          (qspec_then `H` mp_tac) >>
         (impl_tac >- simp[]) >> BETA_TAC >>
         disch_then (qx_choose_then `tv1` strip_assume_tac) >>
         `tv1 = tv` by
           (qpat_x_assum `res = INL tv1` mp_tac >> simp[]) >>
         qpat_x_assum `vv_post H ctx func cenv cx e esi si ci s mid tv1 vv t` mp_tac >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx mid at` by
       (qpat_assum `!h. stmt_state_rel h ctx func cenv cx mid t ==> stmt_state_rel h ctx func cenv cx mid at` irule >>
        qpat_assum `vv_post H ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
        simp[loweringPostsTheory.vv_post_def, NoAsms]) >>
     irule exprSimIfExpWidenedAdapterTheory.vv_post_alloc_mono_frame >>
     simp[] >> qexistsl_tac [`t`,`ci`] >>
     simp[venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def,
          exprLoweringPropsTheory.ci_mono_def] >>
     qpat_assum `!x. not_fresh_at ci x ==> lookup_var x at = lookup_var x t /\ _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv ci` mp_tac >>
     qpat_assum `ci_mono si ci` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.local_ptrs_reserved_def,
          exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `expr_body_pre cenv cx tenv e esi` by
    (qpat_assum `EVERY (\arg. expr_body_pre cenv cx tenv arg esi) (e::es)` mp_tac >>
     simp[NoAsms]) >>
  drule exprSimHypsTheory.post_type_evaluates >>
  disch_then (qx_choose_then `rty` assume_tac) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64` by
    (drule aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound >> simp[]) >>
  `is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)` by
    (`expr_sim_inv cenv cx tenv esi /\ well_typed_expr tenv e` by
       (qpat_assum `expr_body_pre cenv cx tenv e esi`
          (strip_assume_tac o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     drule_all exprSimHypsTheory.post_value_type_widens >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type rty v` by
    (gen_tac >> disch_tac >>
     `expr_body_pre cenv cx tenv e
        (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     `bind (eval_expr cx e) (read_result cx)
        (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ []) =
        (INL v,mid with gas_obs := [])` by
       (qpat_assum `!tail. eval_expr cx e _ = _`
          (qspec_then `[]` mp_tac) >>
        simp[bind_def, exprSimMemorySourceTheory.read_result_gas_obs]) >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
       (mp_then (Pat `bind _ _ _ = _`) mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimHypsTheory.memory_rhs_read_post_typed)) >>
     disch_then (qspecl_then [`cenv`,`tenv`] mp_tac) >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     `tenv.type_defs = get_tenv cx` by
       (qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[exprSimHypsDefsTheory.expr_sim_inv_def,
             vyperTypeInvariantsTheory.env_consistent_def,
             vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     simp[]) >>
  `ci.cs_next_var <= ca.cs_next_var /\ ci.cs_next_id <= ca.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ ci = (_,ca)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     mp_tac (Q.SPECL [`MAX 32 (type_memory_bytes cenv dty)`,`ci`]
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `si.cs_next_var <= ci.cs_next_var /\ si.cs_next_id <= ci.cs_next_id` by
    (qpat_assum `ci_mono si ci` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `MAP FDOM esi.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def] >>
     metis_tac[]) >>
  `~at.vs_halted` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK at,aG,atn)`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  `fn_has_code ca cu func` by
    (qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  qpat_assum `compile_expr cenv (expr_type e) e si = (vv,ci)`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac
      bodyFullUnwrapTheory.unwrap_value_origin_ptr) >>
  disch_then (fn th =>
    qpat_assum `unwrap_value cenv vv ca = (op,cu)`
      (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_inst_ids_distinct _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (qspec_then `rty` mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]] >> NO_TAC)) >>
  strip_tac >>
  `lookup_var aq z = SOME aw /\
   ptr_covers G' tn' aq z (MAX 32 (type_memory_bytes cenv dty))` by
    (qpat_assum `!x. not_fresh_at ca x ==> _`
       (qspec_then `aq` mp_tac) >>
     qpat_assum `not_fresh_at ca aq` mp_tac >>
     qpat_assum `lookup_var aq at = SOME aw` mp_tac >>
     qpat_assum `ptr_covers aG atn aq at _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ghost_inv_at _ _ _ _ _ _ G' tn' z`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> rpt strip_tac >>
     fs[bodyPtrDefsTheory.ghost_inv_def]) >>
  `~z.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec o CONJUNCT1) >>
     simp[fragExecTheory.exit_result_def]) >>
  `fn_has_code cu cs func` by
    (qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next` by
    (qpat_assum `w2n aw + MAX 32 _ <= at.vs_alloca_next` mp_tac >>
     qpat_assum `at.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                    _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o
       MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
       CONJUNCT1 o REWRITE_RULE [loweringPostsTheory.expr_post_def] o cj 2)) >>
  (* One store cut: branch-specific execution, shared frame and tail IH. *)
  qsuff_tac `?wt wG wtn nw.
    nw <= MAX 32 (type_memory_bytes cenv dty) /\
    typed_copy_state_frame cu (w2n aw) nw z wt /\
    ~wt.vs_halted /\ wt.vs_current_bb = cs.cs_current_bb /\
    wt.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func wt /\
    wtn.t_stor = tn'.t_stor /\ wtn.t_trans = tn'.t_trans /\ wtn.t_imm = tn'.t_imm /\
    (!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\
      op_taint wtn (Var p) = op_taint tn' (Var p)) /\
    (!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==>
      (i IN wtn.t_mem <=> i IN tn'.t_mem)) /\
    (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
      value_has_type rt v /\ val_wf rt v /\
      type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
      (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
        val_in_memory rt v (w2n aw) mem)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK wt,wG,wtn))`
  >- (disch_then (qx_choose_then `wt` (qx_choose_then `wG`
        (qx_choose_then `wtn` (qx_choose_then `nw` strip_assume_tac)))) >>
      `si.cs_next_var <= cu.cs_next_var /\ ca.cs_next_var <= cu.cs_next_var` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`ci_mono si ci`, `ci_mono ci ca`, `ci_mono ca cu`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `not_fresh_at cu aq` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >> simp[]) >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp wt) /\
       (!fn inst u. frag_reachable ctx func wt fn inst u ==> dalloca_fmp_headroom inst u)` by
        (conj_tac
         >- (drule typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp >>
             simp[]) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                      gas_origin_ptr_path _ (s,G,tn) marks _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                      gas_origin_ptr_path _ (t,G1,tn1) [] (OK wt,wG,wtn)`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
         `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
           (qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)` (fn path =>
              qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
                qpat_assum `!fn i z. frag_reachable ctx func s fn i z ==> _`
                  (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
                   CONJ path o CONJ no_phi)))) >>
         qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK wt,wG,wtn)` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
             qpat_assum `!fn i z. frag_reachable ctx func t fn i z ==> _`
               (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
                CONJ path o CONJ no_phi)))) >>
      irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
      conj_tac >-
        (irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_result] >>
         gen_tac >> irule storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`wG`,`wt`,`wtn`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule intcall_args_read_result_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >>
      qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` irule >>
      BETA_TAC >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `body_exprs_full_ok cx (e::es)` mp_tac >>
         qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
         qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
         qpat_assum `res = INL tv` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[Once body_exprs_full_ok_def, bind_def, AllCaseEqs()] >>
         metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G0`,`P`,`cenv`,`d`,`dtys1`,`es0`,`flags1`,`rest`,
        `ops ++ [Var aq]`,`pflags ++ [F]`,`pin`,`ptys ++ [dty]`,`s0`,`sa`,`cf`,
        `shadow_func`,`shadow_cf`,`shadow_cs`,`cs`,`tenv`,`tn0`,`tops`,
        `vals ++ [v]`,`ws ++ [aw]`] >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
         qpat_x_assum `!marks xs ee t G1 tn1. _`
           (qspecl_then [`marks ++ marks'`,`v::xs`,`ee`,`t'`,`G1'`,`tn1'`] mp_tac) >>
         (impl_tac >- (
           `gas_path ctx func s (LENGTH marks) (OK wt)` by
             (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (s,G,tn) marks _`
                (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
              qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ [] _`
                (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
              qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
              imp_res_tac fragGasOriginPtrTheory.gas_origin_ptr_path_projections >>
              imp_res_tac fragGasOriginTheory.gas_origin_path_erase >>
              imp_res_tac fragGasModeTheory.gas_marked_path_exec >>
              metis_tac[fragGasPathTheory.gas_path_then, LENGTH, APPEND_NIL, arithmeticTheory.ADD_0]) >>
           conj_tac >-
             (drule gasSummaryComposeTheory.gas_explicit_append_path >>
              disch_then (qspec_then `marks'` assume_tac) >>
              qpat_assum `!tail. eval_expr cx e _ = _` mp_tac >>
              qpat_assum `!tail. eval_exprs cx es _ = _` mp_tac >>
              qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
              qpat_assum `res = INL tv` mp_tac >>
              pop_assum mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
              drule exprSimMemorySourceTheory.read_result_gas_obs >> strip_tac >>
              simp[Once evaluate_def, GSYM bind_assoc, APPEND_ASSOC] >>
              qpat_x_assum `!tail. eval_expr cx e _ = _`
                (qspec_then `gas_explicit marks' wt.vs_gas_readings ++ tail` assume_tac) >>
              gvs[bind_def, AllCaseEqs(), return_def, APPEND_ASSOC] >>
              metis_tac[]) >>
           conj_tac >-
             (simp[NoAsms,LENGTH_APPEND] >>
              irule fragGasPathTheory.gas_path_then >>
              qexists_tac `wt` >> conj_tac
              >- (first_assum ACCEPT_TAC)
              >> first_assum ACCEPT_TAC) >>
           qpat_x_assum `buf.buf_operand::rest = newops` (SUBST_ALL_TAC o SYM) >>
           qpat_assum `buf.buf_operand = Var aq` SUBST_ALL_TAC >>
           rule_assum_tac (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >-
             (qexists_tac `ws1` >>
              ntac 4 (conj_tac >- (simp[NoAsms] >> decide_tac)) >>
              conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- (simp[NoAsms, EVERY_APPEND] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
              conj_tac >-
                (qpat_x_assum `!x. (MEM (Var x) ops \/ x = aq) \/ _ ==> _` mp_tac >>
                 POP_ASSUM_LIST (K all_tac) >> simp[MEM_APPEND] >> metis_tac[]) >>
              conj_tac >-
                (qpat_assum `keep_sites ==> !j. _ ==> ?b cap aid. op_prov G1' _ = _ /\ _`
                   mp_tac >> simp[arithmeticTheory.ADD1]) >>
              conj_tac >-
                (qpat_assum `keep_sites ==> !i j b k c l. _ ==> regions_disjoint b k c l`
                   mp_tac >> simp[arithmeticTheory.ADD1]) >>
              qpat_x_assum `!j rt. j < LENGTH ops + _ /\ _ ==> _` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD_SYM]) >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[]) >>
      `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
          lookup_var x wt = SOME w` by
        (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
         qpat_assum `!x. not_fresh_at ci x ==> _` mp_tac >>
         qpat_assum `!x. not_fresh_at ca x ==> _` mp_tac >>
         qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `ci_mono si ci` mp_tac >>
         qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def,
              typedMemoryCopyTheory.typed_copy_state_frame_def,
              exprLoweringPropsTheory.ci_mono_def,
              loweringStateRelDefsTheory.not_fresh_at_def] >>
         rpt strip_tac >>
         `(!n. ci.cs_next_var <= n ==> x <> STRING #"%" (toString n)) /\
          (!n. ca.cs_next_var <= n ==> x <> STRING #"%" (toString n)) /\
          (!n. cu.cs_next_var <= n ==> x <> STRING #"%" (toString n))` by
           (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
         metis_tac[]) >>
      `!n b sz. local_region cenv es0.scopes s0 n b sz <=>
         local_region cenv mid.scopes wt n b sz` by
        (qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz <=> _` mp_tac >>
         qpat_assum `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==> _` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `stmt_state_rel _ ctx func cenv cx esi s` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
         eq_tac
         >- (rw[loweringStateRelDefsTheory.local_region_def] >>
             `lookup_scopes n mid.scopes <> NONE` by
               metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                         optionTheory.NOT_SOME_NONE] >>
             `not_fresh_at si p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
         rw[loweringStateRelDefsTheory.local_region_def] >>
         `lookup_scopes n esi.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         Cases_on `lookup_scopes n esi.scopes` >> fs[] >>
         rename1 `lookup_scopes n esi.scopes = SOME entry0` >>
         `?w0. lookup_var p s = SOME w0` by
           (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
            qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         `lookup_var p wt = SOME w0` by metis_tac[] >> gvs[]) >>
      conj_tac >- simp[] >>
      `si.cs_next_var <= cs.cs_next_var /\ si.cs_next_id <= cs.cs_next_id` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`ci_mono si ci`, `ci_mono ci ca`, `ci_mono ca cu`, `ci_mono cu cs`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      ntac 2 (conj_tac >-
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[])) >>
      conj_tac >-
        (simp[MEM_APPEND] >> rpt strip_tac >>
         irule freshWritesTheory.not_fresh_at_mono
         >- (qexists_tac `si` >> simp[]) >>
         qexists_tac `ca` >> simp[] >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `ci_mono cu cs` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `!aid b cap. aid < si.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) ==>
         regions_disjoint (w2n aw) (MAX 32 (type_memory_bytes cenv dty)) b cap` by
        (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
         qpat_assum `!aid b len. aid < ci.cs_next_id /\ _ ==> _` mp_tac >>
         qpat_assum `si.cs_next_id <= ci.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         `aid < ci.cs_next_id` by decide_tac >> metis_tac[]) >>
      `!n b cap. local_region cenv esi.scopes s n b cap ==>
         regions_disjoint (w2n aw) (MAX 32 (type_memory_bytes cenv dty)) b cap` by
        (qpat_assum `!sn H. ci.cs_next_id <= sn.cs_next_id /\ _ ==> _`
           (qspecl_then [`ca`,`storage_trace_horizon mid.storage_trace`] mp_tac) >>
         (impl_tac >- simp[]) >>
         qpat_assum `!name b len. local_region cenv mid.scopes at name b len ==> _` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `local_region cenv esi.scopes s n b cap` mp_tac >>
         simp[loweringStateRelDefsTheory.local_region_def] >> strip_tac >>
         `lookup_scopes n mid.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
      `!x. not_fresh_at si x ==> not_fresh_at cu x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[]) >>
      `ghost_kept_at lo cenv esi si G tn s wG wtn` by
        (qpat_assum `!x. not_fresh_at si x ==> not_fresh_at cu x` mp_tac >>
         qpat_assum `nw <= MAX 32 (type_memory_bytes cenv dty)` mp_tac >>
         qpat_assum `ghost_kept_at lo cenv esi si G tn s G' tn'` mp_tac >>
         qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
         qpat_assum `!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==> _` mp_tac >>
         qpat_assum `!aid b cap. aid < si.cs_next_id /\ _ ==> regions_disjoint _ _ _ _` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def,
                          loweringStateRelDefsTheory.regions_disjoint_def] >>
         rpt strip_tac
         >- metis_tac[]
         >- metis_tac[]
         >- (`w2n aw + MAX 32 (type_memory_bytes cenv dty) <= off \/ off + sz <= w2n aw` by
               (qpat_x_assum `!aid b cap. _ ==> _` irule >> metis_tac[]) >>
             `i < w2n aw \/ w2n aw + nw <= i` by
               (FIRST [qpat_assum `w2n aw + MAX 32 _ <= off` mp_tac,
                       qpat_assum `off + sz <= w2n aw` mp_tac] >>
                qpat_assum `off <= i` mp_tac >> qpat_assum `i < off + sz` mp_tac >>
                qpat_assum `nw <= MAX 32 _` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
             `i IN tn'.t_mem` by
               (qpat_x_assum `!i. _ ==> (_ <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
             metis_tac[]) >>
         `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + sz <= w2n aw` by
           (qpat_x_assum `!n b cap. local_region _ _ _ _ _ _ ==> _` irule >> metis_tac[]) >>
         `i < w2n aw \/ w2n aw + nw <= i` by
           (FIRST [qpat_assum `w2n aw + MAX 32 _ <= b` mp_tac,
                   qpat_assum `b + sz <= w2n aw` mp_tac] >>
            qpat_assum `b <= i` mp_tac >> qpat_assum `i < b + sz` mp_tac >>
            qpat_assum `nw <= MAX 32 _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
         `i IN tn'.t_mem` by
           (qpat_x_assum `!i. _ ==> (_ <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
         metis_tac[]) >>
      `wb_frame cenv esi mid si s z` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
      `!off len. off + len <= w2n aw \/ w2n aw + nw <= off ==>
         mem_bytes_at off len wt.vs_memory = mem_bytes_at off len z.vs_memory` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      `!n b cap. local_region cenv esi.scopes s n b cap ==>
         mem_bytes_at b cap wt.vs_memory = mem_bytes_at b cap z.vs_memory` by
        (rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ _ _`
           drule >>
         qpat_assum `nw <= MAX 32 _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `wt.vs_allocas = z.vs_allocas` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
         disch_then (mp_tac o AP_TERM ``\st:venom_state. st.vs_allocas`` o CONJUNCT1) >> simp[]) >>
      `wb_frame cenv esi mid si s wt` by
        (qpat_assum `nw <= MAX 32 _` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s z` mp_tac >>
         qpat_assum `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==> _` mp_tac >>
         qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> mem_bytes_at _ _ _ = _` mp_tac >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len wt.vs_memory = _` mp_tac >>
         qpat_assum `!aid b cap. aid < si.cs_next_id /\ _ ==> regions_disjoint _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         qpat_x_assum `nw <= MAX 32 _` (mk_asm "store_extent") >>
         fs[loweringPostsTheory.wb_frame_def] >>
         conj_tac >-
           (rpt strip_tac >>
            `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= off \/ off + sz <= w2n aw` by
              metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
            `off + sz <= w2n aw \/ w2n aw + nw <= off` by
              (FIRST [qpat_assum `w2n aw + MAX 32 _ <= off` mp_tac,
                      qpat_assum `off + sz <= w2n aw` mp_tac] >>
               asm "store_extent" mp_tac >>
               POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
            `mem_bytes_at off sz wt.vs_memory = mem_bytes_at off sz z.vs_memory` by
              (qpat_x_assum `!off len. _ ==> mem_bytes_at off len wt.vs_memory = _`
                 (qspecl_then [`off`,`sz`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
            `mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz s.vs_memory` by
              (qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz z.vs_memory = _`
                 (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
               disch_then irule >> simp[] >> first_assum ACCEPT_TAC) >>
            metis_tac[]) >>
         irule exprSimPropsTheory.locals_kept_regions_tail >> qexists_tac `z` >>
         simp[] >> first_assum ACCEPT_TAC) >>
      `!n b sz. local_region cenv esi.scopes s n b sz <=>
         local_region cenv mid.scopes wt n b sz` by metis_tac[] >>
      `s.vs_alloca_next <= wt.vs_alloca_next` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `at.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         qpat_assum `t.vs_alloca_next <= at.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
           vs_current_bb := _; vs_inst_idx := _|> = z`
           (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
         simp[] >> decide_tac) >>
      `wt.vs_labels = s.vs_labels` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ (s,G,tn) _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ (t,G1,tn1) _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_labels]) >>
      mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cs`, `t` |-> `wt`,
                     `G1` |-> `wG`, `tn1` |-> `wtn`]
        intcall_args_prefix_frame) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      `FLOOKUP wt.vs_allocas ci.cs_next_id =
         SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
        (qpat_assum `wb_frame cenv mid mid ca at z` mp_tac >>
         qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
         qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
      `FLOOKUP z.vs_allocas ci.cs_next_id =
         SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by metis_tac[] >>
      `op_prov aG (Var aq) =
         SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
        simp[ptrDisciplineTheory.op_prov_def] >>
      `not_fresh_at cu aq` by
        (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `ca` >> simp[] >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `op_prov wG (Var aq) =
         SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
        (qpat_assum `not_fresh_at cu aq` mp_tac >>
         qpat_assum `!x. not_fresh_at ca x ==> _` (qspec_then `aq` mp_tac) >>
         qpat_assum `not_fresh_at ca aq` mp_tac >>
         qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` (qspec_then `aq` mp_tac) >>
         qpat_assum `op_prov aG (Var aq) = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
      `ci.cs_next_id < cs.cs_next_id` by
        (qpat_assum `compile_alloc_buffer _ ci = (buf,ca)` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `ci_mono cu cs` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
              compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
              compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_id_def,
              compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
              exprLoweringPropsTheory.ci_mono_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
      `fn_has_code ci ca func` by
        (qpat_assum `fn_has_code si cf func` mp_tac >>
         qpat_assum `ci_mono si ci` mp_tac >>
         qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `ci_mono cu cs` mp_tac >>
         qpat_assum `ci_mono cs cf` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `ci_mono ca cf` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >>
         `fn_has_code si ca func /\ fn_has_code ca cf func` by
           (irule fragExecTheory.fn_has_code_split >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
         qpat_assum `fn_has_code si ca func` mp_tac >>
         qpat_assum `cs_extends si ci` mp_tac >>
         qpat_assum `cs_extends ci ca` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[fragExecTheory.fn_has_code_split]) >>
      `MEM (mk_inst ci.cs_next_id ALLOCA
         [Lit (n2w (MAX 32 (type_memory_bytes cenv dty)))]
         [STRING #"%" (toString ci.cs_next_var)]) (fn_insts func)` by
        (irule actualAllocExecTheory.actual_alloc_buffer_site >>
         qpat_assum `compile_alloc_buffer _ ci = (buf,ca)` (irule_at Any) >> simp[]) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >>
         Cases_on `j < LENGTH ops`
         >- (qpat_assum `!j rt. j < LENGTH ops /\ _ ==> _ /\ _ /\ _ /\ _ /\
                (~EL j pflags ==> ?b cap aid. op_prov wG _ = _ /\ _)`
               (qspecl_then [`j`,`rt`] mp_tac) >>
             qpat_assum `evaluate_type _ (EL j (ptys ++ [dty])) = SOME rt` mp_tac >>
             qpat_assum `j < LENGTH ops` mp_tac >>
             qpat_assum `LENGTH ws = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH vals = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH ptys = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH pflags = LENGTH ops` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         `j = LENGTH ops` by
           (qpat_assum `j < LENGTH (ops ++ [Var aq])` mp_tac >>
            qpat_assum `~(j < LENGTH ops)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[] ) >>
         qpat_assum `j = LENGTH ops` (fn ji =>
           qpat_assum `LENGTH vals = LENGTH ops` (fn vl =>
             qpat_assum `LENGTH ws = LENGTH ops` (fn wl =>
               qpat_assum `LENGTH pflags = LENGTH ops` (fn fl =>
                 simp[NoAsms, EL_APPEND_EQN, ji, vl, wl, fl])))) >>
         `evaluate_type (get_tenv cx) dty = SOME rt` by
           (qpat_assum `evaluate_type _ (EL j (ptys ++ [dty])) = SOME rt` mp_tac >>
            qpat_assum `j = LENGTH ops` mp_tac >>
            qpat_assum `LENGTH ptys = LENGTH ops` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         `value_has_type rt v /\ val_wf rt v /\
          type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
          (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
            val_in_memory rt v (w2n aw) mem)` by
           (qpat_assum `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==> _` drule >> simp[]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
         conj_tac >-
           (irule exprSimPropsTheory.val_footprint_le >>
            metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
         `lo <= w2n aw` by
           (qpat_assum `allocas_from lo at` mp_tac >>
            qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
         qexistsl_tac [`w2n aw`,`MAX 32 (type_memory_bytes cenv dty)`,`ci.cs_next_id`] >>
         simp[] >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `w2n aw + MAX 32 _ <= z.vs_alloca_next` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
            rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
            simp[]) >>
         conj_tac >-
           (qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> _` mp_tac >>
            qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ b cap` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
         qpat_assum `case pin of NONE => T | SOME (rb,b,k) => FLOOKUP G rb = SOME (b,k) /\ _` mp_tac >>
         qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
         qpat_assum `!aid b len. aid < ci.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` mp_tac >>
         qpat_assum `si.cs_next_id <= ci.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         namedCases_on `pin` ["", "pp"] >> simp[] >>
         PairCases_on `pp` >>
         simp[loweringPostsTheory.vv_post_def,
              loweringStateRelDefsTheory.regions_disjoint_def] >>
         rpt strip_tac >>
         `sa.cs_next_id < ci.cs_next_id` by decide_tac >> metis_tac[]) >>
      simp[] >>
      conj_tac >-
        (rpt strip_tac >>
         qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
           (qspec_then `SUC j` mp_tac) >> simp[]) >>
      `body_const_cells_agree [(NONE,tops)] cx tenv mid` by
        (`well_typed_expr tenv e` by
           (qpat_assum `EVERY (\arg. expr_body_pre cenv cx tenv arg esi) (e::es)` mp_tac >>
            simp[NoAsms] >>
            disch_then (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts o cj 1)) >>
         qpat_assum `!tail. eval_expr cx e _ = _`
           (qspec_then `[]` assume_tac) >>
         `body_const_cells_agree [(NONE,tops)] cx tenv (mid with gas_obs := [])`
           suffices_by simp[] >>
         irule body_const_cells_agree_expr >>
         goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
      `expr_sim_inv cenv cx tenv mid` by
        (qpat_assum `!tail. eval_expr cx e _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
         qpat_assum `res = INL tv` mp_tac >>
         `expr_body_pre cenv cx tenv e esi` by
           (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         `expr_body_pre cenv cx tenv e
           (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
         dxrule exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
         simp[bind_def, exprSimMemorySourceTheory.read_result_gas_obs]) >>
      simp[] >>
      `return_buf_frame d cenv cs wt` by
        (qpat_assum `return_buf_frame d cenv si s` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s wt` mp_tac >>
         qpat_assum `si.cs_next_var <= cs.cs_next_var` mp_tac >>
         qpat_assum `s.vs_alloca_next <= wt.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def] >> rpt strip_tac >>
         irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >> simp[]) >>
      `wb_frame cenv es0 mid sa s0 wt /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 wG wtn` by
        (irule intcall_args_frame_compose >>
         qexistsl [`G`, `esi`, `s`, `si`, `tn`] >> simp[]) >>
      `wb_frame cenv es0 (mid with gas_obs := []) sa s0 wt` by
        (qpat_assum `wb_frame cenv es0 mid sa s0 wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
              loweringPostsTheory.popped_kept_def] >> metis_tac[]) >>
      simp[] >>
      reverse conj_tac >-
        (conj_tac >-
           (qpat_assum `LENGTH (F::flags1) = LENGTH (e::es)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `LENGTH (dty::dtys1) = LENGTH (e::es)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `eval_operands ops wt = SOME ws` mp_tac >>
            `lookup_var aq wt = SOME aw` by
              (qpat_assum `lookup_var aq z = SOME aw` mp_tac >>
               qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
               qpat_assum `not_fresh_at ca aq` mp_tac >>
               qpat_assum `ci_mono ca cu` mp_tac >>
               POP_ASSUM_LIST (K all_tac) >>
               simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
                    exprLoweringPropsTheory.ci_mono_def] >>
               metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
            pop_assum mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            qid_spec_tac `ws` >> Induct_on `ops` >>
            simp[venomStateTheory.eval_operands_def, venomStateTheory.eval_operand_def,
                 AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
         conj_tac >- metis_tac[listTheory.CONS_11] >>
         conj_tac >-
           (disch_tac >>
            mp_tac (Q.INST [`flag` |-> `F`, `op` |-> `Var aq`,
                             `G1` |-> `wG`, `tn1` |-> `wtn`]
               intcall_args_separate_snoc) >>
            (impl_tac >-
              (simp[] >> conj_tac >-
                 (qpat_assum `keep_sites ==> !i j b k c l. _ ==> regions_disjoint b k c l`
                    (drule_then ACCEPT_TAC)) >>
               rpt gen_tac >> strip_tac >>
               `?aid. FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < si.cs_next_id` by
                 (qpat_assum `keep_sites ==> !j. _ ==> ?b cap aid. _`
                    (qspec_then `i` mp_tac o UNDISCH) >>
                  (impl_tac >- simp[]) >> strip_tac >>
                  qpat_assum `op_prov G (EL i ops) = SOME (b,k)` mp_tac >>
                  qpat_assum `op_prov G (EL i ops) = SOME (_,_)` mp_tac >>
                  qpat_assum `FLOOKUP s.vs_allocas aid = SOME (_,_)` mp_tac >>
                  qpat_assum `aid < si.cs_next_id` mp_tac >>
                  POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
               qpat_assum `!aid b cap. aid < si.cs_next_id /\ _ ==> regions_disjoint _ _ _ _`
                 (drule_all_then mp_tac) >>
               simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM])) >>
            simp[]) >>
         conj_tac >-
           (disch_tac >>
            mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cs`, `flag` |-> `F`,
                 `op` |-> `Var aq`, `t` |-> `wt`, `G1` |-> `wG`, `tn1` |-> `wtn`]
              intcall_args_sites_snoc) >>
            (impl_tac >-
              (simp[] >> qexists_tac `ci.cs_next_id` >> simp[arithmeticTheory.MAX_LE] >>
               qexists_tac `mk_inst ci.cs_next_id ALLOCA
                 [Lit (n2w (MAX 32 (type_memory_bytes cenv dty)))]
                 [STRING #"%" (toString ci.cs_next_var)]` >>
               simp[venomInstTheory.mk_inst_def])) >> simp[]) >>
         conj_tac >-
           (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
            qpat_assum `expr_sim_inv cenv cx tenv mid` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[EVERY_MEM] >> rpt strip_tac >>
            irule intcall_args_pre_state >>
            conj_tac >- first_assum ACCEPT_TAC >>
            qexists_tac `esi` >> simp[] >> res_tac) >>
         conj_tac >-
           (qpat_assum `ptr_covers aG atn aq at _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def]) >>
         conj_tac >-
           (qpat_assum `EVERY (\ty. type_memory_bytes cenv ty < _) (dty::dtys1)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
            qexists_tac `si` >>
            qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
            qpat_assum `si.cs_next_var <= cs.cs_next_var` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `LIST_REL _ (MAP expr_type (e::es)) (dty::dtys1)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `fn_has_code shadow_si shadow_cf shadow_func` mp_tac >>
            qpat_assum `ci_mono shadow_si shadow_ci` mp_tac >>
            qpat_assum `ci_mono shadow_ci shadow_ca` mp_tac >>
            qpat_assum `ci_mono shadow_ca shadow_cu` mp_tac >>
            qpat_assum `ci_mono shadow_cu shadow_cs` mp_tac >>
            qpat_assum `ci_mono shadow_cs shadow_cf` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `ci_mono shadow_si shadow_cs` by
              metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
            fs[exprLoweringPropsTheory.ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split]) >>
         conj_tac >-
           (qpat_assum `fn_has_code si cf func` mp_tac >>
            qpat_assum `si.cs_next_var <= cs.cs_next_var` kall_tac >>
            qpat_assum `ci_mono si ci` mp_tac >>
            qpat_assum `ci_mono ci ca` mp_tac >>
            qpat_assum `ci_mono ca cu` mp_tac >>
            qpat_assum `ci_mono cu cs` mp_tac >>
            qpat_assum `ci_mono cs cf` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `ci_mono si cs` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
            fs[exprLoweringPropsTheory.ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split]) >>
         conj_tac >-
           (qpat_assum `gas_admissible _ P esi` mp_tac >>
            qpat_assum `!tail. eval_expr cx e _ = _` mp_tac >>
            qpat_assum `res = INL tv` mp_tac >>
            qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[gas_admissible_def, vyperInterpreterTheory.evaluate_def,
                 vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
            rpt strip_tac >>
            first_x_assum (qspec_then
              `gas_explicit marks s.vs_gas_readings ++ gs` mp_tac) >>
            qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >>
            rpt strip_tac >>
            drule exprSimMemorySourceTheory.read_result_gas_obs >>
            disch_then (qspec_then `gs` assume_tac) >>
            gvs[bind_def] >> metis_tac[]) >>
         qpat_assum `case pin of NONE => T | SOME (rb,b,k) => FLOOKUP wG rb = SOME (b,k) /\ _` mp_tac >>
         qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
         qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         namedCases_on `pin` ["", "pp"] >> simp[] >>
         PairCases_on `pp` >> simp[] >> metis_tac[]) >>
      gen_tac >> disch_tac >>
      `expr_post H ctx func cenv cx e esi si cu s mid v op z /\
       ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
         simp[]) >>
      `stmt_state_rel H ctx func cenv cx mid z` by
        (qpat_assum `expr_post H ctx func cenv cx e esi si cu s mid v op z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
      `local_ptrs_rel func cenv mid.scopes z` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
      `si.cs_next_var <= cu.cs_next_var` by
        (qpat_assum `ci_mono si ci` mp_tac >> qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `local_ptrs_reserved cenv cu` by
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `si` >> simp[]) >>
      `!n b len. local_region cenv mid.scopes z n b len ==>
         w2n aw + nw <= b \/ b + len <= w2n aw` by
        (qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> local_region cenv mid.scopes wt n b sz` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ b cap` mp_tac >>
         qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv cu` mp_tac >>
         qpat_assum `nw <= MAX 32 _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              loweringStateRelDefsTheory.local_ptrs_reserved_def,
              loweringStateRelDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
         `local_region cenv mid.scopes wt n b len` by
           (qpat_x_assum `local_region cenv mid.scopes z n b len` mp_tac >>
            simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
         `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + len <= w2n aw` by metis_tac[] >>
         gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `ghost_inv_at (DF H) lo d cenv cx mid wG wtn wt` by
        (irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `lo <= z.vs_alloca_next` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >> rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >> simp[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `allocas_from lo z` mp_tac >>
            qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def,
                 typedMemoryCopyTheory.typed_copy_state_frame_def] >> rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
            simp[] >> metis_tac[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` mp_tac >>
            qpat_assum `wtn.t_stor = tn'.t_stor` mp_tac >>
            qpat_assum `wtn.t_trans = tn'.t_trans` mp_tac >>
            qpat_assum `wtn.t_imm = tn'.t_imm` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
                 bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def] >>
            rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z` mp_tac >>
            disch_then (fn th =>
              map_every (mp_tac o C AP_TERM th)
                [``\st:venom_state. st.vs_accounts``, ``\st:venom_state. st.vs_transient``,
                 ``\st:venom_state. st.vs_call_ctx``, ``\st:venom_state. st.vs_immutables``]) >>
            simp[] >> metis_tac[]) >>
         qexistsl_tac [`G'`, `func`, `nw`, `z`, `cu`, `w2n aw`, `tn'`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `si` >> simp[] >> metis_tac[]) >>
         conj_tac >-
           (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `si` >> simp[] >> metis_tac[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qpat_assum `!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==> _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            first_x_assum irule >> decide_tac) >>
         conj_tac >-
           (qpat_assum `allocas_from lo at` mp_tac >>
            qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `cenv.ce_is_ctor ==> !name tv v off.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
         FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
           | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
         regions_disjoint off (type_memory_size tv) (w2n aw) nw` by
        (qpat_assum `nw <= MAX 32 _` mp_tac >>
         qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         qpat_assum `MEM (mk_inst ci.cs_next_id ALLOCA _ _) (fn_insts func)` mp_tac >>
         qpat_assum `FLOOKUP z.vs_allocas ci.cs_next_id = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         `regions_disjoint off (type_memory_size tv) (w2n aw)
            (MAX 32 (type_memory_bytes cenv dty))` by
           (drule_at (Pat `MEM _ (fn_insts _)`)
              (INST_TYPE [``:'a`` |-> ``:256``]
                assignEffectfulIndexSnapshotSeparationTheory.snapshot_constructor_allocations_disjoint) >>
            simp[venomInstTheory.mk_inst_def] >>
            disch_then irule >>
            qexistsl_tac [`H`,`cenv`,`ctx`,`cx`,`mid`,`v`,`name`,`z`] >> simp[]) >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
         decide_tac) >>
      conj_tac >-
        (qmatch_abbrev_tac `stmt_state_rel H ctx func cenv cx mid wt` >>
         `stmt_state_rel H ctx func cenv cx mid
           (wt with <|vs_prev_bb := z.vs_prev_bb;
             vs_current_bb := z.vs_current_bb; vs_inst_idx := z.vs_inst_idx|>)` suffices_by
           simp[bodyPtrMakeArrayCopyStateFrameTheory.literal_stmt_state_rel_cursor] >>
         irule exprSimBufferStoreTheory.buffer_store_state_frame >>
         qexistsl_tac [`w2n aw`,`nw`,`z`,`cu`] >>
         qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `!n lb sz. local_region cenv mid.scopes z n lb sz ==> _` mp_tac >>
         qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv cu` mp_tac >>
         qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              typedMemoryCopyTheory.typed_copy_frame_def,
              venomStateTheory.lookup_var_def] >> metis_tac[]) >>
      `storage_well_formed_on cx mid (FST H)` by
        (qpat_assum `expr_post H ctx func cenv cx e esi si cu s mid v op z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
      qpat_assum `storage_well_formed_on cx mid (FST H)` mp_tac >>
      qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid wG wtn wt` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[bodyPtrDefsTheory.ghost_inv_at_def,
           vyperStorageFootprintTheory.storage_well_formed_on_def,
           vyperStorageBackendTheory.get_storage_def] >>
      rpt strip_tac >> simp[]
      >- (Cases_on `b` >> gvs[vyperStorageBackendTheory.get_storage_def] >>
          metis_tac[vyperStorageBackendTheory.get_storage_def]) >>
      metis_tac[]) >>
  Cases_on `is_word_type dty`
  >- (`compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)` by
        (qpat_assum `store_step cu = (u,cs)` mp_tac >>
         qpat_assum `Abbrev (store_step = _)` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         qpat_assum `buf.buf_operand = Var aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[markerTheory.Abbrev_def, contextTheory.compile_store_memory_def] >>
         Cases_on `emit_void MSTORE [Var aq; op] cu` >> simp[]) >>
      `expr_type e = dty` by
        (qpat_assum `LIST_REL (type_widens_to _) _ (dty::dtys1)` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >>
         metis_tac[compileEnvTheory.type_widens_to_word]) >>
      `post_value_type cenv e = dty` by simp[post_value_type_word] >>
      `eval_operand op z = SOME (typed_val_to_w256 rty v)` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `post_value_type cenv e = dty` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tn' op = {}` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def]) >>
      `ptr_covers G' tn' aq z 32` by
        (qpat_assum `ptr_covers G' tn' aq z (MAX 32 _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
         qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> gvs[arithmeticTheory.MAX_DEF]) >>
      `w2n aw + 32 <= z.vs_alloca_next` by
        (qpat_assum `w2n aw + MAX 32 _ <= z.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF]) >>
      `w2n aw + 32 < dimword (:256)` by
        (qpat_assum `w2n aw + MAX 32 _ < dimword (:256)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF]) >>
      qpat_assum `compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)`
        (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac
          logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      `evaluate_type (get_tenv cx) dty = SOME rty` by
        (qpat_assum `post_value_type cenv e = dty` (fn th =>
           qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`
             (ACCEPT_TAC o REWRITE_RULE [th]))) >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
      `value_has_type rty v` by
        (qpat_assum `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type rty v`
          irule >> first_assum ACCEPT_TAC) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `wt` (qx_choose_then `wG` (qx_choose_then `wtn` strip_assume_tac))) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t,G1,tn1) [] (OK wt,wG,wtn)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) _ _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) _ _ /\ _`
           drule >>
         qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') _ _`
           (qspec_then `DF H` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
      `alloca_history func wt` by
        (`cs.cs_current_bb = cu.cs_current_bb /\
          cs.cs_current_insts = cu.cs_current_insts ++
            [mk_inst cu.cs_next_id MSTORE [Var aq;op] []]` by
           (qpat_assum `compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)` mp_tac >>
            qpat_assum `is_word_type dty` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `emit_inst MSTORE [Var aq;op] [] cu = ((),cs)` by
              gvs[contextTheory.compile_store_memory_def,
                  emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
            drule emitHelperPropsTheory.emit_inst_extends >> simp[]) >>
         irule allocaHistoryTheory.alloca_history_frame >>
         qexists_tac `(mstore (w2n aw) (typed_val_to_w256 rty v) z)
                        with vs_inst_idx := LENGTH cs.cs_current_insts` >>
         reverse (rpt conj_tac)
         >- (`alloca_inv z` by
               (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
                  (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                (impl_tac >- first_assum ACCEPT_TAC) >>
                POP_ASSUM_LIST (K all_tac) >> simp[expr_post_def] >> rpt strip_tac >>
                drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
             irule intcall_args_word_store_history >> simp[] >>
             qexistsl_tac [`aq`,`cenv`,`cu`,`dty`,`op`,`vv_type vv`] >> simp[]) >>
         qpat_assum `typed_copy_state_frame _ _ _ z wt` mp_tac >>
         qpat_assum `wt.vs_inst_idx = LENGTH cs.cs_current_insts` mp_tac >>
         qpat_assum `wt.vs_current_bb = cs.cs_current_bb` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `cs.cs_current_bb = cu.cs_current_bb` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.mstore_def,
              venomStateTheory.write_memory_with_expansion_def,
              venomStateTheory.venom_state_component_equality] >>
         metis_tac[]) >>
      qexistsl_tac [`wt`,`wG`,`wtn`,`32`] >>
      simp[] >>
      conj_tac
      >- (irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
          first_assum ACCEPT_TAC) >>
      disj1_tac >>
      `type_memory_size rty = 32` by
        (irule exprSimPropsTheory.word_tv_memory_size >>
         qexistsl_tac [`dty`,`get_tenv cx`] >> simp[]) >> simp[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    (qpat_assum `LIST_REL (type_widens_to _) _ (dty::dtys1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `~is_word_type (expr_type e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `~is_word_type dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq]) >>
  `~is_word_type (post_value_type cenv e)` by
    (strip_tac >>
     qpat_assum `is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)` drule >>
     simp[]) >>
  `?sw. eval_operand op z = SOME sw` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
     metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type (expr_type e)` by
        (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `dty` >> simp[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b` >> simp[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `expr_type e` >>
         simp[vyperTypeSystemTheory.type_widens_to_def, vyperTypeSystemTheory.arg_type_fits_def] >>
         Cases_on `b` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b'` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b''` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def]) >>
      `post_value_type cenv e = expr_type e` by simp[] >>
      `value_has_type rty v /\ type_memory_size rty < 2 ** 64` by simp[] >>
      `(!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           val_in_memory rty v (w2n sw) mem) /\
       (val_footprint rty v <> 0 ==> ?x b sz. op = Var x /\
         FLOOKUP G' x = SOME (b,sz) /\ b <= w2n sw /\
         w2n sw + val_store_size rty v <= b+sz)` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `eval_operand op z = SOME sw` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
         metis_tac[]) >>
      `?len. val_store_size rty v = 32 + 32 * ((len+31) DIV 32) /\
         32 + 32 * ((len+31) DIV 32) <= type_memory_size rty /\
         (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len)` by
        (qpat_assum `is_bytestring_type (expr_type e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
         gvs[] >> drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >> gvs[] >>
         Cases_on `v` >>
         gvs[vyperTypingTheory.value_has_type_def, exprSimPropsTheory.val_store_size_def,
             valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
             vfmConstantsTheory.word_size_def] >>
         qmatch_goalsub_abbrev_tac `(actual_len + 31) DIV 32` >>
         qexists_tac `actual_len` >> simp[] >>
         irule arithmeticTheory.DIV_LE_MONOTONE >> simp[Abbr `actual_len`]) >>
      `!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn'.t_mem` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[representationCleanPtrTheory.robust_mem_word_at_clean]) >>
      `mload (w2n sw) z = n2w len` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len`
           (qspec_then `z.vs_memory` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def, venomStateTheory.mload_def,
              valueEncodingDefsTheory.mem_word_at_def]) >>
      `val_footprint rty v <> 0` by
        (qpat_assum `is_bytestring_type (expr_type e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >> gvs[] >>
         Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
           loweringPostsTheory.val_footprint_def]) >>
      `?src. op = Var src /\ lookup_var src z = SOME sw /\
         ptr_covers G' tn' src z (32+32*((len+31) DIV 32))` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `eval_operand op z = SOME sw` mp_tac >>
         qpat_assum `val_footprint rty v <> 0` mp_tac >>
         qpat_assum `val_store_size rty v = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `32+32*((len+31) DIV 32) <= val_store_size rty v` by simp[] >>
         fs[bodyPtrDefsTheory.ptr_val_ok_def,
            bodyPtrDefsTheory.ptr_mem_ok_def] >>
         gvs[] >> simp[bodyPtrDefsTheory.ptr_covers_def] >>
         fs[venomStateTheory.eval_operand_def] >>
         qexists_tac `sw` >> simp[]) >>
      `len+31 < dimword(:256) /\
       32+32*((len+31) DIV 32) < dimword(:256)` by
        (qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         qpat_assum `type_memory_size rty < 2 ** 64` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
         disch_then (qspec_then `len+31` strip_assume_tac) >>
         qmatch_asmsub_abbrev_tac `len+31 = _ + residue` >>
         `residue < 32` by simp[Abbr `residue`] >>
         gvs[wordsTheory.dimword_def] >> decide_tac) >>
      `type_memory_size rty <= type_memory_bytes cenv dty` by
        (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `expr_type e` >>
         gvs[vyperTypeSystemTheory.type_widens_to_def, vyperTypeSystemTheory.arg_type_fits_def,
           vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
           compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def] >>
         rename1 `expr_type e = BaseT bt` >>
         Cases_on `bt` >> gvs[vyperTypeSystemTheory.arg_type_fits_def,
           vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
           compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def] >>
         gvs[compileEnvTheory.is_bytestring_type_def] >>
         TRY (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[] >> NO_TAC) >>
         Cases_on `b'` >> gvs[compileEnvTheory.is_bytestring_type_def,
           vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.evaluate_type_def,
           valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
           vfmConstantsTheory.word_size_def] >>
         Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def,
           vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.evaluate_type_def,
           valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
           vfmConstantsTheory.word_size_def] >>
         irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
      `ptr_covers G' tn' aq z (32+32*((len+31) DIV 32))` by
        (qpat_assum `ptr_covers G' tn' aq z (MAX 32 _)` mp_tac >>
         qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         qpat_assum `type_memory_size rty <= type_memory_bytes cenv dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
         qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >>
         gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)` by
        (qpat_assum `store_step cu = (u,cs)` mp_tac >>
         qpat_assum `Abbrev (store_step = _)` mp_tac >>
         qpat_assum `~is_word_type dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         qpat_assum `buf.buf_operand = Var aq` mp_tac >>
         qpat_assum `op = Var src` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         gvs[markerTheory.Abbrev_def, contextTheory.compile_store_memory_def,
           comp_ignore_bind_def, comp_bind_def, comp_return_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `compile_store_bytestring (Var src) (Var aq) cu` >>
         gvs[oneline compileEnvTheory.is_bytestring_type_def,
           comp_bind_def, comp_return_def]) >>
      `not_fresh_at cu src /\ not_fresh_at cu aq` by
        (conj_tac
         >- (`!x. vv_operand vv = Var x ==> not_fresh_at ca x` by
               (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `ci` >> simp[]) >>
             qpat_assum `unwrap_value cenv vv ca = (op,cu)`
               (mp_then Any mp_tac exprOperandVarTheory.compiler_unwrap_value_var) >>
             qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at ca x` mp_tac >>
             qpat_assum `op = Var src` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             Cases_on `vv` >> simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `not_fresh_at ca aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `w2n sw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next /\
       w2n aw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next` by
        (conj_tac
         >- (map_every (fn q => qpat_assum q mp_tac)
               [`expr_store_bound cx (post_value_type cenv e) v op z`,
                `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
                `~is_word_type (post_value_type cenv e)`, `eval_operand op z = SOME sw`,
                `val_store_size rty v = 32+32*((len+31) DIV 32)`] >>
             POP_ASSUM_LIST (K all_tac) >>
             simp[exprSimMemDefsTheory.expr_store_bound_def] >> metis_tac[]) >>
         map_every (fn q => qpat_assum q mp_tac)
           [`w2n aw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next`,
            `32+32*((len+31) DIV 32) <= type_memory_size rty`,
            `type_memory_size rty <= type_memory_bytes cenv dty`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `run_inst_seq_mem_ok (emitted_insts cu cs) z` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`,
            `not_fresh_at cu src`, `not_fresh_at cu aq`,
            `lookup_var src z = SOME sw`, `lookup_var aq z = SOME aw`,
            `mload (w2n sw) z = n2w len`,
            `32+32*((len+31) DIV 32) < dimword (:256)`,
            `w2n sw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next`,
            `w2n aw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         irule bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok >>
         qexistsl_tac [`aw`,`Var aq`,`len`,`Var src`,`sw`] >>
         simp[venomStateTheory.eval_operand_def, vfmConstantsTheory.word_size_def] >>
         rpt strip_tac >> gvs[]) >>
      `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts cu cs) (DROP z.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         qpat_assum `fn_has_code cu cs func` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `z.vs_inst_idx = LENGTH cu.cs_current_insts` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         gvs[fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
             rich_listTheory.IS_PREFIX_APPEND,
             DROP_APPEND1, DROP_APPEND2]) >>
      qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
        (mp_then Any mp_tac bodyFullAllocGenericTheory.compile_store_bytestring_origin_ptr_path) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `mload _ _ = _`)) >>
      disch_then (drule_at (Pat `run_inst_seq_mem_ok _ _`)) >>
      disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`] mp_tac) >>
      disch_then (qspecl_then [`G'`,`tn'`,`32+32*((len+31) DIV 32)`] mp_tac) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `bG` (qx_choose_then `btn`
        (qx_choose_then `bt` strip_assume_tac))) >>
      `val_in_memory rty v (w2n sw) z.vs_memory /\ val_wf rty v` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> val_in_memory _ _ _ mem` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
      `val_in_memory rty v (w2n aw) bt.vs_memory /\
       typed_copy_state_frame cu (w2n aw) (type_memory_size rty) z bt` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`,
           `not_fresh_at cu src`, `not_fresh_at cu aq`,
           `lookup_var src z = SOME sw`, `lookup_var aq z = SOME aw`,
           `mload (w2n sw) z = n2w len`,
           `32+32*((len+31) DIV 32) < dimword (:256)`,
           `run_inst_seq (emitted_insts cu cs) z = OK bt`,
           `val_in_memory rty v (w2n sw) z.vs_memory`, `val_wf rty v`,
           `val_store_size rty v = 32+32*((len+31) DIV 32)`,
           `32+32*((len+31) DIV 32) <= type_memory_size rty`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `mem_word_at (w2n sw) z.vs_memory = n2w len` by
           gvs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
         qpat_assum `compile_store_bytestring _ _ _ = _`
           (mp_then Any mp_tac valueCopyTheory.store_bytestring_run_exact) >>
         disch_then (qspecl_then [`z`,`sw`,`aw`,`len`] mp_tac) >>
         simp[venomStateTheory.eval_operand_def, vfmConstantsTheory.word_size_def] >>
         strip_tac >> gvs[]
         >- (irule valueCopyTheory.mcopy_val_in_memory >>
             simp[vfmConstantsTheory.word_size_def] >>
             metis_tac[exprSimPropsTheory.val_footprint_le_store_size]) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
         conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
         simp[typedMemoryCopyTheory.typed_copy_frame_def] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
             simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
         simp[venomExecSemanticsTheory.mcopy_def,
              immutableMemoryFrameTheory.immutable_write_memory_capacity,
              arithmeticTheory.MAX_DEF, vfmConstantsTheory.word_size_def]) >>
      `mem_bytes_at (w2n aw) (32+32*((len+31) DIV 32)) bt.vs_memory =
         mem_bytes_at (w2n sw) (32+32*((len+31) DIV 32)) z.vs_memory` by
        (qpat_assum `bt.vs_memory = (mcopy _ _ _ z).vs_memory` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[valueEncodingProofsTheory.mcopy_mem_bytes_at_same]) >>
      `!i. i < 32+32*((len+31) DIV 32) ==>
         (w2n aw+i IN btn.t_mem <=> w2n sw+i IN tn'.t_mem)` by
        (qpat_assum `btn.t_mem = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[] >> rpt strip_tac >> simp[] >> decide_tac) >>
      `!mem. mem_agree_outside btn.t_mem bt.vs_memory mem ==>
         val_in_memory rty v (w2n aw) mem` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`val_wf rty v`, `val_store_size rty v = 32+32*((len+31) DIV 32)`,
           `mem_bytes_at (w2n aw) (32+32*((len+31) DIV 32)) bt.vs_memory = _`,
           `!i. i < 32+32*((len+31) DIV 32) ==> _`,
           `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> val_in_memory _ _ _ mem`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         `val_footprint rty v <= 32+32*((len+31) DIV 32)` by
           metis_tac[exprSimPropsTheory.val_footprint_le_store_size] >>
         rpt strip_tac >>
         irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`z.vs_memory`,`bt.vs_memory`,`32+32*((len+31) DIV 32)`,
           `w2n sw`,`tn'.t_mem`,`btn.t_mem`] >> simp[]) >>
      qabbrev_tac `bst = bt with vs_inst_idx :=
        z.vs_inst_idx + LENGTH (emitted_insts cu cs)` >>
      `bst.vs_inst_idx = LENGTH cs.cs_current_insts /\
       bst.vs_current_bb = cs.cs_current_bb` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         qpat_assum `z.vs_inst_idx = LENGTH cu.cs_current_insts` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `run_inst_seq (emitted_insts cu cs) z = OK bt` mp_tac >>
         qpat_assum `isPREFIX (emitted_insts cu cs) (DROP z.vs_inst_idx _)` mp_tac >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
            (emitted_insts cu cs)` by
           gvs[bytesCopyCodeTheory.bytes_copy_insts_def,
               venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
         gvs[markerTheory.Abbrev_def, exprLoweringPropsTheory.same_blocks_def] >>
         metis_tac[fragExecTheory.exec_block_run_inst_seq]) >>
      `typed_copy_state_frame cu (w2n aw) (type_memory_size rty) z bst /\
       (!mem. mem_agree_outside btn.t_mem bst.vs_memory mem ==>
         val_in_memory rty v (w2n aw) mem)` by
        (qpat_assum `typed_copy_state_frame cu _ _ z bt` mp_tac >>
         qpat_assum `!mem. mem_agree_outside btn.t_mem bt.vs_memory mem ==> _` mp_tac >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[markerTheory.Abbrev_def, typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.lookup_var_def]) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t,G1,tn1) [] (OK bst,bG,btn)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) [] _ /\ _`
           drule >>
         qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         gvs[markerTheory.Abbrev_def] >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
      `alloca_history func bst` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         map_every (fn q => qpat_assum q mp_tac)
           [`fn_has_code cu cs func`, `fn_inst_ids_distinct func`,
            `alloca_history func z`, `z.vs_current_bb = cu.cs_current_bb`,
            `z.vs_inst_idx = LENGTH cu.cs_current_insts`,
            `run_inst_seq (emitted_insts cu cs) z = OK bt`,
            `bst.vs_inst_idx = LENGTH cs.cs_current_insts`, `Abbrev (bst = _)`,
            `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) [] _ /\ _`,
            `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `alloca_inv z` by
           (qpat_x_assum `!H. _` drule >>
            simp[loweringPostsTheory.expr_post_def] >> rpt strip_tac >>
            drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
         `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cu cs)` by
           gvs[bytesCopyCodeTheory.bytes_copy_insts_def,
               venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
         `alloca_history func (bt with vs_inst_idx := LENGTH cs.cs_current_insts)` by
           (irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
            conj_tac >- first_assum ACCEPT_TAC >>
            qexistsl_tac [`emitted_insts cu cs`,`z`,`cu`] >>
            gvs[exprLoweringPropsTheory.same_blocks_def]) >>
         gvs[markerTheory.Abbrev_def]) >>
      `~bst.vs_halted` by
        (qpat_assum `typed_copy_state_frame cu _ _ z bst` mp_tac >>
         qpat_assum `~z.vs_halted` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.venom_state_component_equality]) >>
      `!i. ~(w2n aw <= i /\ i < w2n aw + type_memory_size rty) ==>
         (i IN btn.t_mem <=> i IN tn'.t_mem)` by
        (qpat_assum `btn.t_mem = _` mp_tac >>
         qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >>
         eq_tac >> simp[] >> rpt strip_tac >> decide_tac) >>
      qexistsl_tac [`bst`,`bG`,`btn`,`type_memory_size rty`] >>
      conj_tac >- (irule arithmeticTheory.LE_TRANS >>
        qexists_tac `type_memory_bytes cenv dty` >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!p. not_fresh_at cu p ==> _ /\ _ /\ _` drule >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> disch_tac >>
      `!mem. mem_agree_outside btn.t_mem bst.vs_memory mem ==>
        value_has_type rt v /\ val_wf rt v /\
        type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
        val_in_memory rt v (w2n aw) mem` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`is_bytestring_type (expr_type e)`, `is_bytestring_type dty`,
            `type_widens_to (get_tenv cx) (expr_type e) dty`,
            `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
            `post_value_type cenv e = expr_type e`, `value_has_type rty v`,
            `evaluate_type (get_tenv cx) dty = SOME rt`,
            `!mem. mem_agree_outside btn.t_mem bst.vs_memory mem ==> _`] >>
         POP_ASSUM_LIST (K all_tac) >> ntac 8 disch_tac >>
         qx_gen_tac `m` >> disch_tac >> gvs[] >>
         qpat_assum `!mem. _ ==> val_in_memory _ _ _ _` (drule_then assume_tac) >>
         drule_all intcall_args_bytestring_widen >> simp[]) >>
      `mem_agree_outside btn.t_mem bst.vs_memory bst.vs_memory` by
        simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
      qpat_assum `!mem. _ ==> value_has_type rt v /\ _` (drule_then strip_assume_tac) >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!mem. _ ==> value_has_type rt v /\ _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  `vv_type vv = lowered_value_type cenv e` by
    (qpat_assum `!e dty ee ci vv cm. _` irule >>
     conj_tac >- (qexistsl_tac [`si`,`ci`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `dty` >> simp[]) >>
     qexists_tac `esi` >> first_assum ACCEPT_TAC) >>
  `~is_bytestring_type (expr_type e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `~is_bytestring_type dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
           metis_tac[valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >> strip_tac >>
     `well_typed_expr tenv e /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv.type_defs /\
      (!fid sig. FLOOKUP tenv.fn_sigs fid = SOME sig ==>
        cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
       (qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        disch_then (strip_assume_tac o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
        fs[exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     drule exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
     disch_then (qspec_then `cenv` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`~is_word_type (expr_type e)`, `~is_bytestring_type (expr_type e)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[loweringPostsTheory.post_value_type_lowered,
         loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `value_has_type rty v /\ val_wf rty v` by
    (`value_has_type rty v` by
       (qpat_assum `!v. read_result cx tv mid = _ ==> value_has_type rty v` irule >>
        first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule memoryValueTypingTheory.value_has_type_val_wf >> first_assum ACCEPT_TAC) >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >>
     qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     disch_then (strip_assume_tac o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
     rpt strip_tac >>
     metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >>
     qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `well_formed_type (get_tenv cx) (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
     strip_tac >- gvs[] >> strip_tac >> disj2_tac >>
     conj_tac >- (irule (CONJUNCT1 typedCopyCompatibilityTheory.arg_type_fits_trans) >>
       qexists_tac `expr_type e` >> simp[]) >> first_assum ACCEPT_TAC) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `well_formed_type (get_tenv cx) (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def,
          vyperTypeSystemTheory.well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `type_memory_bytes cenv dty = type_memory_size dtv /\
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty` by
    (conj_tac >> irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum drule >> qexistsl_tac [`tenv`,`esi`] >> first_assum ACCEPT_TAC) >>
  `value_has_type dtv v` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty`,
        `post_value_type cenv e = lowered_value_type cenv e`,
        `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
        `evaluate_type (get_tenv cx) dty = SOME dtv`, `value_has_type rty v`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[vyperTypeSystemTheory.type_widens_to_def] >>
     irule (CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type) >>
     goal_assum drule >> goal_assum drule >> goal_assum drule >> simp[]) >>
  `val_wf dtv v` by
    (irule memoryValueTypingTheory.value_has_type_val_wf >> first_assum ACCEPT_TAC) >>
  `(!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
       val_in_memory rty v (w2n sw) mem) /\ op_taint tn' op = {}` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`ptr_val_ok cx (post_value_type cenv e) v op G' tn' z`,
        `~is_word_type (post_value_type cenv e)`,
        `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
        `eval_operand op z = SOME sw`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
     metis_tac[]) >>
  `compile_store_memory cenv op (Var aq) dty (lowered_value_type cenv e) cu = ((),cs)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`store_step cu = (u,cs)`, `Abbrev (store_step = _)`,
        `~is_word_type dty`, `~is_bytestring_type dty`,
        `buf.buf_operand = Var aq`, `vv_type vv = lowered_value_type cenv e`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, oneline compileEnvTheory.is_bytestring_type_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK z,G',tn')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] _`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path _ (at,aG,atn) [] _ /\ _` drule >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  reverse (Cases_on `type_memory_size rty = 0`)
  >- (`?src. op = Var src /\ lookup_var src z = SOME sw /\
         ptr_covers G' tn' src z (type_memory_size rty)` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z`,
            `~is_word_type (post_value_type cenv e)`, `eval_operand op z = SOME sw`,
            `op_taint tn' op = {}`, `type_memory_size rty <> 0`,
            `post_value_type cenv e = lowered_value_type cenv e`,
            `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty`] >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         gvs[bodyPtrDefsTheory.ptr_buf_ok_def] >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >>
         gvs[venomStateTheory.eval_operand_def]) >>
      `not_fresh_at cu src /\ not_fresh_at cu aq` by
        (conj_tac
         >- (`!x. vv_operand vv = Var x ==> not_fresh_at ca x` by
               (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `ci` >> simp[]) >>
             qpat_assum `unwrap_value cenv vv ca = (op,cu)`
               (mp_then Any mp_tac exprOperandVarTheory.compiler_unwrap_value_var) >>
             qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at ca x` mp_tac >>
             qpat_assum `op = Var src` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             Cases_on `vv` >> simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `not_fresh_at ca aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `acyclic_struct_metadata cenv.ce_struct_fields` by
        (qpat_assum `body_inv tops ctx cenv cx`
           (ACCEPT_TAC o MATCH_MP bodyInvCodePropsTheory.contract_inv_acyclic_struct_metadata o
            MATCH_MP bodySimTheory.body_inv_contract)) >>
      `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
       (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
         ALL_DISTINCT (MAP FST fields) /\
         EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
           sz = type_memory_size rt) fields)` by
        (qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
      `z.vs_alloca_next < dimword (:256)` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[loweringPostsTheory.expr_post_def] >>
         drule stateRelProjTheory.stmt_state_rel_alloca_room >>
         metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >>
      `w2n sw + type_memory_size rty <= z.vs_alloca_next` by
        (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _` mp_tac >>
         map_every (fn q => qpat_assum q mp_tac)
           [`~is_word_type (post_value_type cenv e)`,
            `post_value_type cenv e = lowered_value_type cenv e`,
            `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
            `eval_operand op z = SOME sw`, `type_memory_size rty <> 0`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      `~is_bytestring_type (lowered_value_type cenv e)` by
        (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` mp_tac >>
         qpat_assum `~is_bytestring_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[vyperTypeSystemTheory.type_widens_to_def] >>
         metis_tac[valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
      `ci.cs_next_id < ca.cs_next_id` by
        (qpat_assum `compile_alloc_buffer _ ci = (buf,ca)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
              compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
              compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
              compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.emit_def] >>
         strip_tac >> gvs[]) >>
      `FLOOKUP z.vs_allocas ci.cs_next_id =
        SOME (w2n aw,MAX 32 (type_memory_bytes cenv dty))` by
        (qpat_assum `wb_frame cenv mid mid ca at z` mp_tac >>
         qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
         qpat_assum `ci.cs_next_id < ca.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
      `alloca_inv z` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> simp[expr_post_def] >> rpt strip_tac >>
         drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
      `local_ptrs_reserved cenv ca` by
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `ci` >> simp[]) >>
      `!name b sz. local_region cenv mid.scopes z name b sz ==>
        w2n aw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + sz <= w2n aw` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`!x. not_fresh_at ca x ==> lookup_var x z = lookup_var x at /\ _`,
            `!name b len. local_region cenv mid.scopes at name b len ==> _`,
            `local_ptrs_reserved cenv ca`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.local_region_def,
              loweringStateRelDefsTheory.local_ptrs_reserved_def,
              loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
      irule (Q.INST [`sa` |-> `si`, `sm` |-> `ci`, `sb` |-> `ca`,
                     `did` |-> `ci.cs_next_id`] intcall_args_aggregate_store_nonzero) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qexists_tac `dtv` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`ca`,`ci`,`aq`,`tv`,`si`,`src`,`rty`,`lowered_value_type cenv e`,`sw`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      map_every (fn q => qpat_assum q mp_tac)
        [`~is_word_type (post_value_type cenv e)`,
         `post_value_type cenv e = lowered_value_type cenv e`,
         `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
         `op = Var src`,
         `compile_store_memory cenv op (Var aq) dty (lowered_value_type cenv e) cu = ((),cs)`,
         `~is_word_type (post_value_type cenv e) ==> vv_at cenv cx _ si ci mid tv _ z \/ _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gnvs[]) >>
  `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rty` by
    (qpat_assum `post_value_type cenv e = lowered_value_type cenv e` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  irule intcall_args_aggregate_store_zero >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt (goal_assum (drule_at Any) >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
QED

Theorem intcall_args_stage_full_p2:
  !es DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
   st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin f P Q R.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv esi /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (supported_value_type tops) dtys /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (vyperState$bind (eval_exprs cx es) f) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) /\
    (!marks xs ee t G1 tn1.
       (!tail. eval_exprs cx es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       LENGTH xs = LENGTH es /\ expr_sim_inv cenv cx tenv ee /\
       (?ws1.
         LENGTH ws1 = LENGTH (ops ++ newops) /\
         LENGTH (vals ++ xs) = LENGTH (ops ++ newops) /\
         LENGTH (ptys ++ dtys) = LENGTH (ops ++ newops) /\
         LENGTH (pflags ++ flags) = LENGTH (ops ++ newops) /\
         eval_operands (ops ++ newops) t = SOME ws1 /\
         EVERY (\op. op_taint tn1 op = {}) (ops ++ newops) /\
         (!x. MEM (Var x) (ops ++ newops) ==> not_fresh_at sf x) /\
         (!j rt. j < LENGTH (ops ++ newops) /\
           evaluate_type (get_tenv cx) (EL j (ptys ++ dtys)) = SOME rt ==>
           value_has_type rt (EL j (vals ++ xs)) /\
           val_wf rt (EL j (vals ++ xs)) /\
           val_footprint rt (EL j (vals ++ xs)) <= type_memory_size rt /\
           (EL j (pflags ++ flags) ==>
             EL j ws1 = typed_val_to_w256 rt (EL j (vals ++ xs))) /\
           (~EL j (pflags ++ flags) ==>
             ?b cap aid.
               op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
               FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
               sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
               lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws1) /\
               w2n (EL j ws1) + type_memory_size rt <= b+cap /\
               (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
                 val_in_memory rt (EL j (vals ++ xs)) (w2n (EL j ws1)) mem) /\
               (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
                 b+cap <= lb \/ lb+sz <= b) /\
               (case pin of NONE => T | SOME (rb,pb,pk) =>
                 b+cap <= pb \/ pb+pk <= b)))) /\
       (case pin of NONE => T | SOME (rb,b,k) =>
         FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
         lookup_var rb t = SOME (n2w b) /\
         FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
         sa.cs_next_id < sf.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
         not_fresh_at sf rb /\
         (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
           b+k <= lb \/ lb+sz <= b)) /\
       wb_frame cenv es0 ee sa s0 t /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
       alloca_history func t /\ sa.cs_next_id <= sf.cs_next_id /\
       sa.cs_next_var <= sf.cs_next_var /\
       (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
          local_region cenv ee.scopes t n b sz) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       MAP FDOM es0.scopes = MAP FDOM ee.scopes /\
       return_buf_frame d cenv sf t /\ ~t.vs_halted /\
       t.vs_current_bb = sf.cs_current_bb /\
       t.vs_inst_idx = LENGTH sf.cs_current_insts /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
       gas_admissible (f xs) P ee ==>
       gas_outcome_full
         (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (f xs) (ee,t,G1,tn1) Q R) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (vyperState$bind (eval_exprs cx es) f) (esi,s,G,tn) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`es`,`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,`tops`,`cenv`,`cx`,`tenv`,`st0`,`sa`,`s0`,`es0`,`G0`,`tn0`,`si`,`sf`,`shadow_si`,`shadow_sf`,`esi`,`s`,`G`,`tn`,`flags`,`dtys`,`newops`,`ops`,`ws`,`vals`,`ptys`,`pflags`,`pin`,`f`,`P`,`Q`,`R`]
    mp_tac (REWRITE_RULE[boolTheory.F_IMP,boolTheory.AND_CLAUSES]
      (Q.INST [`clean_words` |-> `F`, `keep_sites` |-> `F`]
        intcall_args_stage_full_p2_with_path)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!marks xs ee t G1 tn1. _` (qspecl_then [`marks`,`xs`,`ee`,`t`,`G1`,`tn1`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qexists_tac `ws1` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED



(* Compatibility for continuations that only need expr_exit. *)
Theorem intcall_args_stage_full:
  !es DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
   st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin f P Q R.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv esi /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (supported_value_type tops) dtys /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (vyperState$bind (eval_exprs cx es) f) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (!H res ee gt r. expr_exit res r ==> R H res ee gt r) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) /\
    (!marks xs ee t G1 tn1.
       (!tail. eval_exprs cx es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       LENGTH xs = LENGTH es /\ expr_sim_inv cenv cx tenv ee /\
       (?ws1.
         LENGTH ws1 = LENGTH (ops ++ newops) /\
         LENGTH (vals ++ xs) = LENGTH (ops ++ newops) /\
         LENGTH (ptys ++ dtys) = LENGTH (ops ++ newops) /\
         LENGTH (pflags ++ flags) = LENGTH (ops ++ newops) /\
         eval_operands (ops ++ newops) t = SOME ws1 /\
         EVERY (\op. op_taint tn1 op = {}) (ops ++ newops) /\
         (!x. MEM (Var x) (ops ++ newops) ==> not_fresh_at sf x) /\
         (!j rt. j < LENGTH (ops ++ newops) /\
           evaluate_type (get_tenv cx) (EL j (ptys ++ dtys)) = SOME rt ==>
           value_has_type rt (EL j (vals ++ xs)) /\
           val_wf rt (EL j (vals ++ xs)) /\
           val_footprint rt (EL j (vals ++ xs)) <= type_memory_size rt /\
           (EL j (pflags ++ flags) ==>
             EL j ws1 = typed_val_to_w256 rt (EL j (vals ++ xs))) /\
           (~EL j (pflags ++ flags) ==>
             ?b cap aid.
               op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
               FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
               sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
               lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws1) /\
               w2n (EL j ws1) + type_memory_size rt <= b+cap /\
               (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
                 val_in_memory rt (EL j (vals ++ xs)) (w2n (EL j ws1)) mem) /\
               (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
                 b+cap <= lb \/ lb+sz <= b) /\
               (case pin of NONE => T | SOME (rb,pb,pk) =>
                 b+cap <= pb \/ pb+pk <= b)))) /\
       (case pin of NONE => T | SOME (rb,b,k) =>
         FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
         lookup_var rb t = SOME (n2w b) /\
         FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
         sa.cs_next_id < sf.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
         not_fresh_at sf rb /\
         (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
           b+k <= lb \/ lb+sz <= b)) /\
       wb_frame cenv es0 ee sa s0 t /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
       alloca_history func t /\ sa.cs_next_id <= sf.cs_next_id /\
       sa.cs_next_var <= sf.cs_next_var /\
       (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
          local_region cenv ee.scopes t n b sz) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       MAP FDOM es0.scopes = MAP FDOM ee.scopes /\
       return_buf_frame d cenv sf t /\ ~t.vs_halted /\
       t.vs_current_bb = sf.cs_current_bb /\
       t.vs_inst_idx = LENGTH sf.cs_current_insts /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
       gas_admissible (f xs) P ee ==>
       gas_outcome_full
         (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (f xs) (ee,t,G1,tn1) Q R) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (vyperState$bind (eval_exprs cx es) f) (esi,s,G,tn) Q R
Proof
  rpt gen_tac >> strip_tac >>
  irule intcall_args_stage_full_p2 >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx tenv esi` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ es _ _ si = _` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) _ _ shadow_si = _`
    (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `gas_admissible (vyperState$bind (eval_exprs cx es) f) P esi`
    (irule_at Any) >>
  qpat_assum `eval_operands ops s = SOME ws` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >>
  qexistsl [`vals`, `ptys`, `pin`, `pflags`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Theorem intcall_args_stmt_state_rel_push[local]:
  stmt_state_rel H ctx func cenv (cx with stk updated_by CONS (NONE,name)) es s <=>
  stmt_state_rel H ctx func cenv cx es s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.accounts_rel_def,
       loweringStateRelDefsTheory.storage_vars_rel_def,
       loweringStateRelDefsTheory.transient_vars_rel_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.immutable_decl_sep_alt,
       vyperTypeEvalProofsTheory.get_module_code_stk_irrelevant,
       vyperTypeInvariantsTheory.lookup_var_slot_from_layout_context,
       vyperTypeEvalProofsTheory.get_tenv_stk_irrelevant]
QED

Theorem intcall_args_halt_exit_pop[local]:
  halt_exit H (cx with stk updated_by CONS (NONE,name)) es
    (INR HaltException : 'a + exception) r ==>
  halt_exit H cx es (INR HaltException : 'a + exception) r
Proof
  simp[exprSimDefsTheory.halt_exit_def, loweringStateRelDefsTheory.halt_rel_def,
       loweringStateRelDefsTheory.accounts_rel_def]
QED

(* (a) Arguments and frame setup, at (DF H, lo).  The caller's code up to
   the INVOKE, then any code continuation kc, runs against the source up
   to push_function, then any source continuation f, on one witness: the
   arguments' judgments run their staging, and whatever runs the rest of
   the call and f from an intcall_entry_full state (source, memory and
   pointer facts at t) runs the whole call and f.  Supplied arguments and
   omitted defaults use their respective expression-list judgments. *)
Theorem intcall_args_selected_invoke[local]:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 u G tn ==>
  ?bb inst ops argv callee setup entered.
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME
      (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
         cx.in_deploy,ops) /\
    eval_operands ops u = SOME argv /\
    lookup_function
      (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
         cx.in_deploy) ctx.ctx_functions = SOME callee /\
    setup_callee callee argv u = SOME setup /\
    gas_invoke_entry (ctx,func) u callee entered /\
    enters_block callee setup entered /\ ~u.vs_halted
Proof
  strip_tac >>
  `cenv.ce_func_ids = build_func_ids 0 tops /\
   cenv.ce_is_ctor = cx.in_deploy /\
   cenv.ce_func_param_types name = MAP SND args` by
    (drule_then strip_assume_tac intcall_args_body_inv_function_tables >>
     drule_then assume_tac intcall_args_body_inv_constructor >>
     drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
     simp[] >>
     irule intCallLookupTheory.build_func_param_types_distinct >>
     simp[] >> first_assum (irule_at Any) >>
     fs[supportedProgramTheory.supported_program_def,
        supportedNamesTheory.supported_declaration_names_def]) >>
  qhdtm_x_assum `intcall_entry_full`
    (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
  map_every (fn p => qpat_assum p mp_tac)
    [`cenv.ce_func_ids = _`, `cenv.ce_is_ctor = _`,
     `cenv.ce_func_param_types name = _`, `_ = internal_fn_label _ _ _ _`,
     `lookup_block u.vs_current_bb func.fn_blocks = _`,
     `get_instruction _ u.vs_inst_idx = _`, `decode_invoke _ = _`,
     `eval_operands _ u = _`, `gas_invoke_entry _ _ _ _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 9 strip_tac >>
  qpat_assum `gas_invoke_entry _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fragGasFocusTheory.gas_invoke_entry_def]) >>
  gvs[nsid_to_string_def, contextCodegenRelTheory.enters_block_def] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* Recover the argument evidence at the selected package and the
   decoded INVOKE, before entering the callee. *)
Theorem intcall_args_selected_package_entry[local]:
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 u G tn /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (label,ops) /\ eval_operands ops u = SOME argv /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  setup_callee callee argv u = SOME setup /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops T (K global_nonreentrant_slot) cenv.ce_is_ctor
      (if cenv.ce_is_ctor then imm_len tops else 0)
      (mut,nr,rr,name,args,(dflts : expr list),ret,ss)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,ss,rt) ==>
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
    internal_args_rel ce params penv (if has_rb then 1 else 0) argv
      u.vs_alloca_next mem) /\
  (!i off sz.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b bsz.
      op_prov G (EL ((if has_rb then 1 else 0) + i) ops) = SOME (b,bsz) /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
      w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
  u.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx callee setup /\ EVERY (\op. op_taint tn op = {}) ops /\
  ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev) G tn u
Proof
  strip_tac >>
  qhdtm_x_assum `intcall_entry_full`
    (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
  `bb' = bb` by
    (ntac 2 (qpat_x_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `inst' = inst` by
    (ntac 2 (qpat_x_assum `get_instruction _ u.vs_inst_idx = SOME _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `lbl = label /\ arg_ops = ops` by
    (ntac 2 (qpat_x_assum `decode_invoke _ = SOME _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_x_assum `arg_ops = ops` SUBST_ALL_TAC >>
  qpat_x_assum `lbl = label` SUBST_ALL_TAC >>
  `argv' = argv` by
    (ntac 2 (qpat_x_assum `eval_operands _ u = SOME _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!bb inst lbl ops argv. lookup_block _ _ = SOME bb /\ _ ==> _`
    drule_all >> strip_tac >>
  qpat_x_assum `!callee setup use_trans nkeys ilen dflts lbl' ce params has_rb
      is_nr key trans view ctor ilen' ss' rt.
       _ ==> (lbl' = lbl /\ _)`
    (drule_at_then (Pat `set_internal_package_target _ _ = _`)
       (drule_all_then strip_assume_tac)) >>
  qpat_x_assum `!callee setup use_trans nkeys ilen dflts lbl' ce params has_rb
      is_nr key trans view ctor ilen' ss' rt.
       _ ==> ((!mem. mem_agree_outside _ _ mem ==> _) /\ _)`
    drule_all >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!i off sz. _ ==> ?b bsz aid. _`
    (qspecl_then [`i`, `off`, `sz`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `b` (qx_choose_then `bsz` strip_assume_tac)) >>
  qexistsl [`b`, `bsz`] >> simp[]
QED

(* The packaged function's entry is the first block at its lookup name,
   not merely a block covered by the compiler interval. *)
Theorem intcall_args_packaged_head[local]:
  extract_context_with_internals entry ips cs = SOME (ctx,data) /\
  ALL_DISTINCT (ctx_fn_names ctx) /\ lbl <> entry /\
  lookup_function lbl ctx.ctx_functions = SOME callee ==>
  (HD callee.fn_blocks).bb_label = lbl
Proof
  simp[vyperCompilerTheory.extract_context_with_internals_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[venomInstTheory.mk_venom_context_def, venomInstTheory.ctx_fn_names_def,
      venomInstTheory.lookup_function_def, listTheory.FIND_thm,
      venomInstTheory.mk_raw_function_def] >>
  fs[GSYM venomInstTheory.lookup_function_def] >>
  drule venomInstTheory.lookup_function_MEM >> strip_tac >>
  drule fmpAnalysisPropsTheory.lookup_function_name >> strip_tac >>
  drule vyperCompilerTheory.package_internal_blocks_metadata >> strip_tac >>
  `MAP FST (internal_fn_descriptors ips) = MAP (\f. f.fn_name) functions` by
    (irule LIST_EQ >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `EL x (internal_fn_descriptors ips)` >>
     rename1 `EL x (internal_fn_descriptors ips) = p` >> PairCases_on `p` >>
     simp[vyperCompilerTheory.internal_fn_matches_descriptor_def]) >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  rename1 `internal_fn_matches_descriptor p callee` >> PairCases_on `p` >>
  gvs[vyperCompilerTheory.internal_fn_matches_descriptor_def] >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by simp[] >>
  drule_all intCallLookupTheory.package_internal_blocks_mem >> strip_tac >>
  qpat_assum `MEM (mk_internal_function _ _ _ _) _`
    (mp_then Any mp_tac intCallLookupTheory.lookup_function_distinct_mem) >>
  gvs[vyperCompilerTheory.mk_internal_function_metadata] >>
  disch_then (fn th => simp[Once th, vyperCompilerTheory.mk_internal_function_metadata])
QED

Theorem intcall_args_selected_head[local]:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  lookup_function (internal_fn_label (build_func_ids 0 tops name) name
                     (MAP SND args) cx.in_deploy) ctx.ctx_functions = SOME callee ==>
  (HD callee.fn_blocks).bb_label =
    internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) cx.in_deploy
Proof
  strip_tac >>
  drule_then strip_assume_tac intcall_args_body_inv_lowering >>
  Cases_on `cx.in_deploy` >> fs[]
  >- (Cases_on `classify_functions tops` >>
      rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
      `IS_SOME packages3` by
        (qpat_assum `body_inv tops _ cenv cx`
           (mp_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
         simp[bodyInvSplitTheory.contract_inv_def, classify_functions_unit_singleton]) >>
      Cases_on `packages3` >> fs[] >>
      drule_all ctorDeployLoweringCodeTheory.deploy_ctor_lowering_trace >>
      strip_tac >>
      fs[vyperCompilerTheory.install_immutable_reservation_def,
         vyperCompilerTheory.lowering_context_ok_def, venomInstTheory.ctx_fn_names_def] >>
      rename1 `extract_context_with_internals "__deploy" _ _ = SOME (raw,_)` >>
      `internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T <>
         "__deploy"` by simp[internal_fn_label_def] >>
      qpat_assum `extract_context_with_internals _ _ _ = _`
        (mp_then Any mp_tac intcall_args_packaged_head) >>
      simp[venomInstTheory.ctx_fn_names_def] >>
      disch_then irule >> simp[]) >>
  drule_all intCallLookupTheory.lower_vyper_runtime_unit_internal_lookup >>
  strip_tac >> gvs[vyperCompilerTheory.mk_internal_function_metadata]
QED

(* A freshly set-up callee has no predecessor, so a successful entry
   cannot skip a nonempty PHI prefix. *)
Theorem intcall_args_entered_capture[local]:
  setup_callee callee argv u = SOME setup /\
  enters_block callee setup entered /\
  (HD callee.fn_blocks).bb_label = label /\
  new_block label before = (old,entry) ==>
  entered = setup /\ fresh_vars_wrt entry entered /\
  entered.vs_params = argv /\ entered.vs_current_bb = entry.cs_current_bb /\
  entered.vs_inst_idx = LENGTH entry.cs_current_insts /\
  entered.vs_alloca_next = u.vs_alloca_next /\ entered.vs_allocas = FEMPTY /\
  entered.vs_transient = u.vs_transient /\ entered.vs_call_ctx = u.vs_call_ctx /\
  entered.vs_accounts = u.vs_accounts /\ entered.vs_immutables = u.vs_immutables /\
  entered.vs_memory = u.vs_memory /\
  entered.vs_initial_fmp = u.vs_initial_fmp /\
  entered.vs_fmp = u.vs_fmp /\ ~entered.vs_halted
Proof
  strip_tac >> drule emitHelperPropsTheory.new_block_props >> strip_tac >>
  qpat_x_assum `enters_block _ _ _`
    (strip_assume_tac o REWRITE_RULE [contextCodegenRelTheory.enters_block_def]) >>
  `setup.vs_prev_bb = NONE /\ setup.vs_inst_idx = 0` by
    gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()] >>
  drule_all venomExecProofsTheory.eval_phis_no_prev >> strip_tac >>
  gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs(),
      loweringStateRelDefsTheory.fresh_vars_wrt_def]
QED

(* Capture stays in the entry block and preserves the parameter layout. *)
Theorem intcall_args_param_decls_cut[local]:
  !params idx a caps next b.
    compile_internal_param_decls params idx a = ((caps,next),b) ==>
    MAP (\c. (FST c,FST (SND c))) caps = params /\
    b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
    isPREFIX a.cs_current_insts b.cs_current_insts
Proof
  Induct >- simp[moduleLoweringTheory.compile_internal_param_decls_def, comp_return_def] >>
  Cases >> rpt gen_tac >>
  simp[moduleLoweringTheory.compile_internal_param_decls_def,
       loweringShapeRulesTheory.emit_op_eq, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `rest_result` >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_args_capture_cut[local]:
  compile_internal_entry_prefix ce params has_rb a = ((ce1,caps,rpc),b) ==>
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
  isPREFIX a.cs_current_insts b.cs_current_insts
Proof
  Cases_on `has_rb` >>
  simp[intCallCalleeTheory.compile_internal_entry_prefix_def,
       loweringShapeRulesTheory.emit_op_eq, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `pr` >> gvs[] >>
  drule intcall_args_param_decls_cut >> simp[] >> strip_tac >> simp[] >>
  qpat_x_assum `_ ≼ _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  simp[APPEND_ASSOC]
QED

Theorem intcall_args_entry_cuts[local]:
  compile_internal_function_entry ce params has_rb ctor ilen rt a =
    ((ce2,rpc,imm),lock_start) ==>
  ?ce1 caps cap_end fix_end mat_end.
    compile_internal_entry_prefix ce params has_rb a = ((ce1,caps,rpc),cap_end) /\
    (if ctor /\ ilen > 0 then
       ?id buf. compile_fixed_region_with_id ilen cap_end = ((id,buf),fix_end) /\
                imm = SOME buf.buf_operand
     else fix_end = cap_end /\ imm = NONE) /\
    materialize_internal_params ce1 caps fix_end = (ce2,mat_end) /\
    (case rt of
       NONE => lock_start = mat_end
     | SOME ty => if ce.ce_returns_count > 0 then
                    ?buf. compile_alloc_buffer (type_memory_bytes ce ty) mat_end =
                            (buf,lock_start)
                  else lock_start = mat_end)
Proof
  simp[intCallCalleeTheory.compile_internal_function_entry_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  Cases_on `ctor /\ ilen > 0` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `rt` >> gvs[] >>
  rw[] >> rpt (pairarg_tac >> gvs[comp_return_def]) >>
  gvs[comp_return_def] >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[comp_return_def]) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  TRY (Cases_on `ar` >> simp[]) >>
  Cases_on `ce.ce_returns_count > 0` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_return_def]) >>
  goal_assum (drule_at Any)
QED

Theorem intcall_args_lock_cuts[local]:
  compile_internal_function ce params has_rb T key trans view ctor ilen
    ss rt a = ((),final) ==>
  ?ce2 rpc imm lock_start lock_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt a =
      ((ce2,rpc,imm),lock_start) /\
    compile_nonreentrant_lock key trans view lock_start = ((),lock_end) /\
    cs_extends lock_start lock_end /\ cs_extends lock_end final
Proof
  simp[intCallCalleeTheory.compile_internal_function_entry_factorization,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, comp_get_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_internal_function_entry _ _ _ _ _ _ _ = (entry,_)` >>
  PairCases_on `entry` >> gvs[] >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac
  >- metis_tac[entryCompileIntervalsTheory.cs_appends_nonreentrant, cs_appends_def] >>
  drule (SRULE [cs_appends_def] entryCompileIntervalsTheory.cs_appends_stmts) >>
  strip_tac >>
  qmatch_asmsub_rename_tac `block_is_terminated body_end` >>
  Cases_on `block_is_terminated body_end` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule (SRULE [cs_appends_def] (cj 2 entryCompileIntervalsTheory.cs_appends_nonreentrant)) >>
  strip_tac >> Cases_on `rt` >> gvs[] >>
  metis_tac[cs_extends_trans, cs_appends_def, cs_appends_emit_helpers]
QED

(* The capture prefix executes at the new block's actual runtime cursor. *)
Theorem intcall_args_capture_path[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),cap_end) /\
  cs_extends cap_end final /\ fn_has_code entry final callee /\
  entered.vs_current_bb = entry.cs_current_bb /\
  entered.vs_inst_idx = LENGTH entry.cs_current_insts /\
  fresh_vars_wrt entry entered /\ ~entered.vs_halted /\
  allocas_from lo entered /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp entered) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH entered.vs_params /\
  LENGTH entered.vs_params < dimword (:256) ==>
  ?t G' tn' x.
    run_inst_seq (emitted_insts entry cap_end) entered = OK t /\
    t = entered with vs_vars := t.vs_vars /\ fresh_vars_wrt cap_end t /\
    rpc = Var x /\ not_fresh_at cap_end x /\
    lookup_var x t = SOME entered.vs_return_pc_token /\
    op_taint tn' rpc = {} /\
    (!i. i < LENGTH params ==>
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at cap_end p /\
          lookup_var p t = SOME (EL ((if has_rb then 1 else 0) + i) entered.vs_params) /\
          FLOOKUP G' p = (if (if has_rb then 1 else 0) + i < LENGTH PG then
            EL ((if has_rb then 1 else 0) + i) PG else NONE) /\
          op_taint tn' (Var p) = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. inst_seq_ptr D lo ctx callee PG G tn (emitted_insts entry cap_end)
           entered G' tn' /\
      !explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (entered,G,tn) []
        (OK (t with vs_inst_idx := LENGTH cap_end.cs_current_insts),G',tn'))
Proof
  strip_tac >> drule intcall_args_capture_cut >> strip_tac >>
  `cs_extends entry cap_end` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code entry cap_end callee` by metis_tac[fn_has_code_split] >>
  `cap_end.cs_current_insts = entry.cs_current_insts ++ emitted_insts entry cap_end` by
    (qpat_x_assum `_ ≼ _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     simp[exprLoweringPropsTheory.emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `entered.vs_inst_idx + LENGTH (emitted_insts entry cap_end) =
      LENGTH cap_end.cs_current_insts` by
    (qpat_x_assum `cap_end.cs_current_insts = _` (fn th => simp[Once th])) >>
  `lookup_block entered.vs_current_bb callee.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts entry cap_end) (DROP entered.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all intCallEntryFullTheory.compile_internal_entry_prefix_joint >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `(ARB : dead)` (assume_tac o CONJUNCT1)) >>
  drule intCallCalleeTheory.compile_internal_entry_prefix_capture_code >> strip_tac >>
  drule_all intCallEntryFullTheory.internal_capture_seq_ghost_frame >> strip_tac >>
  drule_all intCallEntryFullTheory.compile_internal_entry_prefix_ghost_outputs >> strip_tac >>
  drule intCallCalleeTheory.compile_internal_entry_prefix_shape >> strip_tac >>
  qpat_x_assum `rpc = Var (STRING _ _)` kall_tac >>
  `!i. i < LENGTH params ==>
     ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at cap_end p /\
         lookup_var p t = SOME (EL ((if has_rb then 1 else 0) + i) entered.vs_params) /\
         FLOOKUP G' p = (if (if has_rb then 1 else 0) + i < LENGTH PG then
           EL ((if has_rb then 1 else 0) + i) PG else NONE) /\
         op_taint tn' (Var p) = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
     qexists `p` >> simp[] >>
     qpat_assum `!i. i < LENGTH params ==> SND (SND (EL i caps)) = _` drule >>
     simp[] >> disch_then SUBST1_TAC >>
     qpat_assum `!i. i < _ ==> FLOOKUP G' _ = _ /\ _`
       (qspec_then `(if has_rb then 1 else 0) + i` mp_tac) >>
     qpat_assum `i < LENGTH params` (fn th =>
       simp[NoAsms, th, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  qexistsl [`t`, `G'`, `tn'`, `x`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> gen_tac >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `D` (strip_assume_tac o CONJUNCT1)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `D` (mp_tac o CONJUNCT2)) >>
  qpat_assum `entered.vs_inst_idx + LENGTH (emitted_insts entry cap_end) = _`
    SUBST1_TAC >> simp[NoAsms]
QED

(* The optional fixed-region reservation is an ASSIGN at the actual entry
   cursor. Its output does not replace any of the captured argument values. *)
Theorem intcall_args_fixed_region_path[local]:
  (sb = sa \/ ?ilen id buf. compile_fixed_region_with_id ilen sa = ((id,buf),sb)) /\
  cs_extends sb final /\ fn_has_code sa final func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t G' tn'.
    fresh_vars_wrt sb t /\ t.vs_current_bb = sb.cs_current_bb /\
    t = s with <|vs_vars := t.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!p w. lookup_var p s = SOME w ==> lookup_var p t = SOME w) /\
    (!p. not_fresh_at sa p ==> not_fresh_at sb p) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn'))
Proof
  strip_tac
  >- (gvs[] >> qexistsl [`s`, `G`, `tn`] >>
      simp[venomStateTheory.venom_state_component_equality,
           fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (drule contextPropsTheory.compile_fixed_region_as_assign >>
     simp[loweringShapeRulesTheory.emit_op_eq] >> strip_tac >> gvs[]) >>
  drule contextTheory.compile_fixed_region_with_id_result >> strip_tac >>
  `cs_extends sa sb` by
    (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sb func` by metis_tac[fn_has_code_split] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    simp[exprLoweringPropsTheory.emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = _ ++ emitted_insts _ _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >> simp[NoAsms]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all intCallEntryFullTheory.compile_internal_fixed_region_joint >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule_all contextPropsTheory.compile_fixed_region_zero_correct >> strip_tac >>
  qabbrev_tac `fi = mk_inst sa.cs_next_id ASSIGN [Lit 0w]
    ["%" ++ toString sa.cs_next_var]` >>
  `emitted_insts sa sb = [fi]` by
    (qpat_assum `sb.cs_current_insts = _ ++ [fi]` mp_tac >>
     simp[NoAsms, exprLoweringPropsTheory.emitted_insts_def,
          rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
       ?idx x. i.inst_operands = [Lit idx] /\ i.inst_outputs = [x])
     (emitted_insts sa sb)` by simp[Abbr `fi`, venomInstTheory.mk_inst_def] >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `(ARB : dead)` (assume_tac o CONJUNCT1)) >>
  drule_all intCallEntryFullTheory.internal_capture_seq_ghost_frame >> strip_tac >>
  `!p. not_fresh_at sa p ==>
     FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> first_x_assum (qspec_then `p` mp_tac) >>
     simp[Abbr `fi`, venomInstTheory.mk_inst_def] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qexistsl [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  simp[loweringStateRelDefsTheory.fresh_vars_wrt_def, venomStateTheory.lookup_var_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[])
  >- (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[NoAsms])
  >- (rpt strip_tac >>
      `ss' = t` by
        (ntac 2 (qpat_x_assum `run_inst_seq _ s = OK _` mp_tac) >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
      qpat_x_assum `!op w. eval_operand op s = SOME w ==> _`
        (qspec_then `Var p` mp_tac) >>
      gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >> rpt gen_tac >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `D` (qspec_then `explicit` mp_tac o CONJUNCT2)) >> simp[]
QED

(* At the selected INVOKE, the captured values give the initial
   materialization invariant for the same runtime state and argument map. *)
Theorem intcall_args_capture_materialization_pre[local]:
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 u G tn /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (label,ops) /\ eval_operands ops u = SOME argv /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  setup_callee callee argv u = SOME setup /\
  enters_block callee setup entered /\ (HD callee.fn_blocks).bb_label = label /\
  new_block label before = (old,entry) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy
       (if cx.in_deploy then imm_len tops else 0)
       (mut,nr,rr,name,args,(dflts : expr list),ret,ss)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,ss,rt) /\
  (cx.in_deploy = cenv.ce_is_ctor) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),cap_end) /\
  (fix_end = cap_end \/
   ?n id buf. compile_fixed_region_with_id n cap_end = ((id,buf),fix_end)) /\
  cs_extends cap_end final /\ cs_extends fix_end final /\
  fn_has_code entry final callee /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  ?t G' tn' mr.
    t.vs_current_bb = fix_end.cs_current_bb /\
    t = entered with <|vs_vars := t.vs_vars;
                       vs_inst_idx := LENGTH fix_end.cs_current_insts|> /\
    t.vs_memory = u.vs_memory /\ t.vs_alloca_next = u.vs_alloca_next /\
    t.vs_accounts = u.vs_accounts /\ t.vs_call_ctx = u.vs_call_ctx /\
    t.vs_transient = u.vs_transient /\ t.vs_immutables = u.vs_immutables /\
    t.vs_allocas = FEMPTY /\ ~t.vs_halted /\
    (?x. rpc = Var x /\ not_fresh_at fix_end x /\ op_taint tn' rpc = {}) /\
    mat_pending ce1 penv fix_end t u.vs_alloca_next mr caps /\
    mat_inv callee ce1 penv fix_end t u.vs_alloca_next mr /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i < LENGTH caps ==>
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at fix_end p /\
          lookup_var p t = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
          FLOOKUP G' p = op_prov G (EL ((if has_rb then 1 else 0) + i) ops) /\
          op_taint tn' (Var p) = {}) /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) /\
    (!D explicit. gas_origin_ptr_path
        (D,lo,explicit,ctx,callee,MAP (op_prov G) ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK t,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `tn_start = tn with t_var := FEMPTY` >>
  drule_all intcall_args_entered_capture >> strip_tac >>
  qpat_assum `cx.in_deploy = cenv.ce_is_ctor` (fn th =>
    qpat_assum `set_internal_package_target _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all intcall_args_selected_package_entry >> strip_tac >>
  `internal_args_rel ce params penv (if has_rb then 1 else 0) argv
      u.vs_alloca_next u.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `(if has_rb then 1 else 0) + LENGTH params <= LENGTH entered.vs_params /\
   LENGTH entered.vs_params < dimword (:256)` by
    fs[intCallCalleeTheory.internal_args_rel_def] >>
  `allocas_from lo entered` by simp[ptrDisciplineTheory.allocas_from_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entered` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
       (drule_then (assume_tac o CONJUNCT1 o
          REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def])) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def]) >>
  drule_all intcall_args_capture_path >>
  disch_then (qspecl_then [`tn_start`, `MAP (op_prov G) ops`, `FEMPTY`]
    strip_assume_tac) >>
  drule intcall_args_capture_cut >> strip_tac >>
  `cs_extends entry cap_end` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code cap_end final callee` by metis_tac[fn_has_code_split] >>
  qabbrev_tac `captured = t with vs_inst_idx := LENGTH cap_end.cs_current_insts` >>
  `fresh_vars_wrt cap_end captured` by
    (qpat_x_assum `fresh_vars_wrt cap_end t` mp_tac >>
     simp[Abbr `captured`, loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  `~captured.vs_halted /\ allocas_from lo captured /\
   captured.vs_current_bb = cap_end.cs_current_bb /\
   captured.vs_inst_idx = LENGTH cap_end.cs_current_insts` by
    (simp[Abbr `captured`, ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `t = entered with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp captured` by
    (`allocas_below_fmp captured = allocas_below_fmp entered` by
       (qpat_assum `t = entered with vs_vars := _`
          (mp_tac o Q.AP_TERM `\st.
            allocas_below_fmp (st with vs_inst_idx := LENGTH cap_end.cs_current_insts)`) >>
        simp[NoAsms, Abbr `captured`, ptrDisciplineTheory.allocas_below_fmp_def]) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all intcall_args_fixed_region_path >>
  disch_then (qspecl_then [`tn'`, `MAP (op_prov G) ops`, `G'`]
    (qx_choose_then `fixed` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))) >>
  drule intCallCalleeTheory.compile_internal_entry_prefix_shape >> strip_tac >>
  `internal_args_rel ce1 params penv (if has_rb then 1 else 0) argv
     u.vs_alloca_next u.vs_memory` by gvs[intCallCalleeTheory.internal_args_rel_def] >>
  `LENGTH caps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  drule tupleLoadPropsTheory.eval_operands_length >> strip_tac >>
  `(if has_rb then 1 else 0) + LENGTH params <= LENGTH ops` by
    fs[intCallCalleeTheory.internal_args_rel_def] >>
  `!i. i < LENGTH params ==>
       FST (EL i caps) = FST (EL i params) /\
       FST (SND (EL i caps)) = SND (EL i params) /\
       ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at fix_end p /\
           lookup_var p fixed = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
           FLOOKUP Gf p = op_prov G (EL ((if has_rb then 1 else 0) + i) ops) /\
           op_taint tnf (Var p) = {}` by
    (gen_tac >> disch_tac >>
     `EL i params = (FST (EL i caps), FST (SND (EL i caps)))` by
       (qpat_x_assum `MAP _ caps = params` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
     `lookup_var p captured = SOME (EL ((if has_rb then 1 else 0) + i) argv)` by
       (qpat_assum `lookup_var p t = SOME _` mp_tac >>
        qpat_assum `entered.vs_params = argv` (fn th =>
          simp[NoAsms, th, Abbr `captured`, venomStateTheory.lookup_var_def,
               AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
     `(if has_rb then 1 else 0) + i < LENGTH ops` by
       (qpat_assum `_ + LENGTH params <= LENGTH ops` mp_tac >>
        qpat_assum `i < LENGTH params` mp_tac >>
        Cases_on `has_rb` >> simp[NoAsms] >> decide_tac) >>
     `FLOOKUP G' p = op_prov G (EL ((if has_rb then 1 else 0) + i) ops)` by
       (qpat_assum `FLOOKUP G' p = (if _ then _ else _)` mp_tac >>
        qpat_assum `_ + i < LENGTH ops` (fn th =>
          rewrite_tac[LENGTH_MAP, th] >>
          simp[NoAsms, EL_MAP, th,
               AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
     qexists `p` >>
     qpat_assum `!p. not_fresh_at cap_end p ==> FLOOKUP Gf p = _ /\ _`
       drule >> simp[]) >>
  `!i. i < LENGTH caps ==>
       ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at fix_end p /\
           lookup_var p fixed = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
           FLOOKUP Gf p = op_prov G (EL ((if has_rb then 1 else 0) + i) ops) /\
           op_taint tnf (Var p) = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> _ /\ _ /\ ?p. _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `fixed = entered with <|vs_vars := fixed.vs_vars;
                          vs_inst_idx := LENGTH fix_end.cs_current_insts|>` by
    (qpat_assum `fixed = captured with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
     simp[NoAsms, Abbr `captured`] >>
     qpat_assum `t = entered with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  `fixed.vs_memory = u.vs_memory /\ fixed.vs_alloca_next = u.vs_alloca_next /\
   fixed.vs_accounts = u.vs_accounts /\ fixed.vs_call_ctx = u.vs_call_ctx /\
   fixed.vs_transient = u.vs_transient /\ fixed.vs_immutables = u.vs_immutables /\
   fixed.vs_allocas = FEMPTY /\ ~fixed.vs_halted` by
    (qpat_assum `fixed = entered with <|vs_vars := _; vs_inst_idx := _|>`
       SUBST1_TAC >> simp[]) >>
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `?p. rpc = Var p /\ not_fresh_at fix_end p /\ op_taint tnf rpc = {}`
  >- (qexists `x` >> simp[] >>
      qpat_assum `!p. not_fresh_at cap_end p ==> FLOOKUP Gf p = _ /\ _`
        drule >> fs[]) >>
  `!i. i < LENGTH params ==>
       FST (EL i caps) = FST (EL i params) /\
       FST (SND (EL i caps)) = SND (EL i params) /\
       ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at fix_end p /\
           lookup_var p fixed = SOME (EL ((if has_rb then 1 else 0) + i) argv)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> _ /\ _ /\ ?p. _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists `p` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all intCallCalleeTheory.internal_args_materialization_pre >>
  disch_then (qspec_then `callee` strip_assume_tac) >>
  qpat_x_assum `!n b sz. mr n = SOME (b,sz) <=> _` kall_tac >>
  `tn_start.t_mem = tn.t_mem /\ tn_start.t_stor = tn.t_stor /\
   tn_start.t_trans = tn.t_trans /\ tn_start.t_imm = tn.t_imm` by
    simp[NoAsms, Abbr `tn_start`] >>
  `tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by simp[] >>
  qexistsl [`fixed`, `Gf`, `tnf`, `mr`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> rpt gen_tac >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `D` (qspec_then `explicit` assume_tac o CONJUNCT2)) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`captured`, `G'`, `tn'`, `[]`]
    (irule o SIMP_RULE (srw_ss()) [])) >> simp[]
QED

Theorem args_failed_lock_source[local]:
  lock_if_nr cx nr view src = (INR ex, failed) /\
  (nr ==> cx.nonreentrant_slot = SOME key) ==>
  nr /\
  failed = src with storage_trace := src.storage_trace ++ [StorageLock key] /\
  (if lookup_storage (n2w key) (src.tStorage cx.txn.target) = 1w
   then ex = Error (RuntimeError "nonreentrant lock")
   else ~view /\ cx.txn.is_static /\
        ex = Error (RuntimeError "write in static context"))
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, vyperStateTheory.return_def] >>
  strip_tac >>
  Cases_on `lookup_storage (n2w key) (src.tStorage cx.txn.target) = 1w` >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  gvs[nonreentrantEquivTheory.acquire_nonreentrant_lock_execution,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.check_not_static_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def, vyperStateTheory.raise_def]
QED

Theorem args_failed_lock_agrees[local]:
  lock_if_nr cx nr view src = (INR ex, failed) /\
  (nr ==> cx.nonreentrant_slot = SOME key) /\ key < dimword (:256) /\
  valid_horizon cx st0 H failed.storage_trace /\ state_rel H fn ce cx src u ==>
  valid_horizon cx st0 H src.storage_trace /\
  failed = src with storage_trace := src.storage_trace ++ [StorageLock key] /\
  MEM key (SND H) /\
  (if tload (n2w key) u = 1w then ex = Error (RuntimeError "nonreentrant lock")
   else ~view /\ u.vs_call_ctx.cc_static /\ ex = Error (RuntimeError "write in static context"))
Proof
  strip_tac >>
  drule_all args_failed_lock_source >> strip_tac >>
  `valid_horizon cx st0 H src.storage_trace /\
    storage_locks_separated (FST H) (SND H) /\ MEM key (SND H)` by
    fs[vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.storage_trace_locks_def, listTheory.EVERY_APPEND] >>
  `lookup_storage (n2w key) (src.tStorage cx.txn.target) = tload (n2w key) u` by
    (irule (INST_TYPE [alpha |-> ``:256``] nonreentrantSourceTheory.nonreentrant_lock_agreement) >>
     conj_tac >- fs[] >> conj_tac >- fs[] >> qexistsl_tac [`H`, `ce`, `fn`] >> fs[]) >>
  drule stateRelProjTheory.state_rel_call_ctx_rel >>
  simp[loweringStateRelDefsTheory.call_ctx_rel_def] >> strip_tac >> gvs[]
QED

Theorem args_lock_taint_cut[local]:
  dead_lo_ok H D lo ce cx /\
  stor_taint_ok_at D tn s /\
  MEM key (SND H) /\ key < dimword (:256) ==>
  key_taint tn.t_trans (n2w key) = {}
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `stor_taint_ok H cx (tn with t_imm := {}) s` by
    (qpat_assum `dead_lo_ok H D lo ce cx` (strip_assume_tac o REWRITE_RULE [dead_lo_ok_def]) >>
     qpat_assum `D.d_stor = _` (fn stor =>
       qpat_assum `D.d_trans = _` (fn trans =>
         qpat_assum `stor_taint_ok_at D tn s`
           (strip_assume_tac o REWRITE_RULE [stor_taint_ok_at_def,stor,trans]))) >>
     simp[stor_taint_ok_def]) >>
  drule_all transientLockPtrTheory.nonreentrant_slot_untainted >>
  simp[ptrDisciplineTheory.key_taint_def, pred_setTheory.EXTENSION]
QED

Theorem args_lock_code_cut[local]:
  compile_nonreentrant_lock key T view sb = ((),sl) /\
  cs_extends sb sl /\ cs_extends sl final /\ fn_has_code sb final callee /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb callee.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code key view sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all nonreentrantEntryPathTheory.compile_nonreentrant_lock_transient_prefix >> simp[]
QED

Theorem args_transient_lock_abort_origin_ptr[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code key view st) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  key_taint tn.t_trans (n2w key) = {} /\
  (tload (n2w key) s = 1w \/ (~view /\ s.vs_call_ctx.cc_static)) ==>
  ?t G' tn'. !D explicit.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort (if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort) t,G',tn')
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qabbrev_tac `code = transient_lock_code key view st` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) code` by
    (Cases_on `view` >> simp[Abbr `code`, transientLockPropsTheory.transient_lock_code_def,
                            emitHelperPropsTheory.mk_inst_opcode, venomInstTheory.is_terminator_def]) >>
  `run_inst_seq_mem_ok code s` by
    (irule fragExecMemTheory.run_inst_seq_mem_ok_every >> Cases_on `view` >>
     simp[Abbr `code`, transientLockPropsTheory.transient_lock_code_def, venomInstTheory.mk_inst_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def]) >>
  qabbrev_tac `a = if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort` >>
  `?t. run_inst_seq code s = Abort a t` by
    (Cases_on `tload (n2w key) s = 1w` >> fs[Abbr `a`, Abbr `code`,
                            transientLockPropsTheory.transient_lock_code_execution]) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i code` by
       (qpat_assum `code = _ ++ _` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
     Cases_on `view` >>
     fs[Abbr `code`, transientLockPropsTheory.transient_lock_code_def] >>
     gvs[emitHelperPropsTheory.mk_inst_opcode]) >>
  drule_all fragGasCopyLoopTheory.run_inst_seq_abort_origin_ptr_uniform >>
  strip_tac >>
  `!D. ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'` by
    (gen_tac >> simp[Abbr `code`] >>
     irule transientLockPtrTheory.transient_lock_abort_ptr_ghost >> simp[]) >>
  qpat_assum `!D. ?G' tn'. inst_seq_ptr D 0 _ _ _ _ _ _ _ G' tn'`
    (qspec_then `ARB` (qx_choose_then `J` (qx_choose_then `tj` assume_tac))) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn code s J tj` by
    (gen_tac >>
     qpat_assum `!D. ?G' tn'. inst_seq_ptr D 0 _ _ _ _ _ _ _ G' tn'`
       (qspec_then `D` (qx_choose_then `J1` (qx_choose_then `tk` assume_tac))) >>
     `J1 = J /\ tk = tj` by
       (irule fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique >> metis_tac[]) >>
     irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> gvs[]) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `J`, `tj`] >>
  fs[Abbr `code`, Abbr `a`] >> metis_tac[]
QED

Theorem args_lock_abort_callee[local]:
  (!H. valid_horizon cx st0 H failed.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK s,Gs,ts) /\
    key_taint ts.t_trans (n2w key) = {} /\
    (tload (n2w key) s = 1w \/ (~view /\ s.vs_call_ctx.cc_static))) /\
  ~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block s.vs_current_bb callee.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code key view lock_st)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?r Gc tc.
    (?a t. r = Abort a t) /\
    !H. valid_horizon cx st0 H failed.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) [] (r,Gc,tc)
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H failed.storage_trace`
  >- (qpat_x_assum `?H. valid_horizon _ _ H _` strip_assume_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
      drule_all args_transient_lock_abort_origin_ptr >>
      disch_then (qspecl_then [`MAP (op_prov G) ops`, `Gs`] strip_assume_tac) >>
      qexistsl_tac [`Abort (if tload (n2w key) s = 1w
                           then Revert_abort else ExHalt_abort) t`, `G'`, `tn'`] >>
      conj_tac >- metis_tac[] >>
      qx_gen_tac `H'` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
      qpat_assum `gas_origin_ptr_path (DF H',lo,explicit,ctx,callee,_) _ [] (OK s,Gs,ts)`
        (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`s`, `Gs`, `ts`, `[]`,
        `Abort (if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort) t`,
        `G'`, `tn'`] mp_tac) >> simp[]) >>
  qexistsl_tac [`Abort Revert_abort s`, `Gs`, `ts`] >> simp[] >>
  metis_tac[]
QED

Theorem args_failed_lock_caller_outcome[local]:
  ~u.vs_halted /\
  (!tail. source (ed with gas_obs := tail) = (INR (Error (RuntimeError msg)),
                                             failed with gas_obs := tail)) /\
  lookup_block u.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (label,ops) /\
  gas_invoke_entry (ctx,caller) u callee entered /\
  (!H. valid_horizon cx st0 H failed.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx caller G tn inst u /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (Abort a t,Gc,tc)) /\
  (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) ==>
  gas_outcome_full (DF,lo,explicit,ctx,caller,PG) (cx_tops cx) cx st0 source
    (ed,u,G,tn) Q R
Proof
  strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >> simp[] >>
  qexistsl_tac [`G`, `failed`, `Abort a t`, `INR (Error (RuntimeError msg))`, `tn`] >>
  simp[exit_result_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  conj_tac
  >- (irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      simp[exit_result_def] >>
      irule fragGasOriginPtrInvokeTheory.gas_origin_ptr_invoke_exit >>
      simp[exit_result_def] >>
      qexistsl_tac [`Gc`, `callee`, `entered`, `tc`] >> simp[]) >>
  qpat_assum `!H res ee gt r. _ ==> R H res ee gt r` irule >>
  simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]
QED

Theorem args_materialize_current_bb[local]:
  !caps ce st ce' st'.
    materialize_internal_params ce caps st = (ce',st') ==>
    st'.cs_current_bb = st.cs_current_bb /\ st'.cs_blocks = st.cs_blocks
Proof
  Induct
  >- (simp[moduleLoweringTheory.materialize_internal_params_def, comp_return_def] >> rw[]) >>
  PairCases >> rpt gen_tac >> simp[moduleLoweringTheory.materialize_internal_params_def] >>
  Cases_on `h1`
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >>
      simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def, fresh_id_def,
           fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem args_run_inst_seq_no_invoke[local]:
  !code s t. run_inst_seq code s = OK t ==>
    !i. MEM i code ==> i.inst_opcode <> INVOKE
Proof
  Induct >> simp[exprLoweringPropsTheory.run_inst_seq_def] >>
  rpt gen_tac >> Cases_on `step_inst_base h s` >> simp[] >>
  metis_tac[venomExecProofsTheory.step_inst_base_OK_not_INVOKE]
QED

Theorem args_materialize_to_lock[local]:
  materialize_internal_params ce caps sa = (ce',sm) /\
  fn_has_code sa sm callee /\
  (!i. MEM i (DROP (LENGTH sa.cs_current_insts) sm.cs_current_insts) ==>
       MEM i (fn_insts callee)) /\
  fn_inst_ids_distinct callee /\ ALL_DISTINCT (MAP FST caps) /\
  mat_pending ce env sa s f0 mr caps /\
  (!n1 n2 b1 sz1 b2 sz2.
     n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
     regions_disjoint b1 sz1 b2 sz2) /\
  mat_inv callee ce env sa s f0 mr /\
  s.vs_alloca_next +
    internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) <
    dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
       s.vs_alloca_next + pending_alloca_size callee s <= w2n s.vs_initial_fmp) /\
  lo <= f0 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ es.scopes = [env] /\
  (!nm entry. FLOOKUP env nm = SOME entry ==>
       value_has_type entry.type entry.value) /\
  (!nm p sz. FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at sa p) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at sa x) /\
  (!D. D IN Ds ==> ghost_inv_at D lo d ce cx es G tn s) /\
  EVERY (\c. op_taint tn (SND (SND c)) = {} /\
    (!p off sz entry.
       ~FST (SND c) /\ SND (SND c) = Var p /\
       FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
       FLOOKUP env (FST c) = SOME entry ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
         mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem)) caps /\
  (sb = sm \/ ?n buf. compile_alloc_buffer n sm = (buf,sb)) /\
  fn_has_code sm final callee /\ cs_extends sb final ==>
  ?t G' tn'.
    ~t.vs_halted /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!D. D IN Ds ==> stor_taint_ok_at D tn' t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
       (s,G,tn) [] (OK t,G',tn'))
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  mp_tac (Q.SPECL [`caps`, `ce`, `sa`, `ce'`, `sm`, `callee`, `env`,
    `s`, `f0`, `mr`, `ctx`, `lo`, `d`, `cx`, `es`, `PG`, `G`, `tn`,
    `Ds`, `explicit`] materialize_params_full) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `m` (qx_choose_then `J`
    (qx_choose_then `tj` strip_assume_tac))) >>
  qpat_assum `mat_frame _ _ _` (strip_assume_tac o REWRITE_RULE [intCallCalleeTheory.mat_frame_def]) >>
  qpat_assum `mat_inv _ _ _ _ m _ _` (strip_assume_tac o REWRITE_RULE [intCallCalleeTheory.mat_inv_def]) >>
  qabbrev_tac `mid = m with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
      (s,G,tn) [] (OK mid,J,tj)` by simp[Abbr `mid`] >>
  drule args_materialize_current_bb >> strip_tac >>
  `m.vs_halted = s.vs_halted /\ m.vs_current_bb = s.vs_current_bb /\
    m.vs_transient = s.vs_transient /\ m.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `m = s with <|vs_vars := _; vs_memory := _; vs_allocas := _; vs_alloca_next := _|>` (fn th => CONV_TAC (ONCE_REWRITE_CONV [th])) >>
     simp[]) >>
  `lo <= m.vs_alloca_next` by decide_tac >>
  `~mid.vs_halted /\ allocas_from lo mid /\ lo <= mid.vs_alloca_next /\
    mid.vs_current_bb = sm.cs_current_bb /\ mid.vs_inst_idx = LENGTH sm.cs_current_insts /\
    mid.vs_transient = s.vs_transient /\ mid.vs_call_ctx = s.vs_call_ctx` by
    (simp[Abbr `mid`, ptrDisciplineTheory.allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) ==> _` drule >>
     decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp mid /\
      mid.vs_alloca_next + pending_alloca_size callee mid <= w2n mid.vs_initial_fmp` by
    (strip_tac >>
     `m.vs_alloca_next + pending_alloca_size callee m <=
       s.vs_alloca_next + pending_alloca_size callee s` by
       (irule intCallCalleeTheory.run_inst_seq_static_charge >>
        qexists_tac `DROP (LENGTH sa.cs_current_insts) sm.cs_current_insts` >>
        simp[EVERY_MEM] >> gen_tac >> strip_tac >>
        qpat_assum `run_inst_seq _ s = OK m`
          (MATCH_MP_TAC o MATCH_MP args_run_inst_seq_no_invoke) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `m = s with <|vs_vars := _; vs_memory := _; vs_allocas := _; vs_alloca_next := _|>`
       (mp_tac o Q.AP_TERM `\st. (st.vs_initial_fmp,st.vs_fmp)`) >>
     simp[NoAsms] >> strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `allocas_below_fmp s`
       (strip_assume_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def]) >>
     simp[Abbr `mid`, ptrDisciplineTheory.allocas_below_fmp_def,
          exprLoweringPropsTheory.pending_alloca_size_def] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `alloca_inv m`
           (strip_assume_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def,
                                            venomMemDefsTheory.alloca_next_valid_def]) >>
         first_x_assum drule >> decide_tac) >>
     fs[exprLoweringPropsTheory.pending_alloca_size_def] >> decide_tac) >>
  `!D. stor_taint_ok_at D tj mid <=> stor_taint_ok_at D tj m` by
    simp[Abbr `mid`, stor_taint_ok_at_def] >>
  `!D. D IN Ds ==> stor_taint_ok_at D tj mid` by
    (rpt strip_tac >>
     qpat_assum `!D. stor_taint_ok_at D tj mid <=> _` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at _ _ _ ce' _ _ _ _ _`
       drule >> disch_then (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `sb = sm \/ _` strip_assume_tac
  >- (qexistsl_tac [`mid`, `J`, `tj`] >> simp[]) >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_extends >> strip_tac >>
  mp_tac (Q.SPECL [`sm`, `sb`, `final`, `callee`] fn_has_code_split) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`sm`, `sb`, `callee`, `emitted_insts sm sb`]
    fn_has_code_same_block) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `bytes = (n2w n : bytes32)` >>
  `lookup_block mid.vs_current_bb callee.fn_blocks = SOME bb /\
    get_instruction bb mid.vs_inst_idx = SOME (mk_inst sm.cs_next_id ALLOCA [Lit bytes] [out])` by
    (conj_tac
     >- (qpat_assum `mid.vs_current_bb = sm.cs_current_bb`
           (fn th => PURE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `emitted_insts sm sb = [_]` (fn code =>
       qpat_assum `!i. i < LENGTH (emitted_insts sm sb) ==> _`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [code] o Q.SPEC `0`)) >>
     simp[Abbr `bytes`, Abbr `out`]) >>
  `FLOOKUP mid.vs_allocas sm.cs_next_id = NONE` by
    (qpat_assum `!aid. aid IN FDOM m.vs_allocas ==> _`
       (qspec_then `sm.cs_next_id` assume_tac) >>
     fs[] >> simp[Abbr `mid`, finite_mapTheory.FLOOKUP_DEF]) >>
  qspecl_then [`sm.cs_next_id`, `w2n bytes`, `out`, `mid`] mp_tac loweringHaltTheory.step_alloca_fresh >>
  simp[wordsTheory.w2n_lt] >> strip_tac >>
  qabbrev_tac `alloc = update_var out (n2w mid.vs_alloca_next)
      (mid with <|vs_allocas := mid.vs_allocas |+
          (sm.cs_next_id,(mid.vs_alloca_next,w2n bytes));
        vs_alloca_next := mid.vs_alloca_next + w2n bytes|>)` >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit bytes] [out]) mid = OK alloc`
    by simp[Abbr `alloc`] >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ALLOCA [Lit bytes] [out]` >>
  qabbrev_tac `lock_start = alloc with vs_inst_idx := SUC mid.vs_inst_idx` >>
  `~lock_start.vs_halted /\ allocas_from lo lock_start /\ lo <= lock_start.vs_alloca_next /\
    lock_start.vs_current_bb = sb.cs_current_bb /\
    lock_start.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lock_start.vs_transient = s.vs_transient /\ lock_start.vs_call_ctx = s.vs_call_ctx` by
    (simp[Abbr `lock_start`, Abbr `alloc`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_from_def, finite_mapTheory.FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
     rpt strip_tac >> TRY decide_tac >>
     Cases_on `sm.cs_next_id = aid` >> gvs[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `!aid b sz. FLOOKUP mid.vs_allocas aid = SOME (b,sz) ==> _` drule >>
     simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp lock_start` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp mid /\ _`
       (drule_then strip_assume_tac) >>
     `MEM i (fn_insts callee)` by
       (drule_all fragFuelTheory.lookup_block_get_instruction_fn_insts >>
        simp[Abbr `i`]) >>
     `alloc.vs_alloca_next + pending_alloca_size callee alloc <=
         mid.vs_alloca_next + pending_alloca_size callee mid` by
       (irule intCallCalleeTheory.step_inst_base_static_charge >>
        qexists_tac `i` >>
        simp[Abbr `i`, venomInstTheory.mk_inst_def]) >>
     `mid.vs_alloca_next + w2n bytes <= w2n mid.vs_initial_fmp` by
       (qpat_assum `alloc.vs_alloca_next + pending_alloca_size callee alloc <= _`
          mp_tac >>
        qpat_assum `mid.vs_alloca_next + pending_alloca_size callee mid <= _` mp_tac >>
        simp[NoAsms, Abbr `alloc`, venomStateTheory.update_var_def] >> decide_tac) >>
     qpat_assum `allocas_below_fmp mid`
       (strip_assume_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def]) >>
     simp[Abbr `lock_start`, Abbr `alloc`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_below_fmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = sm.cs_next_id` >> gvs[] >>
     first_x_assum drule >> simp[]) >>
  `!D. stor_taint_ok_at D (step_taint i mid alloc tj) lock_start <=>
        stor_taint_ok_at D tj mid` by
    simp[stor_taint_ok_at_def, Abbr `alloc`, Abbr `lock_start`, venomStateTheory.update_var_def,
         Abbr `mid`, Abbr `i`, bodyPtrPrecompileBuiltinsAllocationFrameTheory.alloca_ghost_frames] >>
  qexistsl_tac [`lock_start`, `step_prov PG J i alloc`, `step_taint i mid alloc tj`] >>
  simp[] >>
  qx_gen_tac `D` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,callee,PG) (mid,J,tj) []
    (OK lock_start,step_prov PG J i alloc,step_taint i mid alloc tj)` by
    (mp_tac (Q.SPECL [`mid`, `ctx`, `lo`, `callee`, `bb`, `sm.cs_next_id`,
        `bytes`, `out`, `alloc`, `D`, `explicit`, `PG`, `J`, `tj`]
        bodyFullAllocGenericTheory.ifexp_alloca_origin_ptr_edge) >>
     simp[Abbr `i`, Abbr `lock_start`]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
       (lock_start,step_prov PG J i alloc,step_taint i mid alloc tj) []
       (OK lock_start,step_prov PG J i alloc,step_taint i mid alloc tj)` by
    (irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (mid,J,tj) []
    (OK lock_start,step_prov PG J i alloc,step_taint i mid alloc tj)` by
    (qpat_assum `gas_origin_ptr_edge _ (mid,J,tj) [] _` (fn edge =>
       qpat_assum `gas_origin_ptr_path _ (lock_start,_,_) [] _` (fn done =>
         ACCEPT_TAC (SIMP_RULE std_ss [APPEND]
           (MATCH_MP (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) (CONJ edge done)))))) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` (qspec_then `D` assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
    (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`mid`,`J`,`tj`,`[]`,`OK lock_start`,
    `step_prov PG J i alloc`, `step_taint i mid alloc tj`] mp_tac) >>
  simp[]
QED

Theorem intcall_args_failed_lock_invoke_outcome[local]:
  body_inv tops ctx cenv cx /\ ctx_inst_ids_distinct ctx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ed.storage_trace ==>
    intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) ed.scopes penv rtv
      (ed with scopes := [penv]) u G tn) /\
  (?H. valid_horizon cx st0 H ed.storage_trace) /\
  lock_if_nr cx nr (is_view_mut mut) ed = (INR err,failed) /\
  (!tail. source (ed with gas_obs := tail) = (INR err,failed with gas_obs := tail)) /\
  (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (ed,u,G,tn) Q R
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ed.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ed.storage_trace ==> _`
    (drule_then assume_tac) >>
  drule_all intcall_args_selected_invoke >>
  disch_then (qx_choose_then `bb` (qx_choose_then `inst`
    (qx_choose_then `ops` (qx_choose_then `argv` (qx_choose_then `callee`
    (qx_choose_then `setup` (qx_choose_then `entered` strip_assume_tac))))))) >>
  drule_all intcall_args_selected_head >> strip_tac >>
  drule_all bodyFullShadowInternalRunTheory.body_inv_selected_internal_code >>
  disch_then (qx_choose_then `label` (qx_choose_then `ce` (qx_choose_then `params`
    (qx_choose_then `has_rb` (qx_choose_then `nr'` (qx_choose_then `key`
    (qx_choose_then `trans` (qx_choose_then `view` (qx_choose_then `ctor`
    (qx_choose_then `ilen` (qx_choose_then `rt` (qx_choose_then `before`
    (qx_choose_then `old` (qx_choose_then `entry`
    (qx_choose_then `final` strip_assume_tac))))))))))))))) >>
  qpat_x_assum `set_internal_package_target _ (package_internal_fn _ _ _ _ _ (subst_consts_fn _ _)) = _`
    (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def]) >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    (strip_tac >> drule_all bodySimTheory.body_inv_nonreentrant_slot >> simp[]) >>
  drule_all args_failed_lock_source >> strip_tac >>
  `nr' = nr /\ key = global_nonreentrant_slot /\ trans /\ view = (mut = View)` by
    ((qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp[compileVyperTheory.set_internal_package_target_def,
          compileVyperTheory.package_internal_fn_def, pairTheory.UNCURRY] >> (gvs[compileVyperTheory.set_internal_package_target_def, compileVyperTheory.package_internal_fn_def, pairTheory.UNCURRY]))) >>
  qpat_x_assum `nr' = nr` SUBST_ALL_TAC >>
  qpat_x_assum `key = global_nonreentrant_slot` SUBST_ALL_TAC >>
  qpat_x_assum `view = (mut = View)` SUBST_ALL_TAC >>
  qpat_x_assum `nr` (SUBST_ALL_TAC o EQT_INTRO) >>
  qpat_x_assum `trans` (SUBST_ALL_TAC o EQT_INTRO) >>
  drule_then strip_assume_tac intcall_args_lock_cuts >>
  drule_then strip_assume_tac intcall_args_entry_cuts >>
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `fix_end = cap_end \/
     ?n id buf. compile_fixed_region_with_id n cap_end = ((id,buf),fix_end)`
  >- (Cases_on `ctor /\ 0 < ilen` >> fs[] >> metis_tac[]) >>
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `lock_start = mat_end \/ ?n buf. compile_alloc_buffer n mat_end = (buf,lock_start)`
  >- (Cases_on `rt` >> fs[] >> Cases_on `0 < ce.ce_returns_count` >> fs[] >> metis_tac[]) >>
  `cs_extends mat_end lock_start` by
    (qpat_assum `lock_start = mat_end \/ _` strip_assume_tac
     >- simp[cs_extends_refl] >>
     drule_then ACCEPT_TAC loweringHaltTheory.compile_alloc_buffer_extends) >>
  `cs_extends fix_end mat_end` by
    (mp_tac (Q.SPECL [`caps`,`ce1`,`fix_end`]
       externalEntryShapeTheory.materialize_internal_params_labels) >> simp[]) >>
  `cs_extends cap_end fix_end` by
    (qpat_assum `fix_end = cap_end \/ _` strip_assume_tac >- simp[cs_extends_refl] >>
     qmatch_asmsub_rename_tac `compile_fixed_region_with_id n cap_end` >>
     mp_tac (Q.SPECL [`n`,`cap_end`] externalEntryShapeTheory.compile_fixed_region_with_id_labels) >>
     simp[]) >>
  `cs_extends entry cap_end` by
    (drule_then strip_assume_tac intcall_args_capture_cut >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends lock_start final /\ cs_extends mat_end final /\
   cs_extends fix_end final /\ cs_extends cap_end final /\ cs_extends entry fix_end` by
    metis_tac[cs_extends_trans] >>
  `cx.in_deploy = cenv.ce_is_ctor` by
    (drule_then ACCEPT_TAC intcall_args_body_inv_constructor) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qhdtm_assum `intcall_entry_full`
       (ACCEPT_TAC o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o cj 7 o
         PURE_REWRITE_RULE [intcall_entry_full_def])) >>
  `fmp_room ctx callee setup` by
    (drule_all bodyFullIntCallByteFrameTheory.intcall_entry_full_fmp_room >>
     simp[]) >>
  `fn_has_code fix_end final callee` by metis_tac[fn_has_code_split] >>
  `fn_has_code fix_end mat_end callee /\ fn_has_code mat_end final callee` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code lock_start final callee` by metis_tac[fn_has_code_split] >>
  qpat_assum `label = internal_fn_label _ _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  `set_internal_package_target cenv.ce_target
      (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy
        (if cx.in_deploy then imm_len tops else 0)
        (mut,T,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_rb,T,global_nonreentrant_slot,T,mut = View,ctor,ilen,ss,rt)` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileVyperTheory.package_internal_fn_def,
          compileVyperTheory.set_internal_package_target_def,
          entryDispatchPropsTheory.build_compile_env_subst_consts_stmts] >>
     Cases_on `cx.in_deploy` >> simp[]) >>
  drule_all intcall_args_capture_materialization_pre >>
  disch_then (qx_choose_then `fixed` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (qx_choose_then `mr` strip_assume_tac)))) >>
  drule_then strip_assume_tac args_materialize_current_bb >>
  `?code. mat_end.cs_current_insts = fix_end.cs_current_insts ++ code` by
    (qpat_x_assum `cs_extends fix_end mat_end` mp_tac >>
     rewrite_tac[cs_extends_def] >>
     disch_then (qx_choose_then `new` assume_tac) >>
     Cases_on `new`
     >- gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     `LENGTH mat_end.cs_blocks = LENGTH ((h::t) ++ fix_end.cs_blocks)` by
       (gvs[] >> metis_tac[]) >>
     fs[]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `!i. MEM i (DROP (LENGTH fix_end.cs_current_insts) mat_end.cs_current_insts) ==>
       MEM i (fn_insts callee)` by
    simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `fn_inst_ids_distinct callee` by
    (drule_then assume_tac venomInstTheory.lookup_function_MEM >>
     drule_all allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn >>
     simp[venomWfTheory.fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
          venomInstIdsPropsTheory.fn_insts_blocks_map_id]) >>
  `!nm entry. FLOOKUP penv nm = SOME entry ==> value_has_type entry.type entry.value` by
    (`scope_well_typed penv` by
       (qhdtm_assum `intcall_entry_full` (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
        drule_then ACCEPT_TAC
          vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success) >>
     pop_assum (mp_tac o REWRITE_RULE [vyperTypeInvariantsTheory.scope_well_typed_def]) >>
     metis_tac[]) >>
  qpat_assum `cx.in_deploy = cenv.ce_is_ctor` (fn th =>
    qpat_assum `set_internal_package_target _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all intcall_args_selected_package_entry >> strip_tac >>
  drule_then strip_assume_tac intcall_args_capture_cut >>
  drule_then strip_assume_tac intCallCalleeTheory.compile_internal_entry_prefix_shape >>
  `internal_args_rel ce params penv (if has_rb then 1 else 0) argv
      u.vs_alloca_next u.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ALL_DISTINCT (MAP FST caps)` by
    (qpat_assum `internal_args_rel _ _ _ _ _ _ _`
       (assume_tac o cj 1 o REWRITE_RULE [intCallCalleeTheory.internal_args_rel_def]) >>
     qpat_x_assum `ALL_DISTINCT (MAP FST params)` mp_tac >>
     qpat_assum `MAP _ caps = params` (SUBST1_TAC o SYM) >>
     simp[NoAsms, MAP_MAP_o, combinTheory.o_DEF, ETA_AX]) >>
  `LENGTH caps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  `EVERY (\c. op_taint tnf (SND (SND c)) = {} /\
     (!p off sz e.
        ~FST (SND c) /\ SND (SND c) = Var p /\
        FLOOKUP ce1.ce_vars (FST c) = SOME (MemLoc off sz) /\
        FLOOKUP penv (FST c) = SOME e ==>
        ptr_covers Gf tnf p fixed sz /\
        !w mem. lookup_var p fixed = SOME w /\
          mem_agree_outside tnf.t_mem fixed.vs_memory mem ==>
          val_in_memory e.type e.value (w2n w) mem)) caps` by
    (rewrite_tac[EVERY_EL] >> gen_tac >> disch_tac >>
     rename1 `i < LENGTH caps` >>
     `i < LENGTH params` by simp[] >>
     `EL i params = (FST (EL i caps), FST (SND (EL i caps)))` by
       (qpat_assum `MAP _ caps = params` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
     qpat_assum `!i. i < LENGTH caps ==> ?p. _` drule >> strip_tac >>
     BETA_TAC >> conj_tac >- simp[] >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!i off sz. _ ==> ?b bsz. _`
       (qspecl_then [`i`, `off`, `sz`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
     `p' = p` by
       (ntac 2 (qpat_x_assum `SND (SND (EL i caps)) = Var _` mp_tac) >>
        simp[NoAsms]) >> pop_assum SUBST_ALL_TAC >>
     conj_tac >-
       (pure_rewrite_tac[ptr_covers_def] >> conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`EL ((if has_rb then 1 else 0) + i) argv`, `b`, `bsz`] >>
        rpt conj_tac >> metis_tac[]) >>
     rpt strip_tac >>
     qpat_assum `!mem. _ ==> internal_args_rel _ _ _ _ _ _ mem`
       (qspec_then `mem` mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (qspec_then `i` mp_tac o cj 5 o
       REWRITE_RULE [intCallCalleeTheory.internal_args_rel_def]) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule memoryValueEncodingTheory.memory_value_rel_val_in_memory >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `(if SND (EL i params) then _ else _)` mp_tac >>
     qpat_assum `EL i params = _` (fn th => PURE_REWRITE_TAC [th, pairTheory.SND]) >>
     qpat_assum `~FST (SND (EL i caps))` (fn th => PURE_REWRITE_TAC [th, COND_CLAUSES]) >>
     strip_tac >> metis_tac[pairTheory.FST, optionTheory.SOME_11]) >>
  `lo <= u.vs_alloca_next` by
    (qhdtm_assum `ghost_inv_at` (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  `!nm p sz. FLOOKUP ce1.ce_vars nm <> SOME (PtrVar p sz)` by
    (qpat_assum `ce1.ce_vars = ce.ce_vars` SUBST1_TAC >>
     qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp[NoAsms, compileVyperTheory.package_internal_fn_def,
          compileVyperTheory.set_internal_package_target_def,
          compileVyperTheory.update_cenv_nonreentrant_def, pairTheory.UNCURRY] >>
     disch_then (strip_assume_tac o GSYM) >>
     simp[compileVyperTheory.build_compile_env_vars]) >>
  `ce.ce_imm_alloca = NONE /\
   (!rb. ce.ce_return_buf = SOME rb ==> ?off. rb = MemLoc off 32)` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp[NoAsms, compileVyperTheory.package_internal_fn_def,
          compileVyperTheory.set_internal_package_target_def,
          compileVyperTheory.update_cenv_nonreentrant_def, pairTheory.UNCURRY] >>
     disch_then (strip_assume_tac o GSYM) >>
     simp[compileVyperTheory.build_compile_env_def,
          compileVyperTheory.allocate_internal_special_vars_def,
          pairTheory.UNCURRY] >>
     rpt (pairarg_tac >> simp[]) >> rpt (IF_CASES_TAC >> simp[])) >>
  `ce1.ce_imm_alloca = NONE /\
   ((~has_rb \/ ce.ce_return_buf = NONE) ==>
    ce1.ce_return_buf = ce.ce_return_buf)` by
    (qpat_assum `compile_internal_entry_prefix _ _ _ _ = _` mp_tac >>
     Cases_on `has_rb` >>
     simp[NoAsms, intCallCalleeTheory.compile_internal_entry_prefix_def,
          comp_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
          compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_id_def,
          compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
     pairarg_tac >> simp[] >>
     disch_then (strip_assume_tac o GSYM) >> simp[]) >>
  `!y sz. ce1.ce_return_buf = SOME (PtrVar (Var y) sz) ==>
          not_fresh_at fix_end y` by
    (rpt gen_tac >> disch_tac >>
     Cases_on `has_rb` >-
      (Cases_on `ce.ce_return_buf` >- fs[] >>
       rename1 `ce.ce_return_buf = SOME rb0` >>
       qpat_assum `!rb. SOME rb0 = SOME rb ==> _`
         (qspec_then `rb0` (strip_assume_tac o SRULE [])) >>
       `y = STRING #"%" (toString entry.cs_next_var)` by fs[] >>
       `x = STRING #"%" (toString (entry.cs_next_var + 1 + LENGTH params))` by fs[] >>
       qpat_assum `not_fresh_at fix_end x` mp_tac >>
       qpat_assum `x = STRING #"%" _` SUBST1_TAC >>
       qpat_assum `y = STRING #"%" _` SUBST1_TAC >>
       simp[NoAsms, loweringStateRelDefsTheory.not_fresh_at_def,
            ASCIInumbersTheory.toString_inj] >> decide_tac) >>
     qpat_assum `(~F \/ ce.ce_return_buf = NONE) ==> _`
       (assume_tac o SRULE []) >>
     `ce.ce_return_buf = SOME (PtrVar (Var y) sz)` by fs[] >>
     qpat_x_assum `!rb. ce.ce_return_buf = SOME rb ==> _`
       (qspec_then `PtrVar (Var y) sz` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ed.storage_trace ==>
       ghost_inv_at (DF H) lo NONE ce1 cx (ed with scopes := [penv])
         Gf tnf fixed` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ed.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
     qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     rewrite_tac[ghost_inv_at_def, return_buf_ptr_def] >>
     rpt conj_tac
     >- (rpt gen_tac >> disch_then (mp_tac o cj 2) >>
         qpat_assum `!nm p sz. FLOOKUP ce1.ce_vars nm <> _`
           (qspecl_then [`name'`, `Var p`, `sz`] mp_tac) >> simp[NoAsms])
     >- (qpat_assum `ce1.ce_return_pc = SOME _` SUBST1_TAC >>
         qpat_assum `rpc = Var x` SUBST1_TAC >>
         qpat_assum `op_taint tnf rpc = _` mp_tac >>
         qpat_assum `rpc = Var x` SUBST1_TAC >> simp[NoAsms])
     >- (qpat_assum `stor_taint_ok_at (DF H) tn u` mp_tac >>
         qpat_assum `tnf.t_stor = tn.t_stor` (fn th => rewrite_tac[stor_taint_ok_at_def, th]) >>
         map_every (fn q => qpat_assum q SUBST1_TAC)
           [`tnf.t_trans = _`, `tnf.t_imm = _`, `fixed.vs_accounts = _`,
            `fixed.vs_call_ctx = _`, `fixed.vs_transient = _`, `fixed.vs_immutables = _`] >>
         simp[NoAsms])
     >- (map_every (fn q => qpat_assum q SUBST1_TAC)
           [`tnf.t_mem = _`, `fixed.vs_memory = _`] >> first_assum ACCEPT_TAC)
     >- (qpat_assum `ce1.ce_imm_alloca = NONE` SUBST1_TAC >> simp[NoAsms])
     >- (rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
         qpat_assum `fixed.vs_allocas = FEMPTY` SUBST1_TAC >> simp[NoAsms]) >>
     qpat_assum `fixed.vs_alloca_next = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `Ds = IMAGE DF { H | valid_horizon cx st0 H ed.storage_trace }` >>
  `!D. D IN Ds ==> ghost_inv_at D lo NONE ce1 cx (ed with scopes := [penv])
       Gf tnf fixed` by
    (qpat_assum `Abbrev (Ds = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     gen_tac >> disch_then (qx_choose_then `H` strip_assume_tac o
       SRULE [pred_setTheory.IN_IMAGE]) >>
     qpat_assum `D = DF H` SUBST1_TAC >>
     qpat_assum `!H. valid_horizon cx st0 H ed.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
       (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp fixed /\
    fixed.vs_alloca_next + pending_alloca_size callee fixed <= w2n fixed.vs_initial_fmp` by
    (strip_tac >>
     drule_all intcall_args_entered_capture >> strip_tac >>
     `setup.vs_allocas = FEMPTY` by
       (qpat_assum `entered = setup` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `fixed = entered with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     qpat_assum `entered = setup` SUBST1_TAC >>
     qpat_x_assum `fmp_room ctx callee setup` mp_tac >>
     simp[exprLoweringPropsTheory.fmp_room_def,
          exprLoweringPropsTheory.pending_alloca_size_def,
          ptrDisciplineTheory.allocas_below_fmp_def] >>
     decide_tac) >>
  `?s Gs ts.
      ~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      s.vs_current_bb = lock_start.cs_current_bb /\
      s.vs_inst_idx = LENGTH lock_start.cs_current_insts /\
      s.vs_transient = fixed.vs_transient /\ s.vs_call_ctx = fixed.vs_call_ctx /\
      (!D. D IN Ds ==> stor_taint_ok_at D ts s) /\
      (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
         MAP (op_prov G) ops) (fixed,Gf,tnf) [] (OK s,Gs,ts))` by
    (irule args_materialize_to_lock >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`caps`, `ce1`, `ce2`, `cx`, `NONE`, `penv`,
       `ed with scopes := [penv]`, `u.vs_alloca_next`, `final`, `mr`, `fix_end`, `mat_end`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt gen_tac >> disch_tac >>
         (metis_tac[]))
     >- (qpat_assum `ce1.ce_return_pc = SOME _` SUBST1_TAC >>
         qpat_assum `rpc = Var x` SUBST1_TAC >>
         qpat_assum `not_fresh_at fix_end x` mp_tac >> simp[NoAsms])
     >- (qpat_assum `ce1.ce_imm_alloca = NONE` SUBST1_TAC >> simp[NoAsms])
     >- (`!ps. internal_stack_size ce1 ps = internal_stack_size ce ps` by
           (Induct >- simp[NoAsms, intCallCalleeTheory.internal_stack_size_def] >>
            Cases >> first_x_assum (fn ih =>
              qpat_assum `ce1.ce_vars = ce.ce_vars` (fn eq =>
                simp[NoAsms, intCallCalleeTheory.internal_stack_size_def, eq, ih]))) >>
         map_every (fn q => qpat_assum q SUBST1_TAC)
           [`fixed.vs_alloca_next = _`, `MAP _ caps = params`] >>
         qpat_assum `!ps. internal_stack_size ce1 ps = _` (qspec_then `params` SUBST1_TAC) >>
         first_assum ACCEPT_TAC)
     >- simp[NoAsms]
     >- (qpat_assum `fixed = entered with <|vs_vars := _; vs_inst_idx := _|>`
           (fn th => CONV_TAC (ONCE_REWRITE_CONV [th])) >> simp[NoAsms])) >>
  drule_all args_lock_code_cut >>
  disch_then (qx_choose_then `lock_bb` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H failed.storage_trace ==>
       valid_horizon cx st0 H ed.storage_trace` by
    (qpat_assum `failed = ed with storage_trace := _` SUBST1_TAC >>
     simp[NoAsms] >> rpt strip_tac >>
     drule_then ACCEPT_TAC gasOutcomeFullTheory.valid_horizon_append) >>
  `!H. valid_horizon cx st0 H failed.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
        MAP (op_prov G) ops) (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK s,Gs,ts) /\
    key_taint ts.t_trans (n2w global_nonreentrant_slot) = {} /\
    (tload (n2w global_nonreentrant_slot) s = 1w \/
      (mut <> View /\ s.vs_call_ctx.cc_static))` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H ed.storage_trace` by
       (qpat_assum `!H. valid_horizon cx st0 H failed.storage_trace ==> _`
          (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     `state_rel H func cenv cx ed u` by
       (irule stateRelProjTheory.stmt_state_rel_state_rel >>
        qexists_tac `ctx` >>
        qpat_assum `!H. valid_horizon cx st0 H ed.storage_trace ==>
           intcall_entry_full _ H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (mp_tac o cj 7 o PURE_REWRITE_RULE [intcall_entry_full_def]) >>
        simp[NoAsms]) >>
     `global_nonreentrant_slot < dimword (:256)` by
       simp[NoAsms, contextTheory.global_nonreentrant_slot_def] >>
     drule_all args_failed_lock_agrees >> strip_tac >>
     `DF H IN Ds` by
       (qpat_assum `Abbrev (Ds = _)`
          (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        simp[NoAsms, pred_setTheory.IN_IMAGE] >> qexists_tac `H` >> simp[]) >>
     conj_tac
     >- (qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK fixed,Gf,tnf)`
           (qspecl_then [`DF H`, `gas_explicit_sites ctx shadow_ctx`] (mp_tac o
             MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
         disch_then (qspecl_then [`fixed`,`Gf`,`tnf`,`[]`,`OK s`,`Gs`,`ts`] mp_tac) >>
         simp[NoAsms] >>
         qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK s,Gs,ts)`
           (qspec_then `DF H` mp_tac) >> simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `!D. D IN Ds ==> stor_taint_ok_at D ts s`
           (drule_then assume_tac) >>
         qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
           (qspec_then `H` assume_tac) >>
         drule_all_then ACCEPT_TAC args_lock_taint_cut) >>
     `tload (n2w global_nonreentrant_slot) s = tload (n2w global_nonreentrant_slot) u /\
      s.vs_call_ctx = u.vs_call_ctx` by
       (rewrite_tac[venomStateTheory.tload_def, venomStateTheory.contract_transient_def] >>
        map_every (fn q => qpat_assum q SUBST1_TAC)
          [`s.vs_transient = _`, `s.vs_call_ctx = _`,
           `fixed.vs_transient = _`, `fixed.vs_call_ctx = _`] >> simp[NoAsms]) >>
     map_every (fn q => qpat_assum q SUBST1_TAC)
       [`tload _ s = tload _ u`, `s.vs_call_ctx = u.vs_call_ctx`] >>
     qpat_assum `if tload _ u = 1w then _ else _` mp_tac >>
     Cases_on `tload (n2w global_nonreentrant_slot) u = 1w`
     >- (qpat_assum `tload _ u = 1w` (fn th => simp[NoAsms, th])) >>
     qpat_assum `~(tload _ u = 1w)`
       (fn th => simp[NoAsms, th, vyperInterpreterTheory.is_view_mut_def])) >>
  drule_all args_lock_abort_callee >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gc`
    (qx_choose_then `tc` strip_assume_tac))) >>
  qpat_x_assum `r = Abort _ _` SUBST_ALL_TAC >>
  `?msg. err = Error (RuntimeError msg)` by
    (qpat_assum `if lookup_storage _ _ = 1w then _ else _` mp_tac >>
     IF_CASES_TAC >> simp[NoAsms] >> metis_tac[]) >>
  qpat_x_assum `err = Error (RuntimeError msg)` SUBST_ALL_TAC >>
  `allocas_from lo u` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx _ G tn u`
       (ACCEPT_TAC o cj 7 o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def])) >>
  `!H. valid_horizon cx st0 H failed.storage_trace ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn inst u` by
    (rpt gen_tac >> disch_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ ops`, `decode_invoke inst = _`, `inst.inst_opcode = INVOKE`,
        `allocas_from lo u`, `ctx_has_dalloca ctx ==> allocas_below_fmp u`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def] >>
     qpat_x_assum `decode_invoke inst = _` mp_tac >>
     simp[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()] >>
     strip_tac >>
     gvs[ptrDisciplineTheory.taint_ok_def, listTheory.EVERY_MEM,
         ptrDisciplineTheory.op_taint_def,
         contextCodegenRelTheory.source_memory_read_ranges_def] >>
     gen_tac >> Cases_on `op = Label label` >> simp[] >>
     Cases_on `MEM op ops` >> simp[]) >>
  irule args_failed_lock_caller_outcome >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gc`, `a`, `bb`, `callee`, `entered`, `failed`,
                `inst`, `label`, `msg`, `ops`, `t`, `tc`] >>
  simp[]
QED

Theorem args_invoke_reach[local]:
  body_inv tops ctx cenv cx /\ MEM fn ctx.ctx_functions /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s0,G0,tn0) [] (OK entry,Ga,tna) /\
  gas_path ctx fn entry n (OK t) /\ gas_path ctx fn t m (OK u) ==>
  !inst. active_inst fn inst u ==> frag_reachable ctx fn s0 fn inst u
Proof
  strip_tac >>
  `gas_path ctx fn s0 0 (OK entry)` by
    (drule bodyFullIfExpReachTheory.gas_origin_ptr_path_erase >> simp[]) >>
  `gas_path ctx fn entry (n + m) (OK u)` by
    (irule gas_path_then >> qexists_tac `t` >> simp[]) >>
  `gas_path ctx fn s0 (n + m) (OK u)` by
    (mp_tac (Q.INST [`s` |-> `s0`, `t` |-> `entry`,
                     `n` |-> `0`, `m` |-> `n+m`, `r` |-> `OK u`]
        fragGasPathTheory.gas_path_then) >>
     simp[]) >>
  qpat_assum `gas_path ctx fn s0 (n + m) (OK u)`
    (mp_then Any mp_tac bodyFullIfExpReachTheory.gas_path_reach) >>
  disch_then (qspecl_then [`fn`,`s0`,`u`] mp_tac) >>
  simp[contextRawReachableTheory.frag_reachable_start] >> metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]
QED

Theorem args_defaults_restore_expr_sim_inv[local]:
  expr_sim_inv ce cx env before /\
  expr_sim_inv (cenv_without_defaults ce name)
    (cx with stk updated_by CONS (NONE,name)) (env with current_src := NONE) after ==>
  expr_sim_inv ce cx env after
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_inv ce cx env before`
    (strip_assume_tac o REWRITE_RULE
       [expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def]) >>
  qpat_x_assum `expr_sim_inv (cenv_without_defaults ce name) _ _ after`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def,
        vyperTypeInvariantsTheory.env_immutables_consistent_def,
        vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def]) >>
  pure_rewrite_tac[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms, vyperTypeInvariantsTheory.env_scopes_consistent_def,
       vyperTypeInvariantsTheory.env_immutables_consistent_def,
       vyperContextTheory.get_tenv_def, vyperContextTheory.get_module_code_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem args_fresh_outputs_code[local]:
  !n st names out. fresh_vars n st = (names,out) ==>
    out.cs_current_bb = st.cs_current_bb /\
    out.cs_current_insts = st.cs_current_insts
Proof
  Induct >>
  simp[fresh_vars_def, comp_return_def, comp_bind_def, fresh_var_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem args_invoke_code_at_cursor[local]:
  fn_has_code st emitted fn /\
  t.vs_current_bb = st.cs_current_bb /\
  t.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?u. emit_void INVOKE (Label lbl :: ops) st = (u,emitted)) \/
   (?n outs. emit_multi_op INVOKE (Label lbl :: ops) n st = (outs,emitted))) ==>
  ?bb inst.
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)
Proof
  strip_tac >>
  `?inst. emitted.cs_current_bb = st.cs_current_bb /\
     emitted.cs_current_insts = st.cs_current_insts ++ [inst] /\
     inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)` by
    ((qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
           comp_return_def, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.decode_invoke_def] >>
      strip_tac >> gvs[] >> NO_TAC) ORELSE
     (qpat_x_assum `emit_multi_op _ _ _ _ = _` mp_tac >>
      simp[emit_multi_op_def, comp_bind_def] >>
      Cases_on `fresh_vars n st` >> simp[] >>
      drule args_fresh_outputs_code >> strip_tac >>
      simp[emit_inst_def, comp_ignore_bind_def, comp_bind_def,
           fresh_id_def, emit_def, comp_return_def, LET_THM] >>
      strip_tac >> gvs[venomInstTheory.mk_inst_def, venomExecSemanticsTheory.decode_invoke_def])) >>
  drule_all fn_has_code_same_block >>
  simp[] >> metis_tac[]
QED

Theorem args_staged_provenance[local]:
  LENGTH tys = LENGTH ops /\
  EVERY (\ty. IS_SOME (evaluate_type tenv ty)) tys /\
  (!j rt. j < LENGTH ops /\ evaluate_type tenv (EL j tys) = SOME rt ==>
    (EL j flags ==> op_prov G (EL j ops) = NONE) /\
    (~EL j flags ==> ?b cap aid.
      op_prov G (EL j ops) = SOME (b,cap) /\
      FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
      lower <= aid /\ aid < upper /\ lo <= b /\ b + cap <= t.vs_alloca_next)) ==>
  !b cap. MEM (SOME (b,cap)) (MAP (op_prov G) ops) ==>
    ?aid. FLOOKUP t.vs_allocas aid = SOME (b,cap) /\ lower <= aid /\ aid < upper /\
          lo <= b /\ b + cap <= t.vs_alloca_next
Proof
  strip_tac >> map_every qx_gen_tac [`b`,`cap`] >>
  rewrite_tac[MEM_MAP, MEM_EL] >> strip_tac >>
  rename1 `n < LENGTH ops` >>
  `?rt. evaluate_type tenv (EL n tys) = SOME rt` by
    (qpat_assum `EVERY _ tys` (mp_tac o REWRITE_RULE[EVERY_EL]) >>
     disch_then (qspec_then `n` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `!j rt. _ ==> _` (qspecl_then [`n`,`rt`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `op_prov G (EL n ops) = SOME (b,cap)` by
    (qpat_assum `SOME (b,cap) = op_prov G y` mp_tac >>
     qpat_assum `y = EL n ops` (fn th => rewrite_tac[th]) >>
     simp[NoAsms]) >>
  `~EL n flags` by
    (spose_not_then assume_tac >>
     qpat_assum `EL n flags ==> _` (drule_then mp_tac) >>
     qpat_assum `op_prov G (EL n ops) = SOME (b,cap)`
       (fn th => simp[NoAsms,th])) >>
  qpat_assum `~EL n flags ==> _` (drule_then (qx_choose_then `bb` (qx_choose_then `cc`
      (qx_choose_then `aid` strip_assume_tac)))) >>
  qexists_tac `aid` >>
  map_every (fn q => qpat_assum q mp_tac)
    [`op_prov G (EL n ops) = SOME (b,cap)`,
     `op_prov G (EL n ops) = SOME (bb,cc)`, `FLOOKUP t.vs_allocas aid = SOME (bb,cc)`,
     `lower <= aid`, `aid < upper`, `lo <= bb`, `bb + cc <= t.vs_alloca_next`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Theorem args_bound_types_evaluate[local]:
  !args vals penv.
    bind_arguments tenv args vals = SOME penv ==>
    EVERY (\ty. IS_SOME (evaluate_type tenv ty)) (MAP SND args)
Proof
  Induct_on `args` >> simp[] >>
  Cases >> Cases_on `vals` >>
  simp[Once bind_arguments_def, AllCaseEqs(), PULL_EXISTS] >>
  metis_tac[]
QED

Theorem args_compile_expr_alloca_interval[local]:
  compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ sa.cs_next_id <= inst.inst_id /\
  inst.inst_id < sm.cs_next_id ==>
  ~not_fresh_at sa p
Proof
  strip_tac >> drule compileExprAllocaFreshTheory.compile_expr_alloca_fresh >> strip_tac >>
  `inst.inst_id IN frag_ids sa sm` by simp[abiEncoderPropsTheory.frag_ids_def] >>
  `cs_extends sa sm` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  mp_tac (Q.INST [`sb` |-> `sm`,
                  `P` |-> `\i. i.inst_opcode = ALLOCA ==>
                       i.inst_id IN frag_ids sa sm /\
                       !q. MEM q i.inst_outputs ==> ~not_fresh_at sa q`]
           compilerInstructionSuffixTheory.added_insts_function_property) >>
  simp[]
QED

Theorem args_return_buffer_geometry[local]:
  (ret <> NoneT ==> 0 < type_memory_size tv) /\
  get_module_code cx NONE = SOME tops /\
  expr_sim_inv ce cx env es /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  evaluate_type (get_tenv cx) ret = SOME tv /\
  compute_func_info
    (\k. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) k))
    ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret)
    ty_args = (nrc,rbs,pvs) ==>
  ((nrc = 0 /\ ret <> NoneT) <=> nrc = 0 /\ 0 < rbs) /\
  (nrc = 0 /\ 0 < rbs ==> rbs = type_memory_size tv)
Proof
  strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret =
    type_memory_size tv` by
    (drule_all expr_sim_inv_memory_size >>
     simp[GSYM structFieldsPropsTheory.type_mem_bytes_type_memory_bytes]) >>
  Cases_on `ret = NoneT` >> gvs[compute_func_info_def, returns_stack_count_def] >>
  Cases_on `nrc = 0` >> gvs[] >> Cases_on `ret` >> gvs[]
QED

Theorem args_enter_invoke[local]:
  lowering_context_ok ctx /\ MEM caller ctx.ctx_functions /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  eval_operands ops s = SOME argv ==>
  ?callee setup entered.
    lookup_function lbl ctx.ctx_functions = SOME callee /\
    setup_callee callee argv s = SOME setup /\
    gas_invoke_entry (ctx,caller) s callee entered
Proof
  strip_tac >>
  `MEM inst (fn_insts caller)` by
    metis_tac[fragFuelTheory.lookup_block_get_instruction_fn_insts] >>
  `ctx_distinct_fn_names ctx /\ wf_invoke_targets ctx` by
    fs[vyperCompilerTheory.lowering_context_ok_def,
       venomWfTheory.ctx_distinct_fn_names_def,
       vyperCompilerTheory.wf_invoke_targets_check_eq] >>
  drule_all vyperCompilerTheory.invoke_target_resolves_uniquely >> strip_tac >>
  `label = lbl` by fs[venomExecSemanticsTheory.decode_invoke_def] >>
  qpat_x_assum `label = lbl` SUBST_ALL_TAC >>
  `MEM callee ctx.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `callee.fn_blocks <> []` by
    fs[vyperCompilerTheory.lowering_context_ok_def, EVERY_MEM, venomWfTheory.fn_has_entry_def] >>
  Cases_on `callee.fn_blocks` >> fs[] >>
  `?setup. setup_callee callee argv s = SOME setup` by
    simp[venomExecSemanticsTheory.setup_callee_def] >>
  `lookup_block setup.vs_current_bb callee.fn_blocks = SOME h /\
    ~setup.vs_halted` by
    gvs[venomExecSemanticsTheory.setup_callee_def, venomInstTheory.lookup_block_def, FIND_thm] >>
  `MEM h callee.fn_blocks` by simp[] >>
  `phi_prefix_length h.bb_instructions = 0` by
    (irule venomExecProofsTheory.no_phis_phi_prefix_length_zero >>
     fs[vyperCompilerTheory.lowering_context_ok_def, vyperCompilerTheory.ptr_ok_check_def, EVERY_MEM] >>
     metis_tac[venomFnInstsProofsTheory.MEM_fn_insts]) >>
  `eval_phis setup h.bb_instructions = OK setup` by metis_tac[eval_phis_no_phi] >>
  qexistsl_tac [`setup`,`setup with vs_inst_idx := 0`] >>
  simp[] >>
  rewrite_tac[fragGasFocusTheory.gas_invoke_entry_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bb`,`inst`,`lbl`,`ops`,`argv`,`setup`,`h`,`setup`] >>
  simp[]
QED

Theorem args_stack_flag_bound[local]:
  !tys n. LENGTH (FILTER I (compute_pass_via_stack tys n)) <= MAX_STACK_ARGS - n
Proof
  Induct >> simp[compute_pass_via_stack_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `n + 1` mp_tac) >> simp[] >> decide_tac
QED

Theorem args_div32_shift[local]:
  !n. (n + 32) DIV 32 = 1 + n DIV 32
Proof
  gen_tac >>
  mp_tac (Q.SPECL [`1`, `n`]
    (MATCH_MP (Q.SPEC `32` arithmeticTheory.ADD_DIV_ADD_DIV) (EQT_ELIM (EVAL (Term `0 < (32:num)`))))) >>
  simp[Once arithmeticTheory.ADD_COMM]
QED

Theorem args_vector_bound[local]:
  flags = compute_pass_via_stack tys n /\
  LENGTH ws = LENGTH flags /\ LENGTH prefix <= 1 /\
  frontier < dimword (:256) /\
  (!i. i < LENGTH flags /\ ~EL i flags ==>
    32 <= sz i /\ offset_of i + sz i <= frontier) /\
  (!i j. i < LENGTH flags /\ j < LENGTH flags /\
    ~EL i flags /\ ~EL j flags /\ i <> j ==>
    offset_of i + sz i <= offset_of j \/ offset_of j + sz j <= offset_of i) ==>
  LENGTH (prefix ++ ws) < dimword (:256)
Proof
  strip_tac >>
  qabbrev_tac `idx = FILTER (\i. ~EL i flags) (rich_list$COUNT_LIST (LENGTH flags))` >>
  `EVERY (\i. i < LENGTH flags /\ ~EL i flags) idx` by
    simp[Abbr `idx`, EVERY_MEM, MEM_FILTER, rich_listTheory.MEM_COUNT_LIST] >>
  `ALL_DISTINCT idx` by
    (simp_tac bool_ss [Abbr `idx`] >> irule FILTER_ALL_DISTINCT >>
     rewrite_tac[rich_listTheory.all_distinct_count_list]) >>
  `CARD (set idx) = LENGTH idx` by
    (irule ALL_DISTINCT_CARD_LIST_TO_SET >> first_assum ACCEPT_TAC) >>
  `CARD (IMAGE (\i. offset_of i DIV 32) (set idx)) = CARD (set idx)` by
    (irule pred_setTheory.CARD_IMAGE_INJ >> simp[] >>
     fs[EVERY_MEM] >> rpt strip_tac >> CCONTR_TAC >>
     qpat_assum `!i j. _ ==> _` (qspecl_then [`x`,`y`] mp_tac) >>
     impl_tac >- metis_tac[] >>
     `32 <= sz x /\ 32 <= sz y` by metis_tac[] >>
     `(offset_of x + 32) DIV 32 = 1 + offset_of x DIV 32` by
       rewrite_tac[args_div32_shift] >>
     `(offset_of y + 32) DIV 32 = 1 + offset_of y DIV 32` by
       rewrite_tac[args_div32_shift] >>
     strip_tac
     >- (`(offset_of x + 32) DIV 32 <= offset_of y DIV 32` by
          (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[] >> decide_tac) >> decide_tac) >>
     `(offset_of y + 32) DIV 32 <= offset_of x DIV 32` by
       (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[] >> decide_tac) >> decide_tac) >>
  `IMAGE (\i. offset_of i DIV 32) (set idx) SUBSET count (2 ** 251)` by
    (simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_IMAGE] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     `i < LENGTH flags /\ ~EL i flags` by
       (qpat_assum `!i. MEM i idx ==> _` drule >> simp[]) >>
     qpat_assum `!j. j < LENGTH flags /\ ~EL j flags ==> _`
       (qspec_then `i` mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     `offset_of i < dimword (:256)` by decide_tac >>
     gvs[] >>
     asm_simp_tac bool_ss [arithmeticTheory.DIV_LT_X, DECIDE (Term `0 < (32:num)`)] >>
     qpat_x_assum `offset_of i < dimword (:256)` mp_tac >>
     simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV (Term `dimindex (:256)`)]) >>
  `CARD (IMAGE (\i. offset_of i DIV 32) (set idx)) <= 2 ** 251` by
    (drule (MATCH_MP (Q.ISPEC `count ((2:num) ** 251)` pred_setTheory.CARD_SUBSET)
                     (Q.SPEC `(2:num) ** 251` pred_setTheory.FINITE_COUNT)) >> simp[]) >>
  `LENGTH (FILTER (\b. ~b) flags) = LENGTH idx` by
    (`MAP (\i. EL i flags) (rich_list$COUNT_LIST (LENGTH flags)) = flags` by
       (irule LIST_EQ >> simp[EL_MAP, rich_listTheory.LENGTH_COUNT_LIST, rich_listTheory.EL_COUNT_LIST]) >>
     qpat_x_assum `MAP (\i. EL i flags) _ = flags` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     simp[Abbr `idx`, rich_listTheory.FILTER_MAP, combinTheory.o_DEF]) >>
  `!bs. LENGTH (FILTER I bs) + LENGTH (FILTER (\b. ~b) bs) = LENGTH bs` by
    (Induct >> simp[] >> Cases >> simp[]) >>
  `LENGTH (FILTER I flags) <= 6` by
    (fs[] >> mp_tac (Q.SPECL [`tys`,`n`] args_stack_flag_bound) >>
     simp[MAX_STACK_ARGS_def] >> decide_tac) >>
  `2 ** 251 + 7 < dimword (:256)` by
       (simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV (Term `dimindex (:256)`)] >> EVAL_TAC) >>
  first_x_assum (qspec_then `flags` assume_tac) >>
  simp_tac bool_ss [LENGTH_APPEND] >> decide_tac
QED

Theorem args_vector_bound_sites[local]:
  flags = compute_pass_via_stack tys n /\
  LENGTH ws = LENGTH flags /\ LENGTH prefix <= 1 /\
  frontier < dimword (:256) /\
  (!i. i < LENGTH flags /\ ~EL i flags ==>
    ?b cap. op_prov G (EL i ops) = SOME (b,cap) /\
      32 <= cap /\ b + cap <= frontier) /\
  (!i j b cap c len. i < j /\ j < LENGTH flags /\
    ~EL i flags /\ ~EL j flags /\
    op_prov G (EL i ops) = SOME (b,cap) /\
    op_prov G (EL j ops) = SOME (c,len) ==>
    regions_disjoint b cap c len) ==>
  LENGTH (prefix ++ ws) < dimword (:256)
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`offset_of` |-> `\i. FST (THE (op_prov G (EL i ops)))`,
     `sz` |-> `\i. SND (THE (op_prov G (EL i ops)))`] args_vector_bound) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> BETA_TAC
  >- (gen_tac >> strip_tac >>
      qpat_assum `!i. _ ==> ?b cap. _` (qspec_then `i` mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> ?b cap. _` (qspec_then `i` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `b` (qx_choose_then `cap` strip_assume_tac)) >>
  qpat_assum `!i. _ ==> ?b cap. _` (qspec_then `j` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `c` (qx_choose_then `len` strip_assume_tac)) >>
  Cases_on `i < j`
  >- (qpat_assum `!i j b cap c len. _ ==> regions_disjoint _ _ _ _`
        (qspecl_then [`i`,`j`,`b`,`cap`,`c`,`len`] mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `j < i` by decide_tac >>
  qpat_assum `!i j b cap c len. _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`j`,`i`,`c`,`len`,`b`,`cap`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >> simp[]
QED

Theorem args_materialization_charge[local]:
  !caps ce sa ce' sb.
    materialize_internal_params ce caps sa = (ce',sb) /\
    ALL_DISTINCT (MAP FST caps) /\
    (!nm off sz. MEM nm (MAP FST caps) /\
       FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==> sz < dimword (:256)) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    ?new.
       sb.cs_current_insts = sa.cs_current_insts ++ new /\
       SUM (MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA) new)) =
       internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
Proof
  `!(caps:(string # bool # operand) list) ce name loc. ~MEM name (MAP FST caps) ==>
      internal_stack_size (ce with ce_vars updated_by (\m. m |+ (name,loc)))
        (MAP (\c. (FST c,FST (SND c))) caps) =
      internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)` by
    (Induct >> simp[intCallCalleeTheory.internal_stack_size_def] >>
     PairCases >> simp[intCallCalleeTheory.internal_stack_size_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  Induct
  >- simp[moduleLoweringTheory.materialize_internal_params_def, comp_return_def,
          intCallCalleeTheory.internal_stack_size_def] >>
  PairCases >> rpt gen_tac >>
  simp[moduleLoweringTheory.materialize_internal_params_def, intCallCalleeTheory.internal_stack_size_def] >>
  rename1 `if is_stack then _ else _` >>
  rename1 `FLOOKUP ce.ce_vars nm` >>
  Cases_on `is_stack` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars nm` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
      rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
      TRY (strip_tac >> first_x_assum drule >> simp[] >>
           disch_then ACCEPT_TAC >> NO_TAC) >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >>
      (impl_tac >- (simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])) >>
      simp[] >> strip_tac >> simp[] >>
      rename1 `FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz)` >>
      `sz < dimword (:256)` by metis_tac[] >>
      simp[FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND,
           exprLoweringPropsTheory.alloca_lit_size_def, venomInstTheory.mk_inst_def, arithmeticTheory.ADD1] >>
      last_assum (qspecl_then [`caps`, `ce`, `nm`, `PtrVar (Var ("%" ++ toString sa.cs_next_var)) sz`] mp_tac) >>
      simp[]) >>
  strip_tac >> first_x_assum drule >>
  (impl_tac >- (simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])) >>
  strip_tac >> simp[] >>
  last_assum irule >>
  first_assum ACCEPT_TAC
QED

Theorem args_callee_compiled_charge_room[local]:
  alloca_room ctx callee setup /\ setup.vs_allocas = FEMPTY /\
  fn_has_code sa sb callee /\ sb.cs_current_insts = sa.cs_current_insts ++ new ==>
  setup.vs_alloca_next +
  SUM (MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA) new))
  < dimword (:256)
Proof
  strip_tac >>
  qpat_assum `fn_has_code _ _ _` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  `MEM bb callee.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `?after. bb.bb_instructions = sa.cs_current_insts ++ new ++ after` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND, APPEND_ASSOC] >>
  `?before rest. callee.fn_blocks = before ++ bb :: rest` by
    metis_tac[MEM_SPLIT] >>
  qpat_x_assum `alloca_room _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.alloca_room_def, exprLoweringPropsTheory.pending_alloca_size_def,
       venomInstTheory.fn_insts_def, venomFnInstsProofsTheory.fn_insts_blocks_flat,
       FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND, FLAT_APPEND] >>
  decide_tac
QED

Theorem args_callee_room[local]:
  alloca_room ctx func u /\ fmp_room ctx func u /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (lbl,ops) /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv u = SOME setup ==>
  alloca_room ctx callee setup /\ fmp_room ctx callee setup /\
  setup.vs_alloca_next = u.vs_alloca_next /\ setup.vs_allocas = FEMPTY
Proof
  strip_tac >>
  `callee.fn_name = lbl` by metis_tac[vyperCompilerTheory.lookup_function_result_name] >>
  `lookup_function func.fn_name ctx.ctx_functions = SOME func` by
    fs[exprLoweringPropsTheory.alloca_room_def] >>
  `inst.inst_operands = Label lbl :: ops` by
    gvs[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()] >>
  `fn_directly_calls ctx func.fn_name callee.fn_name` by
    (simp[fcgDefsTheory.fn_directly_calls_def] >> metis_tac[]) >>
  `setup.vs_alloca_next = u.vs_alloca_next /\ setup.vs_allocas = FEMPTY /\
   setup.vs_initial_fmp = u.vs_initial_fmp /\ setup.vs_fmp = u.vs_fmp /\
   setup.vs_memory = u.vs_memory` by
    gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()] >>
  simp[] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.alloca_room_callee] >>
  `MEM callee ctx.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  pure_rewrite_tac[exprLoweringPropsTheory.fmp_room_def] >> disch_tac >>
  `ctx_has_dalloca ctx` by
    (fs[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  qpat_x_assum `fmp_room ctx func u`
    (mp_tac o REWRITE_RULE [exprLoweringPropsTheory.fmp_room_def]) >>
  simp_tac bool_ss [ASSUME ``ctx_has_dalloca ctx``] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  asm_rewrite_tac[] >>
  qabbrev_tac `above = {g | TC (fn_directly_calls ctx) func.fn_name g}` >>
  qabbrev_tac `below = {g | TC (fn_directly_calls ctx) callee.fn_name g}` >>
  qabbrev_tac `frame = unit_alloca_frame ctx` >>
  `FINITE above /\ ~TC (fn_directly_calls ctx) callee.fn_name callee.fn_name` by
    (fs[Abbr `above`, exprLoweringPropsTheory.alloca_room_def] >>
     metis_tac[relationTheory.TC_RULES]) >>
  `below SUBSET above` by
    (rw[Abbr `below`, Abbr `above`, pred_setTheory.SUBSET_DEF] >>
     metis_tac[relationTheory.TC_RULES]) >>
  `CARD below < CARD above` by
    (irule pred_setTheory.CARD_PSUBSET >>
     simp[pred_setTheory.PSUBSET_MEMBER] >>
     qexists_tac `callee.fn_name` >>
     simp[Abbr `above`, Abbr `below`] >> metis_tac[relationTheory.TC_RULES]) >>
  `pending_alloca_size callee setup <= frame` by
    simp[Abbr `frame`, exprLoweringPropsTheory.pending_alloca_size_le_frame] >>
  `frame * SUC (CARD below) <= frame * CARD above` by
    simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  qpat_x_assum `callee.fn_name = lbl` (SUBST_ALL_TAC o SYM) >>
  qunabbrev_tac `below` >>
  full_simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem args_internal_entry_extends[local]:
  compile_internal_function ce params has_rb nr key trans view ctor ilen
    ss rt entry = ((),final) ==>
  ?ce2 rpc imm after.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,rpc,imm),after) /\
    cs_extends after final
Proof
  simp[intCallCalleeTheory.compile_internal_function_entry_factorization,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, comp_get_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_internal_function_entry _ _ _ _ _ _ _ = (pack,_)` >>
  PairCases_on `pack` >> gvs[] >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >>
  Cases_on `nr` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule (SRULE [cs_appends_def] entryCompileIntervalsTheory.cs_appends_stmts) >>
  strip_tac >>
  qmatch_asmsub_rename_tac `block_is_terminated body_end` >>
  Cases_on `block_is_terminated body_end` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `rt` >> gvs[] >>
  TRY (qpat_assum `compile_nonreentrant_lock _ _ _ _ = _`
    (mp_then Any assume_tac (SRULE [cs_appends_def]
      (cj 1 entryCompileIntervalsTheory.cs_appends_nonreentrant)))) >>
  TRY (qpat_assum `compile_nonreentrant_unlock _ _ _ _ = _`
    (mp_then Any assume_tac (SRULE [cs_appends_def]
      (cj 2 entryCompileIntervalsTheory.cs_appends_nonreentrant)))) >>
  TRY (qpat_assum `emit_inst _ _ _ _ = _`
    (mp_then Any assume_tac (SRULE [cs_appends_def]
      (cj 1 cs_appends_emit_helpers)))) >>
  POP_ASSUM_LIST (fn ths =>
    MAP_EVERY assume_tac (List.filter (can (match_term ``cs_extends x y``) o concl) ths)) >>
  metis_tac[cs_extends_trans]
QED

Theorem args_internal_materialization_room[local]:
  compile_internal_function ce params has_rb nr key trans view ctor ilen
    ss rt entry = ((),final) /\
  fn_has_code entry final callee /\ alloca_room ctx callee setup /\
  setup.vs_allocas = FEMPTY /\ ALL_DISTINCT (MAP FST params) /\
  (!nm off sz. MEM nm (MAP FST params) /\
    FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==> sz < dimword (:256)) ==>
  setup.vs_alloca_next + internal_stack_size ce params < dimword (:256)
Proof
  strip_tac >>
  drule_then strip_assume_tac args_internal_entry_extends >>
  drule_then strip_assume_tac intcall_args_entry_cuts >>
  drule_then strip_assume_tac intcall_args_capture_cut >>
  drule_then strip_assume_tac intCallCalleeTheory.compile_internal_entry_prefix_shape >>
  `cs_extends entry cap_end` by (irule cs_extends_same_block >> simp[]) >>
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `fix_end = cap_end \/
     ?n id buf. compile_fixed_region_with_id n cap_end = ((id,buf),fix_end)`
  >- (Cases_on `ctor /\ 0 < ilen` >> fs[] >> metis_tac[]) >>
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `after = mat_end \/ ?n buf. compile_alloc_buffer n mat_end = (buf,after)`
  >- (Cases_on `rt` >> fs[] >> Cases_on `0 < ce.ce_returns_count` >> fs[] >> metis_tac[]) >>
  `cs_extends cap_end fix_end` by
    (qpat_assum `fix_end = cap_end \/ _` strip_assume_tac >- simp[cs_extends_refl] >>
     qmatch_asmsub_rename_tac `compile_fixed_region_with_id n cap_end` >>
     mp_tac (Q.SPECL [`n`,`cap_end`] externalEntryShapeTheory.compile_fixed_region_with_id_labels) >>
     simp[]) >>
  `cs_extends fix_end mat_end` by
    (mp_tac (Q.SPECL [`caps`,`ce1`,`fix_end`]
       externalEntryShapeTheory.materialize_internal_params_labels) >> simp[]) >>
  `cs_extends mat_end after` by
    (qpat_assum `after = mat_end \/ _` strip_assume_tac
     >- simp[cs_extends_refl] >>
     drule_then ACCEPT_TAC loweringHaltTheory.compile_alloc_buffer_extends) >>
  `fn_has_code fix_end mat_end callee` by
    (irule (cj 1 (Q.SPECL [`fix_end`,`mat_end`,`final`,`callee`] fn_has_code_split)) >>
     metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `MAP FST caps = MAP FST params` by
    (qpat_assum `MAP _ caps = params` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o,combinTheory.o_DEF,ETA_AX]) >>
  `!ps. internal_stack_size ce1 ps = internal_stack_size ce ps` by
    (Induct >> simp[intCallCalleeTheory.internal_stack_size_def] >>
     Cases >> simp[intCallCalleeTheory.internal_stack_size_def]) >>
  qpat_assum `materialize_internal_params _ _ _ = _`
    (mp_then Any mp_tac args_materialization_charge) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all args_callee_compiled_charge_room >>
  simp[]
QED

Theorem args_callee_package_room[local]:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
       cx.in_deploy) ctx.ctx_functions = SOME callee /\
  alloca_room ctx func u /\ fmp_room ctx func u /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME
    (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
       cx.in_deploy, ops) /\
  setup_callee callee argv u = SOME setup /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans keys cenv.ce_is_ctor pad_len
       (mut,nr,rr,name,args,dflts',ret,ss)) =
    (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,ilen,ss',rt) /\
  ALL_DISTINCT (MAP FST params) /\
  (!nm off sz. MEM nm (MAP FST params) /\
    FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==> sz < dimword (:256)) ==>
  u.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx callee setup /\ fmp_room ctx callee setup
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule_all args_callee_room >> strip_tac >>
  drule_all bodyFullShadowInternalRunTheory.body_inv_selected_internal_code >>
  disch_then (qx_choose_then `actual_lbl` (qx_choose_then `actual_ce` (qx_choose_then `actual_params`
    (qx_choose_then `actual_rb` (qx_choose_then `actual_nr` (qx_choose_then `actual_key`
    (qx_choose_then `actual_trans` (qx_choose_then `actual_view` (qx_choose_then `actual_ctor`
    (qx_choose_then `actual_ilen` (qx_choose_then `actual_rt` (qx_choose_then `before`
    (qx_choose_then `old` (qx_choose_then `entry`
    (qx_choose_then `final` strip_assume_tac))))))))))))))) >>
  qpat_x_assum `set_internal_package_target _ (package_internal_fn _ _ _ _ _ (subst_consts_fn _ _)) = _`
    (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def]) >>
  `actual_params = params /\ actual_ce.ce_vars = ce.ce_vars` by
    (qpat_assum `set_internal_package_target _ (package_internal_fn _ T _ _ _ _) = _` mp_tac >>
     qpat_assum `set_internal_package_target _ (package_internal_fn _ use_trans _ _ _ _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compileVyperTheory.set_internal_package_target_def, compileVyperTheory.package_internal_fn_def,
          pairTheory.UNCURRY, compileVyperTheory.update_cenv_nonreentrant_def,
          entryDispatchPropsTheory.build_compile_env_subst_consts_stmts,
          compileVyperTheory.build_compile_env_def] >>
     rpt strip_tac >> gvs[]) >>
  `!ps. internal_stack_size actual_ce ps = internal_stack_size ce ps` by
    (Induct >> simp[intCallCalleeTheory.internal_stack_size_def] >> Cases >> simp[intCallCalleeTheory.internal_stack_size_def]) >>
  drule args_internal_materialization_room >>
  disch_then (qspecl_then [`setup`,`ctx`,`callee`] mp_tac) >>
  simp[] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem args_immutable_subwindow[local]:
  immutable_alloca_sep func ce cx es u /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,cap) /\
  b <= w /\ w + sz <= b + cap ==>
  regions_disjoint io (type_memory_size tv) w sz
Proof
  strip_tac >>
  `regions_disjoint io (type_memory_size tv) b cap` by
    (qpat_assum `immutable_alloca_sep _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.immutable_alloca_sep_def]) >>
     first_x_assum (drule_then (qspecl_then [`nm`,`tv`,`iv`,`io`] mp_tac)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem args_internal_regions_separate[local]:
  !G ops.
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b cap. op_prov G (EL i ops) = SOME (b,cap) /\
      b <= w2n (EL (arg_base + i) (argv:256 word list)) /\
      w2n (EL (arg_base + i) (argv:256 word list)) + sz <= b + cap) /\
  (!i j b cap c len. i < j /\ j < LENGTH params /\
    ~SND (EL i params) /\ ~SND (EL j params) /\
    op_prov G (EL i ops) = SOME (b,cap) /\
    op_prov G (EL j ops) = SOME (c,len) ==>
    regions_disjoint b cap c len) ==>
  !i j offi szi offj szj.
    i < LENGTH params /\ j < LENGTH params /\ i <> j /\
    ~SND (EL i params) /\ ~SND (EL j params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc offi szi) /\
    FLOOKUP ce.ce_vars (FST (EL j params)) = SOME (MemLoc offj szj) ==>
    regions_disjoint (w2n (EL (arg_base + i) argv)) szi
                     (w2n (EL (arg_base + j) argv)) szj
Proof
  rpt strip_tac >>
  qpat_assum `!i off sz. _ ==> ?b cap. _`
    (qspecl_then [`i`,`offi`,`szi`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `b` (qx_choose_then `cap` strip_assume_tac)) >>
  qpat_assum `!i off sz. _ ==> ?b cap. _`
    (qspecl_then [`j`,`offj`,`szj`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `c` (qx_choose_then `len` strip_assume_tac)) >>
  `regions_disjoint b cap c len` by
    (Cases_on `i < j`
     >- (qpat_assum `!i j b cap c len. _ ==> _`
           (qspecl_then [`i`,`j`,`b`,`cap`,`c`,`len`] mp_tac) >> simp[]) >>
     `j < i` by decide_tac >>
     qpat_assum `!i j b cap c len. _ ==> _`
       (qspecl_then [`j`,`i`,`c`,`len`,`b`,`cap`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem args_scope_outcome[local]:
  ~s.vs_halted /\
  (!obs. source (es with gas_obs := obs) =
         scoped ((es with scopes := scopes) with gas_obs := obs)) /\
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0 scoped
    (es with scopes := scopes,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ scoped _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (qpat_assum `gas_bad_storage_at cx st0 scoped _ s marks` mp_tac >>
          pure_rewrite_tac[gasStorageTheory.gas_bad_storage_at_def] >>
          asm_rewrite_tac[]) >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      fs[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac
      >- (qpat_assum `!tail. scoped _ = (res,ee with gas_obs := tail)` mp_tac >>
          simp[]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  reverse conj_tac
  >- (qexists_tac `H` >> fs[]) >>
  qabbrev_tac `enter = \src:evaluation_state.
    (if src with gas_obs := [] = es with gas_obs := [] then
       (INL T,src with scopes := scopes)
     else (INL F,src)) : bool evaluation_result` >>
  qabbrev_tac `rest = \b:bool.
    ignore_bind (if b then scoped else source) (return ())` >>
  `vyperState$bind enter rest = ignore_bind source (return ())` by
    (simp[FUN_EQ_THM,Abbr `enter`,Abbr `rest`,bind_def] >>
     gen_tac >> IF_CASES_TAC >> simp[] >>
     `x = es with gas_obs := x.gas_obs` by
       fs[evaluation_state_component_equality] >>
     qpat_assum `x = es with gas_obs := x.gas_obs` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `!obs. source _ = scoped _`
       (qspec_then `x.gas_obs` mp_tac) >>
     simp[ignore_bind_def,bind_def,evaluation_state_component_equality]) >>
  `gas_marked_exec T (ctx,fn) enter (es,s) [] (INL T)
       (es with scopes := scopes) (OK s)` by
    (simp[gasSummaryTheory.gas_marked_exec_def,gasSummaryTheory.gas_explicit_def,Abbr `enter`,
          evaluation_state_component_equality] >>
     irule fragGasModeTheory.gas_marked_path_from_mem >>
     simp[cj 1 fragGasPathMemTheory.gas_path_mem_rules]) >>
  `gas_exempt_cert T tops (ctx,fn) (rest T)
     ((es with scopes := scopes) with gas_obs := [],s)
     marks (err,ee) (leaf,finish')` by
    (simp[Abbr `rest`] >>
     drule gasExemptCertTheory.gas_exempt_cert_start_gas_obs >> simp[]) >>
  drule_all gasExemptCertTheory.gas_exempt_cert_bind_bool >> simp[]
QED

Theorem args_rest_outcome[local]:
  ~u.vs_halted /\
  (!locked. lock_if_nr cx nr (is_view_mut mut) ed = (INL (),locked) ==>
    !tail. source (ed with gas_obs := tail) =
      bind (intcall_rest cx name mut nr ss ed.scopes rtv) f
        ((ed with scopes := [penv]) with gas_obs := tail)) /\
  (!err failed. lock_if_nr cx nr (is_view_mut mut) ed = (INR err,failed) ==>
    !tail. source (ed with gas_obs := tail) =
      (INR err, failed with <|scopes := ed.scopes; gas_obs := tail|>)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (intcall_rest cx name mut nr ss ed.scopes rtv) f)
    (ed with scopes := [penv],u,G,tn) Q R /\
  (!err failed.
    lock_if_nr cx nr (is_view_mut mut) ed = (INR err,failed) /\
    (!tail. source (ed with gas_obs := tail) =
      (INR err,failed with gas_obs := tail)) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      source (ed,u,G,tn) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    source (ed,u,G,tn) Q R
Proof
  strip_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) ed` >>
  rename1 `lock_if_nr _ _ _ _ = (lock_res,locked)` >>
  Cases_on `lock_res`
  >- (irule args_scope_outcome >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`bind (intcall_rest cx name mut nr ss ed.scopes rtv) f`,
                     `[penv]`] >>
      fs[oneTheory.one]) >>
  qpat_x_assum `!err failed. _ /\ _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    irule >> qexistsl_tac [`y`,`locked`] >>
  simp[] >>
  `locked.scopes = ed.scopes` by metis_tac[ctorDeployLoweringSourceTheory.lock_if_nr_scopes] >>
  `!tail. locked with <|scopes := ed.scopes; gas_obs := tail|> =
         locked with gas_obs := tail` by
    (qpat_assum `locked.scopes = ed.scopes`
       (fn th => simp[NoAsms, evaluation_state_component_equality, GSYM th])) >>
  qx_gen_tac `tail` >>
  qpat_assum `!err failed. _ ==> !tail. _ = (INR err,_)`
    (qspecl_then [`y`,`locked`] mp_tac) >>
  simp[NoAsms] >>
  disch_then (qspec_then `tail` mp_tac) >>
  qpat_assum `!tail. locked with <|scopes := ed.scopes; gas_obs := tail|> = _`
    (fn th => rewrite_tac[th])
QED

Theorem intcall_args_defaults_source_cong[local]:
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx tenv ee /\
  well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt) /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  !gs. eval_exprs (cx with stk updated_by CONS (NONE,name))
          (DROP k (subst_consts_exprs (module_consts_env tops []) dflts))
          (ee with gas_obs := gs) =
       eval_exprs (cx with stk updated_by CONS (NONE,name)) (DROP k dflts)
          (ee with gas_obs := gs)
Proof
  strip_tac >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  qpat_x_assum `body_const_cells_agree [(NONE,tops)] cx tenv ee`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  gen_tac >>
  irule constSubstStmtsTheory.module_consts_intcall_defaults >>
  conj_tac
  >- (qexistsl_tac [`args`,`mut`,`nr`,`ret`,`ss`,`tops`] >> simp[]) >>
  qexistsl_tac [`A`,`art`,`dflt`,`tenv`,`es`,`imms`,`[(NONE,tops)]`,`roots`,`ann`] >>
  gvs[constSubstCorrectTheory.const_cells_agree_def]
QED


Theorem intcall_args_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))) ==>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
      (!v. storage_trace_frame (f v)) /\
      (!v. cs_appends (kc v)) /\
      comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
        kc sa = (out, sb) /\
      comp_bind
        (compile_expr (gas_shadow_env T cenv) ty
           (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
        kc shadow_sa = (out, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        P es0 /\
      (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 s0 /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!H res ee gt r.
         expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
         R H res ee gt r) /\
      (!vv sm prev penv rtv es1 t G tn.
         compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
           (vv, sm) /\
         kc vv sm = (out, sb) /\
         (!H. valid_horizon cx st0 H es1.storage_trace ==>
            intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
              es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
              es1 t G tn) /\
         body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
         (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
         (?H. valid_horizon cx st0 H es1.storage_trace) /\
         gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
           P es1 ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
           Q R) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        (es0, s0, G0, tn0) Q R
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  `call_evaluation_safe cx ((NONE,name)::int_calls_exprs es)` by
    (qpat_assum `expr_body_pre _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE
         [expr_body_pre_split_def, expr_body_pre_mods_def,
          vyperTypeCallGraphTheory.int_calls_expr_def]) >>
     first_assum ACCEPT_TAC) >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_target_not_mem >>
  strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  qpat_assum `cx_tops cx = tops` (fn code =>
    qpat_assum `body_const_cells_agree [(NONE,tops)] cx tenv es0`
      (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def, code])) >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by fs[] >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all_then strip_assume_tac checked_const_substituted_defaults >>
  qabbrev_tac `compiled_dflts = subst_consts_exprs (module_consts_env tops []) dflts` >>
  `MAP expr_type compiled_dflts = MAP expr_type dflts` by simp[Abbr `compiled_dflts`] >>
  `LENGTH compiled_dflts = LENGTH dflts` by
    simp[Abbr `compiled_dflts`, loweringShapePropsTheory.subst_consts_exprs_length] >>
  `eval_expr cx (Call ann (IntCall (NONE,name)) es dflt) =
   bind (eval_exprs cx es) (\vs.
     bind get_scopes (\prev.
       bind (finally
         (ignore_bind (set_scopes [FEMPTY])
           (eval_exprs (cx with stk updated_by CONS (NONE,name))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)))
         (set_scopes prev)) (\dvs.
       bind (lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (NONE,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv))))))))))` by
    simp[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
         ignore_bind_def, bind_apply, return_def, FUN_EQ_THM] >>
  `storage_trace_frame
     (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  qpat_x_assum `eval_expr _ _ = _` SUBST_ALL_TAC >>
  qpat_x_assum `storage_trace_frame _`
    (assume_tac o PURE_REWRITE_RULE [bind_assoc]) >>
  pure_rewrite_tac[bind_assoc] >>
  qpat_x_assum `gas_admissible _ P es0`
    (assume_tac o PURE_REWRITE_RULE [bind_assoc]) >>
  `body_exprs_full_ok cx es` by
    (qpat_x_assum `~MEM _ _ ==> body_exprs_full_ok _ _` mp_tac >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  Cases_on `compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa` >>
  rename1 `compile_expr _ _ _ sa = (vv,sm)` >>
  `kc vv sm = (out,sb)` by
    (qpat_x_assum `comp_bind _ _ sa = _` mp_tac >> simp[comp_bind_def]) >>
  qpat_assum `compile_expr _ _ _ sa = (vv,sm)`
    (assume_tac o REWRITE_RULE [exprSimSendTheory.compile_expr_call]) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa` >>
  rename1 `compile_expr _ _ _ shadow_sa = (shadow_vv,shadow_sm)` >>
  qpat_assum `compile_expr _ _ _ shadow_sa = (shadow_vv,shadow_sm)`
    (assume_tac o REWRITE_RULE
      [gas_shadow_expr_def, exprSimSendTheory.compile_expr_call]) >>
  drule_all_then strip_assume_tac intcall_args_omitted_defaults >>
  qpat_assum `Abbrev (compiled_dflts = _)`
    (fn th => qpat_x_assum `omitted_defaults _ _ _ = DROP _ _`
      (assume_tac o PURE_REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  namedCases_on `cenv.ce_func_info (nsid_to_string (NONE,name))`
    ["rc rbs pvs"] >>
  qpat_assum `compile_call _ _ _ _ _ es _ sa = _`
    (mp_then Any mp_tac intCallStepTheory.compile_call_intcall_shape) >>
  simp[SimpLHS] >> strip_tac >>
  qpat_assum `compile_call _ _ _ _ _ (MAP gas_shadow_expr es) _ shadow_sa = _`
    (mp_then Any mp_tac intCallStepTheory.compile_call_intcall_shape) >>
  simp[SimpLHS, gasShadowCompileHelpersTheory.gas_shadow_env_omitted_defaults,
       gasShadowCompileHelpersTheory.gas_shadow_env_without_defaults] >>
  strip_tac >>
  rename1 `compile_stage_intcall_args _ _ es _ _ st2 = (sup_ops,st2a)` >>
  rename1 `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) _ _ sh_st2 =
    (sh_sup_ops,sh_st2a)` >>
  `gas_shadow_state st2 sh_st2` by
    (reverse (Cases_on `0 < rc' \/ 0 < rbs`) >-
       (`rc' = 0 /\ rbs = 0` by decide_tac >> fs[]) >>
     `?n rb sh_rb. compile_alloc_buffer n sa = (rb,st2) /\
        compile_alloc_buffer n shadow_sa = (sh_rb,sh_st2)` by
       (Cases_on `0 < rc'` >- (gs[] >> qexists_tac `32 * rc'` >> simp[]) >>
        `rc' = 0 /\ 0 < rbs` by decide_tac >> gs[] >> qexists_tac `rbs` >> simp[]) >>
     pop_assum strip_assume_tac >>
     `gas_shadow_compiles (compile_alloc_buffer n) (compile_alloc_buffer n)` by
       simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer] >>
     drule_all (cj 2 bodyFullSharedTheory.gas_shadow_step) >> simp[]) >>
  `!ce xs flags tys sh.
     gas_shadow_compiles (compile_stage_intcall_args compile_expr ce xs flags tys)
       (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
         (if sh then MAP gas_shadow_expr xs else xs) flags tys)` by
    (rpt gen_tac >> irule gasShadowCompileCallSupportTheory.gas_shadow_compiles_stage_intcall_args_env >>
     simp[cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env]) >>
  `sh_sup_ops = sup_ops /\ gas_shadow_state st2a sh_st2a` by
    (qpat_assum `compile_stage_intcall_args _ _ es _ _ st2 = _` mp_tac >>
     qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) _ _ sh_st2 = _` mp_tac >>
     qpat_assum `gas_shadow_state st2 sh_st2` mp_tac >>
     qpat_assum `!ce xs flags tys sh. gas_shadow_compiles _ _`
       (qspecl_then [`cenv`, `es`, `pvs`,
         `TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))`, `T`]
          mp_tac) >>
     SIMP_TAC std_ss [] >> metis_tac[bodyFullSharedTheory.gas_shadow_step]) >>
  rename1 `compile_stage_intcall_args _ _ _ _ _ st2a = (def_ops,st3)` >>
  rename1 `compile_stage_intcall_args _ _ _ _ _ sh_st2a = (sh_def_ops,sh_st3)` >>
  qmatch_asmsub_abbrev_tac `compile_stage_intcall_args compile_expr
    (cenv_without_defaults cenv (nsid_to_string (NONE,name))) ds _ _ st2a` >>
  `ds = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) compiled_dflts` by
    simp[Abbr `ds`] >>
  `sh_def_ops = def_ops /\ gas_shadow_state st3 sh_st3` by
    (qpat_assum `compile_stage_intcall_args _ _ ds _ _ st2a = _` mp_tac >>
     qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr _) _ _ sh_st2a = _` mp_tac >>
     qpat_assum `gas_shadow_state st2a sh_st2a` mp_tac >>
     qpat_assum `!ce xs flags tys sh. gas_shadow_compiles _ _`
       (qspecl_then [`cenv_without_defaults cenv (nsid_to_string (NONE,name))`,
         `ds`, `DROP (LENGTH es) pvs`,
         `DROP (LENGTH es) (TAKE (LENGTH args)
           (cenv.ce_func_param_types (nsid_to_string (NONE,name))))`, `T`] mp_tac) >>
     SIMP_TAC std_ss [] >>
     metis_tac[bodyFullSharedTheory.gas_shadow_step]) >>
  `!ce xs flags tys a ops b.
      compile_stage_intcall_args compile_expr ce xs flags tys a = (ops,b) ==>
      cs_extends a b` by
    (rpt strip_tac >>
     qspecl_then [`compile_expr`, `ce`, `xs`, `flags`, `tys`, `a`]
       mp_tac externalEntryShapeTheory.compile_stage_intcall_args_labels >>
     simp[externalEntryShapeTheory.compile_expr_labels]) >>
  `cs_extends sa st2 /\ cs_extends shadow_sa sh_st2` by
    (reverse (Cases_on `0 < rc' \/ 0 < rbs`) >-
       (`rc' = 0 /\ rbs = 0` by decide_tac >> fs[cs_extends_refl]) >>
     Cases_on `0 < rc'` >-
       (fs[] >> metis_tac[loweringHaltTheory.compile_alloc_buffer_extends]) >>
     `rc' = 0 /\ 0 < rbs` by decide_tac >>
     fs[] >> metis_tac[loweringHaltTheory.compile_alloc_buffer_extends]) >>
  `cs_extends st2 st2a /\ cs_extends st2a st3 /\
   cs_extends sh_st2 sh_st2a /\ cs_extends sh_st2a sh_st3` by
    (rpt conj_tac >> first_x_assum irule >> goal_assum (drule_at Any)) >>
  `!a b. (?ops u. emit_void INVOKE ops a = (u,b)) \/
          (?ops n rb results mid u.
             emit_multi_op INVOKE ops n a = (results,mid) /\
             store_multi_results rb results 0 mid = (u,b)) ==>
          cs_extends a b` by
    (rpt strip_tac
     >- (mp_tac (Q.SPECL [`INVOKE`, `ops`, `a`, `K T`]
                    externalEntryShapeTheory.emit_void_labels) >> simp[]) >>
     irule cs_extends_trans >> qexists_tac `mid` >> conj_tac
     >- (mp_tac (Q.SPECL [`INVOKE`, `ops`, `n`, `a`, `K T`]
                    externalEntryShapeTheory.emit_multi_op_labels) >> simp[]) >>
     mp_tac (Q.SPECL [`rb`, `results`, `0`, `mid`, `K T`]
                 externalEntryShapeTheory.store_multi_results_labels) >> simp[]) >>
  `cs_extends st3 sm /\ cs_extends sh_st3 shadow_sm` by
    (conj_tac >> first_x_assum irule >>
     qmatch_goalsub_rename_tac `emit_void INVOKE _ invoke_start = (_,invoke_end)` >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`0 < rc' ==> ?rb results mid u. _ /\
           emit_multi_op INVOKE _ rc' invoke_start = (results,mid) /\
           store_multi_results _ results 0 mid = (u,invoke_end) /\ _`,
        `rc' = 0 /\ 0 < rbs ==> ?rb u. _ /\
           emit_void INVOKE _ invoke_start = (u,invoke_end) /\ _`,
        `rc' = 0 /\ rbs = 0 ==> ?u. _ /\
           emit_void INVOKE _ invoke_start = (u,invoke_end) /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `rc'` >> Cases_on `rbs` >> simp[] >> metis_tac[]) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac
     >- metis_tac[compileAppendPropsTheory.cs_appends_result_extends] >>
     `kc shadow_vv shadow_sm = (out,shadow_sb)` by
       (qpat_assum `comp_bind _ _ shadow_sa = _` mp_tac >>
        pure_rewrite_tac[comp_bind_def] >> simp[]) >>
     metis_tac[compileAppendPropsTheory.cs_appends_result_extends]) >>
  `!a b c e g z fn.
      cs_extends a b /\ cs_extends b c /\ cs_extends c e /\
      cs_extends e g /\ cs_extends g z /\ fn_has_code a z fn ==>
      fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c e fn /\
      fn_has_code e g fn` by
    (rpt strip_tac >> metis_tac[cs_extends_trans, fn_has_code_mid,
                                cs_extends_refl]) >>
  `fn_has_code sa st2 func /\ fn_has_code st2 st2a func /\
   fn_has_code st2a st3 func /\ fn_has_code st3 sm func` by
    (qpat_assum `!a b c e g z fn. _ ==> fn_has_code a b fn /\ _`
       (qspecl_then [`sa`, `st2`, `st2a`, `st3`, `sm`, `sb`, `func`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `fn_has_code shadow_sa sh_st2 shadow_func /\
   fn_has_code sh_st2 sh_st2a shadow_func /\
   fn_has_code sh_st2a sh_st3 shadow_func /\
   fn_has_code sh_st3 shadow_sm shadow_func` by
    (qpat_assum `!a b c e g z fn. _ ==> fn_has_code a b fn /\ _`
       (qspecl_then [`shadow_sa`, `sh_st2`, `sh_st2a`, `sh_st3`, `shadow_sm`,
                    `shadow_sb`, `shadow_func`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args` by
    simp[nsid_to_string_def, TAKE_DROP] >>
  `!sft ts. ALL_DISTINCT (supported_function_names ts) /\
        MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) ts ==>
        build_func_info sft ts name =
          compute_func_info (\n. MAP (FST o SND) (sft n)) ret
            (type_mem_bytes sft ret) (MAP SND args)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> gen_tac >>
     Induct >> simp[compileVyperTheory.build_func_info_def,
                    supportedNamesTheory.supported_function_names_def] >>
     Cases_on `h` >>
     simp[compileVyperTheory.build_func_info_def,
          supportedNamesTheory.supported_function_names_def,
          loweringShapePropsTheory.MEM_supported_function_names] >>
     rpt strip_tac >> gvs[] >>
     `name <> s` by metis_tac[] >> Cases_on `f = External` >> simp[]) >>
  drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
  drule_then strip_assume_tac intcall_args_body_inv_function_tables >>
  `ALL_DISTINCT (supported_function_names tops)` by
    fs[supportedProgramTheory.supported_program_def,
       supportedNamesTheory.supported_declaration_names_def] >>
  `cenv.ce_func_info (nsid_to_string (NONE,name)) =
    compute_func_info
      (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n))
      ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret)
      (MAP SND args)` by
    (qpat_assum `cenv.ce_func_info = build_func_info _ _` SUBST1_TAC >>
     simp[nsid_to_string_def, NoAsms] >>
     qpat_assum `!sft ts. _ ==> build_func_info sft ts name = _` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `pvs = compute_pass_via_stack (MAP SND args) rc'` by
    (qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _` mp_tac >>
     qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` SUBST1_TAC >>
     simp[NoAsms, compute_func_info_def] >> metis_tac[]) >>
  `LENGTH pvs = LENGTH args` by simp[LENGTH_compute_pass_via_stack] >>
  `!ce xs a. LENGTH xs = LENGTH es ==>
      compile_stage_intcall_args compile_expr ce xs
        (TAKE (LENGTH es) pvs) (TAKE (LENGTH es) (MAP SND args)) a =
      compile_stage_intcall_args compile_expr ce xs pvs
        (TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))) a` by
    (rpt gen_tac >> disch_then (assume_tac o SYM) >>
     qpat_assum `cenv.ce_func_param_types _ = MAP SND args` SUBST1_TAC >>
     `TAKE (LENGTH args) (MAP SND args) = MAP SND args` by simp[] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `LENGTH es = LENGTH xs` SUBST1_TAC >>
     irule (GSYM intcall_args_stage_take) >> simp[]) >>
  `compile_stage_intcall_args compile_expr cenv es
      (TAKE (LENGTH es) pvs) (TAKE (LENGTH es) (MAP SND args)) st2 =
      (sup_ops,st2a)` by simp[] >>
  `compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      (TAKE (LENGTH es) pvs) (TAKE (LENGTH es) (MAP SND args)) sh_st2 =
      (sup_ops,sh_st2a)` by simp[] >>
  `expr_sim_inv cenv cx tenv es0` by
    (qpat_assum `expr_body_pre _ _ _ _ _`
       (ACCEPT_TAC o CONJUNCT1 o
        MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts)) >>
  `env_consistent tenv cx es0` by
    (qpat_assum `expr_sim_inv cenv cx tenv es0`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [expr_sim_inv_def])) >>
  `tenv.type_defs = get_tenv cx` by
    (irule vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
     goal_assum (drule_at Any)) >>
  `LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es)
       (TAKE (LENGTH es) (MAP SND args)) /\
   EVERY (supported_default_expression tops) dflts` by
    (drule_all bodyIntCallSourceTheory.body_intcall_source_selection >>
     qpat_assum `lookup_callable_function _ name tops = SOME _` (fn lookup =>
       qpat_assum `tenv.type_defs = get_tenv cx`
         (fn defs => simp[NoAsms, lookup, defs]))) >>
  `EVERY (\t. type_memory_bytes cenv t < 2 ** 64) (MAP SND args)` by
    (irule (cj 1 intcall_args_allocation_bounds) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `!ts n i. i < LENGTH ts /\ EL i (compute_pass_via_stack ts n) ==>
      is_word_type (EL i ts)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[] >>
     rpt gen_tac >> Cases_on `i` >>
     simp[compute_pass_via_stack_def] >> rw[] >> metis_tac[]) >>
  `!i. i < LENGTH args /\ EL i pvs ==> is_word_type (EL i (MAP SND args))` by
    (rpt gen_tac >>
     qpat_assum `pvs = compute_pass_via_stack _ _` SUBST1_TAC >>
     qpat_assum `!ts n j. _ ==> is_word_type (EL j ts)`
       (qspecl_then [`MAP SND args`,`rc'`,`i`] mp_tac) >>
     simp[NoAsms]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ action _ _ _` >>
  `storage_trace_frame action` by
    (qunabbrev_tac `action` >>
     `LENGTH dflts - (LENGTH args - LENGTH es) =
        LENGTH dflts + LENGTH es - LENGTH args` by decide_tac >>
     qpat_x_assum `storage_trace_frame _` mp_tac >>
     simp[lock_if_nr_def, unlock_if_nr_def, is_view_mut_def, DE_MORGAN_THM]) >>
  (reverse (Cases_on `storage_trace_domain cx st0 es0.storage_trace`)
   >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_bad_nil >>
       (reverse conj_tac >- first_assum ACCEPT_TAC) >>
       qx_gen_tac `tail` >> Cases_on `action (es0 with gas_obs := tail)` >>
       drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >>
       strip_tac >> simp[] >> strip_tac >>
       drule vyperStorageFootprintTheory.storage_trace_domain_prefix >> simp[])) >>
  `valid_horizon cx st0 (storage_trace_horizon es0.storage_trace)
      es0.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 es0.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H es0.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es0.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `type_memory_bytes cenv ret < 2 ** 64` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops`
         (ACCEPT_TAC o CONJUNCT2 o MATCH_MP intcall_args_allocation_bounds o CONJ inv))) >>
  `rc' <= 2 /\ rbs < 2 ** 64` by
    (qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _` mp_tac >>
     qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` SUBST1_TAC >>
     qpat_assum `type_memory_bytes cenv ret < 2 ** 64` mp_tac >>
     drule_then assume_tac intcall_args_body_inv_struct_fields >>
     qpat_assum `cenv.ce_struct_fields = _` (SUBST1_TAC o SYM) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[structFieldsPropsTheory.type_mem_bytes_type_memory_bytes,
          compute_func_info_def] >>
     Cases_on `ret` >>
     simp[returns_stack_count_def, tuple_like_stack_count_def,
          MAX_STACK_RETURNS_def] >> rw[] >> decide_tac) >>
  qabbrev_tac `buf_n = if 0 < rc' then 32 * rc' else rbs` >>
  `32 * rc' < dimword (:256)` by
    (qpat_assum `rc' <= 2` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `rbs < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists_tac `2 ** 64` >>
     conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[wordsTheory.dimword_def, NoAsms])) >>
  `buf_n < dimword (:256)` by
    (Cases_on `0 < rc'` >> simp[Abbr `buf_n`]) >>
  `(0 < rc' \/ 0 < rbs) ==> ?rbuf. compile_alloc_buffer buf_n sa = (rbuf,st2)` by
    (disch_tac >> Cases_on `0 < rc'`
     >- (qpat_assum `0 < rc' ==> ?rb rs st4 u.
                       compile_alloc_buffer (32 * rc') sa = (rb,st2) /\ _` mp_tac >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then (qx_choose_then `rb0` strip_assume_tac) >>
         qexists_tac `rb0` >> simp[Abbr `buf_n`]) >>
     `rc' = 0 /\ 0 < rbs` by decide_tac >>
     qpat_assum `rc' = 0 /\ 0 < rbs ==> ?rb u.
                   compile_alloc_buffer rbs sa = (rb,st2) /\ _` mp_tac >>
     impl_tac >- simp[] >>
     disch_then (qx_choose_then `rb0` strip_assume_tac) >>
     qexists_tac `rb0` >> simp[Abbr `buf_n`]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx es0 G0 tn0 s0` mp_tac >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def, NoAsms]) >>
  `0 < rc' \/ 0 < rbs ==>
   ?rb q w entry Ga tna.
     compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
                       (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
     not_fresh_at st2 q /\ lookup_var q entry = SOME w /\
     ptr_covers Ga tna q entry buf_n /\
     FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,buf_n) /\
     FLOOKUP Ga q = SOME (w2n w,buf_n) /\
     w2n w + buf_n <= entry.vs_alloca_next /\
     (!n b sz. local_region cenv es0.scopes entry n b sz ==>
         regions_disjoint (w2n w) buf_n b sz) /\
     alloca_history func entry /\ ~entry.vs_halted /\
     entry.vs_current_bb = st2.cs_current_bb /\
     entry.vs_inst_idx = LENGTH st2.cs_current_insts /\
     s0.vs_alloca_next <= entry.vs_alloca_next /\
     lo <= w2n w /\ sa.cs_next_id < st2.cs_next_id /\
     sa.cs_next_var <= st2.cs_next_var /\ rb.buf_size = buf_n /\
     wb_frame cenv es0 es0 sa s0 entry /\
     ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga tna /\
     return_buf_frame d cenv st2 entry /\
     (!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 entry /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 Ga tna entry)` by
    (disch_tac >>
     qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb. _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `rb` assume_tac) >>
     drule_all (INST_TYPE [``:'b`` |-> ``:256``]
       bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
     disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
       (qx_choose_then `rq` (qx_choose_then `rw` (qx_choose_then `entry`
         (qx_choose_then `Ga` (qx_choose_then `tna` strip_assume_tac)))))) >>
     `~entry.vs_halted` by
       (qpat_assum `entry with <| vs_vars := _; vs_allocas := _;
          vs_alloca_next := _; vs_inst_idx := _ |> = s0`
          (mp_tac o Q.AP_TERM `\s. s.vs_halted`) >> simp[]) >>
     `!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 entry /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 Ga tna entry` by
       ((qx_gen_tac `H` >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ H es0.storage_trace ==> _ /\ _ /\ _`
          (drule_then strip_assume_tac) >>
        conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        irule (INST_TYPE [``:'a`` |-> ``:256``]
          bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
        rpt (first_assum (irule_at Any)) >> simp[] >> (metis_tac[INST_TYPE [``:'a`` |-> ``:256``]
          bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at]))) >>
     drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
     `lo <= w2n rw` by
       (qpat_assum `allocas_from lo entry`
         (qspecl_then [`sa.cs_next_id`,`w2n rw`,`buf_n`] mp_tac o
          REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
        disch_then irule >> first_assum ACCEPT_TAC) >>
     `sa.cs_next_id < st2.cs_next_id /\ sa.cs_next_var <= st2.cs_next_var` by simp[] >>
     `entry.vs_memory = s0.vs_memory` by
       (qpat_assum `entry with <| vs_vars := _; vs_allocas := _;
           vs_alloca_next := _; vs_inst_idx := _ |> = s0`
         (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >> simp[]) >>
     `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x entry = SOME w` by
       (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (drule_then strip_assume_tac) >> simp[]) >>
     `wb_frame cenv es0 es0 sa s0 entry` by
       (simp[loweringPostsTheory.wb_frame_def, exprSimPropsTheory.locals_kept_mem] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `return_buf_frame d cenv st2 entry` by
       (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
        rpt (first_assum (irule_at Any)) >> simp[]) >>
     `ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga tna` by
       (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es0 s0`
          (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
        `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id
           ==> off + sz <= s0.vs_alloca_next` by
          (rpt strip_tac >>
           qpat_assum `alloca_inv s0`
             (irule o REWRITE_RULE [venomMemDefsTheory.alloca_next_valid_def] o
              CONJUNCT2 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
           goal_assum (drule_at Any)) >>
        `!n b sz. local_region cenv es0.scopes s0 n b sz ==> b + sz <= s0.vs_alloca_next` by
          (rpt strip_tac >> drule_all exprSimConvertFromBytesTheory.dynamic_local_region_bound >> simp[]) >>
        `!x. not_fresh_at sa x ==>
            FLOOKUP Ga x = FLOOKUP G0 x /\ op_taint tna (Var x) = op_taint tn0 (Var x)` by
          (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
             (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
        qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Ga x = _ /\ _` mp_tac >>
        qpat_assum `!i. i IN tna.t_mem <=> _` mp_tac >>
        qpat_assum `lo <= s0.vs_alloca_next` mp_tac >>
        qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
        qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> ntac 5 disch_tac >>
        `ghost_kept_at lo cenv es0 sa G0 tn0 s0 G0 tn0` by
          MATCH_ACCEPT_TAC wordArgsPtrTheory.ghost_kept_at_refl >>
        drule_all_then ACCEPT_TAC bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at) >>
     qexistsl_tac [`rb`,`rq`,`rw`,`entry`,`Ga`,`tna`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* One initial cut for both return modes, with the allocation pinned only
     in the allocating mode. *)
  `?entry Ga tna pin.
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
     (0 < rc' \/ 0 < rbs ==>
        ?rb q (w:bytes32). compile_alloc_buffer buf_n sa = (rb,st2) /\
          rb.buf_operand = Var q /\ rb.buf_size = buf_n /\
          pin = SOME (q,w2n w,buf_n)) /\
     (rc' = 0 /\ rbs = 0 ==> pin = NONE) /\
     (case pin of NONE => T | SOME (q,b,k) =>
        FLOOKUP Ga q = SOME (b,k) /\ op_taint tna (Var q) = {} /\
        lookup_var q entry = SOME (n2w b) /\
        FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (b,k) /\
        sa.cs_next_id < st2.cs_next_id /\ lo <= b /\ b+k <= entry.vs_alloca_next /\
        not_fresh_at st2 q /\
        (!n lb sz. local_region cenv es0.scopes entry n lb sz ==>
           b+k <= lb \/ lb+sz <= b)) /\
     wb_frame cenv es0 es0 sa s0 entry /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga tna /\
     alloca_history func entry /\ sa.cs_next_id <= st2.cs_next_id /\
     sa.cs_next_var <= st2.cs_next_var /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
     (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
        local_region cenv es0.scopes entry n b sz) /\
     return_buf_frame d cenv st2 entry /\ ~entry.vs_halted /\
     entry.vs_current_bb = st2.cs_current_bb /\
     entry.vs_inst_idx = LENGTH st2.cs_current_insts /\
     (!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 entry /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 Ga tna entry)` by
    (reverse (Cases_on `0 < rc' \/ 0 < rbs`)
     >- (`rc' = 0 /\ rbs = 0` by decide_tac >>
         qpat_assum `rc' = 0 /\ rbs = 0 ==> ?u. st2 = sa /\ _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >>
         qexistsl_tac [`s0`,`G0`,`tn0`,`NONE`] >>
         simp[exprSimWordArgsTheory.wb_frame_refl, wordArgsPtrTheory.ghost_kept_at_refl,
              cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q w entry Ga tna. _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `rb` (qx_choose_then `q` (qx_choose_then `w`
       (qx_choose_then `entry` (qx_choose_then `Ga` (qx_choose_then `tna` strip_assume_tac)))))) >>
     `op_taint tna (Var q) = {}` by
       (qpat_assum `ptr_covers Ga tna q entry buf_n`
         (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_covers_def])) >>
     `!n b sz. local_region cenv es0.scopes s0 n b sz <=>
           local_region cenv es0.scopes entry n b sz` by
       (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es0 s0` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
        qpat_assum `wb_frame cenv es0 es0 sa s0 entry` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
        `MAP FDOM es0.scopes = MAP FDOM es0.scopes` by REFL_TAC >>
        drule_all_then ACCEPT_TAC wordArgsPtrTheory.wb_frame_local_regions) >>
     qexistsl_tac [`entry`,`Ga`,`tna`,`SOME (q,w2n w,buf_n)`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (disch_tac >> qexistsl_tac [`rb`,`q`,`w`] >> simp[]) >>
     simp[wordsTheory.n2w_w2n] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!n b sz. local_region cenv es0.scopes entry n b sz ==> regions_disjoint _ _ _ _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `local_ptrs_reserved cenv st2` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at st2 x` by
    ((rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> pure_asm_rewrite_tac[] >> (simp[freshWritesTheory.not_fresh_at_mono]))) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> pure_asm_rewrite_tac[] >>
     simp[freshWritesTheory.not_fresh_at_mono]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
           (CONJ inv member))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (qpat_assum `!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 entry /\ _`
       (qspec_then `storage_trace_horizon es0.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)) >>
  `!fn inst u. frag_reachable ctx func entry fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `(ARB : dead)` (fn path =>
          qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
            qpat_assum `!fn i u. frag_reachable ctx func s0 fn i u ==> _`
              (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
               CONJ path o CONJ no_phi))))) >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qunabbrev_tac `action` >>
  qmatch_goalsub_abbrev_tac `bind (eval_exprs cx es) supplied_tail` >>
  `EVERY (\e. expr_body_pre cenv cx tenv e es0) es` by
    (qpat_assum `expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0`
       mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (strip_assume_tac o
       SIMP_RULE (srw_ss())
         [Once vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeCallGraphTheory.int_calls_expr_def,
          Once byte_widths_expr_def, Once allocLimitsTheory.alloc_limits_expr_def,
          Once supportedExprTraverseTheory.expr_has_evm_run_thm,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedExprTraverseTheory.supported_exprs_exists_every] o
       REWRITE_RULE [expr_body_pre_split_def, expr_body_pre_mods_def]) >>
     simp[listTheory.EVERY_MEM, expr_body_pre_split_def, expr_body_pre_mods_def] >>
     qx_gen_tac `e` >> disch_tac >>
     `call_evaluation_safe cx (int_calls_exprs es)` by
       (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
        qexists_tac `(NONE,name)::int_calls_exprs es` >> simp[]) >>
     imp_res_tac exprSimSourceTheory.int_calls_exprs_every_mem >>
     gvs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_THM] >>
     metis_tac[exprSimSourceTheory.well_typed_exprs_member,
               exprSimSourceTheory.byte_widths_exprs_mem,
               exprSimSourceTheory.alloc_limits_exprs_mem,
               exprSimSourceTheory.call_evaluation_safe_exprs_mem]) >>
  qpat_assum `cx_tops cx = tops` (once_rewrite_tac o single o SYM) >>
  irule (REWRITE_RULE[]
    (Q.INST [`clean_words` |-> `T`, `keep_sites` |-> `T`]
      intcall_args_stage_full_p2_with_path)) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx tenv es0` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ es (TAKE _ _) (TAKE _ _) st2 = _`
    (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) (TAKE _ _) (TAKE _ _) sh_st2 = _`
    (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga tna` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv st2 entry` (irule_at Any) >>
  qpat_assum `(case pin of NONE => T | SOME _ => _)` (irule_at Any) >>
  qexistsl_tac [`[]`,`[]`,`[]`,`[]`,`[]`,`P`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[venomStateTheory.eval_operands_def, listTheory.LENGTH_TAKE,
            rich_listTheory.EL_TAKE, rich_listTheory.EVERY_TAKE] >> NO_TAC)
  >- (qunabbrev_tac `supplied_tail` >>
      simp_tac bool_ss [bind_assoc] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp_tac bool_ss [storage_trace_frame_state_reads] >> gen_tac >>
      irule storage_trace_frame_bind_all >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule (SIMP_RULE (srw_ss()) [bind_assoc, lock_if_nr_def,
                   unlock_if_nr_def, is_view_mut_def, DE_MORGAN_THM]
            intcall_after_defaults_storage_trace_frame) >> first_assum ACCEPT_TAC) >>
      irule storage_trace_frame_finally >>
      simp_tac bool_ss [storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >>
      simp_tac bool_ss [storage_trace_frame_state_updates, evaluate_storage_trace_frame])
  >- (rpt strip_tac >> irule intcall_args_aggregate_physical_type_mods >>
      qpat_assum `body_inv tops ctx cenv cx`
        (mp_then Any (drule_then (irule_at Any))
          exprBodyPrePropsTheory.body_inv_expr_body_pre_mods) >>
      qpat_assum `compile_expr cenv (expr_type e) e ci = (_,cm)` (irule_at Any) >>
      qexists_tac `dty` >> simp[])
  >> TRY (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> is_word_type _` mp_tac >>
      qpat_assum `LENGTH es <= LENGTH args` mp_tac >>
      qpat_assum `LENGTH pvs = LENGTH args` mp_tac >>
      qpat_assum `EL _ (TAKE (LENGTH es) pvs)` mp_tac >>
      qpat_assum `_ < LENGTH es` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[rich_listTheory.EL_TAKE] >> NO_TAC)
  >> TRY (qunabbrev_tac `supplied_tail` >>
      `LENGTH dflts - (LENGTH args - LENGTH es) =
         LENGTH dflts + LENGTH es - LENGTH args` by decide_tac >>
      qpat_x_assum `gas_admissible (bind (eval_exprs cx es) _) P es0` mp_tac >>
      simp[lock_if_nr_def, unlock_if_nr_def, is_view_mut_def, DE_MORGAN_THM] >> NO_TAC) >>
  map_every qx_gen_tac [`marks`,`xs`,`ee`,`t`,`G1`,`tn1`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)) >>
  `!i. active_inst func i t ==> frag_reachable ctx func entry func i t` by
    (qpat_assum `gas_path ctx func entry (LENGTH marks) (OK t)`
       (mp_tac o MATCH_MP bodyFullIfExpReachTheory.gas_path_reach) >>
     disch_then (qspecl_then [`func`,`entry`,`t`] mp_tac) >>
     simp[contextRawReachableTheory.frag_reachable_start]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (rpt strip_tac >>
     qpat_assum `!fn i u. frag_reachable ctx func entry fn i u ==> _`
       (MATCH_MP_TAC o Q.SPECL [`fn`,`inst`,`u`]) >>
     qpat_assum `frag_reachable ctx func t fn inst u`
       (mp_tac o MATCH_MP contextRawReachableTheory.frag_reachable_trans) >>
     disch_then (qspecl_then [`func`,`entry`] mp_tac) >> simp[]) >>
  qpat_assum `!tail. eval_exprs cx es _ = _`
    (qspec_then `[]` assume_tac) >>
  `body_exprs_full_ok (cx with stk updated_by CONS (NONE,name)) ds` by
    (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     qpat_assum `!s1 vs t1. _ ==> body_exprs_full_ok _ _` irule >>
     qpat_assum `eval_exprs cx es _ = (INL xs,_)` (irule_at Any) >>
     simp[Abbr `compiled_dflts`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func (cenv_without_defaults cenv name) cx ee t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     irule exprLoweringPropsTheory.stmt_state_rel_cenv_cong >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee t` (irule_at Any) >>
     simp[cenv_without_defaults_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func (cenv_without_defaults cenv name)
       (cx with stk updated_by CONS (NONE,name)) ee t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func (cenv_without_defaults cenv name) cx ee t`
       (drule_then mp_tac) >>
     simp[intcall_args_stmt_state_rel_push]) >>
  `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` by
    (qpat_assum `expr_body_pre cenv cx tenv (Call _ _ _ _) es0`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
        MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts)) >>
  `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` by
    (qpat_assum `well_typed_expr tenv (Call _ _ _ _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[Once well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `functions_well_typed cx /\ env_consistent tenv cx ee` by
    (qpat_assum `expr_sim_inv cenv cx tenv ee` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_sim_inv_def]) >>
  drule_all vyperTypeEvalProofsTheory.callable_body_typing_from_env_consistent >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
      (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
  `env_context_consistent tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def] >>
  `well_typed_exprs (defaults_env (tenv with current_src := NONE)) compiled_dflts` by
    (simp[Abbr `compiled_dflts`] >>
     drule_all_then ACCEPT_TAC checked_const_substituted_defaults_typed) >>
  `well_typed_exprs (defaults_env (tenv with current_src := NONE)) ds` by
    (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     metis_tac[vyperTypeEvalProofsTheory.well_typed_exprs_DROP]) >>
  `supported_function_body tops Internal args ss /\ supported_pure_exprs tops dflts` by
    (drule_all bodyIntCallSourceTheory.body_intcall_source_selection >>
     simp[] >> metis_tac[]) >>
  `supported_pure_exprs tops compiled_dflts` by
    (qunabbrev_tac `compiled_dflts` >>
     drule_all_then (ACCEPT_TAC o cj 5)
       (SIMP_RULE (srw_ss()) []
         (Q.INST [`vis` |-> `Internal`,
                  `env` |-> `function_entry_env art [(NONE,tops)] NONE Internal args`]
            checked_const_substituted_function))) >>
  `supported_pure_exprs tops ds` by
    (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     pure_rewrite_tac[supportedExprsTheory.supported_pure_exprs_every] >>
     irule rich_listTheory.EVERY_DROP >>
     qpat_assum `supported_pure_exprs tops compiled_dflts`
       (ACCEPT_TAC o REWRITE_RULE [supportedExprsTheory.supported_pure_exprs_every])) >>
  `body_const_cells_agree [(NONE,tops)] cx tenv ee` by
    (`well_typed_exprs tenv es` by
       (rw[constSubstCorrectTheory.frame_well_typed_exprs_every, EVERY_MEM] >>
        qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e es0) es`
          (drule o BETA_RULE o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts)) >>
     qpat_assum `!tail. eval_exprs cx es _ = _`
       (qspec_then `[]` assume_tac) >>
     `body_const_cells_agree [(NONE,tops)] cx tenv (ee with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_exprs >>
     goal_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >> simp[]) >>
  qabbrev_tac `cxd = cx with stk updated_by CONS (NONE,name)` >>
  `body_const_cells_agree [(NONE,tops)] cxd (tenv with current_src := NONE) ee` by
    (simp[Abbr `cxd`] >>
     irule body_const_cells_agree_current_src >>
     `cx with stk updated_by CONS (NONE,name) = cx with stk := (NONE,name)::cx.stk` by
       simp[vyperContextTheory.evaluation_context_component_equality] >>
     pop_assum SUBST1_TAC >>
     irule body_const_cells_agree_stk >> first_assum ACCEPT_TAC) >>
  `!s res fin. eval_exprs cxd ds s = (res,fin) ==> fin.scopes = s.scopes` by
    (rpt strip_tac >>
     `s with scopes := s.scopes = s` by
       simp[NoAsms, evaluation_state_component_equality] >>
     drule_all intcall_args_defaults_scope_action >>
     disch_then (qspecl_then [`cxd`,`s`,`s.scopes`] (mp_tac o
       Q.AP_TERM `\p. (SND p).scopes`)) >>
     qpat_assum `s with scopes := s.scopes = s` (fn update =>
       qpat_assum `eval_exprs cxd ds s = (res,fin)` (fn eval =>
         simp[NoAsms, update, eval]))) >>
  `!src. finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd ds))
            (set_scopes src.scopes) src = eval_exprs cxd ds src` by
    (qx_gen_tac `src` >> Cases_on `eval_exprs cxd ds src` >>
     rename1 `eval_exprs cxd ds src = (res,fin)` >>
     `fin.scopes = src.scopes` by
       (qpat_assum `!s res fin. eval_exprs cxd ds s = (res,fin) ==> _`
          (fn th => drule_all th >> simp[])) >>
     `eval_exprs cxd ds (src with scopes := [FEMPTY]) =
        (res,fin with scopes := [FEMPTY])` by
       (drule_all intcall_args_defaults_scope_action >>
        disch_then (qspecl_then [`cxd`,`src`,`[FEMPTY]`] mp_tac) >>
        qpat_assum `eval_exprs cxd ds src = (res,fin)` (fn th =>
          POP_ASSUM_LIST (K ALL_TAC) >> simp[th])) >>
     Cases_on `res` >>
     qpat_assum `eval_exprs cxd ds src = _` mp_tac >>
     qpat_assum `eval_exprs cxd ds (src with scopes := [FEMPTY]) = _` mp_tac >>
     qpat_assum `fin.scopes = src.scopes` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ignore_bind_apply, set_scopes_def, finally_def, return_def, raise_def,
          evaluation_state_component_equality]) >>
  qabbrev_tac `after_defaults = \prev dvs.
    bind
      (bind (lift_option_type (bind_arguments (get_tenv cx) args (xs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (NONE,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv)))))))) f` >>
  qabbrev_tac `raw_ds = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts` >>
  `!gs scs. eval_exprs cxd ds (ee with <|gas_obs := gs; scopes := scs|>) =
            eval_exprs cxd raw_ds (ee with <|gas_obs := gs; scopes := scs|>)` by
    (rpt gen_tac >>
     qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     simp_tac bool_ss [Abbr `cxd`, Abbr `raw_ds`, Abbr `compiled_dflts`] >>
     `body_const_cells_agree [(NONE,tops)] cx tenv (ee with scopes := scs)` by
       asm_simp_tac bool_ss [body_const_cells_agree_state_updates] >>

     irule intcall_args_defaults_source_cong >>
     qpat_assum `body_const_cells_agree _ cx tenv (ee with scopes := scs)` (irule_at Any) >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` (irule_at Any) >>
     qpat_assum `lookup_callable_function _ _ _ = SOME _` (irule_at Any) >>
     simp[]) >>
  `supplied_tail xs = bind get_scopes (\prev.
     bind (finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd raw_ds))
                   (set_scopes prev)) (after_defaults prev))` by
    (`LENGTH dflts - (LENGTH args - LENGTH es) =
        LENGTH dflts + LENGTH es - LENGTH args` by decide_tac >>
     pop_assum mp_tac >>
     qpat_assum `Abbrev (supplied_tail = _)` mp_tac >>
     qpat_assum `Abbrev (after_defaults = _)` mp_tac >>
     qpat_assum `Abbrev (raw_ds = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[markerTheory.Abbrev_def] >> rpt disch_tac >>
     simp[vyperStateTheory.bind_assoc, lock_if_nr_def, unlock_if_nr_def,
          is_view_mut_def, DE_MORGAN_THM]) >>
  qabbrev_tac `normalized_tail = bind get_scopes (\prev.
     bind (finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd ds))
                   (set_scopes prev)) (after_defaults prev))` >>
  `!gs. supplied_tail xs (ee with gas_obs := gs) =
        normalized_tail (ee with gas_obs := gs)` by
    (qx_gen_tac `gs` >>
     qpat_assum `supplied_tail xs = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [Abbr `normalized_tail`] >>
     `(ee with gas_obs := gs) with scopes := [FEMPTY] =
        (ee with scopes := [FEMPTY]) with gas_obs := gs` by
       simp[NoAsms, evaluation_state_component_equality] >>
     simp[NoAsms, vyperStateTheory.bind_def, finally_def, ignore_bind_apply,
          get_scopes_def, set_scopes_def, return_def] >>
     pop_assum (fn upd => pure_rewrite_tac[upd]) >>
     qpat_assum `!gs scs. eval_exprs cxd ds _ = _`
       (qspecl_then [`gs`, `[FEMPTY]`] (fn th => pure_rewrite_tac[th])) >>
     REFL_TAC) >>
  `gas_admissible normalized_tail P ee` by
    (pure_rewrite_tac[gas_admissible_def] >> rpt gen_tac >>
     qpat_assum `!gs. supplied_tail xs _ = normalized_tail _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `gas_admissible (supplied_tail xs) P ee`
       (ACCEPT_TAC o SPEC_ALL o REWRITE_RULE [gas_admissible_def])) >>
  irule gas_outcome_full_source_cong >> qexists_tac `normalized_tail` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `normalized_tail = bind get_scopes (\prev.
     bind (finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd ds))
                   (set_scopes prev)) (after_defaults prev))` by
    simp[Abbr `normalized_tail`] >>
  `normalized_tail = bind (eval_exprs cxd ds)
       (\dvs src. after_defaults src.scopes dvs src)` by
    (qpat_assum `normalized_tail = bind get_scopes _` SUBST1_TAC >>
     qpat_assum `!src. finally _ _ src = eval_exprs cxd ds src` mp_tac >>
     qpat_assum `!s res fin. eval_exprs cxd ds s = (res,fin) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
     simp[FUN_EQ_THM, bind_apply, get_scopes_def, return_def] >>
     qx_gen_tac `src` >>
     Cases_on `eval_exprs cxd ds src` >>
     rename1 `eval_exprs cxd ds src = (res,fin)` >>
     `fin.scopes = src.scopes` by
       (qpat_assum `!s res fin. eval_exprs cxd ds s = (res,fin) ==> _`
          (fn th => drule_all th >> simp[])) >>
     qpat_assum `!src. finally _ _ src = eval_exprs cxd ds src`
       (qspec_then `src` assume_tac) >>
     Cases_on `res` >> simp[vyperStateTheory.bind_def]) >>
  qpat_assum `normalized_tail = bind (eval_exprs cxd ds) _` SUBST_ALL_TAC >>
  `body_inv tops ctx (cenv_without_defaults cenv name) cxd` by
    (qunabbrev_tac `cxd` >> irule intcall_args_defaults_body_inv >>
     first_assum ACCEPT_TAC) >>
  `expr_sim_inv (cenv_without_defaults cenv name) cxd
      (tenv with current_src := NONE) ee` by
    (qunabbrev_tac `cxd` >> irule intcall_args_defaults_inv >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\e. expr_body_pre (cenv_without_defaults cenv name) cxd
      (tenv with current_src := NONE) e ee) ds` by
    (qunabbrev_tac `cxd` >> qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     irule intcall_args_defaults_pre >>
     qpat_assum `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)`
       (irule_at Any) >>
     qpat_assum `lookup_callable_function cx.in_deploy name tops = SOME _` (irule_at Any) >>
     qpat_assum `MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops` (irule_at Any) >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC)
     >- (`const_name_root cx = const_name_root_mods [(NONE,tops)]` by
           (pure_rewrite_tac[GSYM const_name_root_mods_singleton] >>
            qpat_assum `cx_tops cx = tops` SUBST1_TAC >> REFL_TAC) >>
         pop_assum SUBST1_TAC >>
         irule bodyStorageCasesTheory.supported_exprs_exists_DROP >>
         first_assum ACCEPT_TAC)
     >- (pure_once_rewrite_tac[vyperTypeCallGraphTheory.int_calls_expr_def] >>
         first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `compiled_dflts`]) >>
  `TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name))) =
      MAP SND args` by
    (qpat_assum `cenv.ce_func_param_types _ = MAP SND args` SUBST1_TAC >>
     simp[NoAsms]) >>
  `compile_stage_intcall_args compile_expr (cenv_without_defaults cenv name)
      ds (DROP (LENGTH es) pvs) (DROP (LENGTH es) (MAP SND args)) st2a =
      (def_ops,st3)` by
    (qpat_assum `TAKE (LENGTH args) _ = MAP SND args` (SUBST1_TAC o SYM) >>
     qpat_assum `compile_stage_intcall_args _ _ ds _ _ st2a = _` mp_tac >>
     simp[NoAsms, nsid_to_string_def]) >>
  `compile_stage_intcall_args compile_expr (gas_shadow_env T (cenv_without_defaults cenv name))
      (MAP gas_shadow_expr ds) (DROP (LENGTH es) pvs)
      (DROP (LENGTH es) (MAP SND args)) sh_st2a = (def_ops,sh_st3)` by
    (qpat_assum `TAKE (LENGTH args) _ = MAP SND args` (SUBST1_TAC o SYM) >>
     qpat_assum `sh_def_ops = def_ops` (SUBST1_TAC o SYM) >>
     qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr _) _ _ sh_st2a = _` mp_tac >>
     simp[NoAsms, nsid_to_string_def]) >>
  `!src H tr. valid_horizon cxd src H tr = valid_horizon cx src H tr` by
    ((qunabbrev_tac `cxd` >> POP_ASSUM_LIST (K ALL_TAC) >>
     `!src b. get_storage (cx with stk updated_by CONS (NONE,name)) src b =
               get_storage cx src b` by
       (rpt gen_tac >> Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     `!src regs. storage_well_formed_on (cx with stk updated_by CONS (NONE,name)) src regs =
                 storage_well_formed_on cx src regs` by
       simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     `!regs tr. storage_trace_backends_well_formed
                    (cx with stk updated_by CONS (NONE,name)) regs tr =
                storage_trace_backends_well_formed cx regs tr` by
       (gen_tac >> Induct >>
        simp[vyperStorageFootprintTheory.storage_trace_backends_well_formed_def] >>
        Cases >> simp[]) >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
          vyperStorageFootprintTheory.storage_observations_ok_def] >> (simp[vyperStorageBackendTheory.get_storage_def, vyperStorageFootprintTheory.storage_well_formed_on_def, vyperStorageFootprintTheory.storage_trace_backends_well_formed_def, vyperStorageFootprintTheory.valid_horizon_def, vyperStorageFootprintTheory.storage_observations_ok_def]))) >>
  `!src tr. storage_trace_domain cxd src tr = storage_trace_domain cx src tr` by
    (qpat_assum `!src H tr. valid_horizon cxd src H tr = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     simp[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `cx_tops cxd = cx_tops cx` by
    (qunabbrev_tac `cxd` >>
     simp[NoAsms, cx_tops_def, vyperTypeEvalProofsTheory.get_module_code_stk_irrelevant]) >>
  `!source src u G tn.
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cxd) cxd st0 source (src,u,G,tn) Q R =
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 source (src,u,G,tn) Q R` by
    (qpat_assum `!src H tr. valid_horizon cxd src H tr = _` mp_tac >>
     qpat_assum `!src tr. storage_trace_domain cxd src tr = _` mp_tac >>
     qpat_assum `cx_tops cxd = cx_tops cx` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
     simp[gas_outcome_full_def, gasStorageTheory.gas_bad_storage_at_def]) >>
  `LENGTH ds = LENGTH args - LENGTH es` by
    (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     qpat_assum `LENGTH args - LENGTH es <= LENGTH dflts` mp_tac >>
     qpat_assum `LENGTH compiled_dflts = LENGTH dflts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `MAP expr_type ds = DROP (LENGTH es) (MAP SND args)` by
    (`LENGTH dflts <= LENGTH args` by
       (qpat_assum `MAP expr_type dflts = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
        simp[NoAsms] >> decide_tac) >>
     `LENGTH dflts - (LENGTH args - LENGTH es) + (LENGTH args - LENGTH dflts) =
        LENGTH es` by
       (qpat_assum `LENGTH es <= LENGTH args` mp_tac >>
        qpat_assum `LENGTH args - LENGTH es <= LENGTH dflts` mp_tac >>
        qpat_assum `LENGTH dflts <= LENGTH args` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     qpat_assum `MAP expr_type compiled_dflts = MAP expr_type dflts`
       (fn th => simp[SimpLHS, NoAsms, listTheory.MAP_DROP, th]) >>
     qpat_assum `MAP expr_type dflts = _` SUBST1_TAC >>
     simp[SimpLHS, NoAsms, listTheory.MAP_DROP, rich_listTheory.DROP_DROP_T] >>
     qpat_assum `_ + (LENGTH args - LENGTH dflts) = LENGTH es`
       (fn th => simp[NoAsms, th])) >>
  `LIST_REL (type_widens_to (get_tenv cxd)) (MAP expr_type ds)
      (DROP (LENGTH es) (MAP SND args))` by
    (qpat_assum `MAP expr_type ds = _` SUBST1_TAC >>
     simp[NoAsms, listTheory.EVERY2_refl, vyperTypeArgFitsTheory.type_widens_to_refl]) >>
  `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=>
                 local_region cenv sc s n b k` by
    simp[NoAsms, loweringStateRelDefsTheory.local_region_def, cenv_without_defaults_def] >>
  `get_tenv cxd = get_tenv cx` by
    (qunabbrev_tac `cxd` >> simp[NoAsms, vyperTypeEvalProofsTheory.get_tenv_stk_irrelevant]) >>
  `ci_mono st2 st2a` by
    (qpat_assum `compile_stage_intcall_args _ _ es (TAKE _ _) (TAKE _ _) st2 = _`
       (fn th =>
         qspecl_then [`compile_expr`,`cenv`,`es`,`TAKE (LENGTH es) pvs`,
                      `TAKE (LENGTH es) (MAP SND args)`,`st2`] mp_tac
           exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args >>
         simp[NoAsms, th, cj 1 exprLoweringPropsTheory.compile_expr_ci_mono])) >>
  `local_ptrs_reserved (cenv_without_defaults cenv name) st2a` by
    (pure_rewrite_tac[exprOperandVarTheory.local_ptrs_reserved_without_defaults] >>
     irule exprOperandVarTheory.compiler_ci_mono_reserved >>
     qexists_tac `st2` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. (cenv_without_defaults cenv name).ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at st2a x` by
    (simp[NoAsms, cenv_without_defaults_def] >> rpt strip_tac >>
     irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `st2` >> conj_tac >- first_assum ACCEPT_TAC >>
     first_assum MATCH_MP_TAC >> qexists_tac `sz` >> first_assum ACCEPT_TAC) >>
  `!x sz. (cenv_without_defaults cenv name).ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at st2a x` by
    (simp[NoAsms, cenv_without_defaults_def] >> rpt strip_tac >>
     irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `st2` >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x`
       (qspecl_then [`x`,`sz`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d (cenv_without_defaults cenv name) st2a t =
   return_buf_frame d cenv st2a t` by
    (Cases_on `d` >> TRY (PairCases_on `x`) >>
     simp[NoAsms, return_buf_frame_def, cenv_without_defaults_def]) >>
  `return_buf_frame d (cenv_without_defaults cenv name) st2a t` by
    (qpat_assum `return_buf_frame d (cenv_without_defaults cenv name) st2a t = _`
       SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes (cenv_without_defaults cenv name) = type_memory_bytes cenv` by
    (irule compileEnvTheory.type_memory_bytes_frame >> simp[NoAsms, cenv_without_defaults_def]) >>
  `!ty sub. type_step_offset (cenv_without_defaults cenv name) ty sub =
            type_step_offset cenv ty sub` by
    (qpat_assum `type_memory_bytes (cenv_without_defaults cenv name) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     simp[oneline loweringPostsTheory.type_step_offset_def, cenv_without_defaults_def]) >>
  `!path ty. type_path_offset (cenv_without_defaults cenv name) ty path =
             type_path_offset cenv ty path` by
    (qpat_assum `!ty sub. type_step_offset (cenv_without_defaults cenv name) ty sub = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[loweringPostsTheory.type_path_offset_def]) >>
  `!src dst a u v. wb_frame (cenv_without_defaults cenv name) src dst a u v =
                    wb_frame cenv src dst a u v` by
    (qpat_assum `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=> _` mp_tac >>
     qpat_assum `!path ty. type_path_offset (cenv_without_defaults cenv name) ty path = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
     simp[wb_frame_def, locals_kept_def, loweringPostsTheory.popped_kept_def,
          loweringPostsTheory.dynarray_len_untupled_def, cenv_without_defaults_def]) >>
  `!G tn. ghost_kept_at lo (cenv_without_defaults cenv name) es0 sa G0 tn0 s0 G tn =
          ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn` by
    (qpat_assum `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> simp[ghost_kept_at_def]) >>
  `!H. cx_dead H cxd = cx_dead H cx` by
    (qunabbrev_tac `cxd` >> simp[NoAsms, sourceUnitExecutionTheory.cx_dead_def]) >>
  `!src (regs : (bool # bytes32 # type_value) list).
     storage_well_formed_on cxd src regs = storage_well_formed_on cx src regs` by
    (qunabbrev_tac `cxd` >> POP_ASSUM_LIST (K ALL_TAC) >>
     `!src b. get_storage (cx with stk updated_by CONS (NONE,name)) src b =
               get_storage cx src b` by
       (rpt gen_tac >> Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
  pop_assum (mk_asm "defaults_storage") >>
  `!D src G tn u. ghost_inv_at D lo d (cenv_without_defaults cenv name) cxd src G tn u =
                  ghost_inv_at D lo d cenv cx src G tn u` by
    (qpat_assum `cx_tops cxd = cx_tops cx` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Cases_on `d` >> TRY (PairCases_on `x`) >>
     simp[ghost_inv_at_def, return_buf_ptr_def, cenv_without_defaults_def]) >>
  pop_assum (mk_asm "defaults_ghost") >>
  `!H. valid_horizon cxd st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func (cenv_without_defaults cenv name) cxd ee t /\
     storage_well_formed_on cxd ee (FST H) /\
     ghost_inv_at (DF H) lo d (cenv_without_defaults cenv name) cxd ee G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       (qpat_assum `!src h tr. valid_horizon cxd src h tr = _`
          (fn th => once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func (cenv_without_defaults cenv name) cxd ee t`
       (drule_then assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (asm "defaults_storage" (MATCH_MP_TAC o iffRL o SPEC_ALL) >>
         first_assum ACCEPT_TAC) >>
     asm "defaults_ghost" (MATCH_MP_TAC o iffRL o SPEC_ALL) >>
     first_assum ACCEPT_TAC) >>
  `!j. j < LENGTH ds /\ EL j (DROP (LENGTH es) pvs) ==>
       is_word_type (EL j (DROP (LENGTH es) (MAP SND args)))` by
    (qx_gen_tac `j` >> strip_tac >>
     `j + LENGTH es < LENGTH args` by
       (qpat_assum `j < LENGTH ds` mp_tac >>
        qpat_assum `LENGTH ds = LENGTH args - LENGTH es` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `j + LENGTH es < LENGTH pvs` by
       (qpat_assum `LENGTH pvs = LENGTH args` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     `j + LENGTH es < LENGTH (MAP SND args)` by
       (pure_rewrite_tac[listTheory.LENGTH_MAP] >> first_assum ACCEPT_TAC) >>
     `EL (j + LENGTH es) pvs` by
       (`EL j (DROP (LENGTH es) pvs) = EL (j + LENGTH es) pvs` by
          (irule listTheory.EL_DROP >> first_assum ACCEPT_TAC) >>
        pop_assum (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     `EL j (DROP (LENGTH es) (MAP SND args)) = EL (j + LENGTH es) (MAP SND args)` by
       (irule listTheory.EL_DROP >> first_assum ACCEPT_TAC) >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> _` (MATCH_MP_TAC o SPEC_ALL) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!source src u G tn. gas_outcome_full _ _ cxd _ source (src,u,G,tn) _ _ = _`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule (REWRITE_RULE[]
    (Q.INST [`clean_words` |-> `T`, `keep_sites` |-> `T`]
      intcall_args_stage_full_p2_with_path)) >>
  qpat_assum `body_inv tops ctx (cenv_without_defaults cenv name) cxd`
    (irule_at Any) >>
  qpat_assum `expr_sim_inv (cenv_without_defaults cenv name) cxd
               (tenv with current_src := NONE) ee` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ (cenv_without_defaults cenv name)
               ds _ _ st2a = (def_ops,st3)` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _
               (MAP gas_shadow_expr ds) _ _ sh_st2a = (def_ops,sh_st3)`
    (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `eval_operands _ t = SOME ws1` (irule_at Any) >>
  qexistsl_tac [`xs`,`tn0`,`sa`,`s0`,`TAKE (LENGTH es) (MAP SND args)`,
                `pin`,`TAKE (LENGTH es) pvs`,`es0`,`d`,`P`,`G0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `halt_exit _ cxd _ _ _` >>
       rpt strip_tac >> rename1 `halt_exit H cxd exit_src res r` >>
       qpat_assum `!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\ _ ==> _`
         irule >>
       rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       Cases_on `res = INR HaltException`
       >- (qpat_assum `res = INR HaltException` SUBST_ALL_TAC >>
           qunabbrev_tac `cxd` >>
           qpat_assum `halt_exit H (cx with stk updated_by CONS (NONE,name)) exit_src _ r`
             (mp_then Any ACCEPT_TAC intcall_args_halt_exit_pop)) >>
       irule haltExitProjTheory.halt_exit_not_halt >> first_assum ACCEPT_TAC >> NO_TAC)
  >~ [`!dvs. storage_trace_frame ((\dvs src. after_defaults src.scopes dvs src) dvs)`]
  >- (`!prev dvs. storage_trace_frame (after_defaults prev dvs)` by
        (qunabbrev_tac `after_defaults` >> rpt gen_tac >> BETA_TAC >>
         irule intcall_after_defaults_storage_trace_frame >> first_assum ACCEPT_TAC) >>
      rewrite_tac[storage_trace_frame_def] >>
      map_every qx_gen_tac [`dvs`,`src`,`obs`] >>
      qpat_assum `!prev dvs. storage_trace_frame (after_defaults prev dvs)`
        (qspecl_then [`src.scopes`,`dvs`] mp_tac) >>
      rewrite_tac[storage_trace_frame_def] >>
      disch_then (qspecl_then [`src`,`obs`] mp_tac) >>
      simp[NoAsms]) >>
  TRY (qmatch_goalsub_rename_tac `LENGTH ([] ++ sup_ops)` >>
       pure_rewrite_tac[listTheory.APPEND] >>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND]) >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `LENGTH (DROP _ _)` >>
       qpat_assum `LENGTH ds = LENGTH args - LENGTH es` mp_tac >>
       qpat_assum `LENGTH pvs = LENGTH args` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `vv_type _ = lowered_value_type _ _` >>
       rpt strip_tac >> irule intcall_args_aggregate_physical_type_mods >>
       qpat_assum `body_inv tops ctx (cenv_without_defaults cenv name) cxd`
         (mp_then Any (drule_then (irule_at Any))
           exprBodyPrePropsTheory.body_inv_expr_body_pre_mods) >>
       rpt (first_assum (irule_at Any)) >> NO_TAC) >>
  TRY (qpat_assum `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=> _`
         (fn th => pure_rewrite_tac [th, listTheory.APPEND]) >>
       qpat_assum `get_tenv cxd = get_tenv cx` (fn th => pure_rewrite_tac [th]) >>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND]) >> NO_TAC)
  >~ [`ghost_kept_at lo (cenv_without_defaults cenv name) es0 sa G0 tn0 s0 G1 tn1`]
  >- (qpat_assum `!G tn. ghost_kept_at lo (cenv_without_defaults cenv name) _ _ _ _ _ G tn = _`
        (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC)
  >~ [`wb_frame (cenv_without_defaults cenv name) es0 ee sa s0 t`]
  >- (qpat_assum `!src dst a u v. wb_frame (cenv_without_defaults cenv name) src dst a u v = _`
        (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC)
  >~ [`EVERY (\ty. type_memory_bytes (cenv_without_defaults cenv name) ty < _) (DROP _ _)`]
  >- (qpat_assum `type_memory_bytes (cenv_without_defaults cenv name) = _`
        SUBST1_TAC >> irule rich_listTheory.EVERY_DROP >> first_assum ACCEPT_TAC)
  >~ [`!H. dead_lo_ok H (DF H) lo (cenv_without_defaults cenv name) cxd`]
  >- (qpat_assum `cx_tops cxd = cx_tops cx` mp_tac >>
      qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` mp_tac >>
      qunabbrev_tac `cxd` >> POP_ASSUM_LIST (K ALL_TAC) >>
      simp[dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def,
           cenv_without_defaults_def]) >>
  map_every qx_gen_tac [`dm`,`dvs`,`ed`,`u`,`Gd`,`tnd`] >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cxd (tenv with current_src := NONE) ed` by
    (`well_typed_exprs (tenv with current_src := NONE) ds` by
       (qpat_assum `EVERY (\e. expr_body_pre (cenv_without_defaults cenv name) cxd
          (tenv with current_src := NONE) e ee) ds` mp_tac >>
        simp[NoAsms, constSubstCorrectTheory.frame_well_typed_exprs_every, EVERY_MEM] >>
        disch_tac >> rpt strip_tac >>
        first_x_assum (drule_then (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts))) >>
     `body_const_cells_agree [(NONE,tops)] cxd (tenv with current_src := NONE)
        (ed with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_exprs >>
     qpat_assum `!tail. eval_exprs cxd ds _ = _`
       (qspec_then `[]` (irule_at Any)) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx tenv ed` by
    (`(tenv with current_src := NONE) with current_src := tenv.current_src = tenv` by
       simp[NoAsms, vyperTypeSystemTheory.typing_env_component_equality] >>
     `cxd with stk := cx.stk = cx` by
       simp[NoAsms, Abbr `cxd`, vyperContextTheory.evaluation_context_component_equality] >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cxd
        (tenv with current_src := NONE) ed`
       (mp_tac o Q.INST [`stk` |-> `cx.stk`] o
        MATCH_MP body_const_cells_agree_stk o
        Q.INST [`src` |-> `tenv.current_src`] o MATCH_MP body_const_cells_agree_current_src) >>
     simp[]) >>
  `!inst. active_inst func inst u ==> frag_reachable ctx func s0 func inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `DF (storage_trace_horizon ed.storage_trace)` assume_tac) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`body_inv tops ctx cenv cx`, `MEM func ctx.ctx_functions`,
        `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`,
        `gas_path ctx func entry (LENGTH marks) (OK t)`,
        `gas_path ctx func t (LENGTH dm) (OK u)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[args_invoke_reach]) >>
  rename1 `eval_operands _ u = SOME wd` >>
  qpat_assum `!source src u G tn. gas_outcome_full _ _ cxd _ source (src,u,G,tn) _ _ = _`
    (fn th => once_rewrite_tac[th]) >> BETA_TAC >>
  `?penv. bind_arguments (get_tenv cx) args (xs ++ dvs) = SOME penv` by
    (Cases_on `bind_arguments (get_tenv cx) args (xs ++ dvs)` >> simp[] >>
     `after_defaults ed.scopes dvs (ed with gas_obs := []) =
        (INR (Error (TypeError "IntCall bind_arguments")),ed with gas_obs := [])` by
       (qunabbrev_tac `after_defaults` >>
        simp[lift_option_type_def, vyperStateTheory.bind_def,
             pairTheory.UNCURRY, raise_def]) >>
     `P (INR (Error (TypeError "IntCall bind_arguments")))` by
       (qpat_assum `gas_admissible ((\dvs src. after_defaults src.scopes dvs src) dvs) P ed`
          (qspecl_then [`[]`,`INR (Error (TypeError "IntCall bind_arguments"))`,
                        `ed with gas_obs := []`] (mp_tac o BETA_RULE) o
           REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
        qpat_assum `after_defaults ed.scopes dvs (ed with gas_obs := []) = _`
          (fn th => simp[NoAsms,th])) >>
     qpat_assum `!e. P (INR e) ==> expr_vv_res_ok (INR e)`
       (qspec_then `Error (TypeError "IntCall bind_arguments")` drule) >>
     simp[NoAsms,exprSimDefsTheory.expr_vv_res_ok_def]) >>
  rename1 `bind_arguments (get_tenv cx) args (xs ++ dvs) = SOME penv` >>
  `body_const_cells_agree [(NONE,tops)] cx tenv (ed with scopes := [penv])`
    by simp[] >>
  rename1 `evaluate_type (get_tenv cx) ret = SOME rtv` >>
  `env_context_consistent tenv cx` by
    (qpat_assum `env_consistent tenv cx ee`
       (ACCEPT_TAC o cj 1 o REWRITE_RULE [vyperTypeInvariantsTheory.env_consistent_def])) >>
  `context_function_live cx (NONE,name)` by
    (qpat_assum `env_context_consistent tenv cx` mp_tac >>
     qpat_assum `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperTypeInvariantsTheory.env_context_consistent_def,
          vyperTypeInvariantsTheory.fn_sigs_live_def, optionTheory.IS_SOME_EXISTS] >>
     metis_tac[]) >>
  `ret <> NoneT ==> 0 < type_memory_size rtv` by
    (disch_tac >>
     mp_tac (Q.INST [`env` |-> `tenv`, `src` |-> `NONE`, `tv` |-> `rtv`]
       internalReturnMemoryInputsTheory.callable_return_memory_size_pos) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[NoAsms]) >>
  `?H. valid_horizon cx st0 H ed.storage_trace` by
    (qpat_assum `storage_trace_domain cxd st0 ed.storage_trace` mp_tac >>
     qpat_assum `!src tr. storage_trace_domain cxd src tr = _`
       (fn th => pure_rewrite_tac[th]) >>
     rewrite_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     disch_tac >> qexists_tac `storage_trace_horizon ed.storage_trace` >>
     first_assum ACCEPT_TAC) >>
  `ed.scopes = ee.scopes` by
    (qpat_assum `!s res fin. eval_exprs cxd ds s = (res,fin) ==> _` (fn frame =>
       qpat_assum `!tail. eval_exprs cxd ds _ = _`
         (qspec_then `[]` (mp_tac o MATCH_MP (SPEC_ALL frame)))) >>
     simp[NoAsms]) >>
  `!tail sc. lock_if_nr cx nr (is_view_mut mut)
       (ed with <|scopes := sc; gas_obs := tail|>) =
     (FST (lock_if_nr cx nr (is_view_mut mut) ed),
      SND (lock_if_nr cx nr (is_view_mut mut) ed) with
          <|scopes := sc; gas_obs := tail|>)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
     simp[acquire_nonreentrant_lock_def, ignore_bind_def,
          vyperStateTheory.bind_def, record_storage_event_def,
          get_transient_storage_def, update_transient_def, return_def,
          raise_def, check_not_static_def, check_def, assert_def, COND_RATOR] >>
     rpt IF_CASES_TAC >>
     simp[vyperStateTheory.bind_def, return_def, raise_def,
          update_transient_def, assert_def] >>
     Cases_on `mut = View \/ mut = Pure` >> simp[]) >>
  `!err locked. lock_if_nr cx nr (is_view_mut mut) ed = (INR err,locked) ==>
     !tail.
       after_defaults ed.scopes dvs (ed with gas_obs := tail) =
         (INR err, locked with <|scopes := ed.scopes; gas_obs := tail|>) /\
       bind (intcall_rest cx name mut nr ss ed.scopes rtv) f
         ((ed with scopes := [penv]) with gas_obs := tail) =
         (INR err, locked with <|scopes := [penv]; gas_obs := tail|>)` by
    (map_every qx_gen_tac [`err`,`locked`] >>
     disch_then (fn th =>
       qpat_assum `!tail sc. lock_if_nr _ _ _ _ = _`
         (assume_tac o REWRITE_RULE [th, pairTheory.FST, pairTheory.SND])) >>
     qx_gen_tac `tail` >>
     `ed with <|scopes := ed.scopes; gas_obs := tail|> =
      ed with gas_obs := tail` by
       simp[NoAsms, evaluation_state_component_equality] >>
     `lock_if_nr cx nr (is_view_mut mut) (ed with gas_obs := tail) =
       (INR err, locked with <|scopes := ed.scopes; gas_obs := tail|>)` by
       (qpat_assum `!tail sc. lock_if_nr _ _ _ _ = (INR err,_)`
          (qspecl_then [`tail`,`ed.scopes`] mp_tac) >>
        qpat_assum `ed with <|scopes := ed.scopes; gas_obs := tail|> = _`
          (fn th => rewrite_tac[th])) >>
     `lock_if_nr cx nr (is_view_mut mut)
       ((ed with scopes := [penv]) with gas_obs := tail) =
       (INR err, locked with <|scopes := [penv]; gas_obs := tail|>)` by
       (qpat_assum `!tail sc. lock_if_nr _ _ _ _ = (INR err,_)`
          (qspecl_then [`tail`,`[penv]`] mp_tac) >>
        simp[NoAsms, evaluation_state_component_equality]) >>
     conj_tac
     >- (qunabbrev_tac `after_defaults` >> BETA_TAC >>
         qpat_assum `bind_arguments _ args (xs ++ dvs) = SOME penv` mp_tac >>
         qpat_assum `evaluate_type _ ret = SOME rtv` mp_tac >>
         qpat_assum `lock_if_nr _ _ _ (ed with gas_obs := tail) = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
         ASM_SIMP_TAC std_ss [lift_option_type_def, vyperStateTheory.bind_def,
                      ignore_bind_def, return_def, pairTheory.pair_case_thm, sumTheory.sum_case_def]) >>
     qpat_assum `lock_if_nr _ _ _ ((ed with scopes := [penv]) with gas_obs := tail) = _`
       (fn th => SIMP_TAC std_ss [th,intcall_rest_def,vyperStateTheory.bind_def,
          ignore_bind_def,pairTheory.pair_case_thm,sumTheory.sum_case_def])) >>
  `!locked. lock_if_nr cx nr (is_view_mut mut) ed = (INL (),locked) ==>
     !tail. after_defaults ed.scopes dvs (ed with gas_obs := tail) =
       bind (intcall_rest cx name mut nr ss ed.scopes rtv) f
         ((ed with scopes := [penv]) with gas_obs := tail)` by
    (qx_gen_tac `locked` >> disch_then (fn th =>
       qpat_assum `!tail sc. lock_if_nr _ _ _ _ = _`
         (assume_tac o REWRITE_RULE [th, pairTheory.FST, pairTheory.SND])) >>
     qx_gen_tac `tail` >>
     `ed with <|scopes := ed.scopes; gas_obs := tail|> =
      ed with gas_obs := tail` by
       simp[NoAsms, evaluation_state_component_equality] >>
     `lock_if_nr cx nr (is_view_mut mut) (ed with gas_obs := tail) =
       (INL (), locked with <|scopes := ed.scopes; gas_obs := tail|>)` by
       (qpat_assum `!tail sc. lock_if_nr _ _ _ _ = (INL (),_)`
          (qspecl_then [`tail`,`ed.scopes`] mp_tac) >>
        qpat_assum `ed with <|scopes := ed.scopes; gas_obs := tail|> = _`
          (fn th => rewrite_tac[th])) >>
     qunabbrev_tac `after_defaults` >> BETA_TAC >>
     qpat_assum `bind_arguments _ args (xs ++ dvs) = SOME penv` (fn bth =>
       qpat_assum `evaluate_type _ ret = SOME rtv` (fn rth =>
         SIMP_TAC std_ss [bth,rth,lift_option_type_def,bind_return,ignore_bind_def])) >>
     `((ed with scopes := [penv]) with gas_obs := tail) =
      ((ed with gas_obs := tail) with scopes := [penv])` by
       simp[NoAsms, evaluation_state_component_equality] >>
     qpat_assum `((ed with scopes := [penv]) with gas_obs := tail) = _`
       SUBST1_TAC >>
     once_rewrite_tac[vyperStateTheory.bind_def] >>
     qpat_assum `lock_if_nr _ _ _ (ed with gas_obs := tail) = (INL (),_)`
       (mp_then Any (fn th => rewrite_tac[th])
         (SIMP_RULE std_ss [lift_option_type_def] intcall_args_lock_push_success))) >>
  `!tail. FST (after_defaults ed.scopes dvs (ed with gas_obs := tail)) =
     FST (bind (intcall_rest cx name mut nr ss ed.scopes rtv) f
       ((ed with scopes := [penv]) with gas_obs := tail))` by
    (qpat_assum `!locked. lock_if_nr _ _ _ _ = (INL (),_) ==> _` mp_tac >>
     qpat_assum `!err locked. lock_if_nr _ _ _ _ = (INR err,locked) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `lock_if_nr cx nr (is_view_mut mut) ed` >>
     rename1 `lock_if_nr _ _ _ _ = (lr,locked)` >>
     Cases_on `lr` >> simp[oneTheory.one] >> metis_tac[pairTheory.FST]) >>
  `gas_admissible (bind (intcall_rest cx name mut nr ss ed.scopes rtv) f)
     P (ed with scopes := [penv])` by
    (rewrite_tac[gasContextTheory.gas_admissible_def] >>
     map_every qx_gen_tac [`tail`,`res`,`out_src`] >> disch_tac >>
     Cases_on `after_defaults ed.scopes dvs (ed with gas_obs := tail)` >>
     qpat_assum `after_defaults _ _ _ = (_,_)` (fn ath =>
       qpat_assum `bind (intcall_rest _ _ _ _ _ _ _) f _ = (_,_)` (fn bth =>
         qpat_assum `!tail. FST (after_defaults _ _ _) = _`
           (qspec_then `tail` (SUBST1_TAC o REWRITE_RULE [ath,bth,pairTheory.FST] o SYM)))) >>
     qpat_assum `gas_admissible ((\dvs src. after_defaults src.scopes dvs src) dvs) P ed`
       (qspecl_then [`tail`,`q`,`r`] mp_tac o BETA_RULE o
        REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     qpat_assum `after_defaults _ _ _ = (q,r)`
       (fn th => simp[NoAsms,th])) >>
  `gas_admissible (intcall_rest cx name mut nr ss ed.scopes rtv)
     expr_vv_res_ok (ed with scopes := [penv])` by
    (rewrite_tac[gasContextTheory.gas_admissible_def] >>
     map_every qx_gen_tac [`tail`,`res`,`out_src`] >> disch_tac >>
     Cases_on `res` >-
       (qpat_assum `intcall_rest _ _ _ _ _ _ _ _ = (INL _,_)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[intcall_rest_def, vyperStateTheory.bind_def, ignore_bind_def,
             return_def, CaseEq "prod", CaseEq "sum",
             exprSimDefsTheory.expr_vv_res_ok_def] >>
        rpt strip_tac >> metis_tac[]) >>
     first_x_assum irule >>
     qpat_assum `gas_admissible (bind (intcall_rest _ _ _ _ _ _ _) f) P _`
       (qspec_then `tail` mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     simp[Once vyperStateTheory.bind_def]) >>
  `eval_exprs cxd raw_ds
       ((ee with gas_obs := gas_explicit dm t.vs_gas_readings) with scopes := [FEMPTY]) =
     (INL dvs, (ed with gas_obs := []) with scopes := [FEMPTY])` by
    (`(ee with gas_obs := gas_explicit dm t.vs_gas_readings) with scopes := [FEMPTY] =
        (ee with scopes := [FEMPTY]) with gas_obs := gas_explicit dm t.vs_gas_readings` by
       simp[NoAsms, evaluation_state_component_equality] >>
     pop_assum (fn upd =>
       pure_rewrite_tac[upd] >>
       qpat_assum `!gs scs. eval_exprs cxd ds _ = _`
         (qspecl_then [`gas_explicit dm t.vs_gas_readings`, `[FEMPTY]`]
           (fn th => pure_rewrite_tac[GSYM th])) >>
       pure_rewrite_tac[GSYM upd]) >>
     drule_all intcall_args_defaults_scope_action >>
     disch_then (qspecl_then [`cxd`,`ee with gas_obs := gas_explicit dm t.vs_gas_readings`,
                              `[FEMPTY]`] mp_tac) >>
     qpat_assum `!tail. eval_exprs cxd ds _ = _` (qspec_then `[]` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss)` by
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_push_body >>
     qpat_assum `lookup_callable_function cx.in_deploy name tops = SOME _` (irule_at Any) >>
     qpat_assum `get_module_code cx NONE = SOME tops` (irule_at Any) >>
     qpat_assum `call_evaluation_safe cx ((NONE,name)::_)` (irule_at Any) >> simp[NoAsms]) >>
  qpat_assum `!src dst a u v. wb_frame (cenv_without_defaults cenv name) src dst a u v = _`
    (fn th => qpat_assum `wb_frame (cenv_without_defaults cenv name) es0 ed sa s0 u`
       (strip_assume_tac o REWRITE_RULE [th,wb_frame_def])) >>
  `expr_sim_inv cenv cx tenv ed` by
    (irule args_defaults_restore_expr_sim_inv >>
     qpat_assum `expr_sim_inv (cenv_without_defaults cenv name) cxd _ ed` mp_tac >>
     qunabbrev_tac `cxd` >> disch_then (irule_at Any) >>
     qexists_tac `ee` >> first_assum ACCEPT_TAC) >>
  `((ed with scopes := [penv]) with scopes := ed.scopes) = ed` by
    simp[NoAsms,evaluation_state_component_equality] >>
  `(ed with scopes := [penv]).scopes = [penv]` by simp[NoAsms] >>
  qabbrev_tac `lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
              (nsid_to_string (NONE,name))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor` >>
  `!ops emitted. fn_has_code st3 emitted func /\
      ((?a. emit_void INVOKE (Label lbl::ops) st3 = (a,emitted)) \/
       (?n outs. emit_multi_op INVOKE (Label lbl::ops) n st3 = (outs,emitted))) ==>
      ?bb inst. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME inst /\
        inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     irule args_invoke_code_at_cursor >> qexistsl_tac [`emitted`,`st3`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!ops outs mid rbuf rets.
      emit_multi_op INVOKE (Label lbl::ops) rc' st3 = (outs,mid) /\
      store_multi_results rbuf outs 0 mid = (rets,sm) ==>
      fn_has_code st3 mid func` by
    (rpt strip_tac >>
     `cs_extends st3 mid` by
       (qspecl_then [`INVOKE`,`Label lbl::ops`,`rc'`,`st3`,`K T`]
          mp_tac externalEntryShapeTheory.emit_multi_op_labels >> simp[]) >>
     `cs_extends mid sm` by
       (qspecl_then [`rbuf`,`outs`,`0`,`mid`,`K T`]
          mp_tac externalEntryShapeTheory.store_multi_results_labels >> simp[]) >>
     irule (cj 1 fn_has_code_split) >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sm` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(rc' <> 0 \/ rbs = 0) ==>
      ?bb inst. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME inst /\
        inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,sup_ops ++ def_ops)` by
    (disch_tac >> Cases_on `rc' = 0`
     >- (`rc' = 0 /\ rbs = 0` by
           (qpat_assum `rc' <> 0 \/ rbs = 0` mp_tac >> simp[NoAsms] >>
            qpat_assum `rc' = 0` (fn th => simp[NoAsms,th])) >>
         qpat_assum `rc' = 0 /\ rbs = 0 ==> ?e. st2 = sa /\ _` (drule_all_then strip_assume_tac) >>
         qpat_assum `!ops emitted. fn_has_code st3 emitted func /\ _ ==> ?bb inst. _` irule >>
         qexists_tac `sm` >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> disj1_tac >> goal_assum (drule_at Any)) >>
     `0 < rc'` by
       (qpat_assum `rc' <> 0` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `0 < rc' ==> ?b r m e. compile_alloc_buffer _ sa = (b,st2) /\
                   emit_multi_op INVOKE _ rc' st3 = (r,m) /\ _`
       (drule_then (qx_choose_then `rbuf` (qx_choose_then `results`
          (qx_choose_then `mid` (qx_choose_then `ignored` strip_assume_tac))))) >>
     qpat_assum `!ops emitted. fn_has_code st3 emitted func /\ _ ==> ?bb inst. _`
       irule >> qexists_tac `mid` >> conj_tac
     >~ [`_ \/ _`] >- (disj2_tac >> qexistsl_tac [`rc'`,`results`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!ops outs mid rbuf rets. _ ==> fn_has_code st3 mid func`
       irule >> qexistsl_tac [`sup_ops ++ def_ops`,`results`,`rbuf.buf_operand`,`ignored`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!rbuf. rc' = 0 /\ 0 < rbs /\ compile_alloc_buffer rbs sa = (rbuf,st2) ==>
       ?bb inst. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb u.vs_inst_idx = SOME inst /\
         inst.inst_opcode = INVOKE /\
         decode_invoke inst = SOME (lbl,rbuf.buf_operand :: (sup_ops ++ def_ops))` by
    (gen_tac >> strip_tac >>
     qpat_assum `rc' = 0 /\ 0 < rbs ==> ?b e. compile_alloc_buffer rbs sa = (b,st2) /\
                 emit_void INVOKE _ st3 = (e,sm) /\ _` mp_tac >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `rb` (qx_choose_then `ignored` strip_assume_tac)) >>
     `rb = rbuf` by
       (qpat_assum `compile_alloc_buffer rbs sa = (rb,st2)` mp_tac >>
        qpat_assum `compile_alloc_buffer rbs sa = (rbuf,st2)` (fn th => simp[NoAsms,th])) >>
     qpat_assum `!ops emitted. fn_has_code st3 emitted func /\ _ ==> ?bb inst. _` irule >>
     qexists_tac `sm` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     disj1_tac >> qexists_tac `ignored` >>
     qpat_assum `rb = rbuf` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `st3.cs_next_id <= sm.cs_next_id` by
    (Cases_on `0 < rc'`
     >- (qpat_assum `0 < rc' ==> ?b r m e. compile_alloc_buffer _ sa = (b,st2) /\
                     emit_multi_op INVOKE _ rc' st3 = (r,m) /\ _`
           (drule_then (qx_choose_then `rb` (qx_choose_then `results`
              (qx_choose_then `mid` (qx_choose_then `ignored` strip_assume_tac))))) >>
         `st3.cs_next_id <= mid.cs_next_id` by
           (qpat_assum `emit_multi_op INVOKE _ rc' st3 = (results,mid)`
              (fn eq => mp_tac (REWRITE_RULE[eq] (Q.SPECL
                [`INVOKE`,`Label lbl::(sup_ops ++ def_ops)`,`rc'`,`st3`]
                exprLoweringPropsTheory.ci_mono_emit_multi_op))) >>
            simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
         `mid.cs_next_id <= sm.cs_next_id` by
           (qpat_assum `store_multi_results rb.buf_operand results 0 mid = (ignored,sm)`
              (fn eq => mp_tac (REWRITE_RULE[eq] (Q.SPECL
                [`rb.buf_operand`,`results`,`0`,`mid`]
                exprLoweringPropsTheory.ci_mono_store_multi_results))) >>
            simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
         qpat_assum `st3.cs_next_id <= mid.cs_next_id` mp_tac >>
         qpat_assum `mid.cs_next_id <= sm.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `rc' = 0` by
       (qpat_assum `~(0 < rc')` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `?ops ignored. emit_void INVOKE ops st3 = (ignored,sm)` by
       (Cases_on `rbs = 0`
        >- (qpat_assum `rc' = 0 /\ rbs = 0 ==> ?e. st2 = sa /\ _`
              (drule_all_then strip_assume_tac) >> goal_assum (drule_at Any)) >>
        `0 < rbs` by
          (qpat_assum `rbs <> 0` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        qpat_assum `rc' = 0 /\ 0 < rbs ==> ?b e. compile_alloc_buffer rbs sa = (b,st2) /\ _`
          (drule_all_then strip_assume_tac) >> goal_assum (drule_at Any)) >>
     drule (cj 2 compilerInstructionSuffixTheory.added_insts_emit_void) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `(0 < rc' \/ 0 < rbs) ==> ?rb q b.
     compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\
     rb.buf_size = buf_n /\ pin = SOME (q,b,buf_n) /\
     FLOOKUP Gd q = SOME (b,buf_n) /\ op_taint tnd (Var q) = {} /\
     eval_operand (Var q) u = SOME (n2w b) /\
     FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,buf_n) /\
     sa.cs_next_id < sm.cs_next_id /\ lo <= b /\ b + buf_n <= u.vs_alloca_next /\
     !n lb sz. local_region (cenv_without_defaults cenv name) ed.scopes u n lb sz ==>
       b + buf_n <= lb \/ lb + sz <= b` by
    (disch_tac >>
     qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q w.
                  compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\
                  rb.buf_size = buf_n /\ pin = SOME (q,w2n w,buf_n)`
       (drule_then (qx_choose_then `rb` (qx_choose_then `q`
          (qx_choose_then `w` strip_assume_tac)))) >>
     qpat_assum `case pin of NONE => T | SOME (pinvar,pb,pk) => FLOOKUP Gd pinvar = SOME (pb,pk) /\ _` mp_tac >>
     qpat_assum `pin = SOME (q,w2n w,buf_n)` (fn th => simp[NoAsms,th]) >>
     strip_tac >> qexists_tac `rb` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[venomStateTheory.eval_operand_def] >> NO_TAC) >>
     qpat_assum `sa.cs_next_id < st3.cs_next_id` mp_tac >>
     qpat_assum `st3.cs_next_id <= sm.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!rb. (0 < rc' \/ 0 < rbs) /\ compile_alloc_buffer buf_n sa = (rb,st2) ==>
      vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
             (base_ptr rb)` by
    (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     Cases_on `0 < rc'`
     >- (qpat_assum `0 < rc' ==> ?b r m e. compile_alloc_buffer _ sa = (b,st2) /\
                    emit_multi_op INVOKE _ rc' st3 = (r,m) /\ _`
           (drule_then strip_assume_tac) >>
         qpat_assum `vv = LocatedValue _ _` mp_tac >>
         qpat_assum `compile_alloc_buffer (32 * rc') sa = (_,st2)` mp_tac >>
         qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
         qunabbrev_tac `buf_n` >>
     (qpat_assum `0 < rc'` mp_tac ORELSE qpat_assum `~(0 < rc')` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
     `rc' = 0 /\ 0 < rbs` by
       (qpat_assum `~(0 < rc')` mp_tac >> qpat_assum `0 < rc' \/ 0 < rbs` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `rc' = 0 /\ 0 < rbs ==> ?b e. compile_alloc_buffer rbs sa = (b,st2) /\ _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `vv = LocatedValue _ _` mp_tac >>
     qpat_assum `compile_alloc_buffer rbs sa = (_,st2)` mp_tac >>
     qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
     qunabbrev_tac `buf_n` >>
     (qpat_assum `0 < rc'` mp_tac ORELSE qpat_assum `~(0 < rc')` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `!ty p buf. vv = LocatedValue ty p /\ p.ptr_buf = SOME buf ==>
     ?x off aid.
       p.ptr_operand = Var x /\ op_taint tnd (Var x) = {} /\
       FLOOKUP Gd x = SOME (off,buf.buf_size) /\
       eval_operand p.ptr_operand u = SOME (n2w off) /\
       FLOOKUP u.vs_allocas aid = SOME (off,buf.buf_size) /\
       aid = sa.cs_next_id /\ aid < sm.cs_next_id /\
       lo <= off /\ off + buf.buf_size <= u.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     `0 < rc' \/ 0 < rbs` by
       (spose_not_then assume_tac >>
        `rc' = 0 /\ rbs = 0` by
          (qpat_assum `~(0 < rc') /\ ~(0 < rbs)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        qpat_assum `rc' = 0 /\ rbs = 0 ==> ?e. st2 = sa /\ _`
          (drule_all_then strip_assume_tac) >>
        qpat_assum `vv = StackValue _ _` mp_tac >>
        qpat_assum `vv = LocatedValue _ _` (fn th => simp[NoAsms,th])) >>
     qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q b.
        compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\
        rb.buf_size = buf_n /\ pin = SOME (q,b,buf_n) /\ _` mp_tac >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `rb` (qx_choose_then `q`
       (qx_choose_then `b` strip_assume_tac))) >>
     `p = base_ptr rb` by
       (qpat_assum `!rb. (0 < rc' \/ 0 < rbs) /\ compile_alloc_buffer buf_n sa = (rb,st2) ==> _`
          (qspec_then `rb` mp_tac) >>
        (impl_tac >- simp[]) >>
        qpat_assum `vv = LocatedValue _ p` (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `p = base_ptr rb` SUBST_ALL_TAC >>
     `buf = rb` by
       (qpat_assum `(base_ptr rb).ptr_buf = SOME buf` mp_tac >>
        simp[NoAsms,contextTheory.base_ptr_def]) >>
     qpat_x_assum `buf = rb` SUBST_ALL_TAC >>
     qexistsl_tac [`q`,`b`,`sa.cs_next_id`] >> simp[contextTheory.base_ptr_def]) >>
  `eval_operands (sup_ops ++ def_ops) u = SOME wd` by
    (qpat_assum `eval_operands ([] ++ sup_ops ++ def_ops) u = SOME wd` mp_tac >>
     simp[NoAsms]) >>
  `?bops bws ibb ii.
       lookup_block u.vs_current_bb func.fn_blocks = SOME ibb /\
       get_instruction ibb u.vs_inst_idx = SOME ii /\ ii.inst_opcode = INVOKE /\
       decode_invoke ii = SOME (lbl,bops ++ sup_ops ++ def_ops) /\
       eval_operands (bops ++ sup_ops ++ def_ops) u = SOME (bws ++ wd) /\
       EVERY (\op. op_taint tnd op = {}) bops /\
       ((rc' <> 0 \/ rbs = 0) ==> bops = [] /\ bws = []) /\
       (rc' = 0 /\ 0 < rbs ==>
          ?rb b. compile_alloc_buffer rbs sa = (rb,st2) /\
                 bops = [rb.buf_operand] /\ bws = [n2w b] /\
                 FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,rb.buf_size) /\
                 op_prov Gd rb.buf_operand = SOME (b,rb.buf_size) /\
                 sa.cs_next_id < sm.cs_next_id /\ lo <= b /\
                 b + rb.buf_size <= u.vs_alloca_next)` by
    (Cases_on `rc' = 0 /\ 0 < rbs`
     >- (`0 < rc' \/ 0 < rbs` by simp[] >>
         qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q b.
           compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\ _`
           mp_tac >> (impl_tac >- simp[]) >>
         disch_then (qx_choose_then `rb` (qx_choose_then `q`
           (qx_choose_then `b` strip_assume_tac))) >>
         `buf_n = rbs` by simp[Abbr `buf_n`] >>
         `compile_alloc_buffer rbs sa = (rb,st2)` by
           (qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
            qpat_assum `buf_n = rbs` (fn th => rewrite_tac[th])) >>
         qpat_assum `!rb. rc' = 0 /\ 0 < rbs /\ compile_alloc_buffer rbs sa = (rb,st2) ==> _`
           (qspec_then `rb` mp_tac) >> (impl_tac >- simp[]) >>
         disch_then (qx_choose_then `ibb` (qx_choose_then `ii` strip_assume_tac)) >>
         qexistsl_tac [`[rb.buf_operand]`,`[n2w b]`,`ibb`,`ii`] >>
         simp[venomStateTheory.eval_operands_def,ptrDisciplineTheory.op_prov_def] >>
         qexists_tac `rb` >> simp[]) >>
     `(rc' <> 0 \/ rbs = 0)` by
       (qpat_assum `~(rc' = 0 /\ 0 < rbs)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `(rc' <> 0 \/ rbs = 0) ==> ?bb inst. _` mp_tac >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `ibb` (qx_choose_then `ii` strip_assume_tac)) >>
     qexistsl_tac [`[]`,`[]`,`ibb`,`ii`] >> simp[]) >>
  `EVERY (\ty. IS_SOME (evaluate_type (get_tenv cx) ty)) (MAP SND args)` by
    (qpat_assum `bind_arguments (get_tenv cx) args (xs ++ dvs) = SOME penv`
       (mp_then Any ACCEPT_TAC args_bound_types_evaluate)) >>
  `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)` by
    (qpat_assum `LENGTH (TAKE (LENGTH es) (MAP SND args) ++ DROP (LENGTH es) (MAP SND args)) = _`
       mp_tac >> pure_rewrite_tac[listTheory.TAKE_DROP,listTheory.APPEND] >>
     disch_then ACCEPT_TAC) >>
  `!b cap. MEM (SOME (b,cap)) (MAP (op_prov Gd) (sup_ops ++ def_ops)) ==>
     ?aid. FLOOKUP u.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < st3.cs_next_id /\ lo <= b /\ b + cap <= u.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >> irule args_staged_provenance >>
     qpat_assum `MEM (SOME _) (MAP (op_prov Gd) _)` (irule_at Any) >>
     qpat_assum `EVERY (\ty. IS_SOME (evaluate_type (get_tenv cx) ty)) (MAP SND args)` (irule_at Any) >>
     qexists_tac `pvs` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!j rt. j < LENGTH ([] ++ sup_ops ++ def_ops) /\ _ ==> _` mp_tac >>
     qpat_assum `get_tenv cxd = get_tenv cx` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[listTheory.TAKE_DROP,listTheory.APPEND] >>
     disch_then (fn th => map_every qx_gen_tac [`j`,`rt`] >> strip_tac >>
       qspecl_then [`j`,`rt`] mp_tac th) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `EVERY (\op. op_taint tnd op = {}) (bops ++ sup_ops ++ def_ops)` by
    (qpat_assum `EVERY (\op. op_taint tnd op = {}) ([] ++ sup_ops ++ def_ops)` mp_tac >>
     qpat_assum `EVERY (\op. op_taint tnd op = {}) bops` mp_tac >>
     pure_rewrite_tac[listTheory.EVERY_APPEND,listTheory.APPEND,listTheory.EVERY_DEF] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!b cap. MEM (SOME (b,cap)) (MAP (op_prov Gd) (bops ++ sup_ops ++ def_ops)) ==>
     ?aid. FLOOKUP u.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\ lo <= b /\ b + cap <= u.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >>
     `MEM (SOME (b,cap)) (MAP (op_prov Gd) bops) \/
      MEM (SOME (b,cap)) (MAP (op_prov Gd) (sup_ops ++ def_ops))` by
       (qpat_x_assum `MEM (SOME _) (MAP (op_prov Gd) (bops ++ sup_ops ++ def_ops))`
          mp_tac >>
        pure_rewrite_tac[listTheory.MAP_APPEND,listTheory.MEM_APPEND] >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
     >- (Cases_on `rc' = 0 /\ 0 < rbs`
         >- (qpat_assum `rc' = 0 /\ 0 < rbs ==> ?rb b. _` mp_tac >>
             (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
             qpat_x_assum `MEM (SOME _) (MAP (op_prov Gd) bops)` mp_tac >>
             qpat_assum `bops = [_]` (fn th => rewrite_tac[th]) >>
             qpat_assum `op_prov Gd _ = SOME _` (fn th => simp[NoAsms,th]) >>
             strip_tac >> qexists_tac `sa.cs_next_id` >> simp[]) >>
         qpat_assum `(rc' <> 0 \/ rbs = 0) ==> bops = [] /\ bws = []` mp_tac >>
         (impl_tac >-
           (qpat_assum `~(rc' = 0 /\ 0 < rbs)` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
         strip_tac >> qpat_x_assum `MEM (SOME _) (MAP (op_prov Gd) bops)` mp_tac >>
         qpat_assum `bops = []` (fn th => simp[NoAsms,th])) >>
     qpat_assum `!b cap. MEM (SOME (b,cap)) (MAP (op_prov Gd) (sup_ops ++ def_ops)) ==> _`
       (drule_then strip_assume_tac) >>
     qexists_tac `aid` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `st3.cs_next_id <= sm.cs_next_id` mp_tac >>
     qpat_assum `aid < st3.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `fn_has_code sa sm func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`cs_extends sa st2`,`cs_extends st2 st2a`,
           `cs_extends st2a st3`,`cs_extends st3 sm`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cs_extends_trans])) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ed.storage_trace ==>
     intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
       vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) ed.scopes penv rtv
       (ed with scopes := [penv]) u Gd tnd` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cxd st0 H ed.storage_trace` by
       (qpat_assum `!src h tr. valid_horizon cxd src h tr = _`
          (fn th => once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon cxd st0 H ed.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func cenv cx ed u` by
       (irule exprLoweringPropsTheory.stmt_state_rel_cenv_cong >>
        qpat_assum `stmt_state_rel H ctx func (cenv_without_defaults cenv name) cxd ed u`
          mp_tac >>
        qunabbrev_tac `cxd` >>
        rewrite_tac[intcall_args_stmt_state_rel_push] >>
        disch_then (irule_at Any) >> simp[NoAsms,cenv_without_defaults_def]) >>
     `storage_well_formed_on cx ed (FST H)` by
       (asm "defaults_storage" (MATCH_MP_TAC o iffLR o SPEC_ALL) >>
        first_assum ACCEPT_TAC) >>
     `ghost_inv_at (DF H) lo d cenv cx ed Gd tnd u` by
       (asm "defaults_ghost" (MATCH_MP_TAC o iffLR o SPEC_ALL) >>
        first_assum ACCEPT_TAC) >>
     `storage_well_formed_on cx (ed with scopes := [penv]) (FST H)` by
       (rewrite_tac[vyperFiniteStoragePreservationTheory.storage_well_formed_on_scopes] >>
        first_assum ACCEPT_TAC) >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
          (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
     `fmp_room ctx func u` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
          (ACCEPT_TAC o MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room)) >>
     `ghost_kept_at lo cenv es0 sa G0 tn0 s0 Gd tnd` by
       (qpat_assum `!G tn. ghost_kept_at lo (cenv_without_defaults cenv name) _ _ _ _ _ G tn = _`
          (fn th => once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     `!n b len aid off asz.
        local_region cenv ed.scopes u n b len /\
        FLOOKUP u.vs_allocas aid = SOME (off,asz) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
        regions_disjoint b len off asz` by
       (rpt strip_tac >> spose_not_then assume_tac >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
           (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
         qpat_x_assum `local_region _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[loweringStateRelDefsTheory.local_region_def]) >>
         qpat_x_assum `local_ptrs_rel _ _ _ _`
           (drule_all_then strip_assume_tac o cj 1 o
            REWRITE_RULE[loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
         qpat_x_assum `local_backed _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[loweringStateRelDefsTheory.local_backed_def])
         >- (rename1 `~regions_disjoint b len off asz` >>
             rename1 `FLOOKUP u.vs_allocas aid = SOME (off,asz)` >>
             rename1 `FLOOKUP u.vs_allocas backing.inst_id = SOME (w2n wb,len)` >>
             rename1 `b = w2n w` >>
             rename1 `backing.inst_outputs = [p]` >>
             `wb = w` by
               (qpat_assum `lookup_var p u = SOME wb` mp_tac >>
                qpat_assum `lookup_var p u = SOME w` (fn th => simp[NoAsms,th])) >>
             `FLOOKUP u.vs_allocas backing.inst_id = SOME (b,len)` by
               (qpat_assum `FLOOKUP u.vs_allocas backing.inst_id = SOME (w2n wb,len)` mp_tac >>
                qpat_assum `wb = w` (fn th => rewrite_tac[th]) >>
                qpat_assum `b = w2n w` (fn th => simp[NoAsms,GSYM th])) >>
             `aid = backing.inst_id` by
               (spose_not_then assume_tac >>
                qpat_assum `alloca_inv u`
                  (drule_all_then mp_tac o cj 1 o
                   REWRITE_RULE[venomMemDefsTheory.alloca_inv_def,
                                venomMemDefsTheory.allocas_non_overlapping_def]) >>
                qpat_assum `~regions_disjoint b len off asz`
                  (mp_tac o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def]) >>
                decide_tac) >>
             qpat_x_assum `aid = backing.inst_id` SUBST_ALL_TAC >>
             `not_fresh_at sa p` by
               (qpat_assum `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var p) len)` mp_tac >>
                qpat_assum `local_ptrs_reserved cenv sa`
                  (mp_tac o cj 2 o
                   REWRITE_RULE[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
                POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
             `~not_fresh_at sa p` suffices_by simp[] >>
             irule args_compile_expr_alloca_interval >>
             qexistsl_tac [`ann`,`cenv`,`dflt`,`es`,`func`,
                           `backing`,`name`,`sm`,`ty`,`vv`] >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_x_assum `!aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) ==> _`
           (drule_then mp_tac) >>
         rename1 `~regions_disjoint b len off asz` >>
         rename1 `b = w2n w` >>
         qmatch_goalsub_rename_tac `regions_disjoint (w2n wb) len off asz` >>
         map_every (fn q => qpat_assum q mp_tac)
           [`lookup_var p u = SOME w`, `lookup_var p u = SOME wb`,
            `b = w2n w`, `~regions_disjoint b len off asz`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
     `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee (bws ++ wd) u = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,nr,rr,name,args,(dflts : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
       (lbl' = lbl /\
        (has_rb <=> rc' = 0 /\ 0 < rbs) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP u.vs_labels "runtime_begin")) /\
        state_rel H func ce cx ((ed with scopes := [penv]) with scopes := []) u /\
        internal_immutable_regions ce cx (ed with scopes := [penv]) u.vs_alloca_next /\
        internal_args_rel ce params penv (if has_rb then 1 else 0) (bws ++ wd)
          u.vs_alloca_next u.vs_memory /\
        (!i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           ?aid off asz.
             FLOOKUP u.vs_allocas aid = SOME (off,asz) /\
             (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                    inst.inst_id = aid) /\
             sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
             off <= w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) /\
             w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) + psz <=
               off + asz) /\
        (has_rb ==> !i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           regions_disjoint (w2n (HD (bws ++ wd))) (type_memory_size rtv)
             (w2n (EL (1 + i) (bws ++ wd))) psz) /\
        (ce.ce_is_ctor ==> !i po psz nm tv iv io.
          i < LENGTH params /\ ~SND (EL i params) /\
          FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP (ed with scopes := [penv]).immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd))) psz) /\
        (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP (ed with scopes := [penv]).immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (HD (bws ++ wd))) (type_memory_size rtv)) /\
        u.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
        alloca_room ctx callee setup /\ fmp_room ctx callee setup) /\
       ((!mem. mem_agree_outside tnd.t_mem u.vs_memory mem ==>
           internal_args_rel ce params penv (if has_rb then 1 else 0) (bws ++ wd)
             u.vs_alloca_next mem) /\
        (!i off sz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
           ?b bsz aid.
             op_prov Gd (EL ((if has_rb then 1 else 0) + i) (bops ++ sup_ops ++ def_ops)) =
               SOME (b,bsz) /\
             FLOOKUP u.vs_allocas aid = SOME (b,bsz) /\
             sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
             lo <= b /\ b + bsz <= u.vs_alloca_next /\
             b <= w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) /\
             w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) + sz <= b + bsz) /\
        (has_rb ==>
         ?b bsz aid. op_prov Gd (HD (bops ++ sup_ops ++ def_ops)) = SOME (b,bsz) /\
           FLOOKUP u.vs_allocas aid = SOME (b,bsz) /\
           aid = sa.cs_next_id /\ aid < sm.cs_next_id /\
           lo <= b /\ b + bsz <= u.vs_alloca_next /\
           b <= w2n (HD (bws ++ wd)) /\
           w2n (HD (bws ++ wd)) + type_memory_size rtv <= b + bsz))` by
       (rpt gen_tac >> strip_tac >>
         `lbl' = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
                   cenv.ce_is_ctor /\
          has_rb = ((returns_stack_count
            (\k. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) k)) ret = 0) /\
            ret <> NoneT) /\
          params = ZIP (MAP FST args, compute_pass_via_stack (MAP SND args)
            (returns_stack_count
              (\k. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) k)) ret))` by
           (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
            simp[NoAsms,compileVyperTheory.package_internal_fn_def,
                 compileVyperTheory.set_internal_package_target_def] >> strip_tac >>
            rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (ACCEPT_TAC o SYM))) >>
         drule_then (assume_tac o cj 1) intcall_args_body_inv_function_tables >>
         `lbl' = lbl` by
           (qpat_assum `lbl' = internal_fn_label _ _ _ _` SUBST1_TAC >>
            qunabbrev_tac `lbl` >>
            qpat_assum `cenv.ce_func_ids = _` SUBST1_TAC >>
            qpat_assum `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = _`
              (fn th => rewrite_tac[th]) >>
            simp[NoAsms,nsid_to_string_def]) >>
         `compute_func_info
            (\k. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) k))
            ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret)
            (MAP SND args) = (rc',rbs,pvs)` by
           (qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _` mp_tac >>
            qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` (fn th => simp[NoAsms,th])) >>
         `rc' = returns_stack_count
            (\k. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) k)) ret` by
           (qpat_assum `compute_func_info _ _ _ _ = (rc',rbs,pvs)` mp_tac >>
            simp[NoAsms,compute_func_info_def]) >>
         `has_rb <=> rc' = 0 /\ 0 < rbs` by
           (`cenv.ce_struct_fields = make_struct_fields_map tops` by
              (drule_then ACCEPT_TAC intcall_args_body_inv_struct_fields) >>
            qpat_assum `has_rb = _` SUBST1_TAC >>
            qpat_assum `rc' = returns_stack_count _ _` (SUBST1_TAC o SYM) >>
            irule (cj 1 args_return_buffer_geometry) >>
            rpt (goal_assum (drule_at Any)) >> simp[]) >>
         `ce.ce_module = cenv.ce_module /\
          ce.ce_module_vars = cenv.ce_module_vars /\
          ce.ce_module_var_type = cenv.ce_module_var_type /\
          ce.ce_is_ctor = cenv.ce_is_ctor` by
           (qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
            qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp[compileVyperTheory.package_internal_fn_def,
                 compileVyperTheory.set_internal_package_target_def,
                 compileVyperTheory.update_cenv_nonreentrant_def] >> strip_tac >>
            qpat_assum `_ = ce` (SUBST1_TAC o SYM) >>
            disch_then (fn inv => map_every (fn th => assume_tac (MATCH_MP th inv))
              [intcall_args_body_inv_pins, intcall_args_body_inv_constructor]) >>
            fs[bodySimTheory.cenv_module_pins_def,
                 immutableLocationPropsTheory.build_compile_env_module_vars,
                 compileVyperTheory.build_compile_env_def] >>
            rpt (pairarg_tac >> simp[])) >>
         `ce.ce_is_ctor ==> IS_SOME (FLOOKUP u.vs_labels "runtime_begin")` by
           (qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
              (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_immutable_base_zero) >>
            simp[exprLoweringPropsTheory.immutable_base_zero_alt]) >>
         `state_rel H func ce cx (ed with scopes := []) u` by
           (qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
               (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
             disch_then (mp_tac o MATCH_MP stmtSimReturnTheory.state_rel_scopes_nil) >>
             strip_tac >> irule exprLoweringPropsTheory.state_rel_cenv_cong >>
             qexists `cenv` >> simp[vyperStateTheory.lookup_scopes_def]) >>
         `immutable_alloca_sep func cenv cx ed u` by
           (qpat_assum `stmt_state_rel H ctx func cenv cx ed u`
             (ACCEPT_TAC o MATCH_MP bodyFullIntCallReturnFrameTheory.return_stmt_immutable_sep)) >>
         `internal_immutable_regions ce cx (ed with scopes := [penv]) u.vs_alloca_next` by
           (rewrite_tac[intCallCalleeTheory.internal_immutable_regions_def] >>
             qpat_assum `ce.ce_module = cenv.ce_module` SUBST1_TAC >>
             qpat_assum `ce.ce_module_vars = cenv.ce_module_vars` SUBST1_TAC >>
             qpat_assum `ce.ce_module_var_type = cenv.ce_module_var_type` SUBST1_TAC >>
             qpat_assum `ce.ce_is_ctor = cenv.ce_is_ctor` SUBST1_TAC >>
             simp[NoAsms] >> disch_tac >> reverse conj_tac
             >- (rpt gen_tac >> strip_tac >>
                 dxrule_all (cj 1 immutableDeployAssignFactsTheory.immutable_assign_declared_region) >>
                 simp[NoAsms]) >>
             rpt gen_tac >> strip_tac >> reverse conj_tac
             >- (qpat_assum `immutable_alloca_sep func cenv cx ed u` mp_tac >>
                 simp[NoAsms,exprLoweringPropsTheory.immutable_alloca_sep_def] >>
                 strip_tac >> first_x_assum drule_all >> simp[NoAsms]) >>
             `state_well_typed ed` by
               (qpat_assum `expr_sim_inv cenv cx tenv ed` mp_tac >>
                simp[NoAsms,expr_sim_inv_def]) >>
             irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
             qpat_x_assum `FLOOKUP (case ALOOKUP ed.immutables _ of _ => _ | _ => _) _ = SOME _`
               mp_tac >>
             Cases_on `ALOOKUP ed.immutables cx.txn.target` >> simp[NoAsms] >> strip_tac >>
             drule_all vyperTypeEnvTheory.state_well_typed_immutables_ALOOKUP >> strip_tac >>
             drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >> simp[NoAsms]) >>
         `params = ZIP (MAP FST args,pvs)` by
           (qpat_assum `params = ZIP _` SUBST1_TAC >>
            qpat_assum `compute_func_info _ _ _ _ = (rc',rbs,pvs)` mp_tac >>
            simp[NoAsms,compute_func_info_def] >> strip_tac >> simp[]) >>
         `ALL_DISTINCT (MAP FST args)` by
           (`supported_program tops` by
              (drule_then ACCEPT_TAC (cj 1 bodyInvExecutionPropsTheory.body_inv_main_support)) >>
            qpat_assum `MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops`
              (mp_then Any mp_tac supportedProgramTheory.supported_program_function) >>
            simp[] >> metis_tac[supportedProgramTheory.supported_function_body_binding_contract]) >>
         `ce.ce_vars = FST (allocate_args (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY)` by
           (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp[compileVyperTheory.package_internal_fn_def,
                 compileVyperTheory.set_internal_package_target_def,
                 compileVyperTheory.update_cenv_nonreentrant_def] >> strip_tac >>
            qpat_assum `_ = ce` (SUBST1_TAC o SYM) >>
            simp[NoAsms,compileVyperTheory.build_compile_env_def] >>
            rpt (pairarg_tac >> simp[])) >>
         `MAP FST params = MAP FST args /\ LENGTH params = LENGTH args` by
           (qpat_assum `params = ZIP (MAP FST args,pvs)` SUBST1_TAC >>
            simp[listTheory.LENGTH_ZIP,vyperTypingTheory.MAP_FST_ZIP_MAP_FST]) >>
         `LENGTH wd = LENGTH args` by
           (qpat_assum `LENGTH wd = _` mp_tac >>
            qpat_assum `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)` mp_tac >>
            simp[NoAsms]) >>
         `LENGTH bws = if has_rb then 1 else 0` by
           (qpat_assum `has_rb <=> rc' = 0 /\ 0 < rbs` SUBST1_TAC >>
            Cases_on `rc' = 0 /\ 0 < rbs`
            >- (qpat_assum `rc' = 0 /\ 0 < rbs` strip_assume_tac >>
                qpat_assum `rc' = 0 /\ 0 < rbs ==> ?rb b. _` mp_tac >>
                (impl_tac >- first_assum ACCEPT_TAC) >>
                strip_tac >> simp[]) >>
            `rc' <> 0 \/ rbs = 0` by decide_tac >>
            qpat_assum `rc' <> 0 \/ rbs = 0 ==> bops = [] /\ bws = []` mp_tac >>
            (impl_tac >- simp[]) >>
            strip_tac >> simp[]) >>
         `!i. i < LENGTH params ==>
            FST (EL i params) = FST (EL i args) /\
            SND (EL i params) = EL i pvs /\
            EL ((if has_rb then 1 else 0) + i) (bws ++ wd) = EL i wd` by
           (rpt gen_tac >> strip_tac >>
            `i < LENGTH args` by (qpat_assum `LENGTH params = LENGTH args` (SUBST_ALL_TAC o SYM) >> simp[]) >>
            `EL i params = (FST (EL i args),EL i pvs)` by
              (qpat_assum `params = ZIP _` SUBST1_TAC >>
               simp[listTheory.EL_ZIP,listTheory.EL_MAP,
                    compileEnvTheory.LENGTH_compute_pass_via_stack]) >>
            simp[listTheory.EL_APPEND_EQN]) >>
         `cenv.ce_struct_fields = make_struct_fields_map tops` by
           (drule_then ACCEPT_TAC intcall_args_body_inv_struct_fields) >>
         `!i. i < LENGTH params ==>
            ?off tv.
              evaluate_type (get_tenv cx) (SND (EL i args)) = SOME tv /\
              FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off (type_memory_size tv)) /\
              FLOOKUP penv (FST (EL i params)) = SOME
                <|assignable := T; type := tv; value := EL i (xs ++ dvs); popped := []|>` by
           (rpt strip_tac >>
            `i < LENGTH args` by simp[] >>
            qpat_assum `bind_arguments _ _ _ = SOME penv`
              (mp_then Any mp_tac entryArgPtrsTheory.bind_arguments_lookup_index) >>
            disch_then (qspec_then `i` mp_tac) >> simp[] >>
            disch_then (qx_choose_then `tv` strip_assume_tac) >>
            `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) (SND (EL i args)) =
             type_memory_size tv` by
               (qpat_assum `expr_sim_inv cenv cx tenv ed`
                  (mp_then Any mp_tac expr_sim_inv_memory_size) >>
                disch_then (qspec_then `SND (EL i args)` mp_tac) >>
                simp[GSYM structFieldsPropsTheory.type_mem_bytes_type_memory_bytes]) >>
            qpat_assum `ALL_DISTINCT (MAP FST args)`
              (mp_then Any mp_tac entryStateRelTheory.allocate_args_lookup) >>
            disch_then (qspecl_then [`get_struct_fields (make_struct_fields_map tops)`, `0`, `FEMPTY`]
              (mp_tac o CONJUNCT2)) >>
            simp[Once listTheory.EVERY_EL] >> disch_then (qspec_then `i` mp_tac) >>
            simp[] >> metis_tac[]) >>
         qpat_x_assum `!j rt. j < LENGTH ([] ++ sup_ops ++ def_ops) /\ _ ==> _`
           (mp_tac o SRULE [listTheory.TAKE_DROP,listTheory.APPEND]) >>
         qpat_assum `get_tenv cxd = get_tenv cx` (fn th => simp[NoAsms,th,listTheory.EL_MAP]) >>
         strip_tac >>
         `!mem i. mem_agree_outside tnd.t_mem u.vs_memory mem /\ i < LENGTH params ==>
            ?off sz entry.
              FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) /\
              FLOOKUP penv (FST (EL i params)) = SOME entry /\
              type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
              if SND (EL i params) then
                32 <= sz /\ !b m. mem_word_at b m = EL ((if has_rb then 1 else 0) + i) (bws ++ wd) ==>
                     memory_value_rel entry.type entry.value b m
              else
                w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) + sz <= u.vs_alloca_next /\
                memory_value_rel entry.type entry.value
                  (w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd))) mem` by
           (rpt gen_tac >> strip_tac >>
            qpat_assum `!i. _ ==> ?off tv. _` (drule_then strip_assume_tac) >>
            qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _`
              (drule_then strip_assume_tac) >>
            `i < LENGTH args` by (qpat_assum `LENGTH params = LENGTH args` (SUBST_ALL_TAC o SYM) >> simp[]) >>
            `i < LENGTH def_ops + LENGTH sup_ops` by
              (qpat_assum `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)` mp_tac >>
               qpat_assum `i < LENGTH args` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
               simp[listTheory.LENGTH_APPEND] >> decide_tac) >>
            qpat_assum `!j rt. _ ==> value_has_type rt _ /\ _`
              (qspecl_then [`i`,`tv`] mp_tac) >>
            (impl_tac >- simp[listTheory.EL_MAP]) >> strip_tac >>
            qexistsl [`off`, `type_memory_size tv`,
              `<|assignable := T; type := tv; value := EL i (xs ++ dvs); popped := []|>`] >>
            simp[IgnAsm `params = ZIP _`, IgnAsm `pvs = compute_pass_via_stack _ _`] >>
            Cases_on `EL i pvs`
            >- (`is_word_type (SND (EL i args))` by
                  (qpat_assum `!j. j < LENGTH args /\ EL j pvs ==>
                                  is_word_type (EL j (MAP SND args))`
                     (qspec_then `i` mp_tac) >>
                   qpat_assum `i < LENGTH args` mp_tac >>
                   qpat_assum `EL i pvs` mp_tac >>
                   POP_ASSUM_LIST (K ALL_TAC) >> simp[listTheory.EL_MAP]) >>
                `type_memory_size tv = 32` by
                  (irule exprSimPropsTheory.word_tv_memory_size >>
                   qexistsl [`SND (EL i args)`, `get_tenv cx`] >> simp[]) >>
                simp[] >>
                rpt strip_tac >>
                irule memoryValueEncodingTheory.val_in_memory_memory_value_rel >>
                drule_all exprSimPropsTheory.val_in_memory_word >> simp[]) >>
            qpat_assum `~EL i pvs ==> ?b cap aid. _` (drule_then strip_assume_tac) >>
            qpat_assum `~EL i pvs` (fn th => simp[NoAsms,th]) >>
            conj_tac >- decide_tac >>
            irule memoryValueEncodingTheory.val_in_memory_memory_value_rel >>
            simp[]) >>
         `!j. j < LENGTH (sup_ops ++ def_ops) /\ ~EL j pvs ==>
              ?b cap aid. op_prov Gd (EL j (sup_ops ++ def_ops)) = SOME (b,cap) /\
                FLOOKUP u.vs_allocas aid = SOME (b,cap) /\
                sa.cs_next_id <= aid /\ aid < st3.cs_next_id /\ 32 <= cap /\
                ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                       inst.inst_id = aid` by
           (qpat_assum `!j. j < LENGTH ([] ++ sup_ops ++ def_ops) /\ _ ==> _`
              mp_tac >> simp[NoAsms,listTheory.TAKE_DROP]) >>
         `!i po psz.
            i < LENGTH params /\ ~SND (EL i params) /\
            FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
            ?off cap aid.
              op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (off,cap) /\
              FLOOKUP u.vs_allocas aid = SOME (off,cap) /\
              (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid) /\
              sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\ 32 <= cap /\
              lo <= off /\ off <= w2n (EL i wd) /\ psz + w2n (EL i wd) <= off + cap /\
              off + cap <= u.vs_alloca_next /\
              (case pin of NONE => T | SOME (rb,pb,pk) => off + cap <= pb \/ pb + pk <= off)` by
           (rpt gen_tac >> strip_tac >>
            qpat_assum `!i. _ ==> ?off tv. _`
              (drule_then (qx_choose_then `slot` (qx_choose_then `tv` strip_assume_tac))) >>
            `psz = type_memory_size tv` by
              (qpat_assum `FLOOKUP ce.ce_vars _ = SOME (MemLoc po psz)` mp_tac >>
               qpat_assum `FLOOKUP ce.ce_vars _ = SOME (MemLoc slot (type_memory_size tv))`
                 (fn th => simp[NoAsms,th])) >>
            qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _`
              (drule_then strip_assume_tac) >>
            `~EL i pvs` by
              (qpat_assum `~SND (EL i params)` mp_tac >>
               qpat_assum `SND (EL i params) = EL i pvs` (fn th => simp[NoAsms,th])) >>
            `i < LENGTH (sup_ops ++ def_ops) /\ i < LENGTH args` by
              (map_every (fn tm => qpat_assum tm mp_tac)
                [`i < LENGTH params`, `LENGTH params = LENGTH args`,
                 `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)`] >>
               POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> decide_tac) >>
            qpat_assum `!j rt. _ ==> value_has_type rt _ /\ _`
              (qspecl_then [`i`,`tv`] mp_tac) >>
            (impl_tac >-
              (conj_tac
               >- (qpat_assum `i < LENGTH (sup_ops ++ def_ops)` mp_tac >>
                   POP_ASSUM_LIST (K ALL_TAC) >> simp[listTheory.LENGTH_APPEND] >> decide_tac) >>
               simp[listTheory.EL_MAP])) >> strip_tac >>
            qpat_assum `~EL i pvs ==> ?b cap aid. _`
              (drule_then (qx_choose_then `b` (qx_choose_then `k` (qx_choose_then `a` strip_assume_tac)))) >>
            qpat_assum `!j. j < LENGTH (sup_ops ++ def_ops) /\ _ ==> _`
              (qspecl_then [`i`] mp_tac) >>
            (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
            disch_then (qx_choose_then `b'` (qx_choose_then `k'` (qx_choose_then `a'` strip_assume_tac))) >>
            `b' = b /\ k' = k` by
              (qpat_assum `op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (b',k')` mp_tac >>
               qpat_assum `op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (b,k)`
                 (fn th => simp[NoAsms,th])) >>
            qpat_x_assum `b' = b` SUBST_ALL_TAC >> qpat_x_assum `k' = k` SUBST_ALL_TAC >>
            `a' < sm.cs_next_id` by
              (qpat_assum `a' < st3.cs_next_id` mp_tac >>
               qpat_assum `st3.cs_next_id <= sm.cs_next_id` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
            qexistsl [`b`,`k`,`a'`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- (qmatch_asmsub_rename_tac `site.inst_id = a'` >>
                qexists_tac `site` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
            qpat_assum `psz = type_memory_size tv` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         `!i po psz.
            i < LENGTH params /\ ~SND (EL i params) /\
            FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
            ?aid off asz. FLOOKUP u.vs_allocas aid = SOME (off,asz) /\
              (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid) /\
              sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
              off <= w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) /\
              psz + w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) <= asz + off` by
           (rpt gen_tac >> strip_tac >>
            qpat_assum `!i po psz. _ ==> ?off cap aid. _` (drule_all_then strip_assume_tac) >>
            qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _` (drule_then strip_assume_tac) >>
            qexistsl [`aid`,`off`,`cap`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- (qmatch_asmsub_rename_tac `site.inst_id = aid` >>
                qexists_tac `site` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
            qpat_assum `EL ((if has_rb then 1 else 0) + i) (bws ++ wd) = EL i wd` SUBST1_TAC
            >- first_assum ACCEPT_TAC >>
            qpat_assum `psz + w2n (EL i wd) <= off + cap` mp_tac >>
            simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
         `alloca_room ctx func u` by
           (drule stateRelProjTheory.stmt_state_rel_alloca_room >> simp[]) >>
         `!nm off sz. MEM nm (MAP FST params) /\
            FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==> sz < dimword (:256)` by
           (rpt gen_tac >> strip_tac >>
            qpat_assum `MEM nm (MAP FST params)` (mp_tac o ONCE_REWRITE_RULE [listTheory.MEM_EL]) >>
            disch_then (qx_choose_then `i` strip_assume_tac) >>
            `i < LENGTH params` by
              (qpat_assum `i < LENGTH (MAP FST params)` mp_tac >> simp[NoAsms]) >>
            `nm = FST (EL i params)` by
              (qpat_assum `nm = EL i (MAP FST params)` mp_tac >>
               qpat_assum `i < LENGTH params`
                 (fn th => simp[NoAsms,listTheory.EL_MAP,th])) >>
            qpat_x_assum `nm = FST (EL i params)` SUBST_ALL_TAC >>
            qpat_assum `!i. i < LENGTH params ==> ?off tv.
                 evaluate_type (get_tenv cx) (SND (EL i args)) = SOME tv /\ _`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            disch_then (qx_choose_then `slot` (qx_choose_then `tv` strip_assume_tac)) >>
            `sz = type_memory_size tv` by
              (qpat_assum `FLOOKUP ce.ce_vars _ = SOME (MemLoc off sz)` mp_tac >>
               qpat_assum `FLOOKUP ce.ce_vars _ = SOME (MemLoc slot (type_memory_size tv))`
                 (fn th => simp[NoAsms,th])) >>
            qpat_x_assum `sz = type_memory_size tv` SUBST_ALL_TAC >>
            `i < LENGTH args` by simp[] >>
            `type_memory_bytes cenv (SND (EL i args)) = type_memory_size tv` by
              (irule expr_sim_inv_memory_size >> qexistsl_tac [`cx`,`tenv`,`ed`] >>
               rpt conj_tac >> first_assum ACCEPT_TAC) >>
            qpat_assum `EVERY (\t. type_memory_bytes cenv t < 2 ** 64) (MAP SND args)` mp_tac >>
            rewrite_tac[listTheory.EVERY_EL,listTheory.LENGTH_MAP] >>
            disch_then (qspec_then `i` mp_tac) >>
            simp[NoAsms,listTheory.EL_MAP] >>
            qpat_assum `type_memory_bytes cenv (SND (EL i args)) = _` (fn th => simp[th]) >>
            simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV (Term `dimindex (:256)`)] >>
            decide_tac) >>
         `MEM ii (fn_insts func)` by
           (drule_all fragFuelTheory.lookup_block_get_instruction_fn_insts >> simp[]) >>
         `cx.in_deploy = cenv.ce_is_ctor` by
           (drule_then ACCEPT_TAC intcall_args_body_inv_constructor) >>
         `lbl = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
                 cx.in_deploy` by
           (qpat_assum `lbl' = internal_fn_label _ _ _ _` mp_tac >>
            qpat_assum `lbl' = lbl` (fn th => rewrite_tac[th]) >>
            qpat_assum `cx.in_deploy = cenv.ce_is_ctor` (fn th => rewrite_tac[th])) >>
         `ALL_DISTINCT (MAP FST params)` by
           (qpat_assum `MAP FST params = MAP FST args` SUBST1_TAC >>
            first_assum ACCEPT_TAC) >>
         `u.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
          alloca_room ctx callee setup /\ fmp_room ctx callee setup` by
           (qpat_assum `lbl = internal_fn_label _ _ _ _` SUBST_ALL_TAC >>
            drule_all args_callee_package_room >>
            simp[]) >>
         `has_rb ==> ?rb b. bops = [rb.buf_operand] /\ bws = [n2w b] /\
           op_prov Gd rb.buf_operand = SOME (b,rb.buf_size) /\
           FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,rb.buf_size) /\
           sa.cs_next_id < sm.cs_next_id /\ lo <= b /\
           b + rb.buf_size <= u.vs_alloca_next /\ w2n (HD (bws ++ wd)) = b /\
           type_memory_size rtv = rb.buf_size /\
           (?q. pin = SOME (q,b,rb.buf_size)) /\
           (?inst. MEM inst (fn_insts func) /\
              inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id)` by
           (disch_tac >>
            `rc' = 0 /\ 0 < rbs` by
              (qpat_assum `has_rb <=> rc' = 0 /\ 0 < rbs`
                (MATCH_MP_TAC o iffLR) >> first_assum ACCEPT_TAC) >>
            qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q b.
                 compile_alloc_buffer buf_n sa = (rb,st2) /\ rb.buf_operand = Var q /\
                 rb.buf_size = buf_n /\ pin = SOME (q,b,buf_n) /\ _` mp_tac >>
            (impl_tac >- (disj2_tac >> first_assum ACCEPT_TAC)) >>
            disch_then (qx_choose_then `rb` (qx_choose_then `q`
              (qx_choose_then `b` strip_assume_tac))) >>
            `buf_n = rbs` by (simp[Abbr `buf_n`]) >>
            qpat_assum `rc' = 0 /\ 0 < rbs ==> ?rbuf b. compile_alloc_buffer rbs sa = (rbuf,st2) /\
                       bops = [rbuf.buf_operand] /\ bws = [n2w b] /\ _` mp_tac >>
            (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
            disch_then (qx_choose_then `rbuf` (qx_choose_then `b'` strip_assume_tac)) >>
            `rbuf = rb` by
              (qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
               qpat_assum `buf_n = rbs` SUBST1_TAC >>
               qpat_assum `compile_alloc_buffer rbs sa = (rbuf,st2)` (fn th => simp[NoAsms,th])) >>
            qpat_x_assum `rbuf = rb` SUBST_ALL_TAC >>
            `b' = b` by
              (qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b',rb.buf_size)` mp_tac >>
               qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,buf_n)`
                 (fn th => simp[NoAsms,th])) >>
            qpat_x_assum `b' = b` SUBST_ALL_TAC >>
            `rbs = type_memory_size rtv` by
              (irule (cj 2 args_return_buffer_geometry) >>
               conj_tac >- first_assum ACCEPT_TAC >>
               qexistsl_tac [`cenv`,`cx`,`tenv`,`es0`,`rc'`,`pvs`,`ret`,`tops`,`MAP SND args`] >>
               rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               qpat_assum `compute_func_info _ _ _ _ = (rc',rbs,pvs)` ACCEPT_TAC) >>
            `b < dimword (:256)` by
              (qpat_assum `alloca_room ctx func u`
                 (mp_tac o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt) >>
               qpat_assum `b + rb.buf_size <= u.vs_alloca_next` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
            qexistsl [`rb`,`b`] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- simp[wordsTheory.w2n_n2w]
            >- simp[]
            >- (qexists_tac `q` >> simp[]) >>
            drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
            disch_then (qx_choose_then `outvar` strip_assume_tac) >>
            qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)] [outvar]` >>
            conj_tac >- first_assum ACCEPT_TAC >>
            simp[NoAsms,venomInstTheory.mk_inst_def]) >>
         `has_rb ==> !i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           regions_disjoint (w2n (HD (bws ++ wd))) (type_memory_size rtv)
             (w2n (EL (1 + i) (bws ++ wd))) psz` by
           (disch_tac >> rpt gen_tac >> strip_tac >>
             qpat_assum `has_rb ==> ?rb b. bops = [_] /\ _`
               (drule_then (qx_choose_then `rb` (qx_choose_then `b` strip_assume_tac))) >>
             qpat_assum `!i po psz. _ ==> ?off cap aid. op_prov _ _ = _ /\ _`
               (drule_all_then (qx_choose_then `off` (qx_choose_then `cap` (qx_choose_then `aid` strip_assume_tac)))) >>
             qpat_assum `!i. i < LENGTH params ==> FST (EL i params) = _ /\ _`
               (drule_then strip_assume_tac) >>
             `EL (1 + i) (bws ++ wd) = EL i wd` by
               (qpat_assum `EL ((if has_rb then 1 else 0) + i) (bws ++ wd) = EL i wd`
                 mp_tac >> qpat_assum `has_rb` (fn th => simp[NoAsms,th])) >>
             qpat_assum `w2n (HD (bws ++ wd)) = b` SUBST1_TAC >>
             qpat_assum `type_memory_size rtv = rb.buf_size` SUBST1_TAC >>
             qpat_assum `EL (1 + i) (bws ++ wd) = EL i wd` SUBST1_TAC >>
             qpat_assum `case pin of NONE => T | SOME (pname,pbase,plen) => _` mp_tac >>
             qpat_assum `pin = SOME (_,b,rb.buf_size)` (fn th => rewrite_tac[th]) >>
             simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def] >>
             qpat_assum `off <= w2n (EL i wd)` mp_tac >>
             qpat_assum `psz + w2n (EL i wd) <= off + cap` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
         `ce.ce_is_ctor ==> !i po psz nm tv iv io.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
           FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
           FLOOKUP (case ALOOKUP ed.immutables cx.txn.target of NONE => FEMPTY
                     | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) ==>
           regions_disjoint io (type_memory_size tv)
             (w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd))) psz` by
           (disch_tac >> rpt gen_tac >> strip_tac >>
             qpat_assum `!i po psz. _ ==> ?aid off asz. FLOOKUP u.vs_allocas aid = _ /\ _`
               (drule_all_then (qx_choose_then `aid` (qx_choose_then `b` (qx_choose_then `cap` strip_assume_tac)))) >>
             qpat_assum `FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io)`
               (fn ath => qpat_assum `ce.ce_module = cenv.ce_module` (fn module =>
                  qpat_assum `ce.ce_module_vars = cenv.ce_module_vars` (fn vars =>
                    assume_tac (REWRITE_RULE[module,vars] ath)))) >>
             qpat_assum `FLOOKUP (case ALOOKUP _ cx.txn.target of _ => _ | _ => _) nm = SOME (tv,iv)`
               (fn ath => qpat_assum `ce.ce_module = cenv.ce_module`
                   (fn th => assume_tac (SIMP_RULE (srw_ss()) [th] ath))) >>
             qpat_assum `ce.ce_is_ctor = cenv.ce_is_ctor`
               (fn th => qpat_assum `ce.ce_is_ctor` (assume_tac o REWRITE_RULE [th])) >>
             qmatch_asmsub_rename_tac `alloc.inst_id = aid` >>
             `FLOOKUP u.vs_allocas alloc.inst_id = SOME (b,cap)` by
               (qpat_assum `alloc.inst_id = aid` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
             `w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) + psz <= b + cap` by
               (qpat_assum `psz + w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) <= cap + b`
                  mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
             drule_all args_immutable_subwindow >>
             simp[NoAsms]) >>
         `has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
           FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
           FLOOKUP (case ALOOKUP ed.immutables cx.txn.target of NONE => FEMPTY
                     | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) ==>
           regions_disjoint io (type_memory_size tv)
             (w2n (HD (bws ++ wd))) (type_memory_size rtv)` by
           (strip_tac >> rpt gen_tac >> strip_tac >>
            qpat_assum `has_rb ==> ?rb b. bops = [_] /\ _`
              (drule_then (qx_choose_then `rb` (qx_choose_then `b` strip_assume_tac))) >>
            qpat_assum `FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io)`
              (fn ath => qpat_assum `ce.ce_module = cenv.ce_module` (fn module =>
                 qpat_assum `ce.ce_module_vars = cenv.ce_module_vars` (fn vars =>
                   assume_tac (REWRITE_RULE[module,vars] ath)))) >>
            qpat_assum `FLOOKUP (case ALOOKUP ed.immutables cx.txn.target of _ => _ | _ => _) nm =
                          SOME (tv,iv)`
              (fn ath => qpat_assum `ce.ce_module = cenv.ce_module`
                (fn th => assume_tac (REWRITE_RULE[th] ath))) >>
            qpat_assum `ce.ce_is_ctor = cenv.ce_is_ctor`
              (fn th => qpat_assum `ce.ce_is_ctor` (assume_tac o REWRITE_RULE [th])) >>
            qmatch_asmsub_rename_tac `alloc.inst_id = sa.cs_next_id` >>
            `FLOOKUP u.vs_allocas alloc.inst_id = SOME (b,rb.buf_size)` by
              (qpat_assum `alloc.inst_id = sa.cs_next_id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
            qpat_assum `w2n (HD (bws ++ wd)) = b` SUBST1_TAC >>
            qpat_assum `type_memory_size rtv = rb.buf_size` SUBST1_TAC >>
            mp_tac (Q.INST [`func` |-> `func`, `ce` |-> `cenv`, `cx` |-> `cx`,
              `es` |-> `ed`, `u` |-> `u`, `nm` |-> `nm`, `io` |-> `io`,
              `tv` |-> `tv`, `iv` |-> `iv`, `inst` |-> `alloc`, `b` |-> `b`,
              `cap` |-> `rb.buf_size`, `sz` |-> `rb.buf_size`, `w` |-> `b`]
              args_immutable_subwindow) >>
            (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms])) >>
            disch_then ACCEPT_TAC) >>
         `u.vs_alloca_next < dimword (:256)` by
           (drule_then ACCEPT_TAC exprLoweringPropsTheory.alloca_room_next_lt) >>
         `!i j b k c l. i < j /\ j < LENGTH pvs /\ ~EL i pvs /\ ~EL j pvs /\
             op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (b,k) /\
             op_prov Gd (EL j (sup_ops ++ def_ops)) = SOME (c,l) ==>
             regions_disjoint b k c l` by
           (qpat_assum `!i j b k c l. _ ==> regions_disjoint b k c l` mp_tac >>
            qpat_assum `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)` (mp_tac o GSYM) >>
            qpat_assum `pvs = compute_pass_via_stack _ _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp[listTheory.TAKE_DROP,compileEnvTheory.LENGTH_compute_pass_via_stack]) >>
         `LENGTH (bws ++ wd) < dimword (:256)` by
           (irule args_vector_bound_sites >>
            (conj_tac >- (Cases_on `has_rb` >> simp[])) >>
            qexistsl_tac [`Gd`,`pvs`,`u.vs_alloca_next`,`rc'`,`sup_ops ++ def_ops`,`MAP SND args`] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            TRY (qmatch_goalsub_rename_tac `LENGTH wd = LENGTH pvs` >>
                 simp[compileEnvTheory.LENGTH_compute_pass_via_stack] >> NO_TAC ORELSE all_tac) >>
            rpt gen_tac >> strip_tac >>
            `i < LENGTH (sup_ops ++ def_ops)` by
              (qpat_assum `i < LENGTH pvs` mp_tac >>
               qpat_assum `LENGTH (MAP SND args) = LENGTH (sup_ops ++ def_ops)` (mp_tac o GSYM) >>
               qpat_assum `pvs = compute_pass_via_stack _ _` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               simp[compileEnvTheory.LENGTH_compute_pass_via_stack]) >>
            qpat_assum `!j. j < LENGTH (sup_ops ++ def_ops) /\ _ ==> _`
              (drule_all_then strip_assume_tac) >>
            `MEM (SOME (b,cap)) (MAP (op_prov Gd) (sup_ops ++ def_ops))` by
              (once_rewrite_tac[MEM_EL] >> rewrite_tac[LENGTH_MAP] >>
               qexists_tac `i` >> conj_tac >- first_assum ACCEPT_TAC >>
               qpat_assum `i < LENGTH (sup_ops ++ def_ops)`
                 (fn th => simp_tac bool_ss [EL_MAP,th]) >>
               first_assum (ACCEPT_TAC o SYM)) >>
            qpat_assum `!b cap. MEM (SOME (b,cap)) (MAP (op_prov Gd) (sup_ops ++ def_ops)) ==> _`
              (drule_then strip_assume_tac) >>
            qexistsl_tac [`b`,`cap`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
         `!mem. mem_agree_outside tnd.t_mem u.vs_memory mem ==>
            internal_args_rel ce params penv (if has_rb then 1 else 0) (bws ++ wd)
              u.vs_alloca_next mem` by
           (gen_tac >> disch_tac >> rewrite_tac[intCallCalleeTheory.internal_args_rel_def] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- (qpat_assum `MAP FST params = MAP FST args` SUBST1_TAC >>
                drule_then ACCEPT_TAC vyperCallTheory.bind_arguments_fdom)
            >- (qpat_assum `LENGTH bws = _` (SUBST1_TAC o SYM) >> simp[LENGTH_APPEND])
            >- (rpt gen_tac >> disch_tac >>
                qpat_assum `!mem i. _ ==> ?off sz entry. _`
                  (qspecl_then [`mem`,`i`] mp_tac) >>
                (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
            `!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
               FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
               ?b cap. op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (b,cap) /\
                b <= w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) /\
                w2n (EL ((if has_rb then 1 else 0) + i) (bws ++ wd)) + sz <= b + cap` by
              (rpt gen_tac >> strip_tac >>
               qpat_assum `!i po psz. _ ==> ?off cap aid. op_prov _ _ = _ /\ _`
                 (drule_all_then (qx_choose_then `b` (qx_choose_then `cap`
                   (qx_choose_then `aid` strip_assume_tac)))) >>
               qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _` (drule_then strip_assume_tac) >>
               qexistsl_tac [`b`,`cap`] >>
               qpat_assum `EL ((if has_rb then 1 else 0) + i) (bws ++ wd) = EL i wd`
                 (fn th => simp[NoAsms,th,arithmeticTheory.ADD_COMM]) >>
               rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
                 (qpat_assum `sz + w2n (EL i wd) <= _` mp_tac >>
                  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac))) >>
            `!i j b cap c len. i < j /\ j < LENGTH params /\
               ~SND (EL i params) /\ ~SND (EL j params) /\
               op_prov Gd (EL i (sup_ops ++ def_ops)) = SOME (b,cap) /\
               op_prov Gd (EL j (sup_ops ++ def_ops)) = SOME (c,len) ==>
               regions_disjoint b cap c len` by
              (rpt gen_tac >> strip_tac >> `i < LENGTH params` by decide_tac >>
               qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _`
                 (qspecl_then [`i`] mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
               qpat_assum `!i. _ ==> FST (EL i params) = _ /\ _`
                 (qspecl_then [`j`] mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
               qpat_assum `!i j b k c l. i < j /\ j < LENGTH pvs /\ _ ==> _`
                 (qspecl_then [`i`,`j`,`b`,`cap`,`c`,`len`] mp_tac) >>
               (impl_tac >-
                 (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
                  >- simp[compileEnvTheory.LENGTH_compute_pass_via_stack]
                  >- (qpat_assum `SND (EL i params) = EL i pvs` (SUBST1_TAC o SYM) >>
                      first_assum ACCEPT_TAC) >>
                  qpat_assum `SND (EL j params) = EL j pvs` (SUBST1_TAC o SYM) >>
                  first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
            MATCH_MP_TAC (Q.SPECL [`Gd`, `sup_ops ++ def_ops`]
              args_internal_regions_separate) >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         conj_tac
         >- (
         rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
                           (simp[NoAsms] >> first_assum ACCEPT_TAC))) >>
         conj_tac >- (first_assum irule >> simp[mem_agree_outside_def]) >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_assum `!i po psz. _ ==> ?aid off asz. FLOOKUP u.vs_allocas aid = _ /\ _`
               (drule_all_then (qx_choose_then `aid` (qx_choose_then `off` (qx_choose_then `asz`
                 strip_assume_tac)))) >>
             qexistsl [`aid`,`off`,`asz`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
             >- (qmatch_asmsub_rename_tac `site.inst_id = aid` >>
                 qexists_tac `site` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
             `i + (if has_rb then 1 else 0) = (if has_rb then 1 else 0) + i` by
               rewrite_tac[Once arithmeticTheory.ADD_COMM] >>
             qpat_assum `i + (if has_rb then 1 else 0) = _` SUBST1_TAC >>
             first_assum ACCEPT_TAC) >>
         conj_tac
         >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
         conj_tac
         >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
             qpat_assum `ce.ce_is_ctor ==> !i po psz nm tv iv io. _` mp_tac >>
             simp[NoAsms]) >>
         conj_tac
         >- (qpat_assum `has_rb /\ ce.ce_is_ctor ==> !nm tv iv io. _` mp_tac >>
             simp[NoAsms]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_assum `!i po psz. _ ==> ?off cap aid. op_prov _ _ = _ /\ _`
               (drule_all_then
                 (qx_choose_then `b` (qx_choose_then `cap` (qx_choose_then `aid` strip_assume_tac)))) >>
             `LENGTH bops = LENGTH bws` by
               (map_every (fn t => qpat_assum t
                  (mp_tac o MATCH_MP tupleLoadPropsTheory.eval_operands_length))
                 [`eval_operands (bops ++ sup_ops ++ def_ops) u = SOME (bws ++ wd)`,
                  `eval_operands (sup_ops ++ def_ops) u = SOME wd`] >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[listTheory.LENGTH_APPEND]) >>
             `LENGTH bops = if has_rb then 1 else 0` by
               (qpat_assum `LENGTH bops = LENGTH bws` SUBST1_TAC >>
                first_assum ACCEPT_TAC) >>
             `EL (i + (if has_rb then 1 else 0)) (bops ++ sup_ops ++ def_ops) =
               EL i (sup_ops ++ def_ops)` by
               (qpat_assum `LENGTH bops = _` (SUBST1_TAC o SYM) >>
                once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
                simp_tac (srw_ss() ++ numSimps.ARITH_ss) [rich_listTheory.EL_APPEND2]) >>
             qpat_assum `!i. i < LENGTH params ==> FST (EL i params) = _ /\ _`
               (drule_then strip_assume_tac) >>
             `EL (i + (if has_rb then 1 else 0)) (bws ++ wd) = EL i wd` by
               (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
             qexistsl [`b`,`cap`,`aid`] >>
             qpat_assum `EL _ (bops ++ sup_ops ++ def_ops) = EL i (sup_ops ++ def_ops)` SUBST1_TAC >>
             qpat_assum `EL (i + _) (bws ++ wd) = EL i wd` SUBST1_TAC >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             qpat_assum `sz + w2n (EL i wd) <= b + cap` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
         disch_tac >>
         qpat_assum `has_rb ==> ?rb b. bops = [_] /\ _`
           (drule_then (qx_choose_then `rb` (qx_choose_then `b` strip_assume_tac))) >>
         qexistsl [`b`,`rb.buf_size`] >>
         qpat_assum `bops = [rb.buf_operand]` SUBST1_TAC >>
         qpat_assum `w2n (HD (bws ++ wd)) = b` SUBST1_TAC >>
         qpat_assum `type_memory_size rtv = rb.buf_size` SUBST1_TAC >>
         simp[arithmeticTheory.ADD_COMM]) >>
     rewrite_tac[intcall_entry_full_def] >>
     qpat_assum `((ed with scopes := [penv]) with scopes := ed.scopes) = ed`
       (fn th => rewrite_tac[th]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexistsl_tac [`dflts`,`es0 with gas_obs := gas_explicit marks entry.vs_gas_readings ++ []`,
                       `xs`,`ee with gas_obs := []`,
                       `ee with gas_obs := gas_explicit dm t.vs_gas_readings`,
                       `dvs`,`(ed with gas_obs := []) with scopes := [FEMPTY]`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_assum `Abbrev (raw_ds = _)`
            (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          qunabbrev_tac `cxd` >> first_assum ACCEPT_TAC)
     >- (qexistsl_tac [`st2`,`sup_ops`,`st2a`,`def_ops`,`sup_ops ++ def_ops`,`st3`,
                       `rc'`,`rbs`,`pvs`,`lbl`,`bops ++ sup_ops ++ def_ops`,`ibb`,`ii`,`bws ++ wd`] >>
         `LENGTH es + LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) = LENGTH args` by
           (qpat_assum `LENGTH (omitted_defaults _ _ _) = _` mp_tac >>
            qpat_assum `LENGTH es <= LENGTH args` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
         `omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) = ds` by
           (qpat_assum `omitted_defaults _ _ _ = DROP _ compiled_dflts` mp_tac >>
            qpat_assum `ds = DROP _ compiled_dflts` (fn th => simp[NoAsms,th])) >>
         qpat_assum `LENGTH es + LENGTH (omitted_defaults _ _ _) = LENGTH args`
           (fn th => rewrite_tac[th]) >>
         qpat_assum `omitted_defaults _ _ _ = ds` (fn th => rewrite_tac[th]) >>
         `lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
                  (nsid_to_string (NONE,name))
                  (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor` by
           (qunabbrev_tac `lbl` >> REFL_TAC) >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >~ [`rc' = 0 /\ rbs = 0 ==> _`]
         >- (strip_tac >>
             qpat_assum `rc' = 0 /\ rbs = 0 ==> ?e. st2 = sa /\ _`
               (drule_all_then strip_assume_tac) >>
             qpat_assum `(rc' <> 0 \/ rbs = 0) ==> bops = [] /\ bws = []` mp_tac >>
             (impl_tac >- (disj2_tac >> first_assum ACCEPT_TAC)) >>
             disch_then (SUBST1_TAC o CONJUNCT1) >>
             rewrite_tac[listTheory.APPEND] >> rpt conj_tac >>
             TRY (first_assum ACCEPT_TAC) >> goal_assum (drule_at Any))
         >- (disch_tac >>
             qpat_assum `0 < rc' \/ 0 < rbs ==> ?rb q b.
                 compile_alloc_buffer buf_n sa = (rb,st2) /\ _`
               (drule_then (qx_choose_then `rb` (qx_choose_then `q`
                 (qx_choose_then `b` strip_assume_tac)))) >>
             `vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
                     (base_ptr rb)` by
               (qpat_assum `!rb. (0 < rc' \/ 0 < rbs) /\ _ ==> _`
                  (irule) >> conj_tac >> first_assum ACCEPT_TAC) >>
             Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
               `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                       inst.inst_id = sa.cs_next_id`
             >- (drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
                 disch_then (qx_choose_then `outvar` strip_assume_tac) >>
                 qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf_n)] [outvar]` >>
                 conj_tac >- first_assum ACCEPT_TAC >>
                 simp[NoAsms,venomInstTheory.mk_inst_def]) >>
             qpat_assum `Abbrev (buf_n = _)`
               (fn th => rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
             qexistsl_tac [`rb`,`sa.cs_next_id`,`b`] >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             TRY (qpat_assum `rb.buf_operand = Var q` (fn th => rewrite_tac[th]) >>
                  first_assum ACCEPT_TAC >> NO_TAC ORELSE all_tac) >>
             TRY (qpat_assum `rb.buf_size = buf_n` (fn th => rewrite_tac[th]) >>
                  first_assum ACCEPT_TAC) >>
             TRY (simp[NoAsms] >> NO_TAC)
             >~ [`0 < rc' ==> _`]
             >- (disch_tac >>
                 qpat_assum `0 < rc' ==> ?b r m e. compile_alloc_buffer _ sa = (b,st2) /\
                              emit_multi_op INVOKE _ rc' st3 = (r,m) /\ _`
                   (drule_then (qx_choose_then `rbuf` (qx_choose_then `results`
                     (qx_choose_then `mid` (qx_choose_then `ignored` strip_assume_tac))))) >>
                 `rbuf = rb` by
                   (qpat_assum `compile_alloc_buffer (32 * rc') sa = (rbuf,st2)` mp_tac >>
                    qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
                    qunabbrev_tac `buf_n` >> simp[NoAsms] >>
                    qpat_assum `0 < rc'` (fn th => simp[NoAsms,th])) >>
                 qpat_assum `(rc' <> 0 \/ rbs = 0) ==> bops = [] /\ bws = []` mp_tac >>
                 (impl_tac >- (disj1_tac >> qpat_assum `0 < rc'` mp_tac >> decide_tac)) >>
                 disch_then (SUBST1_TAC o CONJUNCT1) >> rewrite_tac[listTheory.APPEND] >>
                 qexistsl_tac [`results`,`mid`,`ignored`] >>
                 qpat_assum `rbuf = rb` (SUBST1_TAC o SYM) >>
                 conj_tac >> first_assum ACCEPT_TAC) >>
             disch_tac >>
             `rc' = 0 /\ 0 < rbs` by
               (qpat_assum `rc' = 0` mp_tac >>
                qpat_assum `0 < rc' \/ 0 < rbs` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
             `buf_n = rbs` by
               (qpat_assum `rc' = 0` (fn th => simp[NoAsms,Abbr `buf_n`,th])) >>
             `!rbuf. compile_alloc_buffer rbs sa = (rbuf,st2) ==> rbuf = rb` by
               (gen_tac >> qpat_assum `compile_alloc_buffer buf_n sa = (rb,st2)` mp_tac >>
                qpat_assum `buf_n = rbs` (fn th => rewrite_tac[th]) >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
             qpat_assum `rc' = 0 /\ 0 < rbs ==> ?p off. compile_alloc_buffer rbs sa = (p,st2) /\
                          bops = [p.buf_operand] /\ _`
               (drule_all_then (qx_choose_then `p` (qx_choose_then `off` strip_assume_tac))) >>
             `p = rb` by (first_assum irule >> first_assum ACCEPT_TAC) >>
             qpat_x_assum `p = rb` SUBST_ALL_TAC >>
             `off = b` by
               (qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (off,rb.buf_size)` mp_tac >>
                qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,buf_n)`
                  (fn th => simp[NoAsms,th])) >>
             qpat_x_assum `off = b` SUBST_ALL_TAC >>
             qpat_assum `rc' = 0 /\ 0 < rbs ==> ?rbuf e. compile_alloc_buffer rbs sa = (rbuf,st2) /\
                          emit_void INVOKE _ st3 = (e,sm) /\ _`
               (drule_all_then (qx_choose_then `rbuf` (qx_choose_then `ignored` strip_assume_tac))) >>
             `rbuf = rb` by (first_assum irule >> first_assum ACCEPT_TAC) >>
             qpat_x_assum `rbuf = rb` SUBST_ALL_TAC >>
             `cenv.ce_struct_fields = make_struct_fields_map tops` by
               (drule_then ACCEPT_TAC intcall_args_body_inv_struct_fields) >>
             `rbs = type_memory_size rtv` by
               (irule (cj 2 args_return_buffer_geometry) >>
                conj_tac >- first_assum ACCEPT_TAC >>
                qexistsl_tac [`cenv`,`cx`,`tenv`,`es0`,`rc'`,`pvs`,`ret`,`tops`,`MAP SND args`] >>
                rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _` mp_tac >>
                qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` (fn th => simp[NoAsms,th])) >>
             qpat_assum `bops = [rb.buf_operand]` SUBST1_TAC >>
             qpat_assum `bws = [n2w b]` SUBST1_TAC >>
             simp[NoAsms,listTheory.APPEND,listTheory.HD] >> rpt conj_tac
             >- (qpat_assum `emit_void INVOKE _ st3 = (ignored,sm)` mp_tac >> simp[NoAsms])
             >- (qpat_assum `rbs = type_memory_size rtv` (SUBST1_TAC o SYM) >>
                 qpat_assum `buf_n = rbs` (SUBST1_TAC o SYM) >>
                 qpat_assum `rb.buf_size = buf_n` (fn th => simp[NoAsms,th])) >>
             `b MOD dimword (:256) <= b` by simp[arithmeticTheory.MOD_LESS_EQ] >>
             qpat_assum `rbs = type_memory_size rtv` (SUBST1_TAC o SYM) >>
             qpat_assum `buf_n = rbs` (SUBST1_TAC o SYM) >>
             qpat_assum `b MOD dimword (:256) <= b` mp_tac >>
             qpat_assum `b + buf_n <= u.vs_alloca_next` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)
         >- (`lowering_context_ok ctx` by
               (qpat_assum `body_inv _ _ _ _`
                  (mp_tac o MATCH_MP intcall_args_body_inv_lowering) >>
                POP_ASSUM_LIST (K ALL_TAC) >>
                strip_tac >> Cases_on `cx.in_deploy` >> gvs[] >>
                metis_tac[vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry,
                          deployUnitProducersTheory.lower_vyper_deploy_unit_context_ok]) >>
             drule_all args_enter_invoke >> strip_tac >> goal_assum (drule_at Any)) >>
         rpt gen_tac >> strip_tac >>
     qpat_assum `!callee setup use_trans nkeys imm_len pkg_dflts lbl_p ce params
                      has_rb is_nr key trans view ctor imm_len' ss' rt.
                   lookup_function lbl ctx.ctx_functions = SOME callee /\ _ ==> _`
       (drule_all_then (ACCEPT_TAC o CONJUNCT1))) >>
     map_every qx_gen_tac [`actual_bb`,`actual_inst`,`actual_lbl`,`actual_ops`,`actual_words`] >>
     strip_tac >>
     `actual_bb = ibb` by
       (qpat_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME actual_bb` mp_tac >>
        qpat_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME ibb`
          (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `actual_bb = ibb` SUBST_ALL_TAC >>
     `actual_inst = ii` by
       (qpat_assum `get_instruction ibb u.vs_inst_idx = SOME actual_inst` mp_tac >>
        qpat_assum `get_instruction ibb u.vs_inst_idx = SOME ii`
          (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `actual_inst = ii` SUBST_ALL_TAC >>
     `actual_lbl = lbl /\ actual_ops = bops ++ sup_ops ++ def_ops` by
       (qpat_assum `decode_invoke ii = SOME (actual_lbl,actual_ops)` mp_tac >>
        qpat_assum `decode_invoke ii = SOME (lbl,bops ++ sup_ops ++ def_ops)`
          (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `actual_lbl = lbl` SUBST_ALL_TAC >>
     qpat_x_assum `actual_ops = bops ++ sup_ops ++ def_ops` SUBST_ALL_TAC >>
     `actual_words = bws ++ wd` by
       (qpat_assum `eval_operands (bops ++ sup_ops ++ def_ops) u = SOME actual_words` mp_tac >>
        qpat_assum `eval_operands (bops ++ sup_ops ++ def_ops) u = SOME (bws ++ wd)`
          (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `actual_words = bws ++ wd` SUBST_ALL_TAC >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!callee setup use_trans nkeys imm_len pkg_dflts lbl_p ce params
                      has_rb is_nr key trans view ctor imm_len' ss' rt. _ ==> _`
       (drule_all_then (ACCEPT_TAC o CONJUNCT2))) >>
  BETA_TAC >>
  MATCH_MP_TAC (BETA_RULE
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
             `tops` |-> `cx_tops cx`, `G` |-> `Gd`, `tn` |-> `tnd`,
             `source` |-> `\src. after_defaults src.scopes dvs src`] args_rest_outcome)) >>
  simp_tac bool_ss [vyperStateTheory.evaluation_state_accfupds] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qx_gen_tac `err` >> qx_gen_tac `failed` >> disch_tac >>
      qpat_assum `!err failed. lock_if_nr _ _ _ _ = (INR err,failed) ==>
                              !tail. _ /\ _`
        (qspecl_then [`err`, `failed`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (fn agreement =>
        qx_gen_tac `tail` >>
        qspec_then `tail` (ACCEPT_TAC o CONJUNCT1) agreement))
  >- (qpat_assum `!v m prev penv rtv es1 t G tn. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
        (qspecl_then [`vv`, `sm`, `ed.scopes`, `penv`, `rtv`,
                      `ed with scopes := [penv]`, `u`, `Gd`, `tnd`] mp_tac) >>
      simp_tac bool_ss [vyperStateTheory.evaluation_state_accfupds] >>
      (impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qexists_tac `H` >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (BETA_RULE
    (Q.INST [`G` |-> `Gd`, `tn` |-> `tnd`,
             `source` |-> `\src. after_defaults src.scopes dvs src`]
      intcall_args_failed_lock_invoke_outcome)) >>
  simp_tac bool_ss [vyperStateTheory.evaluation_state_accfupds] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `H` >>
  qpat_assum `valid_horizon cx st0 H ed.storage_trace` ACCEPT_TAC
QED
