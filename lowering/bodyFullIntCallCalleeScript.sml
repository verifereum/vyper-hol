Theory bodyFullIntCallCallee
Ancestors bodyFullShadowBodyInv sourceUnitExecution[qualified,ignore_grammar] loweringStateRelDefs[qualified,ignore_grammar] bodyPtrDefs[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar] finite_map[qualified,ignore_grammar] pair[qualified,ignore_grammar]
  transientLockProps[qualified,ignore_grammar] ptrSafeRun[qualified,ignore_grammar]
  runtimeSymSrcClassifiedSource[qualified,ignore_grammar]
  bodySimEntry[qualified,ignore_grammar] nonreentrantEntry[qualified,ignore_grammar]
  fragGasCopyLoop[qualified,ignore_grammar] opcodeClass[qualified,ignore_grammar]
  exprPtrUnwrapFrames[qualified,ignore_grammar]
  bodyFullGhostFrame[qualified,ignore_grammar] augAssignFullStoreGhost[qualified,ignore_grammar]
  ghostPcTransportPtr[qualified,ignore_grammar]
  bodyIntCallSeams fragGasFocus gasOutcomeFullCompose gasOutcomeFull gasStorage
  vyperStorageFootprint vyperStorageTrace vyperState venomState
  contextRawReachable contextCodegenRel contextCodegenRelProps
  vyperInterpreter gasContext stmtSimDefs exprSimDefs compileEnv
  bodyFullIntCallDefs bodyFullIntCallByteFrame bodyFullPreds
  constSubst constSubstStmtsPreserve bodyFullIntCallCheckedBody
  vyperTypeContractFunction bodySimFull[qualified]
  bodyInvSplit bodyCallSupport[qualified,ignore_grammar] bodyInvCodeProps bodyInvExecutionProps bodyInvMetadataProps
  bodyInvIntCallPinsProps contractInvContextProps
  moduleVariableKeyProps compileUnit bodyFullPostsMods[qualified,ignore_grammar]
  bodyQualifiedStmtSupport linkedConstAnnotations constSubstMods[qualified]
  bodyFullIfExpReach[qualified,ignore_grammar] bodyFullHashKeccakFixed[qualified,ignore_grammar]
  ctorDeployLoweringSource nonreentrantEquiv internalReturnMemoryMem
  internalReturnStackAggregate[qualified,ignore_grammar]
  bodyExprPreFacts fragExec intCallCallee stmtSimProps emitHelper context
  compileVyper gasShadow gasShadowState gasShadowModuleOps
  gasShadowCompileContext gasShadowStmtEnv bodyFullIntCallEntryShadow entryInternalAppend entryCompileIntervals
  intCallLookup ctorDeployLoweringPrefix venomExecProps
  externalEntryShape abiDecoderAppend intCallEntryFull exprLoweringProps
  storageCopyGasPath fragGasOriginPtrLoop contextProps
  intCallMaterializeFull memoryValueEncoding moduleLowering venomInst o1PassContract o1PipelineCompose unitShapeDefs entryStateRel stmtSimReturn stateRelProj
  accountsRelProps[qualified,ignore_grammar] vyperTypeContract vyperTypeInitialState vyperTypeEvalProofs vyperTypeInvariants vyperContext externalBodyFrame vyperTypeValues[qualified] vyperValueOperation[qualified]

Theorem intcall_callee_compile_tables_mods[local]:
  contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx ce cx' /\
  cx'.in_deploy = cx.in_deploy ==>
  ce.ce_func_return_type = cenv.ce_func_return_type /\
  ce.ce_flag_member_id = cenv.ce_flag_member_id /\
  ce.ce_flag_n_members = cenv.ce_flag_n_members /\
  ce.ce_method_id = cenv.ce_method_id /\
  ce.ce_struct_fields = cenv.ce_struct_fields /\
  ce.ce_hashmap_info = cenv.ce_hashmap_info /\
  ce.ce_module_var_type = cenv.ce_module_var_type /\
  ce.ce_module_vars = cenv.ce_module_vars /\
  ce.ce_modules = cenv.ce_modules /\
  ce.ce_is_ctor = cenv.ce_is_ctor
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def] >> strip_tac >> simp[]
QED

Theorem intcall_callee_singleton_keys[local]:
  body_inv tops ctx cenv cx ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >> drule bodySimTheory.body_inv_contract >>
  disch_then (qspecl_then [`NONE`,`tops`] mp_tac o
    MATCH_MP contract_inv_unqualified_variable_keys) >> simp[]
QED

Theorem intcall_callee_singleton_frame[local]:
  body_inv tops ctx cenv cx ==>
  (cenv.ce_is_ctor <=> cx.in_deploy) /\ cenv_module_pins tops cenv
Proof
  strip_tac >> conj_tac
  >- drule_then (ACCEPT_TAC o MATCH_MP contract_inv_constructor) bodySimTheory.body_inv_contract >>
  drule_then ACCEPT_TAC intcall_args_body_inv_pins
QED

Definition intcall_ghost_opcodes_def:
  intcall_ghost_opcodes ctx <=>
    !fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DRET
End

Theorem intcall_callee_pre_fmp_context[local]:
  body_inv tops ctx cenv cx ==> intcall_ghost_opcodes ctx
Proof
  strip_tac >>
  `lowering_context_ok ctx` by
    (qpat_x_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP contract_inv_lowering_context o
        MATCH_MP bodySimTheory.body_inv_contract)) >>
  fs[vyperCompilerTheory.lowering_context_ok_def] >>
  drule ptrOkCheckTheory.ptr_ok_check_sound >>
  simp[listTheory.EVERY_MEM, intcall_ghost_opcodes_def,
       ptrDisciplineTheory.fn_ptr_ok_def] >> metis_tac[]
QED

Theorem intcall_callee_src_storage_trace_frame[local]:
  storage_trace_frame (intcall_callee_src cx name mut nr ss)
Proof
  pure_rewrite_tac[intcall_callee_src_def] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_optional_locks] >>
  irule storage_trace_frame_try >>
  simp[storage_trace_frame_function_handler] >>
  irule storage_trace_frame_ignore_bind >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_return]
QED

Theorem intcall_callee_bad_entry[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  ~storage_trace_domain cx st0 es.storage_trace ==>
  gas_outcome_full (DF,lo,explicit,ctx,callee,PG)
    (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
    (es,entered,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bad_nil >> reverse conj_tac
  >- fs[gas_invoke_entry_def] >>
  gen_tac >>
  Cases_on `intcall_callee_src cx name mut nr ss (es with gas_obs := tail)` >>
  drule_at Any storage_trace_frame_preserves_bad_domain >>
  simp[intcall_callee_src_storage_trace_frame]
QED

(* The byte frame uses the entry horizon, while the post is checked at
   the callee's final trace. *)
Theorem intcall_callee_entry_horizon[local]:
  intcall_callee_src cx name mut nr ss (es with gas_obs := xs) =
    (res, ee with gas_obs := ys) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  drule_at Any storage_trace_frame_prefix >>
  simp[intcall_callee_src_storage_trace_frame] >>
  metis_tac[valid_horizon_append]
QED

Theorem intcall_callee_entry_decode[local]:
  gas_invoke_entry (ctx,func) s callee entered /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (label,ops) /\
  eval_operands ops s = SOME argv ==>
  ~s.vs_halted /\ inst.inst_opcode = INVOKE /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  ?setup first phi_state.
    setup_callee callee argv s = SOME setup /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    ~phi_state.vs_halted /\
    entered = phi_state with vs_inst_idx :=
      phi_prefix_length first.bb_instructions
Proof
  rw[gas_invoke_entry_def] >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_callee_invoke_label[local]:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup ==>
  lbl = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
          cenv.ce_is_ctor /\
  alloca_room ctx callee setup
Proof
  rw[intcall_entry_full_def] >>
  qpat_x_assum `lookup_function lbl _ = SOME callee` mp_tac >>
  qpat_x_assum `setup_callee callee argv t = SOME setup` mp_tac >>
  qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
  qpat_x_assum `lookup_block _ _ = SOME bb'` mp_tac >>
  qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
  qpat_x_assum `get_instruction bb' _ = SOME inst'` mp_tac >>
  qpat_x_assum `decode_invoke inst = _` mp_tac >>
  qpat_x_assum `decode_invoke inst' = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops t = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops' t = _` mp_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  `bb' = bb` by
    (qpat_assum `lookup_block _ _ = SOME bb'` mp_tac >>
     qpat_assum `lookup_block _ _ = SOME bb` (rewrite_tac o single) >> simp[NoAsms]) >>
  `inst' = inst` by
    (qpat_assum `get_instruction bb' _ = SOME inst'` mp_tac >>
     qpat_assum `bb' = bb` (rewrite_tac o single) >>
     qpat_assum `get_instruction bb _ = SOME inst` (rewrite_tac o single) >> simp[NoAsms]) >>
  `lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
          cenv.ce_is_ctor /\ arg_ops' = arg_ops` by
    (qpat_assum `decode_invoke inst' = SOME _` mp_tac >>
     qpat_assum `inst' = inst` (rewrite_tac o single) >>
     qpat_assum `decode_invoke inst = SOME _` (rewrite_tac o single) >> simp[NoAsms]) >>
  `argv' = argv` by
    (qpat_assum `eval_operands arg_ops' t = SOME argv'` mp_tac >>
     qpat_assum `arg_ops' = arg_ops` (rewrite_tac o single) >>
     qpat_assum `eval_operands arg_ops t = SOME argv` (rewrite_tac o single) >> simp[NoAsms]) >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _`
    (qspecl_then [`callee`,`setup`] mp_tac) >>
  qpat_assum `lbl = internal_fn_label _ _ _ _` (once_rewrite_tac o single o SYM) >>
  qpat_assum `argv' = argv` (rewrite_tac o single) >>
  qpat_assum `lookup_function lbl _ = SOME callee` (rewrite_tac o single) >>
  qpat_assum `setup_callee callee argv t = SOME setup` (rewrite_tac o single) >>
  strip_tac >>
  qpat_x_assum `!use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _`
    (qspecl_then [`F`, `\x:string. 0`, `0`, `([]:expr list)`] mp_tac) >>
  simp[] >>
  qabbrev_tac `pack = set_internal_package_target cenv.ce_target
    (package_internal_fn tops F (\x:string. 0) cenv.ce_is_ctor 0
      (mut,nr,rr,name,args,([]:expr list),ret,ss))` >>
  `FST pack = internal_fn_label (build_func_ids 0 tops name) name
      (MAP SND args) cenv.ce_is_ctor` by
    simp[Abbr `pack`, package_internal_fn_def, set_internal_package_target_def] >>
  PairCases_on `pack` >>
  disch_then (qspecl_then [`pack0`,`pack1`,`pack2`,`pack3`,`pack4`,`pack5`,
    `pack6`,`pack7`,`pack8`,`pack9`,`pack10`,`pack11`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `FST _ = _` (assume_tac o REWRITE_RULE [pairTheory.FST]) >>
  metis_tac[]
QED

(* Only the target field changes when re-targeting the selected package.
   Argument layout does not require equality of the two policy witnesses. *)
Theorem intcall_callee_selected_args[local]:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys cenv.ce_is_ctor alloc_len
       (mut,nr,rr,name,args,(dflts:expr list),ret,ss)) =
    (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
  state_rel H callee ce cx (es1 with scopes := []) t /\
  internal_immutable_regions ce cx es1 t.vs_alloca_next /\
  internal_args_rel ce params penv (if has_rb then 1 else 0) argv
    t.vs_alloca_next t.vs_memory /\
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    internal_args_rel ce params penv (if has_rb then 1 else 0) argv
      t.vs_alloca_next mem) /\
  (!i off sz.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz.
       op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
       w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
  (has_rb ==> ?b bsz.
    op_prov G (HD arg_ops) = SOME (b,bsz) /\
    b <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= b + bsz /\
    b + bsz <= t.vs_alloca_next /\ lo <= b) /\
  (has_rb ==> w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next) /\
  (has_rb ==> !i off sz.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
       (w2n (EL (1 + i) argv)) sz) /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?inst b cap. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       FLOOKUP t.vs_allocas inst.inst_id = SOME (b,cap) /\
       b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
       w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + cap)
Proof
  strip_tac >>
  `set_internal_package_target cenv.ce_target
      (package_internal_fn tops use_trans nkeys cenv.ce_is_ctor alloc_len
         (mut,nr,rr,name,args,dflts,ret,ss)) =
      (lbl',ce with ce_target := cenv.ce_target,params,has_rb,is_nr,key,
       trans,view,ctor,imm_len',ss',rt)` by
    (qpat_x_assum `set_internal_package_target target _ = _` mp_tac >>
     qabbrev_tac `pack = package_internal_fn tops use_trans nkeys cenv.ce_is_ctor
       alloc_len (mut,nr,rr,name,args,dflts,ret,ss)` >>
     PairCases_on `pack` >> simp[set_internal_package_target_def] >>
     strip_tac >> gvs[]) >>
  `internal_stack_size (ce with ce_target := cenv.ce_target) params =
     internal_stack_size ce params` by (irule internal_stack_size_vars >> simp[]) >>
  qpat_x_assum `intcall_entry_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
  qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
  qpat_x_assum `lookup_block _ _ = SOME bb'` mp_tac >>
  qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
  qpat_x_assum `get_instruction bb' _ = SOME inst'` mp_tac >>
  qpat_x_assum `decode_invoke inst = _` mp_tac >>
  qpat_x_assum `decode_invoke inst' = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops t = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops' t = _` mp_tac >>
  qpat_x_assum `!bb inst lbl arg_ops argv. _ ==> EVERY _ _ /\ _` mp_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _` mp_tac >>
  qpat_x_assum `set_internal_package_target cenv.ce_target _ = _` mp_tac >>
  qpat_x_assum `setup_callee callee argv t = SOME setup` mp_tac >>
  qpat_x_assum `lookup_function lbl _ = SOME callee` mp_tac >>
  qpat_x_assum `internal_stack_size _ _ = internal_stack_size _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt (disch_then strip_assume_tac) >>
  qpat_x_assum `lookup_block _ _ = SOME bb'` mp_tac >>
  qpat_assum `lookup_block _ _ = SOME bb` (rewrite_tac o single) >>
  simp[NoAsms] >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `get_instruction _ _ = SOME inst'` mp_tac >>
  qpat_assum `get_instruction _ _ = SOME inst` (rewrite_tac o single) >>
  simp[NoAsms] >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `decode_invoke _ = SOME (lbl'',arg_ops')` mp_tac >>
  qpat_assum `decode_invoke _ = SOME (lbl,arg_ops)` (rewrite_tac o single) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `lbl = lbl''` SUBST_ALL_TAC >>
  qpat_x_assum `arg_ops = arg_ops'` SUBST_ALL_TAC >>
  qpat_x_assum `eval_operands _ t = SOME argv'` mp_tac >>
  qpat_assum `eval_operands _ t = SOME argv` (rewrite_tac o single) >>
  simp[NoAsms] >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `!bb inst lbl arg_ops argv. _ ==> EVERY _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!ca su ut nk len ds lab ce' ps rb nr' k tr v c il ss' rt'.
    _ ==> lab = _ /\ _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!ca su ut nk len ds lab ce' ps rb nr' k tr v c il ss' rt'.
    _ ==> (!mem. _) /\ _` (drule_all_then strip_assume_tac) >>
  conj_tac
  >- (`state_rel H callee (ce with ce_target := cenv.ce_target) cx (es1 with scopes := []) t` by
        metis_tac[stateRelProjTheory.state_rel_scopes_nil_func] >>
      irule state_rel_cenv_cong >>
      qexists_tac `ce with ce_target := cenv.ce_target` >> simp[]) >>
  conj_tac
  >- (qpat_assum `internal_immutable_regions _ _ _ _` mp_tac >>
      simp[NoAsms, internal_immutable_regions_def]) >>
  gvs[internal_args_rel_def] >> rpt strip_tac
  >- (qpat_assum `!i off sz. _ ==> ?b bsz aid. op_prov _ _ = _ /\ _`
        (drule_all_then strip_assume_tac) >> goal_assum (drule_at Any) >> simp[])
  >- (qpat_assum `_ ==> ?b bsz. op_prov _ (HD _) = _ /\ _`
        (drule_all_then strip_assume_tac) >> goal_assum (drule_at Any) >> simp[])
  >- (qpat_assum `_ ==> ?b bsz. op_prov _ (HD _) = _ /\ _` mp_tac >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
      goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i off sz. _ ==> ?aid b cap. FLOOKUP _ aid = _ /\ _`
    (drule_all_then strip_assume_tac) >>
  map_every (fn p => qpat_x_assum p mp_tac)
    [`_ .inst_id = _`, `MEM _ (fn_insts func)`, `_ .inst_opcode = ALLOCA`,
     `FLOOKUP t.vs_allocas _ = SOME _`, `_ <= w2n _`, `_ + w2n _ <= _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_callee_body_admissible[local]:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv)
    expr_vv_res_ok es /\
  (!gs. lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := gs) =
    (INL (), locked with gas_obs := gs)) ==>
  gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
    (stmt_res_ok NoLoop) locked
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _ ==> expr_vv_res_ok res`
    (qspec_then `gs` mp_tac) >>
  pure_rewrite_tac[intcall_rest_def, ignore_bind_def, bind_def] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `!xs. lock_if_nr _ _ _ _ = _` kall_tac >>
  Cases_on `res` >- (rename1 `INL u` >> Cases_on `u` >> simp[stmt_res_ok_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[stmt_res_ok_def, try_def, handle_function_def, finally_def,
       finally_unless_halt_def, ignore_bind_def, bind_def,
       pop_function_def, set_scopes_def, return_def, raise_def,
       unlock_if_nr_def, release_nonreentrant_lock_def, record_storage_event_def,
       get_transient_storage_def, update_transient_def,
       COND_RATOR, vyperMiscTheory.option_CASE_rator] >>
  Cases_on `nr /\ mut <> View /\ mut <> Pure` >>
  Cases_on `cx.nonreentrant_slot` >>
  fs[expr_vv_res_ok_def, handle_function_def, raise_def]
QED

(* The compiled module has a location for every declared storage key.
   The entry relation reflects each of those locations into the source layout. *)
Theorem intcall_callee_live[local]:
  body_inv tops ctx cenv cx /\ stmt_state_rel H ctx func cenv cx ee t ==>
  context_function_live cx (NONE,name)
Proof
  strip_tac >>
  drule stmt_state_rel_vars_rels >> strip_tac >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then assume_tac intcall_callee_singleton_keys >>
  drule_then strip_assume_tac body_inv_module_locations >>
  `get_module_code cx NONE = SOME tops` by (drule body_inv_main_code >> simp[]) >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[supportedProgramTheory.supported_program_def,
      get_module_code_def, context_function_live_def, function_live_def] >>
  disj1_tac >> simp[module_allocated_def, listTheory.EVERY_MEM] >>
  `!id tr n. FLOOKUP (add_module_var_locations tops FEMPTY) (NONE,id) =
    SOME (if tr then TransientLoc (n2w n) else StorageLoc (n2w n)) ==>
    IS_SOME (lookup_var_slot_in_layouts cx.layouts cx.txn.target tr NONE id)` by
    (rpt gen_tac >> disch_tac >> drule_all entry_module_lookup_immutable_frame >>
     Cases_on `tr` >>
     gvs[loweringStateRelDefsTheory.storage_vars_rel_def,
         loweringStateRelDefsTheory.transient_vars_rel_def] >>
     metis_tac[lookup_var_slot_in_layouts_def, lookup_var_slot_from_layout_def,
               optionTheory.IS_SOME_EXISTS]) >>
  qx_gen_tac `top` >> disch_tac >> Cases_on `top` >>
  gvs[toplevel_allocated_def] >>
  TRY (rename1 `MEM (VariableDecl vis mut id ty sl) tops` >> Cases_on `mut`) >>
  gvs[toplevel_allocated_def] >>
  (rename1 `MEM (VariableDecl vis _ id ty sl) tops` ORELSE
   rename1 `MEM (HashMapDecl vis tr id kt vt sl) tops`) >>
  `?n. sl = SOME n` by
    metis_tac[supported_storage_decl_slot, supported_hashmap_decl_slot] >>
  gvs[] >>
  first_x_assum irule >> qexists_tac `n` >>
  drule_then (drule_then (qspec_then `FEMPTY` mp_tac))
    (REWRITE_RULE [AND_IMP_INTRO |> GSYM] add_module_var_locations_mem) >>
  simp[toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
       finite_mapTheory.FLOOKUP_EMPTY, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem intcall_callee_typed_env[local]:
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 ==>
  ?env env_after.
    env.current_src = NONE /\ env.type_defs = tenv.type_defs /\
    env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
    env.bare_global_assignable = tenv.bare_global_assignable /\
    env.toplevel_vtypes = tenv.toplevel_vtypes /\ env.flag_members = tenv.flag_members /\
    type_stmts env ret (subst_consts_stmts (module_consts_env tops []) ss) = SOME env_after /\
    (?env_raw. type_stmts env ret ss = SOME env_raw) /\
    (!id ty. MEM (id,ty) args ==> FLOOKUP env.var_types id = SOME ty) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args) /\
    env_scopes_consistent env cx es1
Proof
  strip_tac >>
  qhdtm_assum `intcall_entry_full`
    (fn th => map_every STRIP_ASSUME_TAC
      (List.take (CONJUNCTS (REWRITE_RULE [intcall_entry_full_def] th), 8))) >>
  `env_context_consistent tenv cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def] >>
  qpat_assum `body_const_cells_agree _ cx tenv es1`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  `check_function_body cx.layouts cx.txn.target [(NONE,tops)] art NONE Internal mut nr
      args dflts ret ss` by
    (drule_all_then ACCEPT_TAC checked_singleton_internal_function_body) >>
  qabbrev_tac `checked = function_entry_env art [(NONE,tops)] NONE Internal args` >>
  qabbrev_tac `env = checked with
    <|toplevel_vtypes := tenv.toplevel_vtypes; flag_members := tenv.flag_members|>` >>
  `static_maps_transfer_env checked env` by
    (qunabbrev_tac `env` >> qunabbrev_tac `checked` >>
     irule vyperTypeContractFunctionTheory.function_entry_env_static_maps_transfer >>
     fs[constSubstCorrectTheory.frame_maps_def] >> qexists_tac `cx` >> simp[]) >>
  `?env_after. type_stmts env ret
      (subst_consts_stmts (module_consts_env tops []) ss) = SOME env_after` by
    (irule vyperTypeContractFunctionTheory.type_stmts_static_maps_transfer >>
     qpat_assum `static_maps_transfer_env checked env` (irule_at Any) >>
     fs[check_function_body_def, Abbr `checked`, optionTheory.IS_SOME_EXISTS,
        constSubstModsTheory.consts_env_mods_singleton,
        constSubstModsTheory.subst_consts_mods_singleton]) >>
  `?env_raw. type_stmts env ret ss = SOME env_raw` by
    (irule vyperTypeContractFunctionTheory.type_stmts_static_maps_transfer >>
     qpat_assum `static_maps_transfer_env checked env` (irule_at Any) >>
     fs[check_function_body_def, Abbr `checked`, optionTheory.IS_SOME_EXISTS]) >>
  `ALL_DISTINCT (MAP FST args)` by fs[check_function_body_def, params_ok_def] >>
  `(!id ty. MEM (id,ty) args ==>
       FLOOKUP env.var_types id = SOME ty /\ IS_SOME (FLOOKUP env.var_assignable id)) /\
   (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
   (!n b. FLOOKUP env.var_assignable n = SOME b ==> ?ty. MEM (n,ty) args)` by
    (simp[Abbr `env`, Abbr `checked`, function_entry_env_def, artifact_env_def] >>
     rpt conj_tac >> rpt strip_tac
     >- (drule_all vyperTypeContractContextTheory.FOLDL_extend_local_args_formal_lookup >> simp[])
     >- (drule_all vyperTypeContractContextTheory.FOLDL_extend_local_args_formal_lookup >> simp[])
     >- (drule_all vyperTypeContractContextTheory.FOLDL_extend_local_args_var_types_range >> simp[]) >>
     drule_all vyperTypeContractContextTheory.FOLDL_extend_local_args_var_assignable_range >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`env`, `env_after`] >>
  `es1 = es1 with scopes := [penv]` by
    simp[evaluation_state_component_equality] >>
  `env_scopes_consistent env cx es1` by
    (pop_assum (fn th => CONV_TAC (RAND_CONV (REWR_CONV th))) >>
     irule vyperTypeBindArgumentsTheory.bind_arguments_env_scopes_consistent >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[Abbr `env`, Abbr `checked`, function_entry_env_def, artifact_env_def,
     vyperTypeContractContextTheory.FOLDL_extend_local_args_static,
     constSubstCorrectTheory.frame_maps_def, env_context_consistent_def,
     get_tenv_def] >>
  metis_tac[]
QED

Theorem intcall_callee_lock_fields[local]:
  lock_if_nr cx nr view es = (res,locked) ==>
  locked.scopes = es.scopes /\ locked.immutables = es.immutables /\
  locked.accounts = es.accounts /\ locked.outcomes = es.outcomes
Proof
  strip_tac >> drule_then assume_tac lock_if_nr_scopes >> simp[] >>
  Cases_on `nr` >> fs[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> fs[raise_def] >>
  gvs[acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
      check_not_static_def, check_def, assert_def, return_def, raise_def,
      COND_RATOR, AllCaseEqs()]
QED

Theorem intcall_callee_enter_context[local]:
  env_context_consistent old cx /\
  env.current_src = NONE /\ env.type_defs = old.type_defs /\
  env.fn_sigs = old.fn_sigs /\ env.bare_globals = old.bare_globals /\
  env.bare_global_assignable = old.bare_global_assignable /\
  env.toplevel_vtypes = old.toplevel_vtypes /\ env.flag_members = old.flag_members ==>
  env_context_consistent env (cx with stk updated_by CONS (NONE,name))
Proof
  simp[env_context_consistent_def, current_module_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
  strip_tac >> gs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_callee_locked_source[local]:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) ==>
  ?env env_after.
    env.type_defs = tenv.type_defs /\ env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
    env.bare_global_assignable = tenv.bare_global_assignable /\
    env.toplevel_vtypes = tenv.toplevel_vtypes /\
    type_stmts env ret (subst_consts_stmts (module_consts_env tops []) ss) = SOME env_after /\
    (?env_raw. type_stmts env ret ss = SOME env_raw) /\
    (!id ty. MEM (id,ty) args ==> FLOOKUP env.var_types id = SOME ty) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args) /\
    env_consistent env (cx with stk updated_by CONS (NONE,name)) locked /\
    state_well_typed locked /\ popped_keys_indexed locked.scopes /\
    locked.accounts = es1.accounts /\ locked.outcomes = es1.outcomes
Proof
  strip_tac >>
  drule_all intcall_callee_typed_env >> strip_tac >>
  drule_all intcall_callee_lock_fields >> strip_tac >>
  qhdtm_x_assum `intcall_entry_full`
    (fn th => map_every STRIP_ASSUME_TAC
      (List.take (CONJUNCTS (REWRITE_RULE [intcall_entry_full_def] th), 8))) >>
  rename1 `type_stmts env ret (subst_consts_stmts (module_consts_env tops []) ss) = SOME env_after` >>
  qexistsl [`env`, `env_after`] >> simp[] >>
  `env_context_consistent tenv cx /\
   env_immutables_consistent tenv cx (es1 with scopes := prev) /\
   state_well_typed (es1 with scopes := prev)` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def] >>
  conj_tac >-
    (simp[env_consistent_def] >>
     conj_tac >- (irule intcall_callee_enter_context >> simp[] >> qexists `tenv` >> simp[]) >>
     conj_tac >-
       (qpat_x_assum `env_scopes_consistent env cx es1` mp_tac >>
        simp[env_scopes_consistent_stk_irrelevant, env_scopes_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `env_immutables_consistent tenv cx _` mp_tac >>
     simp[env_immutables_consistent_def, get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success >>
  drule_then assume_tac external_bind_arguments_popped >>
  fs[state_well_typed_def]
QED

Theorem intcall_callee_locked_body[local]:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv)
    expr_vv_res_ok es /\
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
    body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) compiled_ss) /\
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) ==>
  body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) compiled_ss /\
  gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
    (stmt_res_ok NoLoop) locked
Proof
  strip_tac >> conj_tac
  >- (first_x_assum irule >> rpt strip_tac >>
      fs[lock_if_nr_def] >> Cases_on `cx.nonreentrant_slot` >>
      fs[raise_def, ignore_bind_def, bind_def, check_not_static_def,
         check_def, assert_def, return_def, AllCaseEqs()]) >>
  irule intcall_callee_body_admissible >>
  qexistsl_tac [`es`, `mut`, `nr`, `prev`, `rtv`] >>
  simp[Excl "lock_if_nr_def"] >>
  gen_tac >>
  `locked.outcomes = es.outcomes` by
    (Cases_on `nr` >> fs[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> fs[raise_def] >>
     gvs[acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
         check_not_static_def, check_def, assert_def, return_def, raise_def,
         COND_RATOR, AllCaseEqs()]) >>
  drule_then assume_tac lock_if_nr_scopes >>
  `es with <|scopes := es.scopes; outcomes := es.outcomes; gas_obs := gs|> =
   es with gas_obs := gs` by simp[evaluation_state_component_equality] >>
  `locked with <|scopes := es.scopes; outcomes := es.outcomes; gas_obs := gs|> =
   locked with gas_obs := gs` by simp[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`s` |-> `es`, `view` |-> `is_view_mut mut`,
    `scs` |-> `es.scopes`, `oc` |-> `es.outcomes`, `gobs` |-> `gs`]
    lock_if_nr_transport) >>
  simp[Excl "lock_if_nr_def"]
QED

Theorem intcall_callee_final_horizon_bytes[local]:
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  intcall_callee_src cx name mut nr ss (es1 with gas_obs := xs) =
    (res,ee with gas_obs := ys) /\
  valid_horizon cx st0 H ee.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
    MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
    marks (IntRet ir s',G',tn') ==>
  !b sz. (cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b) /\
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  strip_tac >>
  drule_all intcall_callee_entry_horizon >> strip_tac >>
  mp_tac intcall_callee_caller_memory_bytes >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem intcall_callee_step_prov_protected_sites[local]:
  (!v b sz. FLOOKUP G v = SOME (b,sz) ==> x < b \/ b + sz <= x) /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
    x < b \/ b + sz <= x) /\ inst.inst_opcode <> DALLOCA ==>
  !v b sz. FLOOKUP (step_prov PG G inst u) v = SOME (b,sz) ==>
    x < b \/ b + sz <= x
Proof
  rpt strip_tac >> fs[ptrDisciplineTheory.step_prov_def] >>
  drule runtimeProvenanceSourcesTheory.set_prov_source >> strip_tac
  >- metis_tac[] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[ptrDisciplineTheory.out_prov_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[ptrDisciplineTheory.out_prov_def, AllCaseEqs()] >> metis_tac[listTheory.EL_MEM]) >>
  gvs[ptrDisciplineTheory.out_prov_def, AllCaseEqs()] >>
  drule ptrDisciplineTheory.first_prov_origin >> metis_tac[]
QED

Theorem intcall_callee_base_protected_sites[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
  step_inst_base inst s = OK u ==>
  ptr_byte_frame_inv (ctx,x) (step_prov PG G inst u) u
Proof
  simp[ptr_byte_frame_inv_def] >> strip_tac >>
  `u.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp] >>
  `x < u.vs_alloca_next /\
   (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
      x < b \/ b + sz <= x)` by
    (Cases_on `inst.inst_opcode = ALLOCA`
     >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
         simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >>
         metis_tac[bodyFullIntCallByteFrameTheory.exec_alloca_protected_byte_sites]) >>
     `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
       metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_fields] >>
     simp[] >> metis_tac[]) >>
  simp[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  drule_at Any intcall_callee_step_prov_protected_sites >>
  disch_then (qspec_then `x` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Theorem intcall_callee_protected_write_range[local]:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\ lo <= x /\
  ptr_byte_frame_inv (ctx,x) G s ==>
  x NOTIN range_bytes (source_memory_write_ranges inst s)
Proof
  simp[ptrDisciplineTheory.range_bytes_def, pred_setTheory.GSPECIFICATION] >>
  strip_tac >> rpt gen_tac >> CCONTR_TAC >> gvs[] >>
  `len <> 0 /\ lo < off + len` by decide_tac >>
  fs[ptr_byte_frame_inv_def, ptrDisciplineTheory.access_ok_def] >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges _ _) /\ _ ==> _`
    (qspecl_then [`off`, `len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!v off sz. _` drule >> decide_tac
QED

Theorem intcall_callee_protected_ordinary_step:
  step_inst fuel ctx inst s = OK u /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx) /\ inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> DRET /\
  ~in_revert_forward fn s /\ lo <= x /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
  ptr_byte_frame_inv (ctx,x) G s /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\ x NOTIN tn.t_mem ==>
  ptr_byte_frame_inv (ctx,x) (step_prov PG G inst u) u /\
  (!v. op_taint (step_taint inst s u tn) (Var v) SUBSET count 32) /\
  x NOTIN (step_taint inst s u tn).t_mem
Proof
  strip_tac >>
  `step_inst_base inst s = OK u` by gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `inst.inst_opcode = DALLOCA ==>
     x < w2n s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp /\
     u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (strip_tac >>
     `ctx_has_dalloca ctx` by metis_tac[] >>
     `allocas_below_fmp s` by
       (drule ptrSafeRunTheory.ptr_safe_step_inst_ok >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def]) >>
     conj_tac >-
       (fs[ptr_byte_frame_inv_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
        decide_tac) >>
     conj_tac >-
       (drule ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp >> simp[]) >>
     irule venomMemProofsTheory.step_inst_base_preserves_alloca_fields >>
     qexists_tac `inst` >> simp[]) >>
  conj_tac >-
    (reverse (Cases_on `inst.inst_opcode = DALLOCA`)
     >- metis_tac[intcall_callee_base_protected_sites] >>
     res_tac >>
     `!v w. inst.inst_outputs = [v] /\ lookup_var v u = SOME w ==> x < w2n w` by
       (rpt strip_tac >>
        gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs(),
          update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
     fs[ptr_byte_frame_inv_def] >> conj_tac
     >- (rpt strip_tac >>
         fs[ptrDisciplineTheory.step_prov_def] >>
         drule runtimeProvenanceSourcesTheory.set_prov_source >> strip_tac
         >- metis_tac[] >>
         gvs[ptrDisciplineTheory.out_prov_def, AllCaseEqs()] >> metis_tac[]) >>
     metis_tac[]) >>
  conj_tac >- (drule lowerDloadMaskBoundsTheory.ld_step_taint_bound >> simp[]) >>
  `x < s.vs_alloca_next` by fs[ptr_byte_frame_inv_def] >>
  `x NOTIN new_site_bytes s u` by
    (reverse (Cases_on `inst.inst_opcode = DALLOCA`)
     >- metis_tac[taintAgreeTheory.step_inst_base_new_site_bytes_frontier] >>
     qpat_assum `inst.inst_opcode = DALLOCA ==> x < _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[ptrDisciplineTheory.new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF] >>
     decide_tac) >>
  `access_ok lo G fn inst s` by
    metis_tac[ptrSafeRunTheory.ptr_safe_step_inst_ok, ptrSafeRunTheory.ptr_inst_ok_def] >>
  `x NOTIN range_bytes (source_memory_write_ranges inst s)` by
    metis_tac[intcall_callee_protected_write_range] >>
  `!op j. MEM op inst.inst_operands /\ j IN op_taint tn op ==> j < 32` by
    (drule lowerDloadMaskBoundsTheory.ld_op_taint_bound >>
     simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  simp[ptrDisciplineTheory.step_taint_def] >>
  drule_all taintAgreeTheory.mem_taint_frame_source_range >> simp[]
QED

(* Factor the entry into the four straight-line compiler phases. *)
Theorem intcall_callee_entry_phases[local]:
  compile_internal_function_entry ce params has_rb ctor ilen rt entry =
    ((ce2,pc,imm),prologue) ==>
  ?ce1 caps capture reserved materialized.
    compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
    (if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE) capture = (imm,reserved) /\
    materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
    (case rt of NONE => comp_return ()
      | SOME ty => if 0 < ce.ce_returns_count then
           comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
             (comp_return ())
         else comp_return ()) materialized = ((),prologue) /\
    cs_extends capture reserved /\ cs_extends reserved materialized /\
    cs_extends materialized prologue
Proof
  strip_tac >>
  Cases_on `compile_internal_entry_prefix ce params has_rb entry` >>
  rename1 `_ = (prefix,capture)` >> PairCases_on `prefix` >>
  qabbrev_tac `reserve = if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE` >>
  qabbrev_tac `scratch = case rt of NONE => comp_return ()
      | SOME ty => if 0 < ce.ce_returns_count then
           comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
             (comp_return ())
         else comp_return ()` >>
  Cases_on `reserve capture` >> rename1 `reserve capture = (im,reserved)` >>
  Cases_on `materialize_internal_params prefix0 prefix1 reserved` >>
  rename1 `materialize_internal_params _ _ _ = (cm,materialized)` >>
  Cases_on `scratch materialized` >>
  rename1 `scratch materialized = (u,last)` >> Cases_on `u` >>
  `cs_appends reserve` by
    (simp[Abbr `reserve`] >> IF_CASES_TAC >> simp[cs_appends_return] >>
     irule cs_appends_bind >> simp[cs_appends_return] >>
     rw[cs_appends_def] >>
     qspec_then `ilen` (qspec_then `st` mp_tac) compile_fixed_region_with_id_labels >>
     simp[]) >>
  `cs_appends scratch` by
    (Cases_on `rt` >> simp[Abbr `scratch`, cs_appends_return] >>
     IF_CASES_TAC >> simp[cs_appends_abi_alloc_buffer, cs_appends_return,
                          cs_appends_ignore_bind]) >>
  `cs_extends capture reserved /\ cs_extends reserved materialized /\
   cs_extends materialized last` by
    (conj_tac >- fs[cs_appends_def] >> conj_tac >- (
       qspecl_then [`prefix1`, `prefix0`, `reserved`] mp_tac
         materialize_internal_params_labels >> simp[]) >> fs[cs_appends_def]) >>
  gvs[compile_internal_function_entry_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  unabbrev_all_tac >>
  gvs[arithmeticTheory.GREATER_DEF, comp_ignore_bind_def]
QED

Theorem intcall_callee_capture_same_blocks[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) ==>
  same_blocks entry capture /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\ MAP FST caps = MAP FST params
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_internal_param_decls _ _ _ = (pr,mid)` >> PairCases_on `pr` >>
  drule internal_param_decls_projection >> simp[same_blocks_def] >> strip_tac >> gvs[]
QED

Theorem intcall_callee_setup_capture[local]:
  setup_callee callee argv t = SOME setup ==>
  fresh_vars_wrt entry setup /\ setup.vs_params = argv /\
  ~setup.vs_halted /\ allocas_from lo setup /\ setup.vs_allocas = FEMPTY
Proof
  Cases_on `NULL callee.fn_blocks` >>
  simp[venomExecSemanticsTheory.setup_callee_def] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[ptrDisciplineTheory.allocas_from_def,
       loweringStateRelDefsTheory.fresh_vars_wrt_def]
QED

(* The capture starts with PARAM or RETPC_PARAM, never a PHI. *)
Theorem intcall_callee_capture_entry[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  fn_has_code entry capture callee /\
  entry.cs_current_insts = [] /\ setup.vs_current_bb = entry.cs_current_bb /\
  setup.vs_inst_idx = 0 /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions ==>
  entered = setup /\ entered.vs_inst_idx = LENGTH entry.cs_current_insts /\
  lookup_block entered.vs_current_bb callee.fn_blocks = SOME first /\
  isPREFIX (emitted_insts entry capture) (DROP entered.vs_inst_idx first.bb_instructions)
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [same_blocks_def])
    (cj 1 intcall_callee_capture_same_blocks) >>
  `isPREFIX (emitted_insts entry capture) first.bb_instructions` by
    gvs[fn_has_code_def, emitted_insts_def] >>
  `emitted_insts entry capture <> []` by
    (drule compile_internal_entry_prefix_shape >> simp[]) >>
  drule_then assume_tac compile_internal_entry_prefix_capture_code >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  Cases_on `emitted_insts entry capture` >>
  gvs[venomExecSemanticsTheory.eval_phis_def,
      venomExecSemanticsTheory.phi_prefix_length_def,
      venom_state_component_equality]
QED

Theorem intcall_callee_capture_cursor[local]:
  same_blocks entry capture /\ cs_extends entry capture /\
  s.vs_current_bb = entry.cs_current_bb /\
  s.vs_inst_idx = LENGTH entry.cs_current_insts ==>
  s.vs_inst_idx + LENGTH (emitted_insts entry capture) = LENGTH capture.cs_current_insts /\
  s.vs_current_bb = capture.cs_current_bb
Proof
  strip_tac >>
  `isPREFIX entry.cs_current_insts capture.cs_current_insts` by
    gvs[same_blocks_def, cs_extends_def] >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  gvs[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
      venom_state_component_equality]
QED

(* The optional fixed base is just a fresh assignment, not a new allocation. *)
Theorem intcall_callee_reserve[local]:
  (if reserve then
     comp_bind (compile_fixed_region_with_id ilen)
       (\ar. comp_return (SOME (SND ar).buf_operand))
   else comp_return NONE) sa = (imm,sb) /\
  fn_has_code sa sb func /\ fresh_vars_wrt sa s /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    u.vs_current_bb = sb.cs_current_bb /\ fresh_vars_wrt sb u /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x) /\ not_fresh_at sb x) /\
    (if reserve then
       ?x. imm = SOME (Var x) /\ not_fresh_at sb x /\
           lookup_var x u = SOME 0w /\ FLOOKUP G' x = NONE /\
           op_taint tn' (Var x) = {}
     else imm = NONE) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
                   (OK u,G',tn')
Proof
  reverse (Cases_on `reserve`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[venom_state_component_equality, fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  PairCases_on `ar` >>
  rename1 `compile_fixed_region_with_id ilen sa = ((id,buf),sb)` >>
  drule compile_fixed_region_as_assign >>
  disch_then (assume_tac o MATCH_MP (SPEC_ALL emit_op_same_blocks)) >>
  drule_then strip_assume_tac compile_fixed_region_with_id_result >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qexists_tac `bb` >> asm_rewrite_tac []) >>
  pop_assum strip_assume_tac >>
  drule_all compile_internal_fixed_region_joint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK v` >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x v = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x) /\ not_fresh_at sb x` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var) /\ not_fresh_at sb x` by
       fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     `emitted_insts sa sb = [mk_inst sa.cs_next_id ASSIGN [Lit 0w]
         [STRING #"%" (toString sa.cs_next_var)]]` by
       simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `D` strip_assume_tac) >>
     `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
       ?idx out. i.inst_operands = [Lit idx] /\ i.inst_outputs = [out])
       (emitted_insts sa sb)` by simp[venomInstTheory.mk_inst_def] >>
     drule_all internal_capture_seq_ghost_frame >> strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[venomInstTheory.mk_inst_def] >>
     gvs[run_inst_seq_def, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         eval_operand_def, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  fs[same_blocks_def, loweringStateRelDefsTheory.fresh_vars_wrt_def,
     venom_state_component_equality, eval_operand_def, lookup_var_def,
     ptrDisciplineTheory.op_prov_def] >>
  gvs[loweringStateRelDefsTheory.not_fresh_at_def, ASCIInumbersTheory.toString_inj,
      eval_operand_def, lookup_var_def, ptrDisciplineTheory.op_prov_def]
QED

(* Before materialization there are no callee-owned allocations or local
   pointers. The borrowed regions are named by the distinct parameters. *)
Theorem intcall_callee_materialize_pre[local]:
  internal_args_rel ce params env idx argv s.vs_alloca_next s.vs_memory /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  (!i. i < LENGTH params ==>
    ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at st p /\
        lookup_var p s = SOME (EL (idx + i) argv)) /\
  s.vs_allocas = FEMPTY /\ fresh_vars_wrt st s ==>
  ?mr. mat_pending ce env st s s.vs_alloca_next mr caps /\
       mat_inv func ce env st s s.vs_alloca_next mr /\
       (!n1 n2 b1 sz1 b2 sz2.
          n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
          regions_disjoint b1 sz1 b2 sz2) /\
       (!n b sz. mr n = SOME (b,sz) <=>
          ?i off. i < LENGTH params /\ ~SND (EL i params) /\
            FST (EL i params) = n /\
            FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
            b = w2n (EL (idx + i) argv))
Proof
  strip_tac >> fs[internal_args_rel_def] >>
  `!i j. i < LENGTH params /\ j < LENGTH params /\
      FST (EL i params) = FST (EL j params) ==> i = j` by
    (fs[listTheory.EL_ALL_DISTINCT_EL_EQ, listTheory.EL_MAP] >> metis_tac[]) >>
  `?mr. !n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL (idx + i) argv)` by
    (simp[GSYM SKOLEM_THM] >> gen_tac >>
     Cases_on `?i off sz. i < LENGTH params /\ ~SND (EL i params) /\
       FST (EL i params) = n /\ FLOOKUP ce.ce_vars n = SOME (MemLoc off sz)`
     >- (pop_assum strip_assume_tac >>
         qexists_tac `SOME (w2n (EL (idx + i) argv),sz)` >>
         rpt gen_tac >> eq_tac
         >- (strip_tac >> gvs[] >> metis_tac[]) >>
         strip_tac >> `i = i'` by metis_tac[] >> gvs[]) >>
     qexists_tac `NONE` >> simp[] >> metis_tac[]) >>
  `LENGTH caps = LENGTH params` by metis_tac[listTheory.LENGTH_MAP] >>
  `!i. i < LENGTH params ==> FST (EL i caps) = FST (EL i params) /\
      FST (SND (EL i caps)) = SND (EL i params)` by
    (gen_tac >> disch_tac >>
     `EL i (MAP (\c. (FST c,FST (SND c))) caps) = EL i params` by
       asm_rewrite_tac [] >>
     pop_assum mp_tac >> qpat_x_assum `MAP _ caps = params` kall_tac >>
     Cases_on `EL i params` >> simp[listTheory.EL_MAP]) >>
  qexists_tac `mr` >> conj_tac
  >- (simp[mat_pending_def,listTheory.EVERY_EL] >> rpt strip_tac >>
      `n < LENGTH params` by decide_tac >>
      qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
      qpat_assum `!i. i < LENGTH params ==> ?off sz entry. _` drule >> strip_tac >>
      qexistsl_tac [`p`,`EL (n + idx) argv`,`off`,`sz`,`entry`] >>
      qpat_x_assum `(if SND (EL n params) then _ else _)` mp_tac >>
      Cases_on `SND (EL n params)`
      >- asm_rewrite_tac [] >>
      asm_rewrite_tac [] >> strip_tac >>
      reverse conj_tac >- asm_rewrite_tac [] >>
      qexistsl_tac [`n`,`off`] >> simp[]) >>
  conj_tac
  >- (simp[mat_inv_def,venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       loweringStateRelDefsTheory.local_ptrs_rel_def,
       loweringStateRelDefsTheory.local_region_def] >>
      `!name entry. lookup_scopes name [env] = SOME entry ==>
          ?off sz. FLOOKUP ce.ce_vars name = SOME (MemLoc off sz)` suffices_by
        (disch_tac >> rpt strip_tac >>
         qpat_assum `!name entry. lookup_scopes name [env] = SOME entry ==> _`
           drule >> strip_tac >> fs[]) >>
      rpt strip_tac >> fs[lookup_scopes_def,AllCaseEqs()] >>
      `name IN FDOM env` by fs[finite_mapTheory.FLOOKUP_DEF] >>
      `MEM name (MAP FST params)` by
        (qpat_x_assum `name IN FDOM env` mp_tac >> simp[]) >>
      pop_assum mp_tac >> simp[listTheory.MEM_EL,listTheory.EL_MAP] >>
      strip_tac >>
      qpat_assum `!i. i < LENGTH params ==> ?off sz entry. _` drule >>
      strip_tac >> qexistsl_tac [`off`,`sz`] >>
      asm_rewrite_tac [] >> simp[listTheory.EL_MAP]) >>
  reverse conj_tac >- (qpat_assum `!n b sz. mr n = SOME (b,sz) <=> _` mp_tac >>
    simp[NoAsms, arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  qpat_x_assum `mr n1 = SOME (b1,sz1)` mp_tac >>
  simp[] >> disch_then (qx_choose_then `ii` (qx_choose_then `oi` strip_assume_tac)) >>
  qpat_x_assum `mr n2 = SOME (b2,sz2)` mp_tac >>
  simp[] >> disch_then (qx_choose_then `jj` (qx_choose_then `oj` strip_assume_tac)) >>
  `ii <> jj` by (strip_tac >> fs[]) >>
  qpat_x_assum `!i j offi szi offj szj. _`
    (qspecl_then [`ii`,`jj`,`oi`,`sz1`,`oj`,`sz2`] mp_tac) >>
  asm_rewrite_tac [] >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_callee_materialize_captures[local]:
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  (!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
     lookup_var p s = SOME (EL (idx + i) argv) /\
     FLOOKUP J p = op_prov G (EL (idx + i) arg_ops) /\
     op_taint qt (Var p) = {}) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz. op_prov G (EL (idx + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL (idx + i) argv) /\
       w2n (EL (idx + i) argv) + sz <= b + bsz) /\
  (!mem. mem_agree_outside qt.t_mem s.vs_memory mem ==>
     internal_args_rel ce params env idx argv frontier mem) /\
  (!nm e. FLOOKUP env nm = SOME e ==> value_has_type e.type e.value) ==>
  EVERY (\c. op_taint qt (SND (SND c)) = {} /\
     (!p off sz e. ~FST (SND c) /\ SND (SND c) = Var p /\
       FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
       FLOOKUP env (FST c) = SOME e ==>
       ptr_covers J qt p s sz /\
       !w mem. lookup_var p s = SOME w /\
         mem_agree_outside qt.t_mem s.vs_memory mem ==>
         val_in_memory e.type e.value (w2n w) mem)) caps
Proof
  strip_tac >> simp[listTheory.EVERY_EL] >> qx_gen_tac `i` >> disch_tac >>
  `i < LENGTH params` by metis_tac[listTheory.LENGTH_MAP] >>
  `FST (EL i caps) = FST (EL i params) /\
   FST (SND (EL i caps)) = SND (EL i params)` by
    (`EL i (MAP (\c. (FST c,FST (SND c))) caps) = EL i params` by
       asm_rewrite_tac[] >>
     pop_assum mp_tac >> Cases_on `EL i params` >>
     simp[listTheory.EL_MAP, IgnAsm `MAP _ caps = params`]) >>
  qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >>
  disch_then (qx_choose_then `q` strip_assume_tac) >> simp[] >>
  rpt strip_tac
  >- (simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `!mem. mem_agree_outside _ _ mem ==> _` drule >>
  rewrite_tac[internal_args_rel_def] >> strip_tac >>
  qpat_assum `!i. i < LENGTH params ==> ?off sz e. _` drule >>
  strip_tac >> gvs[] >>
  mp_tac (CONJUNCT1 memory_encoding_bridges) >>
  rewrite_tac[memory_encoding_bridge_def] >> metis_tac[]
QED

Theorem intcall_callee_capture_buffer[local]:
  compile_internal_entry_prefix ce params T st = ((ce',caps,rpc),st') /\
  0 < LENGTH s.vs_params /\ fresh_vars_wrt st' u /\
  run_inst_seq (emitted_insts st st') s = OK u ==>
  lookup_var (STRING #"%" (toString st.cs_next_var)) u = SOME (HD s.vs_params) /\
  not_fresh_at st' (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule compile_internal_entry_prefix_shape >> simp[] >>
  disch_then (strip_assume_tac o REWRITE_RULE [GSYM arithmeticTheory.ADD1]) >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v = update_var p (HD s.vs_params) s` >>
  `step_inst_base (mk_inst st.cs_next_id PARAM [Lit 0w] [p]) s = OK v` by
    simp[Once venomExecSemanticsTheory.step_inst_base_def,
         venomInstTheory.mk_inst_def, Abbr `v`, listTheory.EL] >>
  qpat_x_assum `run_inst_seq (emitted_insts _ _) _ = _` mp_tac >>
  simp[listTheory.GENLIST_CONS, combinTheory.o_DEF, run_inst_seq_def] >>
  strip_tac >>
  `lookup_var p u = lookup_var p v` by
    (irule appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars >>
     goal_assum (drule_at Any) >>
     simp[listTheory.EVERY_GENLIST, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def, Abbr `p`, ASCIInumbersTheory.toString_inj]) >>
  `lookup_var p v = SOME (HD s.vs_params)` by
    simp[Abbr `v`, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  asm_rewrite_tac[] >>
  `p IN FDOM u.vs_vars` by
    (qpat_assum `lookup_var p u = lookup_var p v` (rewrite_tac o single o GSYM) >>
     qpat_assum `lookup_var p v = SOME _` mp_tac >>
     qpat_assum `lookup_var p u = lookup_var p v` (rewrite_tac o single o GSYM) >>
     simp[lookup_var_def, finite_mapTheory.flookup_thm, NoAsms]) >>
  qpat_assum `fresh_vars_wrt st' u`
    (qspec_then `st.cs_next_var` mp_tac o
     REWRITE_RULE [loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  simp[Abbr `p`, loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj, NoAsms] >>
  qpat_assum `p IN FDOM u.vs_vars` mp_tac >> (simp[])
QED

Theorem intcall_callee_package_slots[local]:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor alloc_len
      (mut,nr,rr,name,args,(dflts:expr list),ret,ss)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) /\
  compile_internal_entry_prefix ce params has_rb st = ((ce',caps,rpc),st') ==>
  (!n p sz. FLOOKUP ce'.ce_vars n <> SOME (PtrVar p sz)) /\
  ce'.ce_imm_alloca = NONE /\
  ce'.ce_return_buf =
    (if has_rb then SOME (PtrVar (Var (STRING #"%" (toString st.cs_next_var))) 32)
     else NONE)
Proof
  strip_tac >>
  conj_tac
  >- (drule compile_internal_entry_prefix_shape >> strip_tac >>
      qpat_assum `ce'.ce_vars = ce.ce_vars` (rewrite_tac o single) >>
      gvs[package_internal_fn_def,set_internal_package_target_def,
          update_cenv_nonreentrant_def, cj 3 build_compile_env_vars]) >>
  `ce.ce_imm_alloca = NONE /\
   ce.ce_return_buf = (if has_rb then SOME (MemLoc (SND (allocate_args
     (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY)) 32) else NONE)` by
    (Cases_on `allocate_args (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY` >>
     gvs[package_internal_fn_def, set_internal_package_target_def,
         update_cenv_nonreentrant_def, build_compile_env_def, pairTheory.UNCURRY,
         allocate_internal_special_vars_def] >> IF_CASES_TAC >> simp[]) >>
  reverse (Cases_on `has_rb`)
  >- (qpat_x_assum `compile_internal_entry_prefix _ _ F _ = _` mp_tac >>
      simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def,
           pairTheory.UNCURRY] >>
      strip_tac >> gvs[]) >>
  `ce'.ce_imm_alloca = NONE` by
    (qpat_x_assum `compile_internal_entry_prefix _ _ T _ = _` mp_tac >>
     simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def,
          pairTheory.UNCURRY] >>
     strip_tac >> gvs[]) >>
  drule compile_internal_entry_prefix_shape >> simp[]
QED

(* Restrict the code of the selected real function to the body that
   starts after its prologue and lock. *)
Theorem intcall_lowering_suffix[local]:
  !ce params has_rb nr key trans view ctor ilen ss rt entry final
   ce2 pc imm prologue a ce' b callee.
    compile_internal_function ce params has_rb nr key trans view ctor ilen
      ss rt entry = ((),final) /\
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,pc,imm),prologue) /\
    (if nr then compile_nonreentrant_lock key trans view else comp_return ())
      prologue = ((),a) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss a = (ce',b) /\
    cs_extends entry a /\ fn_has_code entry final callee ==>
    cs_extends a final /\ fn_has_code a b callee /\ fn_has_code b final callee /\
    (if block_is_terminated b then ((),b)
     else comp_ignore_bind
       (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
       (case rt of NONE => emit_inst RET [pc] []
         | SOME _ => emit_inst INVALID [] []) b) = ((),final)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a b` by metis_tac[stmts_env_cs_mono, cs_mono_def] >>
  `(if block_is_terminated b then ((),b)
     else comp_ignore_bind
       (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
       (case rt of NONE => emit_inst RET [pc] []
         | SOME _ => emit_inst INVALID [] []) b) = ((),final)` by
    (qpat_x_assum `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`
       mp_tac >>
     simp[compile_internal_function_entry_factorization, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, comp_get_def, compile_stmts_env] >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `block_is_terminated b` >> simp[] >>
     Cases_on `rt` >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  `cs_extends b final` by
    (Cases_on `block_is_terminated b` >> gvs[cs_extends_refl] >>
     Cases_on `(if nr then compile_nonreentrant_unlock key trans view
       else comp_return ()) b` >>
     rename1 `_ = (u,m)` >> Cases_on `u` >>
     gvs[comp_ignore_bind_def, comp_bind_def] >>
     `cs_extends b m` by
       (Cases_on `nr` >> Cases_on `view` >> Cases_on `trans` >>
        gvs[compile_nonreentrant_unlock_def, comp_return_def] >>
        fs[GSYM emit_inst_def, emit_void_def] >>
        metis_tac[cs_extends_emit_inst, cs_extends_refl]) >>
     `cs_extends m final` by
       (Cases_on `rt` >> gvs[] >> metis_tac[cs_extends_emit_inst]) >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends a final` by metis_tac[cs_extends_trans] >>
  `fn_has_code a final callee` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

(* On a normal landing the source tail casts NoneV. Admissibility of
   that tail rules out the TypeError from a nonvoid result type. *)
Theorem intcall_callable_fallthrough_void[local]:
  evaluate_type (get_tenv cx) ret = SOME ret_tv /\
  gas_admissible (intcall_rest cx name mut nr ss prev ret_tv) expr_vv_res_ok es /\
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
  eval_stmts (cx with stk updated_by CONS (NONE,name)) ss locked = (INL (),ee)
  ==> ret = NoneT
Proof
  strip_tac >>
  `?post. unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := prev) =
          (INL (),post)` by
    (Cases_on `nr /\ ~is_view_mut mut` >> Cases_on `cx.nonreentrant_slot` >>
     simp[unlock_if_nr_def, Excl "is_view_mut_def",
          vyperStateTheory.return_def, release_nonreentrant_lock_execution]) >>
  `safe_cast ret_tv NoneV <> NONE` by
    (strip_tac >>
     `intcall_rest cx name mut nr ss prev ret_tv es =
        (INR (Error (TypeError "IntCall cast ret")),post)` by
       simp[intcall_rest_def, vyperStateTheory.ignore_bind_def,
            vyperStateTheory.bind_def, vyperStateTheory.finally_unless_halt_def,
            vyperStateTheory.finally_def, vyperStateTheory.try_def,
            Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def",
            pop_function_def, set_scopes_def, vyperStateTheory.return_def,
            vyperStateTheory.raise_def, vyperStateTheory.lift_option_type_def] >>
     qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     pure_rewrite_tac[gas_admissible_def] >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[expr_vv_res_ok_def]) >>
  `ret_tv = NoneTV` by
    (Cases_on `ret_tv` >> fs[Once vyperValueOperationTheory.safe_cast_def] >>
     rename1 `BaseTV bt` >> Cases_on `bt` >>
     fs[Once vyperValueOperationTheory.safe_cast_def, pairTheory.UNCURRY] >>
     gvs[AllCaseEqs()] >> metis_tac[vyperASTTheory.bound_nchotomy]) >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_NoneTV_imp_NoneT]
QED

Theorem intcall_callee_fallthrough_exit:
  evaluate_type (get_tenv cx) ret = SOME ret_tv /\
  gas_admissible (intcall_rest cx name mut nr ss prev ret_tv) expr_vv_res_ok es /\
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
  eval_stmts (cx with stk updated_by CONS (NONE,name)) ss locked = (INL (),ee) /\
  rt = (if ret = NoneT then NONE else SOME ret) /\
  (ret = NoneT ==> ce.ce_returns_count = 0) /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
  ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr /\ ~view ==> ~cx.txn.is_static) /\
  ~block_is_terminated b /\
  (if block_is_terminated b then ((),b)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key T view else comp_return ())
     (case rt of NONE => emit_inst RET [Var rpc] []
       | SOME _ => emit_inst INVALID [] []) b) = ((),final) /\
  fn_has_code b final callee /\ stmt_lands NoLoop b (INL ()) s /\
  ret_pc_ok ce b s /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     dead_lo_ok H (DF H) lo ce (cx with stk updated_by CONS (NONE,name)) /\
     state_rel H callee ce (cx with stk updated_by CONS (NONE,name)) ee s /\
     ghost_inv_at (DF H) lo d ce (cx with stk updated_by CONS (NONE,name)) ee G tn s)
  ==>
  intcall_callee_src cx name mut nr ss es = (INL NoneV,ee) /\
  ?G' tn'. tn'.t_mem = tn.t_mem /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,PG) (s,G,tn) []
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (return_unlock_state ce s),G',tn') /\
      intret_q H callee ce (cx with stk updated_by CONS (NONE,name)) ret_tv NoneV ee
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (return_unlock_state ce s)) /\
      stor_taint_ok_at (DF H) tn' (return_unlock_state ce s) /\
      (!i. i < lo /\ i IN tn'.t_mem ==>
        imm_section_dead (cx_tops cx)
          (mem_bytes_at 0 lo (return_unlock_state ce s).vs_memory) i)
Proof
  strip_tac >> conj_tac
  >- (pure_rewrite_tac[intcall_callee_src_def, vyperStateTheory.ignore_bind_def,
                       vyperStateTheory.bind_def, vyperStateTheory.try_def,
                       vyperStateTheory.return_def] >>
      simp[Excl "lock_if_nr_def", Excl "is_view_mut_def", vyperStateTheory.try_def,
           vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
           vyperStateTheory.return_def]) >>
  drule_all intcall_callable_fallthrough_void >> strip_tac >>
  `compile_stmt ce NoLoop (BaseT BoolT) (Return NONE) b = ((),final)` by
    gvs[Once stmtLoweringTheory.compile_stmt_def,
        stmtLoweringTheory.compile_return_unlock_def] >>
  reverse (Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`)
  >- (qexistsl [`G`,`tn`] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac `cxf = cx with stk updated_by CONS (NONE,name)` >>
  `allocas_from lo s /\ op_taint tn (Var rpc) = {} /\
   (nr /\ ~view ==> ~s.vs_call_ctx.cc_static)` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
     drule state_rel_call_ctx_rel >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def, Abbr `cxf`,
          bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts` by
    fs[loweringPostsTheory.stmt_lands_def] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `sa` |-> `b`, `sb` |-> `final`,
                  `func` |-> `callee`, `lctx` |-> `NoLoop`, `ty` |-> `BaseT BoolT`,
                  `slot_size` |-> `sz`] compile_return_none_int_origin_ptr_taint) >>
  simp[] >> strip_tac >>
  qexistsl [`G'`,`tn'`] >> simp[] >> qx_gen_tac `Hfinal` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `Hfinal` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac
  >- (simp[intret_q_def, loweringStateRelDefsTheory.result_rel_def,
            loweringStateRelDefsTheory.intret_vals_match_def] >>
      qexists_tac `s` >> simp[] >>
      qexists_tac `(return_unlock_state ce s).vs_inst_idx` >>
      simp[venom_state_component_equality]) >>
  qpat_assum `dead_lo_ok Hfinal _ _ _ _`
    (mp_then (Pos hd) mp_tac return_unlock_exit_taint) >>
  simp[Abbr `cxf`, cx_tops_def, get_module_code_stk_irrelevant] >>
  disch_then (qspecl_then [`tn'`,`tn`,`s`,`ee`,`d`,`G`] mp_tac) >>
  simp[]
QED

Theorem intcall_callee_block_terminated_test[local]:
  block_is_terminated st <=>
    st.cs_current_insts <> [] /\ is_terminator (LAST st.cs_current_insts).inst_opcode
Proof
  Cases_on `st.cs_current_insts` >> simp[block_is_terminated_def]
QED

Theorem intcall_callee_open_append[local]:
  st'.cs_current_insts = st.cs_current_insts ++ code /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\ ~block_is_terminated st ==>
  ~block_is_terminated st'
Proof
  Cases_on `code` >- simp[intcall_callee_block_terminated_test] >>
  strip_tac >>
  qpat_assum `EVERY _ (h::t)`
    (qspec_then `LAST (h::t)` mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
  simp[intcall_callee_block_terminated_test, rich_listTheory.MEM_LAST]
QED

Theorem intcall_callee_capture_open[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  entry.cs_current_insts = [] ==>
  ~block_is_terminated capture
Proof
  strip_tac >> drule_then strip_assume_tac compile_internal_entry_prefix_shape >>
  gvs[emitted_insts_def, intcall_callee_block_terminated_test, mk_inst_def, is_terminator_def]
QED

Theorem intcall_callee_fixed_reserve_resources[local]:
  (if reserve then
     comp_bind (compile_fixed_region_with_id ilen)
       (\ar. comp_return (SOME (SND ar).buf_operand))
   else comp_return NONE) capture = (imm,reserved) ==>
  (~block_is_terminated capture ==> ~block_is_terminated reserved) /\
  (!p. imm = SOME (Var p) ==> ~not_fresh_at capture p)
Proof
  Cases_on `reserve` >- (
    simp[comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
    strip_tac >> PairCases_on `ar` >> gvs[] >>
    drule_then strip_assume_tac compile_fixed_region_with_id_result >>
    conj_tac
    >- (strip_tac >> irule intcall_callee_open_append >>
        goal_assum (drule_at Any) >> simp[mk_inst_def, is_terminator_def]) >>
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[comp_return_def]
QED

Theorem intcall_callee_materialize_shape[local]:
  !caps ce st ce' st'.
    materialize_internal_params ce caps st = (ce',st') ==>
    st'.cs_current_bb = st.cs_current_bb /\
    st.cs_next_var <= st'.cs_next_var /\
    ce' = ce with ce_vars := ce'.ce_vars /\
    ((EVERY (\c. !p. SND (SND c) = Var p ==> not_fresh_at st p) caps /\
      (!n p sz. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p)) ==>
     (!n p sz. FLOOKUP ce'.ce_vars n = SOME (PtrVar (Var p) sz) ==> not_fresh_at st' p)) /\
    ?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
           EVERY (\i. i.inst_opcode <> INVOKE) code /\
           EVERY (\i. ~is_terminator i.inst_opcode) code
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >> simp[] >~ [`emit_op _ _`]
      >- (simp[emit_op_def, emit_void_def, comp_bind_def,
               comp_ignore_bind_def, comp_return_def, fresh_id_def,
               fresh_var_def, emit_def] >>
          strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY decide_tac
          >- (strip_tac >>
              qpat_x_assum `EVERY _ caps /\ _ ==> !n p sz. _` mp_tac >>
              (impl_tac >- (
                qmatch_asmsub_abbrev_tac `materialize_internal_params _ caps cs = _` >>
                `st.cs_next_var <= cs.cs_next_var` by simp[Abbr `cs`] >>
                conj_tac
                >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
                    irule freshWritesTheory.not_fresh_at_mono >>
                    qexists_tac `st` >> simp[] >>
                    qpat_assum `EVERY _ caps` (qspec_then `c` mp_tac o SRULE [listTheory.EVERY_MEM]) >> simp[]) >>
                map_every qx_gen_tac [`nm`,`p`,`sz`] >>
                Cases_on `h0 = nm` >> simp[finite_mapTheory.FLOOKUP_UPDATE]
                >- (strip_tac >> qpat_assum `STRING _ _ = p` (SUBST1_TAC o SYM) >>
                    simp[Abbr `cs`, loweringStateRelDefsTheory.not_fresh_at_def,
                         ASCIInumbersTheory.toString_inj]) >>
                strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `st` >> simp[] >>
                qpat_assum `!n p sz. FLOOKUP ce.ce_vars n = _ ==> _` irule >>
                goal_assum (drule_at Any))) >>
              simp[]) >>
          qexists_tac `[mk_inst st.cs_next_id ALLOCA [Lit (n2w n0)]
                          [STRING #"%" (toString st.cs_next_var)];
                        mk_inst (st.cs_next_id + 1) MSTORE
                          [Var (STRING #"%" (toString st.cs_next_var)); h2] []] ++ code` >>
          simp[mk_inst_def, is_terminator_def]) >>
      strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  TRY (first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `EVERY _ caps /\ _ ==> !n p sz. _` mp_tac >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`nm`,`p`,`sz`] >>
     Cases_on `h0 = nm` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])) >>
  simp[]
QED

Theorem intcall_callee_materialize_avoids[local]:
  !caps ce st ce' st' p.
    materialize_internal_params ce caps st = (ce',st') /\
    not_fresh_at st p /\
    ~MEM (Var p) (MAP (SND o SND) caps) /\
    (!n sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)) ==>
    !n sz. FLOOKUP ce'.ce_vars n <> SOME (PtrVar (Var p) sz)
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[]) >>
      Cases_on `x` >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >>
      simp[finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gvs[loweringStateRelDefsTheory.not_fresh_at_def, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
                arithmeticTheory.LESS_EQ_ADD]) >>
  strip_tac >> first_x_assum drule >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

(* Preserve the reserved immutable operand in the materialization invariant.
   The decoration does not change either the instructions or the locals. *)
Theorem intcall_callee_materialize_imm[local]:
  !caps ce st ce' st' imm.
    materialize_internal_params ce caps st = (ce',st') ==>
    materialize_internal_params (ce with ce_imm_alloca := imm) caps st =
      (ce' with ce_imm_alloca := imm,st')
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >> simp[] >>
      simp[emit_op_def, emit_void_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def, fresh_id_def,
           fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem intcall_callee_stack_size_imm[local,simp]:
  !params ce imm.
    internal_stack_size (ce with ce_imm_alloca := imm) params =
    internal_stack_size ce params
Proof
  Induct >- simp[internal_stack_size_def] >> PairCases >>
  simp[internal_stack_size_def]
QED

Theorem intcall_callee_materialize_imm_invs[local,simp]:
  (mat_pending (ce with ce_imm_alloca := imm) env st s f0 mr caps =
   mat_pending ce env st s f0 mr caps) /\
  (mat_inv f (ce with ce_imm_alloca := imm) env st s f0 mr =
   mat_inv f ce env st s f0 mr)
Proof
  simp[mat_pending_def, mat_inv_def, loweringStateRelDefsTheory.local_ptrs_rel_def,
       loweringStateRelDefsTheory.local_region_def]
QED

Theorem intcall_callee_return_buf_imm[local,simp]:
  (return_buf_ptr dest (ce with ce_imm_alloca := imm) G tn s =
    return_buf_ptr dest ce G tn s) /\
  (return_buf_ptr dest (ce with <|ce_imm_alloca := imm; ce_alloca_locals := flag|>) G tn s =
    return_buf_ptr dest ce G tn s)
Proof
  Cases_on `dest` >- simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
  rename1 `SOME ret_range` >> PairCases_on `ret_range` >>
  simp[bodyPtrDefsTheory.return_buf_ptr_def]
QED

Theorem intcall_callee_ghost_imm[local]:
  ghost_inv_at D lo dest (ce with <|ce_imm_alloca := imm; ce_alloca_locals := flag|>) cx es G tn s <=>
  ghost_inv_at D lo dest (ce with ce_imm_alloca := NONE) cx es G tn s /\
  (!x. lo <> 0 /\ imm = SOME (Var x) ==> FLOOKUP G x = NONE /\ op_taint tn (Var x) = {})
Proof
  Cases_on `dest` >- (simp[bodyPtrDefsTheory.ghost_inv_at_def,
    bodyPtrDefsTheory.return_buf_ptr_def] >> metis_tac[]) >>
  rename1 `SOME ret_range` >> PairCases_on `ret_range` >>
  simp[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.return_buf_ptr_def] >> metis_tac[]
QED

Theorem intcall_callee_alloca_room[local]:
  alloca_inv s /\ fmp_room ctx func s ==>
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
   s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp)
Proof
  rw[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def,
     fmp_room_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
  res_tac >> decide_tac
QED

Theorem intcall_callee_scratch_joint[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  alloca_room ctx func s /\ fmp_room ctx func s /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\ FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n w) ==>
  ?u G' tn'.
    alloca_inv u /\
    (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas i.inst_id = SOME (b,sz) ==>
      sz = w2n w) /\
    u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    alloca_room ctx func u /\ fmp_room ctx func u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb u) /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP u.vs_allocas aid = SOME r) /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
        FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < u.vs_alloca_next)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')
Proof
  strip_tac >> drule_then strip_assume_tac abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = (n2w n : 256 word)` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit w] [out]` >>
  `MEM ins (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     goal_assum (drule_at Any) >> simp[Abbr `ins`, Abbr `out`, Abbr `w`]) >>
  `s.vs_alloca_next + w2n w < dimword (:256) /\
   alloca_room ctx func (s with <|vs_allocas := s.vs_allocas |+
     (sa.cs_next_id,(s.vs_alloca_next,w2n w)); vs_alloca_next := s.vs_alloca_next + w2n w|>)` by
    (qspecl_then [`func`,`s`,`ins`,`w`,`ctx`] mp_tac alloca_room_fresh >>
     `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit w] /\
      ins.inst_id = sa.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >> simp[]) >>
  qabbrev_tac `t = update_var out (n2w s.vs_alloca_next) (s with <|
     vs_allocas := s.vs_allocas |+ (sa.cs_next_id,(s.vs_alloca_next,w2n w));
     vs_alloca_next := s.vs_alloca_next + w2n w|>)` >>
  `step_inst_base ins s = OK t` by
    (simp[Abbr `t`, Abbr `ins`, GSYM wordsTheory.n2w_w2n] >>
     qspecl_then [`sa.cs_next_id`, `w2n w`, `out`, `s`] mp_tac loweringHaltTheory.step_alloca_fresh >>
     simp[finite_mapTheory.FLOOKUP_DEF, wordsTheory.w2n_lt]) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `exec_alloca ins s w = OK t` by
    simp[Abbr `ins`, Abbr `t`, mk_inst_def,
         venomExecSemanticsTheory.exec_alloca_def, finite_mapTheory.FLOOKUP_DEF] >>
  `fmp_room ctx func t` by
    (irule fmp_room_exec_alloca >> goal_assum (drule_at Any) >>
     simp[Abbr `ins`, mk_inst_def]) >>
  `fmp_room ctx func u` by
    (qspecl_then [`ctx`,`func`,`t`,`u`] mp_tac fmp_room_fields_cong >>
     simp[Abbr `u`]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK u,step_prov PG G ins t,step_taint ins s t tn)` by
    (`emitted_insts sa sb = [ins]` by simp[Abbr `ins`, Abbr `out`, Abbr `w`] >>
     rpt gen_tac >>
     `ptr_inst_ok D lo 0 ctx func G tn ins s` by
       (simp[Abbr `ins`] >> irule exprPtrUnwrapAllocationTheory.unwrap_alloc_ptr_check >>
        simp[] >> simp[Abbr `t`, update_var_def]) >>
     simp[NoAsms, Abbr `u`] >>
     irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sa` >>
     simp[emitHelperPropsTheory.inst_extends_def, run_inst_seq_def,
          fragExecMemTheory.run_inst_seq_mem_ok_last, fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     simp[Abbr `ins`, mk_inst_def, is_terminator_def,
          instMemFrontierTheory.below_frontier_no_ranges,
          memSafeRunTheory.inst_dload_in_section_def] >>
     rpt strip_tac >> Cases_on `pre` >> gvs[]) >>
  `step_prov PG G ins t = G |+ (out,(s.vs_alloca_next,w2n w)) /\
   step_taint ins s t tn = tn with <| t_mem := tn.t_mem UNION
       {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + w2n w};
       t_var := tn.t_var |+ (out,{}) |>` by
    (qspecl_then [`sa.cs_next_id`, `w2n w`, `out`, `s`, `t`, `PG`, `G`, `tn`] mp_tac
       allocationPtrTheory.fresh_alloca_ghost >>
     simp[wordsTheory.w2n_lt, finite_mapTheory.FLOOKUP_DEF, Abbr `ins`]) >>
  `alloca_inv t` by metis_tac[allocaHistoryTheory.history_base_alloca_inv] >>
  `alloca_inv u` by simp[Abbr `u`, venomMemProofsTheory.alloca_inv_set_inst_idx] >>
  `!i v b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit v] /\ FLOOKUP u.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n v` by
    (simp[NoAsms, Abbr `u`, Abbr `t`, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt gen_tac >> Cases_on `i.inst_id = sa.cs_next_id` >> simp[] >> strip_tac
     >- (`i = ins` by
           (irule localPtrsPropsTheory.fn_inst_ids_distinct_inj >>
            conj_tac >- simp[Abbr `ins`, mk_inst_def] >>
            qexists_tac `func` >> simp[]) >>
         gvs[Abbr `ins`, mk_inst_def]) >>
     qpat_assum `!i w b sz. _ ==> sz = w2n w` irule >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`u`,`step_prov PG G ins t`,`step_taint ins s t tn`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `u`, Abbr `t`, update_var_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, venom_state_component_equality,
    ptrDisciplineTheory.op_taint_def] >>
  TRY (irule alloca_room_fields >> goal_assum (drule_at Any) >> simp[])
  >- (fs[ptrDisciplineTheory.allocas_from_def, finite_mapTheory.FLOOKUP_UPDATE,
         AllCaseEqs()] >> metis_tac[])
  >- (rpt strip_tac >> simp[loweringStateRelDefsTheory.fresh_vars_wrt_def, Abbr `out`] >>
      fs[loweringStateRelDefsTheory.fresh_vars_wrt_def])
  >- (fs[finite_mapTheory.FLOOKUP_DEF] >> rw[] >> gvs[])
  >- (rw[] >> gvs[AllCaseEqs()]) >>
  rpt strip_tac >> `x <> out` by fs[Abbr `out`,loweringStateRelDefsTheory.not_fresh_at_def] >> simp[]
QED

(* The trace of the lock itself is known before selecting the gas marks of
   the body.  The intrinsic horizon of this prefix pins the lock word. *)
Theorem intcall_callee_lock_trace[local]:
  cx.nonreentrant_slot = SOME key ==>
  (SND (lock_if_nr cx T view es)).storage_trace =
    es.storage_trace ++ [StorageLock key]
Proof
  strip_tac >> Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  Cases_on `lookup_storage (n2w key) (es.tStorage cx.txn.target) = 1w` >>
  simp[lock_if_nr_def, acquire_nonreentrant_lock_execution,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, check_not_static_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.raise_def]
QED

Theorem intcall_callee_lock_horizon[local]:
  valid_horizon cx st H (tr ++ [StorageLock key]) ==>
  valid_horizon cx st H tr /\
  storage_locks_separated (FST H) (SND H) /\ MEM key (SND H)
Proof
  simp[valid_horizon_def, storage_observations_ok_def, storage_trace_locks_def]
QED

Theorem intcall_callee_bad_lock[local]:
  cx.nonreentrant_slot = SOME key /\ ~s.vs_halted /\
  ~storage_trace_domain cx st0 (es.storage_trace ++ [StorageLock key]) ==>
  gas_outcome_full (DF,lo,explicit,ctx,callee,PG) (cx_tops cx) cx st0
    (intcall_callee_src cx name mut T ss) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bad_nil >> reverse conj_tac >- simp[] >>
  gen_tac >>
  Cases_on `lock_if_nr cx T (is_view_mut mut) (es with gas_obs := tail)` >>
  drule intcall_callee_lock_trace >>
  disch_then (qspecl_then [`is_view_mut mut`, `es with gas_obs := tail`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `q` >>
  rewrite_tac[intcall_callee_src_def] >>
  once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_def] >>
  qpat_assum `lock_if_nr _ _ _ _ = _` (rewrite_tac o single) >> simp[] >>
  Cases_on `try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss; return NoneV od)
                handle_function r` >> simp[] >>
  `storage_trace_frame
     (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss; return NoneV od)
          handle_function)` by
    (irule storage_trace_frame_try >> simp[storage_trace_frame_function_handler] >>
     irule storage_trace_frame_ignore_bind >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  metis_tac[storage_trace_frame_preserves_bad_domain]
QED

Theorem intcall_callee_lock_clean[local]:
  dead_lo_ok (H : (bool # 256 word # type_value) list # num list) D lo cenv cx /\
  stor_taint_ok_at D tn s /\ MEM key (SND H) /\ key < dimword (:256) ==>
  key_taint tn.t_trans (n2w key) = {}
Proof
  simp[bodyPtrDefsTheory.dead_lo_ok_def, bodyPtrDefsTheory.stor_taint_ok_at_def] >>
  strip_tac >> simp[ptrDisciplineTheory.key_taint_def, pred_setTheory.EXTENSION] >>
  rpt strip_tac >>
  qpat_assum `tn.t_trans SUBSET _`
    (mp_tac o REWRITE_RULE[pred_setTheory.SUBSET_DEF]) >>
  disch_then (qspec_then `(n2w key,x)` mp_tac) >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  simp[sourceUnitExecutionTheory.cx_dead_def] >>
  simp[loweringStateRelDefsTheory.storage_dead_def]
QED

(* Each scratch consumer reads the preceding write, even after cursor advance. *)
Theorem intcall_callee_lock_steps[local]:
  (step_inst_base (mk_inst id EQ [Var x;Lit 1w] [y])
     ((update_var x v s) with vs_inst_idx := j) =
   OK (update_var y (bool_to_word (v = 1w))
       ((update_var x v s) with vs_inst_idx := j))) /\
  (step_inst_base (mk_inst id ISZERO [Var x] [y])
     ((update_var x v s) with vs_inst_idx := j) =
   OK (update_var y (bool_to_word (v = 0w))
       ((update_var x v s) with vs_inst_idx := j))) /\
  (step_inst_base (mk_inst id ASSERT [Var x] [])
     ((update_var x v s) with vs_inst_idx := j) =
   if v = 0w then
     Abort Revert_abort (revert_state (set_returndata []
       ((update_var x v s) with vs_inst_idx := j)))
   else OK ((update_var x v s) with vs_inst_idx := j))
Proof
  rpt conj_tac >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  simp[venomExecSemanticsTheory.exec_pure1_def,
       venomExecSemanticsTheory.exec_pure2_def, mk_inst_def,
       instIdxIndepTheory.eval_op_inst_idx,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var]
QED

Theorem intcall_callee_lock_scratch_allocas[local]:
  allocas_from lo ((update_var x v s) with vs_inst_idx := j) =
  allocas_from lo s
Proof
  simp[ptrDisciplineTheory.allocas_from_def, update_var_def]
QED

Theorem intcall_callee_lock_scratch_taint[local]:
  (op_taint (step_taint (mk_inst id TLOAD [Lit k] [y]) s u tn) (Var y) =
     key_taint tn.t_trans k) /\
  (op_taint (step_taint (mk_inst id EQ [Var x;Lit 1w] [y]) s u tn) (Var y) = {}) /\
  (op_taint (step_taint (mk_inst id ISZERO [Var x] [y]) s u tn) (Var y) = {}) /\
  (op_taint tn (Lit k) = {})
Proof
  rpt conj_tac >>
  simp[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.step_taint_def,
       ptrDisciplineTheory.out_taint_def, ptrDisciplineTheory.set_var_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE, mk_inst_def, eval_operand_def] >>
  Cases_on `lookup_var x s` >> simp[]
QED

(* The lock uses only scalar temporaries. In particular the loaded lock
   word must be clean before it can feed EQ. *)
Theorem intcall_callee_lock_inst_ptr[local]:
  MEM op [TLOAD; EQ; ISZERO; ASSERT; TSTORE] /\
  (!a. MEM a args ==> op_taint tn a = {}) /\
  (op = EQ ==> !x y. args <> [Var x; Var y]) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst id op args outs) s
Proof
  strip_tac >>
  `op <> INVOKE /\ ~is_terminator op` by (fs[] >> simp[is_terminator_def]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, mk_inst_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
  conj_tac
  >- (fs[] >> simp[contextCodegenRelTheory.source_memory_read_ranges_def,
                    codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  conj_tac
  >- (fs[] >> simp[contextCodegenRelTheory.source_memory_read_ranges_def, mk_inst_def] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `step_inst 0 ctx (mk_inst id op args outs) s = OK s'` by
        simp[venomExecSemanticsTheory.step_inst_non_invoke, mk_inst_def] >>
      drule_at Any oracleExecPropsTheory.step_inst_noninvoke_oracle >>
      fs[mk_inst_def] >> strip_tac >> fs[]) >>
  rpt strip_tac >> drule opcodeClassTheory.step_inst_base_no_halt >> simp[]
QED

Theorem intcall_callee_lock_ptr_seq[local]:
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ key_taint tn.t_trans (n2w key) = {} ==>
  ?G' tn'. !D.
    inst_seq_ptr D lo ctx func PG G tn
      (transient_lock_code key view st) s G' tn'
Proof
  strip_tac >>
  `!D. ?G' tn'. inst_seq_ptr D lo ctx func PG G tn
      (transient_lock_code key view st) s G' tn'` suffices_by
    (strip_tac >> first_assum (qspec_then `DF0` strip_assume_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  gen_tac >> simp[transientLockPropsTheory.transient_lock_code_def] >>
  `step_inst_base (mk_inst st.cs_next_id TLOAD [Lit (n2w key)]
      [STRING #"%" (toString st.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (tload (n2w key) s) s)` by
    (irule transientLockPropsTheory.step_TLOAD >> simp[eval_operand_def]) >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def, RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (irule intcall_callee_lock_inst_ptr >> simp[intcall_callee_lock_scratch_taint]) >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def, RIGHT_EXISTS_AND_THM,
       intcall_callee_lock_steps] >>
  conj_tac >- (irule intcall_callee_lock_inst_ptr >>
               simp[intcall_callee_lock_scratch_allocas, intcall_callee_lock_scratch_taint,
                    exprPtrUnwrapFramesTheory.copy_allocas_update,
                    DISJ_IMP_THM, FORALL_AND_THM]) >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def, RIGHT_EXISTS_AND_THM,
       intcall_callee_lock_steps] >>
  conj_tac >- (irule intcall_callee_lock_inst_ptr >>
               simp[intcall_callee_lock_scratch_allocas, intcall_callee_lock_scratch_taint,
                    exprPtrUnwrapFramesTheory.copy_allocas_update,
                    DISJ_IMP_THM, FORALL_AND_THM]) >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def, RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (irule intcall_callee_lock_inst_ptr >>
               simp[intcall_callee_lock_scratch_allocas, intcall_callee_lock_scratch_taint,
                    exprPtrUnwrapFramesTheory.copy_allocas_update,
                    DISJ_IMP_THM, FORALL_AND_THM]) >>
  Cases_on `tload (n2w key) s = 1w` >>
  simp[intcall_callee_lock_steps, venomExecSemanticsTheory.bool_to_word_def] >>
  Cases_on `view` >> simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def, RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (irule intcall_callee_lock_inst_ptr >>
               simp[intcall_callee_lock_scratch_allocas, intcall_callee_lock_scratch_taint,
                    exprPtrUnwrapFramesTheory.copy_allocas_update,
                    DISJ_IMP_THM, FORALL_AND_THM]) >>
  CASE_TAC >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def]
QED

(* Use the exterior frame at the pre-store state; a non-view guard then
   changes exactly the transient word and its taint. *)
Theorem intcall_callee_lock_landing_ghost[local]:
  compile_nonreentrant_lock key T view st = ((),a) /\
  run_inst_seq (emitted_insts st a) s = OK u /\
  ghost_inv_at D lo dret ce cx es G tn s /\
  local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  locked.scopes = es.scopes /\
  (!x. not_fresh_at st x ==>
       FLOOKUP Gl x = FLOOKUP G x /\ op_taint tnl (Var x) = op_taint tn (Var x)) /\
  tnl.t_mem = tn.t_mem /\ tnl.t_stor = tn.t_stor /\ tnl.t_imm = tn.t_imm /\
  tnl.t_trans = (if view then tn.t_trans else key_update tn.t_trans (n2w key) {}) /\
  (~view ==> dead_lo_ok (H : (bool # 256 word # type_value) list # num list) D lo ce cx /\
             s.vs_call_ctx.cc_address = cx.txn.target /\
             storage_locks_separated (FST H) (SND H) /\ MEM key (SND H) /\
             key < dimword (:256)) ==>
  ghost_inv_at D lo dret ce cx locked Gl tnl (u with vs_inst_idx := j)
Proof
  strip_tac >>
  qabbrev_tac `checked = transientLockProps$transient_lock_checked_state st key s` >>
  `u = if view then checked else tstore (n2w key) 1w checked` by
    (drule transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
     disch_then (fn th => qpat_x_assum `run_inst_seq _ _ = OK _`
        (mp_tac o REWRITE_RULE[th, transientLockPropsTheory.transient_lock_code_execution])) >>
     simp[Abbr `checked`, AllCaseEqs()] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==> lookup_var x checked = lookup_var x s` by
    (rpt strip_tac >>
     `!n. st.cs_next_var <= n ==> x <> STRING #"%" (toString n)` by
       fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     simp[Abbr `checked`, transientLockPropsTheory.transient_lock_checked_state_def,
          emitHelperPropsTheory.lookup_var_update_var]) >>
  `!x. op_taint (tnl with t_trans := tn.t_trans) (Var x) = op_taint tnl (Var x)` by
    simp[ptrDisciplineTheory.op_taint_def] >>
  `ghost_inv_at D lo dret ce cx locked Gl (tnl with t_trans := tn.t_trans) checked` by
    (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qexistsl [`G`, `es`, `s`, `st`, `tn`] >>
     simp[Abbr `checked`, transientLockPropsTheory.transient_lock_checked_state_def,
          update_var_def]) >>
  Cases_on `view`
  >- (`tnl with t_trans := tn.t_trans = tnl` by
        simp[ptrDisciplineTheory.taint_component_equality] >>
      fs[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx]) >>
  fs[] >>
  qabbrev_tac `pre_tn = tnl with t_trans := tn.t_trans` >>
  `ghost_inv_at D lo dret ce cx locked Gl
      (pre_tn with t_trans := key_update pre_tn.t_trans (n2w key) {})
      (tstore (n2w key) 1w checked with vs_inst_idx := j)` by
    (irule (SRULE [] (Q.INST [`tr` |-> `T`] (INST_TYPE [alpha |-> ``:256``]
        augAssignFullStoreGhostTheory.ghost_inv_at_storage_word_store))) >>
     conj_tac
     >- simp[Abbr `checked`, transientLockPropsTheory.transient_lock_checked_state_def,
             update_var_def] >>
     conj_tac
     >- (qexists_tac `H` >> simp[nonreentrantSourceTheory.nonreentrant_storage_dead_frame]) >>
     qexists_tac `locked` >> simp[]) >>
  `pre_tn with t_trans := key_update pre_tn.t_trans (n2w key) {} = tnl` by
    simp[Abbr `pre_tn`, ptrDisciplineTheory.taint_component_equality] >>
  fs[]
QED

Theorem intcall_callee_lock_step_taint_fields[local]:
  MEM op [TLOAD;EQ;ISZERO;ASSERT;TSTORE] /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  (step_taint (mk_inst id op args outs) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id op args outs) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id op args outs) s u tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst id op args outs) s u tn).t_trans =
    (if op = TSTORE then ptrDiscipline$store_taint TSTORE tn
       (mk_inst id op args outs) s tn.t_trans else tn.t_trans)
Proof
  strip_tac >>
  `new_site_bytes s u = {}` by
    (simp[ptrDisciplineTheory.new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF,
          pred_setTheory.EXTENSION] >> metis_tac[]) >>
  fs[] >> gvs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.adopt_reset_def,
             ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
             ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.step_writes_def,
             ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
             codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  namedCases_on `args` ["", "a as1"] >> simp[] >>
  namedCases_on `as1` ["", "b as2"] >> simp[] >>
  Cases_on `as2` >> simp[] >> CASE_TAC >> simp[]
QED

Theorem intcall_callee_lock_success_ghost_fields[local]:
  inst_seq_ptr D lo ctx fn PG G tn (transient_lock_code key view st) s Gl tnl /\
  tload (n2w key) s <> 1w /\ (~view ==> ~s.vs_call_ctx.cc_static) ==>
  (!x. not_fresh_at st x ==>
       FLOOKUP Gl x = FLOOKUP G x /\ op_taint tnl (Var x) = op_taint tn (Var x)) /\
  tnl.t_mem = tn.t_mem /\ tnl.t_stor = tn.t_stor /\ tnl.t_imm = tn.t_imm /\
  tnl.t_trans = (if view then tn.t_trans else key_update tn.t_trans (n2w key) {})
Proof
  strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id TLOAD [Lit (n2w key)]
      [STRING #"%" (toString st.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (tload (n2w key) s) s)` by
    (irule transientLockPropsTheory.step_TLOAD >> simp[eval_operand_def]) >>
  Cases_on `view` >> fs[] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[transientLockPropsTheory.transient_lock_code_def,
       fragGasSeqPtrTheory.inst_seq_ptr_def, intcall_callee_lock_steps,
       venomExecSemanticsTheory.bool_to_word_def] >>
  simp[transientLockPropsTheory.step_TSTORE_lit, update_var_def,
       fragGasSeqPtrTheory.inst_seq_ptr_def] >>
  strip_tac >> rpt (qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` kall_tac) >>
  (reverse conj_tac
   >- (simp[intcall_callee_lock_step_taint_fields, tstore_def] >>
       simp[ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.op_taint_def,
            mk_inst_def, eval_operand_def, intcall_callee_lock_step_taint_fields])) >>
  rpt gen_tac >> strip_tac >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  simp[decoderGhostFramePtrTheory.step_prov_other_output,
       decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def]
QED

Theorem intcall_callee_lock_shape[local]:
  compile_nonreentrant_lock key T view sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\ inst_extends sa sb
Proof
  strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `view` >> gvs[comp_return_def] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  metis_tac[same_blocks_def, emitHelperPropsTheory.inst_extends_def,
            emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, listTheory.APPEND_ASSOC]
QED

(* The successful guard only writes its three scratch registers and, for a
   non-view function, the lock slot. Frame concrete entry resources at the
   cursor used by the first instruction of the body. *)
Theorem intcall_callee_lock_concrete_fields[local]:
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u /\ fresh_vars_wrt pro s ==>
    fresh_vars_wrt a (u with vs_inst_idx := LENGTH a.cs_current_insts) /\ ((u with vs_inst_idx := LENGTH a.cs_current_insts).vs_halted = s.vs_halted) /\
    (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_current_bb = s.vs_current_bb /\ (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_labels = s.vs_labels /\
    (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_allocas = s.vs_allocas /\ (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
    (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_fmp = s.vs_fmp /\ (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_initial_fmp = s.vs_initial_fmp /\
    (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_memory = s.vs_memory /\
    (!x. not_fresh_at pro x ==> lookup_var x (u with vs_inst_idx := LENGTH a.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule_then assume_tac transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
  drule_then assume_tac transientLockFramePropsTheory.compile_nonreentrant_lock_transient_counter >>
  `fresh_vars_wrt a (transient_lock_checked_state pro key s)` by
    (irule transientLockFramePropsTheory.transient_lock_checked_fresh_vars >> simp[]) >>
  Cases_on `view` >>
  gvs[transientLockPropsTheory.transient_lock_code_execution, AllCaseEqs(),
      loweringStateRelDefsTheory.fresh_vars_wrt_def, tstore_def] >>
  simp[transientLockPropsTheory.transient_lock_checked_state_def, update_var_def] >>
  simp[loweringStateRelDefsTheory.not_fresh_at_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem intcall_callee_lock_open[local]:
  compile_nonreentrant_lock key T view pro = ((),a) ==>
  ~block_is_terminated a
Proof
  strip_tac >> drule_then strip_assume_tac intcall_callee_lock_shape >>
  drule_then assume_tac transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
  Cases_on `view` >> Cases_on `pro.cs_current_insts` >>
  gvs[emitHelperPropsTheory.inst_extends_def, block_is_terminated_def,
      transientLockPropsTheory.transient_lock_code_def, mk_inst_def, is_terminator_def,
      listTheory.LAST_CONS_cond, listTheory.LAST_APPEND_CONS]
QED

Theorem intcall_callee_lock_landing_concrete[local]:
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u /\
  stmt_state_rel H ctx fn ce cx es s /\ state_rel H fn ce cx locked u /\
  locked.scopes = es.scopes /\ locked.immutables = es.immutables /\
  fresh_vars_wrt pro s /\ local_ptrs_reserved ce pro /\ ret_pc_ok ce pro s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  return_buf_frame dret ce pro s /\
  ~s.vs_halted /\ s.vs_current_bb = pro.cs_current_bb ==>
    stmt_state_rel H ctx fn ce cx locked (u with vs_inst_idx := LENGTH a.cs_current_insts) /\
    fresh_vars_wrt a (u with vs_inst_idx := LENGTH a.cs_current_insts) /\ local_ptrs_reserved ce a /\ ret_pc_ok ce a (u with vs_inst_idx := LENGTH a.cs_current_insts) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    return_buf_frame dret ce a (u with vs_inst_idx := LENGTH a.cs_current_insts) /\ ~block_is_terminated a /\
    ~(u with vs_inst_idx := LENGTH a.cs_current_insts).vs_halted /\ (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_current_bb = a.cs_current_bb /\
    (u with vs_inst_idx := LENGTH a.cs_current_insts).vs_inst_idx = LENGTH a.cs_current_insts /\
    (!x. not_fresh_at pro x ==> lookup_var x (u with vs_inst_idx := LENGTH a.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> simp[LET_THM, blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  drule_all intcall_callee_lock_concrete_fields >>
  simp[LET_THM, blockPrefixEquivTheory.lookup_var_set_inst_idx, NoAsms] >> strip_tac >>
  drule_then assume_tac transientLockFramePropsTheory.compile_nonreentrant_lock_transient_counter >>
  drule_then strip_assume_tac intcall_callee_lock_shape >>
  drule_then assume_tac intcall_callee_lock_open >>
  `stmt_state_rel H ctx fn ce cx locked u` by
    (fs[stmt_state_rel_def] >>
     rpt conj_tac
     >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >> simp[])
     >- (irule alloca_room_fields >> qexists_tac `s` >> simp[])
     >- (irule fmp_room_fields >> qexists_tac `s` >> simp[])
     >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >> simp[] >>
         rpt strip_tac >> qexists_tac `id` >>
         metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame])
     >- (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
         metis_tac[local_ptrs_reserved_imm_base]) >>
     metis_tac[]) >>
  simp[stmt_state_rel_inst_idx] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `pro` >> simp[])
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`ce`,`s`,`pro`] >>
      simp[blockPrefixEquivTheory.lookup_var_set_inst_idx] >> metis_tac[])
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`pro`] >>
  simp[blockPrefixEquivTheory.lookup_var_set_inst_idx] >> metis_tac[]
QED

Theorem intcall_callee_lock_path[local]:
  compile_nonreentrant_lock key T view sa = ((),sb) /\
  fn_has_code sa sb callee /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ key_taint tn.t_trans (n2w key) = {} ==>
  ?G' tn'. (!D. inst_seq_ptr D lo ctx callee PG G tn (emitted_insts sa sb) s G' tn') /\
    (!u. run_inst_seq (emitted_insts sa sb) s = OK u ==>
         !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) []
           (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    (!a u. run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
         ?j. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) []
           (Abort a (u with vs_inst_idx := j),G',tn'))
Proof
  strip_tac >>
  drule_then assume_tac transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
  `?G' tn'. !D. inst_seq_ptr D lo ctx callee PG G tn (emitted_insts sa sb) s G' tn'` by
    (simp[] >> irule intcall_callee_lock_ptr_seq >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
     (emitted_insts sa sb)` by
    (Cases_on `view` >> simp[transientLockPropsTheory.transient_lock_code_def, is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule nonreentrantEntryTheory.lock_opcodes_mem_ok >>
     Cases_on `view` >> simp[transientLockPropsTheory.transient_lock_code_def]) >>
  `!i w. MEM i (transient_lock_code key view sa) ==>
       unitTransformDefs$dalloca_no_wrap i w` by
    (Cases_on `view` >> simp[transientLockPropsTheory.transient_lock_code_def] >>
     rpt strip_tac >> gvs[]) >>
  `(ctx_has_dalloca ctx ==>
      !pre i post u. emitted_insts sa sb = pre ++ i::post /\
        run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_assum `emitted_insts _ _ = transient_lock_code _ _ _`
       (SUBST1_TAC o SYM) >>
     qpat_assum `emitted_insts _ _ = _ ++ _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`G'`,`tn'`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `sa` >> simp[]) >>
  rpt strip_tac >>
  `?bb. lookup_block s.vs_current_bb callee.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[emitHelperPropsTheory.inst_extends_def] >>
     drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> metis_tac[]) >>
  drule_all fragGasCopyLoopTheory.run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qexists_tac `j` >> rpt gen_tac >>
  first_assum irule >> first_assum MATCH_ACCEPT_TAC
QED

Theorem intcall_callee_lock_read[local]:
  state_rel (H : (bool # 256 word # type_value) list # num list) func ce cx (es with scopes := []) t /\
  MEM key (SND H) /\ key < dimword (:256) /\
  s.vs_transient = t.vs_transient /\ s.vs_call_ctx = t.vs_call_ctx ==>
  lookup_storage (n2w key) (es.tStorage cx.txn.target) = tload (n2w key) s /\
  s.vs_call_ctx.cc_static = cx.txn.is_static
Proof
  strip_tac >> drule_then assume_tac state_rel_call_ctx_rel >>
  conj_tac
  >- (`tload (n2w key) s = tload (n2w key) t` by
        simp[venomStateTheory.tload_def, venomStateTheory.contract_transient_def] >>
      `storage_read_live H T ((es with scopes := []).tStorage cx.txn.target)
         (n2w key) (BaseTV (UintT 256))` by
        simp[accountsRelPropsTheory.nonreentrant_slot_read_live] >>
      drule_all state_rel_transient_lookup >> simp[]) >>
  fs[loweringStateRelDefsTheory.call_ctx_rel_def]
QED

Theorem intcall_callee_lock_run[local]:
  cx.nonreentrant_slot = SOME key /\
  lookup_storage (n2w key) (es.tStorage cx.txn.target) = tload (n2w key) s /\
  s.vs_call_ctx.cc_static = cx.txn.is_static /\
  compile_nonreentrant_lock key T view sa = ((),sb) ==>
  (?e u. lock_if_nr cx T view es = (INL (),e) /\
          run_inst_seq (emitted_insts sa sb) s = OK u) \/
  (?e u. lock_if_nr cx T view es = (INR (Error (RuntimeError "nonreentrant lock")),e) /\
          run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u) \/
  (?e u. lock_if_nr cx T view es = (INR (Error (RuntimeError "write in static context")),e) /\
          run_inst_seq (emitted_insts sa sb) s = Abort ExHalt_abort u)
Proof
  strip_tac >> drule_then assume_tac transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
  Cases_on `tload (n2w key) s = 1w` >> Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  simp[transientLockPropsTheory.transient_lock_code_execution, lock_if_nr_def,
       acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
       return_def, check_not_static_def, check_def, assert_def, raise_def]
QED

(* A matched lock abort exits before evaluating the body. *)
Theorem intcall_callee_lock_abort_source:
  lock_if_nr cx nr (is_view_mut mut) es = (INR (Error (RuntimeError msg)),ee) ==>
  !tail. intcall_callee_src cx name mut nr ss (es with gas_obs := tail) =
           (INR (Error (RuntimeError msg)),ee with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  drule_then (qspec_then `tail` assume_tac) externalCallSelectedTheory.lock_if_nr_with_gas_obs >>
  rewrite_tac[intcall_callee_src_def] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_def] >> simp[]
QED

Theorem intcall_callee_lock_abort[local]:
  ~s.vs_halted /\
  lock_if_nr cx nr (is_view_mut mut) es = (INR (Error (RuntimeError msg)),ee) /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,PG) (s,G,tn) []
         (Abort ab u,Gl,tnl)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,callee,PG) (cx_tops cx) cx st0
    (intcall_callee_src cx name mut nr ss) (es,s,G,tn) Q
    (\H res ee gt r. intcall_callee_exit_full (DF,lo) H func cenv cx mut nr
      rtv retc rb n m t tn0 res ee gt r)
Proof
  strip_tac >>
  irule gas_outcome_full_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gl`, `ee`, `Abort ab u`, `INR (Error (RuntimeError msg))`, `tnl`] >>
  conj_tac >- (irule intcall_callee_lock_abort_source >> first_assum ACCEPT_TAC) >>
  simp[exit_result_def, intcall_callee_exit_full_def, intcall_callee_exit_def,
       expr_exit_def, haltExitProjTheory.halt_exit_not_halt]
QED

(* The capture phase updates only the two return locations. *)
Theorem intcall_callee_capture_env[local]:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),st') ==>
  ce1 = ce with <|ce_return_buf := ce1.ce_return_buf;
                  ce_return_pc := ce1.ce_return_pc|>
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[compile_env_component_equality]
QED

Theorem intcall_callee_param_capture_names[local]:
  !params i st caps next st'.
    compile_internal_param_decls params i st = ((caps,next),st') ==>
    MAP FST caps = MAP FST params /\
    EVERY (\c. ?p. SND (SND c) = Var p) caps
Proof
  Induct >- simp[moduleLoweringTheory.compile_internal_param_decls_def, comp_return_def] >>
  PairCases >> simp[moduleLoweringTheory.compile_internal_param_decls_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_internal_param_decls _ _ _ = (r,_)` >>
  PairCases_on `r` >> gvs[] >> first_x_assum (drule_then strip_assume_tac) >> simp[]
QED

Theorem intcall_callee_prefix_capture_names[local]:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),st') ==>
  MAP FST caps = MAP FST params /\ EVERY (\c. ?p. SND (SND c) = Var p) caps
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_internal_param_decls _ _ _ = (r,_)` >>
  PairCases_on `r` >> gvs[] >> drule intcall_callee_param_capture_names >> simp[]
QED

Theorem intcall_callee_package_metadata[local]:
  set_internal_package_target target
    (package_internal_fn tops T (K global_nonreentrant_slot) deploy ilen
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss',rt) ==>
  ce = (build_compile_env tops Internal mut name args ret ss T) with
     <|ce_is_ctor := deploy; ce_raw_return := rr;
       ce_nonreentrant := (nr,global_nonreentrant_slot,T,mut = View);
       ce_target := target|> /\
  MAP FST params = MAP FST args /\ rt = (if ret = NoneT then NONE else SOME ret)
Proof
  simp[set_internal_package_target_def, package_internal_fn_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[vyperTypingTheory.MAP_FST_ZIP_MAP_FST, LENGTH_compute_pass_via_stack]
QED

Theorem intcall_callee_body_formals[local]:
  ce.ce_vars = (build_compile_env tops Internal mut name args ret ss T).ce_vars /\
  MAP FST params = MAP FST args /\
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),st') /\
  materialize_internal_params ce1 caps st'' = (ce2,a) ==>
  (!n l. FLOOKUP ce2.ce_vars n = SOME l ==> MEM n (MAP FST args)) /\
  (!n. MEM n (MAP FST args) ==> ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz))
Proof
  strip_tac >>
  drule_then strip_assume_tac intcall_callee_prefix_capture_names >>
  `ce1.ce_vars = ce.ce_vars` by metis_tac[compile_internal_entry_prefix_shape] >>
  conj_tac
  >- (rpt strip_tac >> drule_all bodySimEntryTheory.materialize_internal_params_bound >>
      simp[] >> Cases_on `FLOOKUP ce1.ce_vars n` >> gvs[] >>
      metis_tac[bodySimEntryTheory.build_compile_env_bound]) >>
  rpt strip_tac >> irule materialize_internal_params_ptrs >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[cj 1 build_compile_env_vars]
QED

(* This is the actual body environment, not a comparison with the
   entry variant that omits constructor reservation. *)
Theorem intcall_callee_body_env[local]:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),st') /\
  materialize_internal_params ce1 caps st'' = (ce2,a) ==>
  ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> =
  ce with <|ce_vars := ce2.ce_vars; ce_return_buf := ce2.ce_return_buf;
            ce_return_pc := ce2.ce_return_pc; ce_imm_alloca := imm;
            ce_alloca_locals := T|>
Proof
  strip_tac >>
  drule_then assume_tac intcall_callee_capture_env >>
  drule_then strip_assume_tac intcall_callee_materialize_shape >>
  simp[compile_env_component_equality] >>
  rpt conj_tac >>
  qpat_assum `ce2 = _` (fn th => simp[Once th]) >>
  qpat_assum `ce1 = _` (fn th => simp[Once th])
QED

Theorem intcall_callee_formal_type[local]:
  body_ce.ce_var_type = (build_compile_env tops Internal mut name args ret ss T).ce_var_type /\
  supported_function_body tops Internal args ss /\ MEM (id,ty) args ==>
  body_ce.ce_var_type id = SOME ty
Proof
  strip_tac >>
  `~MEM id (MAP FST (collect_locals ss))` by
    metis_tac[supported_function_arg_not_collect_locals] >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule supportedProgramTheory.supported_function_body_binding_contract >> simp[]) >>
  `ALOOKUP (REVERSE args) id = SOME ty` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     simp[listTheory.MAP_REVERSE, listTheory.ALL_DISTINCT_REVERSE]) >>
  `ALOOKUP (REVERSE (collect_locals ss)) id = NONE` by
    simp[alistTheory.ALOOKUP_NONE, listTheory.MAP_REVERSE] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[listTheory.REVERSE_APPEND, alistTheory.ALOOKUP_APPEND]
QED

Theorem intcall_callee_classified[local]:
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops /\
  classify_functions tops = (exts,ints,fb,ctor) ==>
  MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,ds,ret,ss)) ints
Proof
  strip_tac >>
  `MEM (subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,ds,ret,ss))
      (FST (SND (classify_functions tops)))` by
    (pure_rewrite_tac[constSubstTheory.subst_consts_fn_def, loweringShapePropsTheory.MEM_classify_internal] >>
     qexistsl_tac [`ds`, `ss`] >> simp[constSubstTheory.subst_consts_fn_def]) >>
  qpat_assum `classify_functions tops = (exts,ints,fb,ctor)`
    (fn eq => first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [eq]))
QED

Theorem intcall_callee_allocs[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops /\
  (if deploy then ?rbc. lower_vyper_deploy_unit tops policy rbc = SOME unit
   else lower_vyper_runtime_unit tops policy = SOME unit) ==>
  fn_allocs_ok tops (subst_consts_fn (module_consts_env tops []) (mut,nr,rr,name,args,ds,ret,ss))
Proof
  strip_tac >> qabbrev_tac `cl = classify_functions tops` >>
  PairCases_on `cl` >> fs[markerTheory.Abbrev_def] >>
  `MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,ds,ret,ss)) cl1` by
    metis_tac[intcall_callee_classified] >>
  Cases_on `deploy` >> fs[] >>
  metis_tac[lower_vyper_deploy_unit_allocs_ok, lower_vyper_runtime_unit_allocs_ok]
QED

Theorem intcall_callee_body_bounds[local]:
  fn_allocs_ok tops (mut,nr,rr,name,args,ds,ret,ss) /\
  allocLimitsProps$alloc_env_agree
    (build_compile_env tops Internal mut name args ret ss F) body_ce /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  env_consistent env cx locked /\
  type_stmts env ret ss = SOME env' /\ ~body_ce.ce_is_external /\
  ~supported_stmts_expr_exists (const_name_root_mods body_ce.ce_modules) ss /\
  qualified_stmts_decls_ok body_ce.ce_modules ss ==>
  locals_alloc_ok body_ce env /\ stmts_exprs_ok body_ce ss
Proof
  strip_tac >> drule_all allocLimitsPropsTheory.fn_allocs_ok_body >> strip_tac >>
  conj_tac
  >- (simp[bodySimTheory.locals_alloc_ok_def] >> rpt strip_tac >>
      `MEM (id,ty) args` by metis_tac[] >>
      fs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  irule externalBodyWidthsTheory.stmt_exprs_ok_from_traversal_bounds >> simp[] >>
  irule externalBodyWidthsTheory.type_stmts_excludes_bad_widths >>
  goal_assum (drule_at Any) >>
  fs[env_consistent_def] >> conj_tac
  >- (rpt strip_tac >>
      fs[env_scopes_consistent_def, vyperTypeSystemTheory.well_formed_type_def] >>
      `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
      metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  fs[env_context_consistent_def]
QED

Theorem intcall_callee_subst_return_alloc[local]:
  fn_allocs_ok tops (subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,ds,ret,ss)) ==>
  type_memory_bytes (build_compile_env tops Internal mut name args ret ss F) ret < 2 ** 64
Proof
  simp[constSubstTheory.subst_consts_fn_def, fn_allocs_ok_def] >> strip_tac >>
  `type_memory_bytes (build_compile_env tops Internal mut name args ret ss F) ret =
   type_memory_bytes (build_compile_env tops Internal mut name args ret
     (subst_consts_stmts (module_consts_env tops []) ss) F) ret` by
    (irule type_memory_bytes_struct_fields >> simp[build_compile_env_ce_struct_fields]) >>
  simp[]
QED

(* Updates made by the internal entry do not change module metadata. *)
Theorem intcall_callee_body_metadata_mods[local]:
  contract_inv mods exps ctx caller cx /\ ALOOKUP mods src = SOME tops /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit_mods mods exps policy rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps policy = SOME unit) /\
  ctx = unit.cu_context /\
  body_ce = (build_compile_env_unit mods src Internal mut name args ret ss T) with
    <|ce_is_ctor := cx.in_deploy; ce_target := policy.rpol_target;
      ce_raw_return := rr; ce_nonreentrant := nrinfo;
      ce_vars := vars; ce_return_buf := rb; ce_return_pc := rpc;
      ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  contract_inv mods exps ctx body_ce (cx with stk updated_by CONS (src,name)) /\
  module_body_inv mods src tops body_ce (cx with stk updated_by CONS (src,name)) /\
  allocLimitsProps$alloc_env_agree
    (build_compile_env_unit mods src Internal mut name args ret ss F) body_ce /\
  body_ce.ce_var_type = (build_compile_env_unit mods src Internal mut name args ret ss T).ce_var_type /\
  ~body_ce.ce_is_external
Proof
  strip_tac >>
  fs[contract_inv_def, module_body_inv_def, cenv_module_pins_mods_def,
     allocLimitsPropsTheory.alloc_env_agree_def, get_tenv_stk_irrelevant,
     build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  gvs[immutable_section_layout_mods_def] >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  conj_tac >- (qexistsl [`policy`, `unit`] >> simp[]) >>
  conj_tac
  >- (simp[NoAsms, bodyCallSupportTheory.linked_body_calls_resolved_def,
           vyperTypeInvariantsTheory.context_function_live_context] >>
      qpat_assum `linked_body_calls_resolved _ cx`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [bodyCallSupportTheory.linked_body_calls_resolved_def])) >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> res_tac
QED

Theorem intcall_callee_body_metadata[local]:
  body_inv tops ctx caller cx /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit tops policy rbc = SOME unit
   else lower_vyper_runtime_unit tops policy = SOME unit) /\
  ctx = unit.cu_context /\
  body_ce = (build_compile_env tops Internal mut name args ret ss T) with
    <|ce_is_ctor := cx.in_deploy; ce_target := policy.rpol_target;
      ce_raw_return := rr; ce_nonreentrant := nrinfo;
      ce_vars := vars; ce_return_buf := rb; ce_return_pc := rpc;
      ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  body_inv tops ctx body_ce (cx with stk updated_by CONS (NONE,name)) /\
  allocLimitsProps$alloc_env_agree
    (build_compile_env tops Internal mut name args ret ss F) body_ce /\
  body_ce.ce_var_type = (build_compile_env tops Internal mut name args ret ss T).ce_var_type /\
  ~body_ce.ce_is_external
Proof
  strip_tac >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `src` |-> `NONE`]
    (SPEC_ALL intcall_callee_body_metadata_mods)) >>
  simp[NoAsms, lower_vyper_deploy_unit_mods_singleton,
       lower_vyper_runtime_unit_mods_singleton, build_compile_env_unit_singleton] >>
  impl_tac >- fs[] >>
  strip_tac >> simp[bodySimTheory.body_inv_split_def, bodySimTheory.cenv_module_pins_split_def] >>
  fs[module_body_inv_def, contract_inv_def]
QED

Theorem intcall_callee_dead_lo[local]:
  body_ce.ce_is_ctor = caller.ce_is_ctor /\ dead_lo_ok H D lo caller cx ==>
  dead_lo_ok H D lo body_ce (cx with stk updated_by CONS k)
Proof
  simp[bodyPtrDefsTheory.dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def,
       cx_tops_def, get_module_code_stk_irrelevant]
QED

Theorem module_body_inv_active_module[local]:
  module_body_inv mods src tops cenv cx ==> cenv.ce_module = src
Proof
  simp[module_body_inv_def]
QED

Theorem intcall_callee_expr_inv_mods[local]:
  contract_inv mods exps ctx caller cx /\
  contract_inv mods exps ctx body_ce (cx with stk updated_by CONS (src,name)) /\
  module_body_inv mods src tops body_ce (cx with stk updated_by CONS (src,name)) /\
  expr_sim_inv_mods mods caller cx tenv (es with scopes := prev) /\
  env_consistent env (cx with stk updated_by CONS (src,name)) locked /\
  state_well_typed locked /\ popped_keys_indexed locked.scopes /\
  locked.accounts = es.accounts /\ locked.outcomes = es.outcomes /\
  env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
  env.bare_global_assignable = tenv.bare_global_assignable /\
  env.toplevel_vtypes = tenv.toplevel_vtypes /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
      ?p sz. FLOOKUP body_ce.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> body_ce.ce_var_type id = SOME ty) ==>
  expr_sim_inv_mods mods body_ce (cx with stk updated_by CONS (src,name)) env locked
Proof
  strip_tac >>
  drule_then assume_tac module_body_inv_active_module >>
  `env.current_src = src` by
    fs[env_consistent_def, env_context_consistent_def, current_module_def] >>
  `body_ce.ce_func_return_type = caller.ce_func_return_type /\
   body_ce.ce_flag_member_id = caller.ce_flag_member_id /\
   body_ce.ce_flag_n_members = caller.ce_flag_n_members /\
   body_ce.ce_method_id = caller.ce_method_id /\
   body_ce.ce_struct_fields = caller.ce_struct_fields /\
   body_ce.ce_hashmap_info = caller.ce_hashmap_info /\
   body_ce.ce_module_var_type = caller.ce_module_var_type /\
   body_ce.ce_module_vars = caller.ce_module_vars /\
   body_ce.ce_modules = caller.ce_modules /\
   body_ce.ce_is_ctor = caller.ce_is_ctor` by
    (`(cx with stk updated_by CONS (src,name)).in_deploy = cx.in_deploy` by simp[] >>
     drule_all intcall_callee_compile_tables_mods >> simp[]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[exprSimHypsDefsTheory.expr_sim_inv_mods_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def,
       exprSimHypsDefsTheory.bare_globals_layout_def,
       get_module_code_stk_irrelevant, get_tenv_stk_irrelevant,
       context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!sid id ty. _ ==> _ /\ _`
    (qspecl_then [`sid`,`id`,`ty`] mp_tac) >> simp[]
QED

Theorem intcall_callee_expr_inv_singleton[local]:
  body_inv tops ctx caller cx /\ body_inv tops ctx body_ce (cx with stk updated_by CONS (NONE,name)) /\
  expr_sim_inv caller cx tenv (es with scopes := prev) /\
  env_consistent env (cx with stk updated_by CONS (NONE,name)) locked /\
  state_well_typed locked /\ popped_keys_indexed locked.scopes /\
  locked.accounts = es.accounts /\ locked.outcomes = es.outcomes /\
  env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
  env.bare_global_assignable = tenv.bare_global_assignable /\
  env.toplevel_vtypes = tenv.toplevel_vtypes /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
      ?p sz. FLOOKUP body_ce.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> body_ce.ce_var_type id = SOME ty) ==>
  expr_sim_inv body_ce (cx with stk updated_by CONS (NONE,name)) env locked
Proof
  strip_tac >>
  qpat_assum `body_inv tops ctx caller cx` (fn inv =>
    MAP_EVERY strip_assume_tac
      [MATCH_MP bodySimTheory.body_inv_contract inv, MATCH_MP body_inv_main_code inv]) >>
  qpat_assum `body_inv tops ctx body_ce _` (fn inv =>
    MAP_EVERY assume_tac
      [MATCH_MP bodySimTheory.body_inv_contract inv, MATCH_MP bodySimTheory.body_inv_module inv]) >>
  `expr_sim_inv_mods [(NONE,tops)] caller cx tenv (es with scopes := prev)` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_split_def] >>
  drule_all intcall_callee_expr_inv_mods >> strip_tac >>
  `ALOOKUP (cx with stk updated_by CONS (NONE,name)).sources
     (cx with stk updated_by CONS (NONE,name)).txn.target = SOME [(NONE,tops)]` by
    (qpat_assum `contract_inv [(NONE,tops)] [] ctx body_ce _`
       (ACCEPT_TAC o MATCH_MP contract_inv_singleton_source_modules)) >>
  qpat_assum `contract_inv [(NONE,tops)] [] ctx body_ce _`
    (assume_tac o MATCH_MP contract_inv_immutable_section_layout) >>
  `body_ce.ce_module = NONE` by
    (qpat_assum `body_inv tops ctx body_ce _`
       (mp_tac o MATCH_MP body_inv_module_locations) >> simp[]) >>
  drule_all bodyFullPostsModsTheory.expr_sim_inv_mods_singleton >>
  disch_then (qspecl_then [`locked`, `env`] (fn eq =>
    qpat_assum `expr_sim_inv_mods _ body_ce _ env locked` (ACCEPT_TAC o EQ_MP eq)))
QED

(* The compiler's placeholder return type for a void body does not affect
   either statement compilation: a well-typed void body has no valued return. *)
Theorem intcall_callee_body_return_type[local]:
  body_inv tops ctx ce cx /\ supported_stmts tops bindings ss /\
  type_stmts env ret ss = SOME env' /\
  rt = (if ret = NoneT then NONE else SOME ret) ==>
  stmts_env ce NoLoop ret ss =
    stmts_env ce NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss /\
  stmts_env (gas_shadow_env T ce) NoLoop ret (MAP gas_shadow_stmt ss) =
    stmts_env (gas_shadow_env T ce) NoLoop
      (case rt of SOME ty => ty | NONE => BaseT BoolT) (MAP gas_shadow_stmt ss)
Proof
  strip_tac >> Cases_on `ret = NoneT` >> gvs[] >>
  drule_then assume_tac externalCallSelectedTheory.type_stmts_none_valued_return >>
  conj_tac
  >- (irule stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >>
      simp[] >> metis_tac[]) >>
  irule stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >>
  simp[gas_shadow_valued_return] >> metis_tac[gas_shadow_supported_stmts]
QED

(* The selected body client gets the same source typing and substitution
   facts used by the ordinary body simulation. *)
Definition intcall_callee_body_inputs_def:
  intcall_callee_body_inputs tops ctx pushed body_ce ret rt ss locked <=>
    let compiled_ss = subst_consts_stmts (module_consts_env tops []) ss in
    body_inv tops ctx body_ce pushed /\
    (!gs. eval_stmts pushed ss (locked with gas_obs := gs) =
          eval_stmts pushed compiled_ss (locked with gas_obs := gs)) /\
    stmts_env body_ce NoLoop ret compiled_ss =
      stmts_env body_ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty) compiled_ss /\
    stmts_env (gas_shadow_env T body_ce) NoLoop ret (MAP gas_shadow_stmt compiled_ss) =
      stmts_env (gas_shadow_env T body_ce) NoLoop
        (case rt of NONE => BaseT BoolT | SOME ty => ty) (MAP gas_shadow_stmt compiled_ss) /\
    ?bindings env env_after.
      supported_stmts tops bindings compiled_ss /\
      (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) compiled_ss ==>
                occurs_abi_decode_target target tops) /\
      body_const_cells_agree [(NONE,tops)] pushed env locked /\
      expr_sim_inv body_ce pushed env locked /\ ce_locals_declared body_ce env /\
      locals_alloc_ok body_ce env /\ type_stmts env ret compiled_ss = SOME env_after /\
      stmts_exprs_ok body_ce compiled_ss /\ call_evaluation_safe pushed (int_calls_stmts compiled_ss)
End

(* This interface separates source typing and the paired body compiler
   from the execution that reaches the body. The return frame is abstract. *)
Theorem intcall_callee_locked_body_frag[local]:
  body_inv tops ctx caller cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops /\
  ds_comp = subst_consts_exprs (module_consts_env tops []) ds /\
  ss_comp = subst_consts_stmts (module_consts_env tops []) ss /\
  intcall_entry_full (DF,lo,d) H tops ctx func caller cx tenv name es sa sb vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
    body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss_comp) /\
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit tops policy rbc = SOME unit
   else lower_vyper_runtime_unit tops policy = SOME unit) /\
  ctx = unit.cu_context /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy ilen
      (mut,nr,rr,name,args,ds_comp,ret,ss_comp)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> /\
  frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,PG,callee,sf)
    (cx with stk updated_by CONS (NONE,name)) RetQ body_ce ret ==>
    stmt_frag_full (DF,lo,dret,ctx,shadow_ctx,PG,callee,sf)
      (cx with stk updated_by CONS (NONE,name)) NoLoop RetQ body_ce
      (stmts_env body_ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty) ss_comp)
      (stmts_env (gas_shadow_env T body_ce) NoLoop
        (case rt of NONE => BaseT BoolT | SOME ty => ty) (MAP gas_shadow_stmt ss_comp))
      (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) locked /\
    gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) (stmt_res_ok NoLoop) locked /\
    body_ce.ce_is_ctor = caller.ce_is_ctor /\
    intcall_callee_body_inputs tops ctx (cx with stk updated_by CONS (NONE,name))
      body_ce ret rt ss locked
Proof
  strip_tac >>
  drule_all intcall_callee_locked_source >> strip_tac >>
  drule_then strip_assume_tac intcall_callee_package_metadata >>
  `(!n l. FLOOKUP body_ce.ce_vars n = SOME l ==> MEM n (MAP FST args)) /\
   (!n. MEM n (MAP FST args) ==> ?p sz. FLOOKUP body_ce.ce_vars n = SOME (PtrVar (Var p) sz))` by
    (`ce.ce_vars = (build_compile_env tops Internal mut name args ret ss_comp T).ce_vars` by simp[] >>
     drule_all intcall_callee_body_formals >> simp[]) >>
  `body_inv tops ctx body_ce (cx with stk updated_by CONS (NONE,name)) /\
   allocLimitsProps$alloc_env_agree (build_compile_env tops Internal mut name args ret ss_comp F) body_ce /\
   body_ce.ce_var_type = (build_compile_env tops Internal mut name args ret ss_comp T).ce_var_type /\
   ~body_ce.ce_is_external` by
    (drule_all intcall_callee_body_env >> disch_then (qspec_then `imm` assume_tac) >>
     irule intcall_callee_body_metadata >> simp[] >> metis_tac[]) >>
  `body_ce.ce_is_ctor = caller.ce_is_ctor /\ supported_program tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `body_inv tops ctx caller cx` (fn inv =>
       MAP_EVERY strip_assume_tac
         [MATCH_MP body_inv_main_support inv,
          MATCH_MP intcall_callee_singleton_keys inv,
          MATCH_MP contract_inv_constructor (MATCH_MP bodySimTheory.body_inv_contract inv)]) >>
     qpat_assum `body_inv tops ctx body_ce _`
       (strip_assume_tac o MATCH_MP contract_inv_constructor o
        MATCH_MP bodySimTheory.body_inv_contract) >>
     simp[]) >>
  `cx_tops cx = tops` by
    (qpat_assum `body_inv tops ctx caller cx`
       (ACCEPT_TAC o CONJUNCT2 o MATCH_MP body_inv_main_code)) >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,ds_comp,ret,ss_comp)` by
    (drule_all (Q.INST [`deploy` |-> `cx.in_deploy`] intcall_callee_allocs) >>
     simp[constSubstTheory.subst_consts_fn_def]) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx tenv es1`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  `check_function_body cx.layouts cx.txn.target [(NONE,tops)] art NONE
      Internal mut nr args ds ret ss` by
    (drule_all_then ACCEPT_TAC checked_singleton_internal_function_body) >>
  `supported_function_body tops Internal args ss` by
    (`Internal <> Deploy` by simp[] >>
     drule_all supportedProgramTheory.supported_program_function >> simp[]) >>
  `supported_pure_exprs tops ds` by
    (drule_all supportedProgramTheory.supported_program_declaration >>
     simp[supportedProgramTheory.supported_declaration_body_def]) >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  qpat_assum `cx_tops cx = tops` (fn eq =>
    qpat_assum `constants_fold_module _ _ _ (cx_tops cx) _ = _`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  `supported_function_body tops Internal args ss_comp` by
    (qpat_assum `ss_comp = subst_consts_stmts _ _` SUBST1_TAC >>
     drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`vis` |-> `Internal`,
       `env` |-> `function_entry_env art [(NONE,tops)] NONE Internal args`]
       checked_const_substituted_function)) >> simp[]) >>
  `!n ty. FLOOKUP env.var_types n = SOME ty ==>
          body_ce.ce_var_type n = SOME ty /\
          ?p sz. FLOOKUP body_ce.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     metis_tac[intcall_callee_formal_type, listTheory.MEM_MAP, pairTheory.FST]) >>
  `ce_locals_declared body_ce env` by
    (`!n. MEM n (MAP FST args) ==> n IN FDOM env.var_types` by
       (rw[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
        res_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
     metis_tac[bodySimEntryTheory.ce_locals_declared_params]) >>
  qhdtm_x_assum `intcall_entry_full`
    (fn th => map_every STRIP_ASSUME_TAC
      (List.take (CONJUNCTS (REWRITE_RULE [intcall_entry_full_def] th), 8))) >>
  `expr_sim_inv body_ce (cx with stk updated_by CONS (NONE,name)) env locked` by
    (irule intcall_callee_expr_inv_singleton >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rpt strip_tac >> first_x_assum drule >> simp[] >> NO_TAC) >>
     (metis_tac[])) >>
  `body_const_cells_agree [(NONE,tops)] cx env es1` by
    (`frame_maps env art` by
       (qpat_assum `frame_maps tenv art`
          (strip_assume_tac o REWRITE_RULE [constSubstCorrectTheory.frame_maps_def]) >>
        rewrite_tac [constSubstCorrectTheory.frame_maps_def] >>
        asm_rewrite_tac []) >>
     rewrite_tac [body_const_cells_agree_def] >>
     qexistsl_tac [`roots`, `art`, `imms`, `A`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       irule constSubstStmtsTheory.const_subst_context_static >>
       qexists_tac `tenv` >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  `body_const_cells_agree [(NONE,tops)] (cx with stk updated_by CONS (NONE,name)) env locked` by
    (`cx with stk updated_by CONS (NONE,name) = cx with stk := (NONE,name)::cx.stk` by
       simp[vyperContextTheory.evaluation_context_component_equality] >>
     pop_assum SUBST1_TAC >>
     irule body_const_cells_agree_stk >>
     drule_all intcall_callee_lock_fields >> strip_tac >>
     irule (iffLR body_const_cells_agree_immutables) >>
     qexists_tac `es1` >> simp[]) >>
  `~supported_stmts_expr_exists (const_name_root_mods body_ce.ce_modules) ss_comp` by
    (qpat_assum `ss_comp = subst_consts_stmts _ _` SUBST1_TAC >>
     irule intcall_checked_body_const_name_free >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `type_stmts env ret ss_comp = SOME env_after` by simp[] >>
  `qualified_stmts_decls_ok body_ce.ce_modules ss_comp` by
    (`body_ce.ce_modules = [(NONE,tops)]` by
       (qpat_assum `body_inv tops _ body_ce _`
         (ACCEPT_TAC o MATCH_MP contract_inv_cenv_modules o
          MATCH_MP bodySimTheory.body_inv_contract)) >>
     drule_all (SIMP_RULE (srw_ss())
       [constSubstModsTheory.consts_env_mods_singleton,
        constSubstModsTheory.subst_consts_mods_singleton]
       (Q.INST [`mods` |-> `[(NONE,tops)]`]
         checked_qualified_body_decl_resolution)) >> simp[]) >>
  drule_all intcall_callee_body_bounds >> strip_tac >>
  drule_all intcall_callee_locked_body >> strip_tac >>
  `?bindings. supported_stmts tops bindings ss_comp` by
    (qexists `args ++ supported_stmts_bindings T ss_comp ++ supported_stmts_bindings F ss_comp` >>
     fs[supportedProgramTheory.supported_function_body_def]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss_comp ==>
    occurs_abi_decode_target target tops` by
    (rpt strip_tac >>
     `supported_stmts_expr_exists (expr_abi_decode_target_root target) ss` by
       metis_tac[checked_const_substitution_abi_decode_target] >>
     `occurs_abi_decode_target target [FunctionDecl Internal mut nr rr name args ds ret ss]` by
       simp[supportedProgramTheory.occurs_abi_decode_target_function] >>
     fs[supportedProgramTheory.occurs_abi_decode_target_def, listTheory.EXISTS_MEM] >>
     metis_tac[]) >>
  `int_calls_stmts ss_comp = int_calls_stmts ss` by
    (qpat_assum `ss_comp = subst_consts_stmts _ _` SUBST1_TAC >>
     drule_all checked_const_substitution_int_calls >> simp[]) >>
  `!gs. eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
                 (locked with gas_obs := gs) =
         eval_stmts (cx with stk updated_by CONS (NONE,name)) ss_comp
                 (locked with gas_obs := gs)` by
    (drule_all intcall_callee_lock_fields >> strip_tac >>
     gen_tac >> sym_tac >>
     qpat_assum `ss_comp = subst_consts_stmts _ _` SUBST1_TAC >>
     irule constSubstStmtsTheory.const_subst_intcall_body >>
     qpat_assum `cx_tops cx = tops` (fn eq =>
       qpat_assum `const_subst_context roots cx tenv _ _ art`
         (irule_at Any o PURE_REWRITE_RULE [eq])) >>
     qexistsl_tac [`Internal`, `ret`, `cx.in_deploy`, `args`] >>
     simp[] >> rpt conj_tac
     >- fs[constSubstCorrectTheory.const_cells_agree_def]
     >- (rpt strip_tac >>
         drule_all constSubstStmtsTheory.module_consts_env_constant_expr >> simp[]) >>
     fs[check_function_body_def]) >>
  drule_all intcall_callee_body_return_type >> strip_tac >>
  `intcall_callee_body_inputs tops ctx (cx with stk updated_by CONS (NONE,name))
      body_ce ret rt ss locked` by
    (simp[NoAsms,intcall_callee_body_inputs_def] >>
     qpat_assum `ss_comp = subst_consts_stmts _ _` (pure_rewrite_tac o single o SYM) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`bindings`,`env`,`env_after`] >>
     qpat_assum `int_calls_stmts ss_comp = _` (pure_rewrite_tac o single) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `stmts_env body_ce NoLoop ret ss_comp = _`
    (pure_once_rewrite_tac o single o SYM) >>
  qpat_assum `stmts_env _ NoLoop ret (MAP gas_shadow_stmt ss_comp) = _`
    (pure_once_rewrite_tac o single o SYM) >>
  irule bodySimFullTheory.stmt_frag_full_source_cong >>
  qexists_tac `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss_comp` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `body_stmts_full_ok _ ss_comp` (mp_tac o REWRITE_RULE [body_stmts_full_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`dret`,`PG`,`tops`,`bindings`,`ctx`,`shadow_ctx`,
    `callee`,`sf`,`body_ce`,`env`,`env_after`,`ret`,`NoLoop`,`RetQ`,`locked`] mp_tac) >>
  simp[] >> gvs[]
QED

(* Apply the checked paired body fragments at the successful lock landing.
   RetQ is supplied by the caller of this lemma, not chosen by the body. *)
Theorem intcall_callee_locked_body_outcome[local]:
  body_inv tops ctx caller cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops /\
  ds_comp = subst_consts_exprs (module_consts_env tops []) ds /\
  ss_comp = subst_consts_stmts (module_consts_env tops []) ss /\
  intcall_entry_full (DF,lo,d) H tops ctx func caller cx tenv name es sa sb vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
    body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss_comp) /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit tops policy rbc = SOME unit
   else lower_vyper_runtime_unit tops policy = SOME unit) /\
  ctx = unit.cu_context /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy ilen
      (mut,nr,rr,name,args,ds_comp,ret,ss_comp)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
  frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,PG,callee,sf)
    (cx with stk updated_by CONS (NONE,name)) RetQ body_ce ret /\
  stmts_env body_ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty) ss_comp body_start = (env_end,body_end) /\
  stmts_env (gas_shadow_env T body_ce) NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty)
    (MAP gas_shadow_stmt ss_comp) shadow_start = (gas_shadow_env T env_end,shadow_end) /\
  gas_shadow_state body_start shadow_start /\ gas_shadow_state body_end shadow_end /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function callee sf /\ MEM callee ctx.ctx_functions /\
  MEM sf shadow_ctx.ctx_functions /\ fn_has_code body_start body_end callee /\
  fn_has_code shadow_start shadow_end sf /\
  (!K. dead_lo_ok K (DF K) lo caller cx) /\
  fn_inst_ids_distinct callee /\ local_ptrs_reserved body_ce body_start /\
  ret_pc_ok body_ce body_start at_body /\
  (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at body_start x) /\
  ~block_is_terminated body_start /\ return_buf_frame dret body_ce body_start at_body /\
  return_buf_sep dret body_ce locked at_body /\
  alloca_history callee at_body /\ (ctx_has_dalloca ctx ==> allocas_below_fmp at_body) /\
  (!fn inst s. frag_reachable ctx callee at_body fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!K. valid_horizon (cx with stk updated_by CONS (NONE,name)) st0 K locked.storage_trace ==>
    stmt_state_rel K ctx callee body_ce (cx with stk updated_by CONS (NONE,name)) locked at_body /\
    storage_well_formed_on (cx with stk updated_by CONS (NONE,name)) locked (FST K) /\
    ghost_inv_at (DF K) lo dret body_ce (cx with stk updated_by CONS (NONE,name)) locked Gbody tnbody at_body) /\
  ~at_body.vs_halted /\ at_body.vs_current_bb = body_start.cs_current_bb /\
  at_body.vs_inst_idx = LENGTH body_start.cs_current_insts ==>
  intcall_callee_body_inputs tops ctx (cx with stk updated_by CONS (NONE,name))
    body_ce ret rt ss locked /\
  gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) (stmt_res_ok NoLoop) locked /\
  (!K. dead_lo_ok K (DF K) lo body_ce (cx with stk updated_by CONS (NONE,name))) /\
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,PG)
    (cx_tops (cx with stk updated_by CONS (NONE,name))) (cx with stk updated_by CONS (NONE,name)) st0 (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) (locked,at_body,Gbody,tnbody)
    (\K res ee G' tn' t'. ?ce'.
       stmt_lands NoLoop body_end res t' /\ ~t'.vs_halted /\
       (res = INL () ==> ~block_is_terminated body_end /\ ce' = env_end) /\
       cenv_top_ext body_ce ce' ee.scopes /\
       stmt_state_rel K ctx callee ce' (cx with stk updated_by CONS (NONE,name)) ee t' /\
       storage_well_formed_on (cx with stk updated_by CONS (NONE,name)) ee (FST K) /\
       return_buf_frame dret ce' body_end t' /\ alloca_history callee t' /\
       return_buf_sep dret ce' ee t' /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
       at_body.vs_alloca_next <= t'.vs_alloca_next /\
       ghost_inv_at (DF K) lo dret ce' (cx with stk updated_by CONS (NONE,name)) ee G' tn' t' /\
       (!x w. not_fresh_at body_start x /\ lookup_var x at_body = SOME w ==>
              lookup_var x t' = SOME w) /\
       (!aid b. FLOOKUP at_body.vs_allocas aid = SOME b ==>
                FLOOKUP t'.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at body_start x ==>
            FLOOKUP G' x = FLOOKUP Gbody x /\ op_taint tn' (Var x) = op_taint tnbody (Var x)) /\
       alloca_frame body_ce locked body_start at_body ce' ee t' /\
       (!aid off sz i.
          FLOOKUP at_body.vs_allocas aid = SOME (off,sz) /\ aid < body_start.cs_next_id /\
          (!n b sz'. local_region body_ce locked.scopes at_body n b sz' ==>
                     off + sz <= b \/ b + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tnbody.t_mem))
    (\K res ee gt r.
       (!tail. stmt_exit_ptr (RetQ K) (ee with gas_obs := tail) res gt r) /\
       halt_exit K (cx with stk updated_by CONS (NONE,name)) ee res r /\
       (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `stmt_frag_full (DF,lo,dret,ctx,shadow_ctx,PG,callee,sf)
      (cx with stk updated_by CONS (NONE,name)) NoLoop RetQ body_ce
      (stmts_env body_ce NoLoop (case rt of NONE => BaseT BoolT | SOME ty => ty) ss_comp)
      (stmts_env (gas_shadow_env T body_ce) NoLoop
         (case rt of NONE => BaseT BoolT | SOME ty => ty) (MAP gas_shadow_stmt ss_comp))
      (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) locked /\
    gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
      (stmt_res_ok NoLoop) locked /\
    body_ce.ce_is_ctor = caller.ce_is_ctor /\
    intcall_callee_body_inputs tops ctx (cx with stk updated_by CONS (NONE,name))
      body_ce ret rt ss locked` by
    (drule_all intcall_callee_locked_body_frag >> simp[NoAsms]) >>
  `!K. dead_lo_ok K (DF K) lo body_ce (cx with stk updated_by CONS (NONE,name))` by
    (gen_tac >> irule intcall_callee_dead_lo >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_x_assum `stmt_frag_full` (mp_tac o REWRITE_RULE [bodySimFullTheory.stmt_frag_full_def]) >>
  disch_then (qspecl_then [`st0`,`body_start`,`body_end`,`shadow_start`,`shadow_end`,
                          `at_body`,`Gbody`,`tnbody`,`env_end`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[NoAsms]
QED

Theorem intcall_ghost_merge_sites[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state s cs)) = SOME t ==>
  ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs))) t
Proof
  strip_tac >>
  `ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs))) t =
   ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs)))
     (adopt_return_fmp ir (merge_callee_state s cs))` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >>
     simp[update_var_def, ptr_byte_frame_inv_def] >> metis_tac[]) >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[ptr_byte_frame_inv_def, venomExecSemanticsTheory.adopt_return_fmp_def,
      venomExecSemanticsTheory.merge_callee_state_def,
      finite_mapTheory.FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem intcall_ghost_current_opcode[local]:
  intcall_ghost_opcodes ctx /\
  MEM func ctx.ctx_functions /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DRET
Proof
  strip_tac >>
  `MEM inst (fn_insts func)` by
    (simp[fn_insts_def] >> irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
     qexists_tac `bb` >> gvs[get_instruction_def] >> metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  fs[intcall_ghost_opcodes_def] >>
  metis_tac[]
QED

Theorem intcall_ghost_terminator_sites[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK u ==>
  ptr_byte_frame_inv (ctx,x) (entry_prov func u G) u
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke,
              venomMemProofsTheory.step_inst_base_preserves_alloca_fields] >>
  `u.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke,
              ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp] >>
  fs[ptr_byte_frame_inv_def] >> metis_tac[bodyFullIntCallByteFrameTheory.ptr_byte_frame_entry_prov]
QED

Theorem intcall_callee_protected_ghost_run_rules:
  (!fuel ctx PG G tn inst s D lo func x u.
    step_inst fuel ctx inst s = OK u /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ (inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx) /\
    inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DRET /\
    ~in_revert_forward func s /\ lo <= x /\
    ptr_safe_step D lo fuel ctx func PG G tn inst s /\
    ptr_byte_frame_inv (ctx,x) G s /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    (!v. op_taint tn (Var v) SUBSET count 32) /\ x NOTIN tn.t_mem ==>
    ptr_byte_frame_inv (ctx,x) (step_prov PG G inst u) u /\
    (!v. op_taint (step_taint inst s u tn) (Var v) SUBSET count 32) /\
    x NOTIN (step_taint inst s u tn).t_mem) ==>
  (!fuel ctx PG G tn inst s. !D lo func x u.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    (!v. op_taint tn (Var v) SUBSET count 32) /\ x NOTIN tn.t_mem /\
    intcall_ghost_opcodes ctx /\
    (inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx) /\ inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DRET /\
    ptr_safe_step D lo fuel ctx func PG G tn inst s /\
    ~in_revert_forward func s /\ ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK u ==>
    ptr_byte_frame_inv (ctx,x) (FST (ghost_step fuel ctx PG G tn inst s)) u /\
    (!v. op_taint (SND (ghost_step fuel ctx PG G tn inst s)) (Var v) SUBSET count 32) /\
    x NOTIN (SND (ghost_step fuel ctx PG G tn inst s)).t_mem) /\
  (!fuel ctx func PG G tn bb s. !D lo x ir t.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    (!v. op_taint tn (Var v) SUBSET count 32) /\ x NOTIN tn.t_mem /\
    intcall_ghost_opcodes ctx /\
    MEM func ctx.ctx_functions /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    ptr_safe_block D lo fuel ctx func PG G tn bb s /\
    block_run fuel ctx func bb s = IntRet ir t ==>
    x NOTIN (SND (ghost_block fuel ctx func PG G tn bb s)).t_mem) /\
  (!fuel ctx func PG G tn s. !D lo x ir t.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    (!v. op_taint tn (Var v) SUBSET count 32) /\ x NOTIN tn.t_mem /\
    intcall_ghost_opcodes ctx /\
    MEM func ctx.ctx_functions /\ ptr_safe_blocks D lo fuel ctx func PG G tn s /\
    run_blocks fuel ctx func s = IntRet ir t ==>
    x NOTIN (SND (ghost_blocks fuel ctx func PG G tn s)).t_mem)
Proof
  disch_tac >> ho_match_mp_tac ptrSafeRunTheory.ghost_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume intcall_callee_protected_ghost_run_rules[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[ptrSafeRunTheory.ghost_step_def, pairTheory.FST, pairTheory.SND] >>
  qpat_x_assum `!fuel ctx PG G tn inst s D lo func x u. _`
    (drule_all_then ACCEPT_TAC)
QED

Resume intcall_callee_protected_ghost_run_rules[invoke]:
  qpat_x_assum `!fuel ctx PG G tn inst s D lo func x u. _` kall_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  `ptr_byte_frame_inv (ctx,x) FEMPTY callee_s` by
    (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     qpat_x_assum `ptr_byte_frame_inv (ctx,x) G s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[venomExecSemanticsTheory.setup_callee_def, ptr_byte_frame_inv_def] >> gvs[]) >>
  `!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==> x < b \/ b + sz <= x` by
    (qpat_x_assum `ptr_byte_frame_inv (ctx,x) G s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_byte_frame_inv_def] >>
     metis_tac[bodyFullIntCallByteFrameTheory.ptr_byte_frame_invoke_params]) >>
  `ptr_safe_blocks D lo fuel ctx callee_fn (MAP (op_prov G) arg_ops)
     FEMPTY (tn with t_var := FEMPTY) callee_s` by
    (qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once ptrSafeRunTheory.ptr_safe_step_def]) >>
  `MEM callee_fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `x NOTIN (SND (ghost_blocks fuel ctx callee_fn (MAP (op_prov G) arg_ops)
     FEMPTY (tn with t_var := FEMPTY) callee_s)).t_mem` by
    (qpat_x_assum `!D' lo' x'. _` (qspecl_then [`D`, `lo`, `x`] mp_tac) >>
     simp[lowerDloadMaskBoundsTheory.ld_var_taint_bound_iff] >> metis_tac[]) >>
  simp[ptrSafeRunTheory.ghost_step_def, pairTheory.FST, pairTheory.SND] >>
  conj_tac >- metis_tac[intcall_ghost_merge_sites] >>
  fs[lowerDloadMaskBoundsTheory.ld_var_taint_bound_iff, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume intcall_callee_protected_ghost_run_rules[block]:
  qpat_x_assum `!fuel ctx PG G tn inst s D lo func x u. _` kall_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `~in_revert_forward func s` by
    (CCONTR_TAC >> fs[in_revert_forward_def] >>
     Cases_on `exec_block fuel ctx bb s` >> gvs[ptrSafeRunTheory.block_run_def] >>
     metis_tac[stepWriteFootprintForwardTheory.revert_forward_at_no_normal]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- gvs[ptrSafeRunTheory.block_run_def, Once venomExecSemanticsTheory.exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `ptr_safe_step D lo fuel ctx func PG G tn inst s` by
    metis_tac[ptrSafeRunTheory.ptr_safe_block_head] >>
  `inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DRET` by
    metis_tac[intcall_ghost_current_opcode] >>
  `(inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx)` by
    (strip_tac >> simp[ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
     qexists_tac `func` >> simp[] >> qexists_tac `inst` >> simp[fn_insts_def] >>
     irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
     qexists_tac `bb` >> gvs[get_instruction_def] >> metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  Cases_on `step_inst fuel ctx inst s`
  >~ [`step_inst fuel ctx inst s = OK u`]
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- suspend "terminator" >>
      `ptr_byte_frame_inv (ctx,x) (FST (ghost_step fuel ctx PG G tn inst s)) u /\
       (!v. op_taint (SND (ghost_step fuel ctx PG G tn inst s)) (Var v) SUBSET count 32) /\
       x NOTIN (SND (ghost_step fuel ctx PG G tn inst s)).t_mem` by metis_tac[] >>
      `u.vs_current_bb = s.vs_current_bb` by metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
      `ptr_byte_frame_inv (ctx,x) (FST (ghost_step fuel ctx PG G tn inst s))
         (u with vs_inst_idx := SUC s.vs_inst_idx)` by simp[bodyFullIntCallByteFrameTheory.ptr_byte_frame_inv_inst_idx] >>
      `ptr_safe_block D lo fuel ctx func PG
         (FST (ghost_step fuel ctx PG G tn inst s))
         (SND (ghost_step fuel ctx PG G tn inst s)) bb
         (u with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[ptrSafeRunTheory.ptr_safe_block_step] >>
      `block_run fuel ctx func bb (u with vs_inst_idx := SUC s.vs_inst_idx) = IntRet ir t` by
        metis_tac[ptrSafeRunTheory.block_run_step] >>
      drule_all ptrSafeRunTheory.ghost_block_step >> disch_then (rewrite_tac o single) >>
      qpat_x_assum `!inst' s''. _ /\ _ /\ ~is_terminator inst'.inst_opcode ==> !D lo x ir t. _`
        (qspecl_then [`inst`,`u`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `block_run _ _ _ _ _ = _` mp_tac >>
  simp[ptrSafeRunTheory.block_run_def, Once venomExecSemanticsTheory.exec_block_def] >>
  strip_tac >> gvs[] >> metis_tac[ptrSafeRunTheory.ghost_block_intret, pairTheory.SND]
QED

Resume intcall_callee_protected_ghost_run_rules[terminator]:
  `~u.vs_halted` by
    (qpat_x_assum `block_run _ _ _ _ _ = _` mp_tac >>
     simp[ptrSafeRunTheory.block_run_def, Once venomExecSemanticsTheory.exec_block_def] >>
     Cases_on `u.vs_halted` >> simp[]) >>
  `ptr_byte_frame_inv (ctx,x) (entry_prov func u G) u` by metis_tac[intcall_ghost_terminator_sites] >>
  `ptr_safe_blocks D lo fuel ctx func PG (entry_prov func u G)
     (entry_taint_vars func u tn) u` by metis_tac[ptrSafeRunTheory.ptr_safe_block_terminator] >>
  `run_blocks fuel ctx func u = IntRet ir t` by metis_tac[ptrSafeRunTheory.block_run_terminator] >>
  `!v. op_taint (entry_taint_vars func u tn) (Var v) SUBSET count 32` by
    metis_tac[lowerDloadMaskBoundsTheory.ld_entry_taint_vars_bound] >>
  `x NOTIN (entry_taint_vars func u tn).t_mem` by
    (simp[ptrDisciplineTheory.entry_taint_vars_def] >> CASE_TAC >> simp[]) >>
  drule_all ptrSafeRunTheory.ghost_block_terminator >> disch_then (rewrite_tac o single) >>
  qpat_x_assum `!inst' s''. _ /\ _ /\ is_terminator inst'.inst_opcode /\
    ~s''.vs_halted ==> _` (qspecl_then [`inst`,`u`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >> simp[] >> metis_tac[]
QED

Resume intcall_callee_protected_ghost_run_rules[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[Once venomExecSemanticsTheory.run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- gvs[Once venomExecSemanticsTheory.run_blocks_def] >>
  rename1 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      `ptr_byte_frame_inv (ctx,x) G (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
       sp.vs_current_bb = s.vs_current_bb` by
        (drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
         disch_then (fn th => once_rewrite_tac[th]) >>
         qpat_x_assum `ptr_byte_frame_inv (ctx,x) G s` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_byte_frame_inv_def] >> metis_tac[]) >>
      `block_run n ctx func bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
       IntRet ir t` by metis_tac[ptrSafeRunTheory.run_blocks_block_run] >>
      `ptr_safe_block D lo n ctx func PG G tn bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        metis_tac[ptrSafeRunTheory.ptr_safe_blocks_block] >>
      drule_all ptrSafeRunTheory.ghost_blocks_block >> disch_then (rewrite_tac o single) >>
      qpat_x_assum `!fuel' bb' s_phi. _` (qspecl_then [`n`,`bb`,`sp`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >>
      simp[] >> fs[ptr_byte_frame_inv_def] >> metis_tac[]) >>
  gvs[Once venomExecSemanticsTheory.run_blocks_def]
QED
Finalise intcall_callee_protected_ghost_run_rules

Theorem intcall_callee_final_horizon_taint_frame:
  body_inv tops ctx cenv cx /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  intcall_callee_src cx name mut nr ss (es1 with gas_obs := xs) =
    (res,ee with gas_obs := ys) /\
  valid_horizon cx st0 H ee.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
    MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
    marks (IntRet ir s',G',tn') ==>
  !i. lo <= i /\ i < t.vs_alloca_next /\ i IN tn'.t_mem /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      i < off \/ off + asz <= i) ==>
    i IN tn.t_mem
Proof
  strip_tac >>
  drule_all intcall_callee_entry_horizon >> strip_tac >>
  qpat_x_assum `!H. _ ==> intcall_entry_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_then assume_tac intcall_callee_pre_fmp_context >>
  gen_tac >> strip_tac >> CCONTR_TAC >>
  `!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==>
    i < b \/ b + sz <= i` by
    (qhdtm_assum `intcall_entry_full`
       (mp_tac o last o CONJUNCTS o REWRITE_RULE [intcall_entry_full_def]) >>
     disch_then (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!b bsz. MEM (SOME (b,bsz)) (MAP (op_prov G) arg_ops) ==> _` mp_tac >>
     qpat_x_assum `!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_all intcall_callee_entry_decode >> strip_tac >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fmp_room ctx callee setup` by metis_tac[intcall_entry_full_fmp_room] >>
  `ptr_byte_frame_inv (ctx,i) FEMPTY setup` by
    (gvs[venomExecSemanticsTheory.setup_callee_def, ptr_byte_frame_inv_def] >>
     rpt strip_tac >> fs[fmp_room_def] >> decide_tac) >>
  `ptr_byte_frame_inv (ctx,i) FEMPTY entered` by
    (qpat_assum `entered = _` SUBST1_TAC >>
     PURE_REWRITE_TAC [ptr_byte_frame_inv_inst_idx] >>
     qpat_assum `eval_phis setup _ = OK phi_state`
       (fn run => once_rewrite_tac [MATCH_MP
          venomExecProofsTheory.eval_phis_only_updates_vs_vars run]) >>
     qpat_assum `ptr_byte_frame_inv (ctx,i) FEMPTY setup` mp_tac >>
     simp[NoAsms,ptr_byte_frame_inv_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!v. op_taint (tn with t_var := FEMPTY) (Var v) SUBSET count 32` by
    simp[lowerDloadMaskBoundsTheory.ld_var_taint_bound_iff] >>
  qpat_x_assum `entered = _` kall_tac >>
  drule_then (qx_choose_then `fuel` strip_assume_tac o SRULE [exit_result_def])
    fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
  Cases_on `lookup_block entered.vs_current_bb callee.fn_blocks` >>
  gvs[run_from_def, ptrSafeRunTheory.ptr_safe_run_def,
      ptrSafeRunTheory.ghost_run_def, GSYM ptrSafeRunTheory.block_run_def] >>
  mp_tac intcall_callee_protected_ghost_run_rules >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
                drule_all_then ACCEPT_TAC intcall_callee_protected_ordinary_step)) >>
  disch_then (assume_tac o cj 2) >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME callee_bb` >>
  `i NOTIN (SND (ghost_block fuel ctx callee (MAP (op_prov G) arg_ops)
               FEMPTY (tn with t_var := FEMPTY) callee_bb entered)).t_mem` by
    (first_x_assum irule >> simp[] >>
     qexistsl [`DF H`, `lo`] >> simp[]) >>
  gvs[pairTheory.SND]
QED

Theorem intcall_callee_buffered_return_relayout[local]:
  body_inv tops ctx ce cx /\ same_frame ce cenv /\
  expr_sim_inv cenv cx env es /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\ lo <= w2n bw /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant))) /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_returns_count = 0 /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  (!ety. expr_sim_full
      (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ety e es /\
    expr_vv_sim_full
      (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ety e es) /\
  (!H v ee gt r. intret_mem_q H func ce cx tv bw v ee r /\
    (!ir u. r = IntRet ir u ==>
      (!mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
         val_in_memory tv v (w2n bw) mem) /\
      stor_taint_ok_at (DF H) (SND gt) u /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
         imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i)) ==>
    RetQ H v ee gt r) ==>
  stmt_frag_full
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  drule_all_then assume_tac body_inv_same_frame >>
  `cenv.ce_module = NONE /\ cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_module_var_type = build_var_type_map tops /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    cx_tops cx = tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       MAP_EVERY strip_assume_tac
         [MATCH_MP body_inv_main_code inv, MATCH_MP intcall_callee_singleton_keys inv,
          MATCH_MP body_inv_module_locations inv, MATCH_MP intcall_args_body_inv_pins inv,
          MATCH_MP contract_inv_struct_fields (MATCH_MP bodySimTheory.body_inv_contract inv)]) >>
     fs[bodySimTheory.cenv_module_pins_def, make_struct_fields_map_mods_singleton]) >>
  `cenv.ce_returns_count = 0 /\ cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz)` by
      fs[bodySimTheory.same_frame_def, compile_env_component_equality] >>
  `(cenv.ce_is_ctor ==> !nm io ity itv.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
     cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
     evaluate_type (get_tenv cx) ity = SOME itv ==>
     regions_disjoint io (type_memory_size itv) (w2n bw) (type_memory_size tv))` by
    (rpt strip_tac >>
     `ce.ce_is_ctor` by metis_tac[bodyPtrDefsTheory.same_frame_is_ctor] >>
     `lo = imm_len tops` by fs[bodyPtrDefsTheory.dead_lo_ok_def] >>
     `immutable_section_layout cenv tops` by
       metis_tac[bodySimTheory.body_inv_immutable_section_layout] >>
     `FLOOKUP cenv.ce_module_vars (NONE,nm) = SOME (ImmutableLoc io)` by metis_tac[] >>
     qpat_x_assum `immutable_section_layout _ _`
       (drule_then (qx_choose_then `pre` (qx_choose_then `post`
           (qx_choose_then `vis` (qx_choose_then `decl_ty` (qx_choose_then `slot`
             strip_assume_tac))))) o
        REWRITE_RULE [immutableRelationTheory.immutable_section_layout_def]) >>
     `MEM (VariableDecl vis Immutable nm decl_ty slot) tops` by simp[] >>
     drule_all_then strip_assume_tac bodyStorageMetadataTheory.build_maps_variable >>
     `ity = decl_ty` by
       (qpat_x_assum `build_var_type_map _ (NONE,nm) = SOME decl_ty` mp_tac >>
        simp[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> gvs[]) >>
     `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ity =
      type_memory_size itv` by
       metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
                 structFieldsPropsTheory.type_mem_bytes_type_memory_bytes] >>
     `io + type_memory_size itv <= imm_len tops` by
       (gvs[] >>
        qpat_x_assum `type_mem_bytes _ _ = type_memory_size itv` mp_tac >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
        strip_tac >>
        simp[immSectionDeadTheory.imm_len_def, compute_immutables_len_append,
             compute_immutables_len_def] >> decide_tac) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     disj1_tac >> decide_tac) >>
  irule stmtSimReturnTheory.stmt_frag_full_retq_weaken >>
  irule_at Any internal_return_memory_relayout_robust_taint >>
  qexistsl [`tops`,`rsz`,`rpc`,`env`,`ce`] >>
  gvs[] >> first_assum ACCEPT_TAC
QED

(* The callee's own allocations start above the caller's frontier.
   A live local below it is borrowed from a covering caller allocation. *)
Theorem intcall_callee_immutable_sep[local]:
  immutable_alloca_sep caller cenv cx src t /\
  cenv.ce_is_ctor = ce.ce_is_ctor /\ cenv.ce_module = ce.ce_module /\
  cenv.ce_module_vars = ce.ce_module_vars /\
  cenv.ce_module_var_type = ce.ce_module_var_type /\ src.immutables = es.immutables /\
  t.vs_alloca_next <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> t.vs_alloca_next <= b) /\
  (!id b sz. local_region ce es.scopes s id b sz ==>
     t.vs_alloca_next <= b \/
     ?i base len. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
       FLOOKUP t.vs_allocas i.inst_id = SOME (base,len) /\
       base <= b /\ b + sz <= base + len) ==>
  immutable_alloca_sep callee ce cx es s
Proof
  strip_tac >>
  `!off n. off + n <= t.vs_alloca_next /\
    (!i b sz. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> regions_disjoint off n b sz) ==>
    off + n <= s.vs_alloca_next /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> regions_disjoint off n b sz) /\
    (!id b sz. local_region ce es.scopes s id b sz ==> regions_disjoint off n b sz)` by
    (rpt gen_tac >> strip_tac >> conj_tac >- decide_tac >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id b sz. local_region ce es.scopes s id b sz ==> _`
       (drule_then strip_assume_tac)
     >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_assum `!i b sz. MEM i (fn_insts caller) /\ _ ==> _` drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `immutable_alloca_sep caller cenv cx src t` mp_tac >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  strip_tac >> Cases_on `ce.ce_is_ctor` >> gvs[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name ty tv off. _ ==> _` (drule_all_then strip_assume_tac) >>
      qpat_assum `!off n. _ ==> _` (qspecl_then [`off`,`type_memory_size tv`] mp_tac) >>
      impl_tac >- (conj_tac >- decide_tac >> rpt strip_tac >> res_tac) >>
      strip_tac >> conj_tac >- decide_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name tv v off. _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!off n. _ ==> _` (qspecl_then [`off`,`type_memory_size tv`] mp_tac) >>
  impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> conj_tac >- decide_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = _ ==> regions_disjoint _ _ _ _`
        drule >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem intcall_callee_scratch_resources[local]:
  prologue = materialized \/
  (?n buf. compile_alloc_buffer n materialized = (buf,prologue)) ==>
  materialized.cs_next_var <= prologue.cs_next_var /\
  (~block_is_terminated materialized ==> ~block_is_terminated prologue)
Proof
  disch_then (DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)
  >- simp[] >>
  drule_then strip_assume_tac abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
  Cases_on `materialized.cs_current_insts` >>
  gvs[block_is_terminated_def, mk_inst_def, is_terminator_def,
      listTheory.LAST_CONS_cond, listTheory.LAST_APPEND_CONS]
QED

Theorem intcall_callee_prologue_body_resources:
  local_ptrs_reserved body_ce materialized /\
  materialized.cs_next_var <= prologue.cs_next_var /\
  ~block_is_terminated materialized /\
  (~block_is_terminated materialized ==> ~block_is_terminated prologue) /\
  ret_pc_ok ce1 reserved at_reserve /\
  return_buf_frame ret_dest ce1 reserved at_reserve /\
  body_ce.ce_return_pc = ce1.ce_return_pc /\
  body_ce.ce_return_buf = ce1.ce_return_buf /\
  reserved.cs_next_var <= prologue.cs_next_var /\
  (!q. not_fresh_at reserved q ==> lookup_var q at_pro = lookup_var q at_reserve) /\
  at_reserve.vs_alloca_next <= at_pro.vs_alloca_next /\
  alloca_inv at_pro /\ alloca_room ctx callee at_pro /\ fmp_room ctx callee at_pro /\
  immutable_alloca_sep callee body_ce cx es1 at_pro /\ immutable_base_zero body_ce at_pro /\
  (!i w b sz. MEM i (fn_insts callee) /\ i.inst_opcode = ALLOCA /\
     i.inst_operands = [Lit w] /\ FLOOKUP at_pro.vs_allocas i.inst_id = SOME (b,sz) ==>
     sz = w2n w) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==> state_rel H callee body_ce cx es1 at_pro) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gmat tnmat at_mat) /\
  local_ptrs_rel callee body_ce es1.scopes at_mat /\
  (!n q sz. FLOOKUP body_ce.ce_vars n = SOME (PtrVar (Var q) sz) ==>
     not_fresh_at materialized q) /\
  (!q. body_ce.ce_imm_alloca = SOME (Var q) ==> not_fresh_at materialized q) /\
  (!q sz. body_ce.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at materialized q) /\
  (!q sz. body_ce.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at materialized q) /\
  (!q. not_fresh_at materialized q ==>
     lookup_var q at_pro = lookup_var q at_mat /\ FLOOKUP Gpro q = FLOOKUP Gmat q /\
     op_taint tnpro (Var q) = op_taint tnmat (Var q)) /\
  at_pro with <|vs_vars := at_mat.vs_vars; vs_allocas := at_mat.vs_allocas;
    vs_alloca_next := at_mat.vs_alloca_next; vs_inst_idx := at_mat.vs_inst_idx|> = at_mat /\
  allocas_from lo at_pro /\ at_mat.vs_alloca_next <= at_pro.vs_alloca_next /\
  tnpro.t_stor = tnmat.t_stor /\ tnpro.t_trans = tnmat.t_trans /\ tnpro.t_imm = tnmat.t_imm /\
  (!i. i IN tnpro.t_mem <=> i IN tnmat.t_mem \/
    (at_mat.vs_alloca_next <= i /\ i < at_pro.vs_alloca_next)) ==>
  local_ptrs_reserved body_ce prologue /\ ~block_is_terminated prologue /\
  ret_pc_ok body_ce prologue at_pro /\ return_buf_frame ret_dest body_ce prologue at_pro /\
  (!q sz. body_ce.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
  (!q sz. body_ce.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==> stmt_state_rel H ctx callee body_ce cx es1 at_pro) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gpro tnpro at_pro)
Proof
  strip_tac >> rpt conj_tac
  >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
      qexists_tac `materialized` >> simp[])
  >- simp[]
  >- (irule stmtSimPropsTheory.ret_pc_ok_frame >>
      qexistsl_tac [`ce1`,`at_reserve`,`reserved`] >> simp[])
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`ce1`,`at_reserve`,`reserved`] >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `materialized` >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `materialized` >> simp[])
  >- (simp[exprLoweringPropsTheory.stmt_state_rel_def] >> rpt strip_tac >>
      qpat_assum `!i w b sz. MEM i (fn_insts callee) /\ _ /\ _ /\ FLOOKUP at_pro.vs_allocas _ = _ ==> _`
        (irule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> disch_tac >>
  irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at_vars >>
  conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gmat`,`at_pro.vs_alloca_next`,`callee`,`at_mat`,`materialized`,`tnmat`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[]
QED

Theorem intcall_callee_buffered_frame_ret[local]:
  body_inv tops ctx ce cx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\ lo <= w2n bw /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant))) /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_returns_count = 0 /\
  ty <> NoneT /\ ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  (!H v ee gt r. intret_mem_q H func ce cx tv bw v ee r /\
    (!ir u. r = IntRet ir u ==>
      (!mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
         val_in_memory tv v (w2n bw) mem) /\
      stor_taint_ok_at (DF H) (SND gt) u /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
         imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i)) ==>
    RetQ H v ee gt r) ==>
  frame_ret_ok_full
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ ce ty
Proof
  strip_tac >> pure_rewrite_tac[bodySimFullTheory.frame_ret_ok_full_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `eo` >- gvs[vyperTypeSystemTheory.type_stmt_def] >>
  rename1 `Return (SOME e)` >>
  `!ety. expr_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv' cx ety e es /\
   expr_vv_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv' cx ety e es` by metis_tac[] >>
  mp_tac (Q.INST [`cenv` |-> `cenv'`] intcall_callee_buffered_return_relayout) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem intcall_callee_frame_return[local]:
  body_inv tops ctx ce cx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_returns_count = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ty /\
  (has_rb <=> ce.ce_returns_count = 0 /\ ty <> NoneT) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (ty <> NoneT ==> evaluate_type (get_tenv cx) ty = SOME tv) /\
  (has_rb ==> lo <= w2n bw /\ 0 < type_memory_size tv /\
              type_memory_size tv + 64 < dimword (:256)) /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant))) ==>
  frame_ret_ok_full
    (DF,lo,(if has_rb then SOME (bw,type_memory_size tv) else NONE),
     ctx,shadow_ctx,PG,func,sf) cx
    (\H v ee gt r. intret_q H func ce cx tv v ee r /\
      !ir u. r = IntRet ir u ==>
        (has_rb ==> !mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
           val_in_memory tv v (w2n bw) mem) /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
           imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i))
    ce ty
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ty ==> ce.ce_returns_count = 1` by
    (qpat_assum `ce.ce_returns_count = _` (once_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `ty` >>
     simp[returns_stack_count_def,is_word_type_def]) >>
  `?pc slot. ce.ce_return_pc = SOME (PtrVar (Var pc) slot)` by
    (qexistsl [`rpc`,`rsz`] >> first_assum ACCEPT_TAC) >>
  Cases_on `has_rb`
  >- (simp[NoAsms] >> irule intcall_callee_buffered_frame_ret >>
      `~is_word_type ty` by
        (strip_tac >> first_x_assum drule >> fs[]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qexists_tac `tops` >> first_assum ACCEPT_TAC >> NO_TAC) >>
      fs[intCallReturnMemTheory.intret_mem_q_def]) >>
  simp[NoAsms] >>
  `frame_ret_ok_full (DF,lo,NONE,ctx,shadow_ctx,PG,func,sf) cx
    (\H v ee gt r. intret_q H func ce cx tv v ee r /\
      !ir u. r = IntRet ir u /\
        ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
          FST (SND (SND ce.ce_nonreentrant))) ==>
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
           imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i))
    ce ty` by
    (Cases_on `ty = NoneT`
     >- (qpat_assum `ty = NoneT` SUBST_ALL_TAC >>
         irule stmtSimReturnTheory.internal_frame_ret_none_full_taint >>
         fs[returns_stack_count_def]) >>
     Cases_on `is_word_type ty`
     >- (irule stmtSimReturnTheory.internal_frame_ret_word_full_taint >>
         fs[]) >>
     irule internalReturnStackAggregateTheory.internal_frame_ret_stack_aggregate_full_taint >>
     fs[]) >>
  qpat_x_assum `frame_ret_ok_full _ _ _ _ _`
    (assume_tac o REWRITE_RULE [bodySimFullTheory.frame_ret_ok_full_def]) >>
  pure_rewrite_tac[bodySimFullTheory.frame_ret_ok_full_def] >>
  rpt gen_tac >> strip_tac >>
  irule stmtSimReturnTheory.stmt_frag_full_retq_weaken >>
  qpat_assum `!cenv' env lctx eo es. _ ==> stmt_frag_full _ _ _ _ _ _ _ _ _`
    (drule_all_then (irule_at Any)) >> simp[]
QED

(* Newly materialized locals lie above the entry frontier. Borrowed
   regions lie outside the caller's return buffer by the entry contract. *)
Theorem intcall_callee_materialized_return_buf_sep[local]:
  mat_inv callee ce env materialized s frontier borrowed /\
  es.scopes = [env] /\
  (!bw capacity. d = SOME (bw,capacity) ==>
    w2n bw + capacity <= frontier /\
    !name b sz. borrowed name = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint (w2n bw) capacity b sz) ==>
  return_buf_sep d ce es s
Proof
  Cases_on `d` >- simp[bodySimFullTheory.return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  simp[bodySimFullTheory.return_buf_sep_def, mat_inv_def,
       ptrDisciplineTheory.allocas_from_def] >>
  strip_tac >>
  conj_tac
  >- (rpt strip_tac >> res_tac >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!n b sz. local_region ce [env] s n b sz ==> _`
    (drule_then strip_assume_tac)
  >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  first_x_assum drule >> simp[]
QED


(* Parameter setup and locking consume no explicit gas readings. Keep
   the source state's lock trace while carrying the selected body marks. *)
Theorem intcall_callee_body_gas_source[local]:
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) ==>
  !gs. intcall_callee_src cx name mut nr ss (es with gas_obs := gs) =
    case eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
           (locked with gas_obs := gs) of
      (INL _,ee) => (INL NoneV,ee)
    | (INR err,ee) => handle_function err ee
Proof
  strip_tac >> gen_tac >>
  `lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := gs) =
      (INL (), locked with gas_obs := gs)` by
    (irule externalCallSelectedTheory.lock_if_nr_with_gas_obs >>
     first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[intcall_callee_src_def, ignore_bind_def, bind_def, try_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
                 (locked with gas_obs := gs)` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >>
  simp[ignore_bind_def, bind_def, return_def, try_def]
QED

Theorem intcall_callee_body_exempt[local]:
  (!tail. lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := tail) =
          (INL (), locked with gas_obs := tail)) /\
  gas_path_mem ctx callee s 0 (OK t) /\
  gas_exempt_cert T (cx_tops cx) (ctx,callee)
    (ignore_bind (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) (return ()))
    (locked,t) marks (err,ee) (leaf,leaf_end) ==>
  gas_exempt_cert T (cx_tops cx) (ctx,callee)
    (ignore_bind (intcall_callee_src cx name mut nr ss) (return ()))
    (es,s) marks (err,ee) (leaf,leaf_end)
Proof
  disch_then strip_assume_tac >>
  qabbrev_tac `callee_eval = eval_stmts (cx with stk updated_by CONS (NONE,name)) ss` >>
  `gas_marked_exec T (ctx,callee) (lock_if_nr cx nr (is_view_mut mut))
      (es,s) [] (INL ()) locked (OK t)` by
    simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  `gas_exempt_cert T (cx_tops cx) (ctx,callee)
     (ignore_bind (try (ignore_bind callee_eval (return NoneV)) handle_function) (return ()))
     (locked with gas_obs := [],t) marks (err,ee) (leaf,leaf_end)` by
    (rewrite_tac[vyperStateTheory.ignore_bind_try_unit, vyperStateTheory.ignore_bind_return_twice] >>
     irule gasExemptCertTheory.gas_exempt_cert_handler >> qexists_tac `ee` >>
     conj_tac >- simp[handle_function_def, ignore_bind_def, bind_def, raise_def] >>
     qpat_assum `gas_exempt_cert T _ _ (ignore_bind callee_eval _) (locked,t) _ _ _`
       (mp_tac o MATCH_MP gasExemptCertTheory.gas_exempt_cert_start_gas_obs) >> simp[]) >>
  `gas_exempt_cert T (cx_tops cx) (ctx,callee)
      (bind (lock_if_nr cx nr (is_view_mut mut))
        (\x:unit. ignore_bind
          (try (ignore_bind callee_eval (return NoneV)) handle_function) (return ())))
      (es,s) ([] ++ marks) (err,ee) (leaf,leaf_end)` by
    (irule gasExemptCertTheory.gas_exempt_cert_bind_unit >>
     qexistsl_tac [`locked`,`t`,`()`] >>
     BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_exempt_cert T _ _ (bind (lock_if_nr _ _ _) _) (es,s) _ _ _` mp_tac >>
  qpat_assum `Abbrev (callee_eval = _)`
    (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[NoAsms, intcall_callee_src_def, ignore_bind_def, bind_assoc]
QED

Theorem intcall_callee_handle_frame[local]:
  handle_function err (ee with gas_obs := gs) =
    (FST (handle_function err ee),ee with gas_obs := gs)
Proof
  Cases_on `err` >> simp[handle_function_def, return_def, raise_def]
QED

Theorem intcall_callee_body_gas_trace[local]:
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) ==>
  !gs. SND (intcall_callee_src cx name mut nr ss (es with gas_obs := gs)) =
    SND (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
            (locked with gas_obs := gs))
Proof
  strip_tac >> gen_tac >>
  qpat_assum `lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked)`
    (qspec_then `gs` (pure_rewrite_tac o single) o
     MATCH_MP intcall_callee_body_gas_source) >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
              (locked with gas_obs := gs)` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >>
  simp[] >> Cases_on `y` >>
  simp[handle_function_def, return_def, raise_def]
QED

Theorem intcall_callee_body_error[local]:
  expr_exit (res:unit + exception) r ==>
  ?err. res = INR err /\ handle_function err es = (INR err,es) /\
        expr_exit (INR err:value + exception) r
Proof
  Cases_on `res` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `INR e` >> Cases_on `e` >>
  simp[expr_exit_def, handle_function_def, return_def, raise_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  simp[expr_exit_def, handle_function_def, return_def, raise_def]
QED

Theorem intcall_callee_body_storage[local]:
  type_stmts env ret ss = SOME env_after /\
  runtime_consistent env cx locked /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  eval_stmts cx ss (locked with gas_obs := gs) = (res,ee with gas_obs := tail) /\
  valid_horizon cx st0 H ee.storage_trace /\
  (valid_horizon cx st0 H locked.storage_trace ==>
     storage_well_formed_on cx locked (FST H)) ==>
  storage_well_formed_on cx ee (FST H)
Proof
  strip_tac >>
  `valid_horizon cx st0 H locked.storage_trace` by
    (`storage_trace_frame (eval_stmts cx ss)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     qpat_assum `eval_stmts cx ss _ = (res,ee with gas_obs := tail)`
       (fn run => qpat_assum `storage_trace_frame (eval_stmts cx ss)`
         (mp_tac o (fn frame => MATCH_MP storage_trace_frame_prefix (CONJ frame run)))) >>
     simp[NoAsms] >> strip_tac >>
     qpat_assum `valid_horizon cx st0 H ee.storage_trace` mp_tac >>
     qpat_assum `ee.storage_trace = locked.storage_trace ++ _`
       (pure_rewrite_tac o single) >>
     metis_tac[valid_horizon_append]) >>
  `storage_well_formed_on cx locked (FST H)` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx (ee with gas_obs := tail) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  `storage_well_formed_on cx (locked with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx locked (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  mp_tac (Q.SPECL [`cx`,`ss`,`env`,`ret`,`env_after`,
     `locked with gas_obs := gs`,`res`,`ee with gas_obs := tail`]
    (cj 2 (Q.SPEC `H` vyperFiniteStoragePreservationTheory.eval_storage_well_formed_on_mutual))) >>
  impl_tac >-
    (qpat_assum `valid_horizon cx st0 H ee.storage_trace`
       (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,
              vyperTypeInvariantsTheory.gas_obs_type_invariants]
     >> simp[]) >>
  simp[]
QED

(* The target Return has performed the unlock. Match it to the source
   release and transport the scope-empty state relation to the caller. *)
Theorem intcall_callee_intret_post[local]:
  body_inv tops ctx cenv cx /\
  body_inv tops ctx ce (cx with stk updated_by CONS (NONE,name)) /\
  ce.ce_returns_count = ret_count /\
  ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  (nr /\ ~view ==> regions_consistent (FST H) /\
     storage_locks_separated (FST H) (SND H) /\
     storage_observations_ok cx H trace /\ MEM (StorageLock key) trace) /\
  storage_well_formed_on cx ee (FST H) /\
  intret_q H callee ce (cx with stk updated_by CONS (NONE,name)) rtv v
    (ee with scopes := []) (IntRet ir u) ==>
  ?ee'. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ee') /\
    storage_well_formed_on cx ee' (FST H) /\
    state_rel H func cenv cx (ee' with scopes := []) u /\
    LENGTH ir.iret_values = ret_count /\ ir.iret_adopt_fmp = NONE /\
    intret_vals_match rtv v ir.iret_values
Proof
  strip_tac >>
  `LENGTH ir.iret_values = ret_count` by
    (qpat_assum `intret_q _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [intret_q_def]) >>
     simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all stmtSimReturnTheory.intret_q_source_epilogue >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_x_assum `result_rel H callee rtv ce _ (INR (ReturnException v),out) (IntRet ir u)`
    (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.result_rel_def]) >>
  `unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := []) = (INL (),out)` by
    (Cases_on `nr` >> Cases_on `view` >>
     fs[unlock_if_nr_def, return_def]) >>
  Cases_on `unlock_if_nr cx nr (is_view_mut mut) ee` >>
  rename1 `unlock_if_nr _ _ _ _ = (result,ee')` >>
  qpat_assum `unlock_if_nr cx nr (is_view_mut mut) ee = (result,ee')`
    (mp_tac o MATCH_MP
      (Q.INST [`sc` |-> `[]`] externalCallSelectedTheory.unlock_if_nr_with_scopes)) >>
  qpat_assum `unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := []) = (INL (),out)`
    (pure_rewrite_tac o single) >> simp[NoAsms] >> strip_tac >>
  asm_rewrite_tac [] >>
  conj_tac
  >- (`(nr /\ ~is_view_mut mut) <=> nr /\ ~view` by
        (Cases_on `nr` >> fs[Excl "is_view_mut_def"]) >>
      Cases_on `nr /\ ~view`
      >- (`nr` by fs[] >>
          qpat_assum `nr ==> cx.nonreentrant_slot = SOME key /\ _`
            (drule_then strip_assume_tac) >>
          `~is_view_mut mut` by
            (qpat_assum `view <=> is_view_mut mut` (pure_rewrite_tac o single o SYM) >>
             qpat_assum `nr /\ ~view` (ACCEPT_TAC o cj 2)) >>
          `release_nonreentrant_lock cx.txn.target key ee = (INL (),ee')` by
            (qpat_assum `unlock_if_nr cx nr (is_view_mut mut) ee = _` mp_tac >>
             pure_rewrite_tac[unlock_if_nr_def] >>
             qpat_assum `(nr /\ ~is_view_mut mut) <=> nr /\ ~view`
               (pure_rewrite_tac o single) >>
             asm_simp_tac bool_ss [optionTheory.option_case_def]) >>
          irule vyperFiniteStoragePreservationTheory.release_lock_preserves_storage_well_formed_on >>
          qpat_assum `nr /\ ~view ==> regions_consistent (FST H) /\ _`
            (fn guard => qpat_assum `nr /\ ~view`
               (strip_assume_tac o MATCH_MP guard)) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl_tac [`cx.txn.target`,`key`,`trace`,`INL ()`,`ee`] >>
          fs[Excl "is_view_mut_def"]) >>
      `~(nr /\ ~is_view_mut mut)` by
        (qpat_assum `(nr /\ ~is_view_mut mut) <=> nr /\ ~view`
           (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
      `ee' = ee` by
        (qpat_assum `unlock_if_nr cx nr (is_view_mut mut) ee = _` mp_tac >>
         pure_rewrite_tac[unlock_if_nr_def] >>
         qpat_assum `(nr /\ ~is_view_mut mut) <=> nr /\ ~view`
           (pure_rewrite_tac o single) >>
         asm_simp_tac bool_ss [return_def, pairTheory.PAIR_EQ]) >>
      simp[]) >>
  `state_rel H callee ce cx (ee' with scopes := []) u` by
    (qpat_assum `out = ee' with scopes := []`
       (fn scope => qpat_assum `state_rel H callee ce _ out u`
          (mp_tac o PURE_REWRITE_RULE [scope])) >>
     simp[loweringStateRelDefsTheory.state_rel_def,
          loweringStateRelDefsTheory.storage_vars_rel_def,
          loweringStateRelDefsTheory.transient_vars_rel_def,
          loweringStateRelDefsTheory.accounts_rel_def, lookup_var_slot_from_layout_def,
          get_module_code_stk_irrelevant, get_tenv_stk_irrelevant]) >>
  once_rewrite_tac[Q.INST [`f1` |-> `func`,`f2` |-> `callee`]
                       stateRelProjTheory.state_rel_scopes_nil_func] >>
  irule exprLoweringPropsTheory.state_rel_cenv_cong >> qexists_tac `ce` >>
  qpat_assum `body_inv tops ctx cenv cx` (strip_assume_tac o MATCH_MP body_inv_module_locations) >>
  qpat_assum `body_inv tops ctx ce _` (strip_assume_tac o MATCH_MP body_inv_module_locations) >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP contract_inv_constructor o MATCH_MP bodySimTheory.body_inv_contract) >>
  qpat_assum `body_inv tops ctx ce _`
    (assume_tac o MATCH_MP contract_inv_constructor o MATCH_MP bodySimTheory.body_inv_contract) >>
  fs[vyperStateTheory.lookup_scopes_def]
QED

Theorem intcall_callee_exit_assemble[local]:
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
  storage_well_formed_on cx out (FST H) /\
  state_rel H func cenv cx (out with scopes := []) s /\
  intret_vals_match rtv v ir.iret_values /\
  LENGTH ir.iret_values = ret_count /\ ir.iret_adopt_fmp = NONE /\
  (!b sz. (cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b) /\
     b + sz <= t.vs_alloca_next /\
     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       n <= aid /\ aid < m ==> regions_disjoint b sz off asz) ==>
     mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  stor_taint_ok_at (DF H) tn' s /\
  (!i. i < lo /\ i IN tn'.t_mem ==>
     imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) i) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tn'.t_mem /\
     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       n <= aid /\ aid < m ==> i < off \/ off + asz <= i) ==> i IN tn.t_mem) /\
  (!p. rb = SOME p ==>
     !mem. mem_agree_outside tn'.t_mem s.vs_memory mem ==>
     val_in_memory rtv v (w2n p) mem) ==>
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv ret_count rb n m t tn
    (INL v) ee (G',tn') (IntRet ir s)
Proof
  strip_tac >>
  rewrite_tac[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def] >>
  conj_tac
  >- (disj2_tac >> qexistsl_tac [`v`,`ir`,`s`,`out`] >>
      simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      rpt strip_tac >> first_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_callee_source_storage[local]:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  intcall_entry_full (DF,lo,d) H0 tops ctx func cenv cx tenv name es sa sb vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
  eval_stmts (cx with stk updated_by CONS (NONE,name)) ss (locked with gas_obs := gs) =
    (res,ee with gas_obs := tail) /\
  valid_horizon cx st0 H ee.storage_trace /\
  (valid_horizon cx st0 H locked.storage_trace ==>
    storage_well_formed_on cx locked (FST H)) ==>
  storage_well_formed_on cx (ee with gas_obs := tail) (FST H)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac intcall_callee_locked_source >>
  rename1 `type_stmts env ret ss = SOME env_raw` >>
  qabbrev_tac `pushed = cx with stk updated_by CONS (NONE,name)` >>
  qhdtm_assum `intcall_entry_full`
    (fn th => map_every STRIP_ASSUME_TAC
      (List.take (CONJUNCTS (REWRITE_RULE [intcall_entry_full_def] th), 8))) >>
  `accounts_well_typed es1.accounts /\ context_well_typed cx /\
   functions_well_typed cx` by
    (qpat_assum `expr_sim_inv cenv cx tenv _`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     fs[]) >>
  `runtime_consistent env pushed locked /\ functions_well_typed pushed` by
    (simp[vyperTypeExprSoundnessTheory.runtime_consistent_def, Abbr `pushed`,
          functions_well_typed_stk_irrelevant, context_well_typed_stk_irrelevant]) >>
  `!tr. valid_horizon pushed st0 H tr <=> valid_horizon cx st0 H tr` by
    simp[NoAsms, Abbr `pushed`, valid_horizon_def,
         vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
         vyperFiniteStoragePreservationTheory.storage_observations_ok_stk] >>
  `valid_horizon pushed st0 H ee.storage_trace /\
   (valid_horizon pushed st0 H locked.storage_trace ==>
     storage_well_formed_on pushed locked (FST H))` by
    (qpat_assum `!tr. valid_horizon pushed st0 H tr <=> _` (pure_rewrite_tac o single) >>
     simp[NoAsms, Abbr `pushed`,
          vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on pushed ee (FST H)` by
    (mp_tac (Q.INST [`cx` |-> `pushed`,`tail` |-> `tail`,
        `env` |-> `env`,`env_after` |-> `env_raw`,`ret` |-> `ret`,
        `ss` |-> `ss`,`res` |-> `res`,`locked` |-> `locked`,
        `st0` |-> `st0`,`H` |-> `H`,`ee` |-> `ee`,`gs` |-> `gs`]
        intcall_callee_body_storage) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        simp[NoAsms, Abbr `pushed`] >> first_assum ACCEPT_TAC)) >>
     simp[NoAsms]) >>
  `storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `storage_well_formed_on pushed ee (FST H)` mp_tac >>
     simp[NoAsms, Abbr `pushed`, vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk]) >>
  `storage_well_formed_on cx (ee with gas_obs := tail) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  simp[]
QED

Theorem intcall_callee_return_count[local]:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (ret_count,rbs,pvs) /\
  body_ce.ce_struct_fields = cenv.ce_struct_fields /\
  body_ce.ce_returns_count = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields body_ce.ce_struct_fields n)) ret /\
  (has_rb <=> body_ce.ce_returns_count = 0 /\ ret <> NoneT) /\
  (has_rb ==> 0 < type_memory_bytes cenv ret) ==>
  body_ce.ce_returns_count = ret_count /\
  (has_rb <=> ret_count = 0 /\ 0 < rbs)
Proof
  strip_tac >>
  drule_all_then mp_tac bodyFullIntCallReturnMetadataTheory.callable_func_info_in_env >>
  qpat_assum `cenv.ce_func_info _ = (ret_count,rbs,pvs)`
    (pure_rewrite_tac o single) >>
  rewrite_tac[compute_func_info_def, LET_THM] >>
  qpat_assum `body_ce.ce_struct_fields = cenv.ce_struct_fields`
    (pure_rewrite_tac o single o SYM) >>
  qpat_assum `body_ce.ce_returns_count = returns_stack_count _ ret`
    (pure_rewrite_tac o single o SYM o REWRITE_RULE [ETA_THM]) >>
  simp[NoAsms, compute_func_info_def, LET_THM] >> strip_tac >>
  Cases_on `has_rb` >> Cases_on `ret` >> fs[]
QED

Theorem intcall_callee_intret_clear_scopes[local]:
  intret_q H callee ce cx rtv v ee r ==>
  intret_q H callee ce cx rtv v (ee with scopes := []) r
Proof
  rewrite_tac[intret_q_def, loweringStateRelDefsTheory.result_rel_def] >>
  strip_tac >>
  rename1 `r = IntRet ir (return_unlock_state ce before_ret with vs_inst_idx := cursor)` >>
  qexistsl_tac [`ir`,`before_ret`,`cursor`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  irule stmtSimReturnTheory.state_rel_scopes_nil >> first_assum ACCEPT_TAC
QED

Theorem intcall_callee_fallthrough_metadata_mods[local]:
  cenv_top_ext ce ce' scopes /\ contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx ==>
  contract_inv mods exps ctx ce' cx /\ module_body_inv mods src tops ce' cx /\
  ce'.ce_return_pc = ce.ce_return_pc /\
  ce'.ce_nonreentrant = ce.ce_nonreentrant /\
  ce'.ce_returns_count = ce.ce_returns_count /\
  ce'.ce_is_ctor = ce.ce_is_ctor
Proof
  strip_tac >>
  drule_then assume_tac bodySimTheory.cenv_top_ext_same_frame >>
  drule_all body_inv_same_frame_mods >> strip_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `cenv_top_ext ce ce' scopes`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.cenv_top_ext_def]) >>
  qpat_assum `ce' with <|ce_vars := _;ce_var_type := _;ce_dynarray_capacity := _|> = ce`
    (once_rewrite_tac o single o SYM) >> simp[]
QED

Theorem intcall_callee_fallthrough_metadata[local]:
  cenv_top_ext ce ce' scopes /\ body_inv tops ctx ce cx ==>
  body_inv tops ctx ce' cx /\
  ce'.ce_return_pc = ce.ce_return_pc /\
  ce'.ce_nonreentrant = ce.ce_nonreentrant /\
  ce'.ce_returns_count = ce.ce_returns_count /\
  ce'.ce_is_ctor = ce.ce_is_ctor
Proof
  strip_tac >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_then assume_tac bodySimTheory.body_inv_module >>
  drule_all intcall_callee_fallthrough_metadata_mods >> strip_tac >> simp[] >>
  irule body_inv_same_frame >> metis_tac[bodySimTheory.cenv_top_ext_same_frame]
QED

Theorem intcall_callee_source_frame[local]:
  pushed = cx with stk updated_by CONS (NONE,name) /\
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
  (!tail. eval_stmts pushed ss (locked with gas_obs := gs ++ tail) =
          (res,ee with gas_obs := tail)) /\
  storage_trace_domain pushed st0 ee.storage_trace /\
  (!H tr. valid_horizon pushed st0 H tr <=> valid_horizon cx st0 H tr) ==>
  (!tail. intcall_callee_src cx name mut nr ss (es1 with gas_obs := gs ++ tail) =
    ((case res of INL _ => INL NoneV | INR err => FST (handle_function err ee)),
       ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H locked.storage_trace)
Proof
  strip_tac >> conj_tac
  >- (gen_tac >>
      qpat_assum `lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked)`
        (qspec_then `gs ++ tail` mp_tac o MATCH_MP intcall_callee_body_gas_source) >>
      qpat_assum `pushed = _` (pure_rewrite_tac o single o SYM) >>
      qpat_assum `!tail. eval_stmts pushed ss _ = (res,ee with gas_obs := tail)`
        (qspec_then `tail` (pure_rewrite_tac o single)) >>
      Cases_on `res` >> simp[NoAsms, LET_THM, intcall_callee_handle_frame]) >>
  conj_tac
  >- (qpat_assum `storage_trace_domain pushed st0 ee.storage_trace` mp_tac >>
      rewrite_tac[storage_trace_domain_def] >>
      qpat_assum `!H tr. valid_horizon pushed st0 H tr <=> _`
        (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  `storage_trace_frame (eval_stmts pushed ss)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qpat_assum `!tail. eval_stmts pushed ss _ = (res,ee with gas_obs := tail)`
    (fn source => qpat_assum `storage_trace_frame (eval_stmts pushed ss)`
       (mp_tac o (fn frame => MATCH_MP storage_trace_frame_prefix
         (CONJ frame (Q.SPEC `[]` source))))) >>
  simp[NoAsms] >> strip_tac >>
  qpat_assum `ee.storage_trace = locked.storage_trace ++ _` (once_rewrite_tac o single) >>
  gen_tac >> MATCH_ACCEPT_TAC valid_horizon_append
QED

Theorem intcall_callee_body_error_exit[local]:
  pushed = cx with stk updated_by CONS (NONE,name) /\
  vres = ((case (res : unit + exception) of INL _ => INL NoneV
                      | INR err => FST (handle_function err ee))) /\
  expr_exit res r /\ halt_exit H pushed (ee with gas_obs := []) res r ==>
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv ret_count rb n m t tn
      vres (ee with gas_obs := []) gt r
Proof
  strip_tac >>
  qpat_assum `expr_exit res r`
    (strip_assume_tac o MATCH_MP (Q.INST [`es` |-> `ee`] intcall_callee_body_error)) >>
  gvs[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
      halt_exit_def, loweringStateRelDefsTheory.halt_rel_def,
      loweringStateRelDefsTheory.accounts_rel_def]
QED

Theorem intcall_callee_return_to_caller[local]:
  body_inv tops ctx cenv cx /\
  body_inv tops ctx ce (cx with stk updated_by CONS (NONE,name)) /\
  ce.ce_returns_count = ret_count /\
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\ view = is_view_mut mut) /\
  valid_horizon cx st0 H locked.storage_trace /\
  (nr /\ ~view ==>
    MEM (StorageLock global_nonreentrant_slot) locked.storage_trace) /\
  storage_well_formed_on cx ee (FST H) /\
  intret_q H callee ce (cx with stk updated_by CONS (NONE,name)) rtv v (ee with scopes := []) (IntRet ir s) /\
  (!b sz. (cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b) /\
     b + sz <= t.vs_alloca_next /\
     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       n <= aid /\ aid < m ==> regions_disjoint b sz off asz) ==>
     mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  stor_taint_ok_at (DF H) tn' s /\
  (!i. i < lo /\ i IN tn'.t_mem ==>
     imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) i) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tn'.t_mem /\
     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       n <= aid /\ aid < m ==> i < off \/ off + asz <= i) ==> i IN tn.t_mem) /\
  (!p. rb = SOME p ==>
     !mem. mem_agree_outside tn'.t_mem s.vs_memory mem ==>
     val_in_memory rtv v (w2n p) mem) ==>
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv ret_count rb n m t tn
    (INL v) ee (G',tn') (IntRet ir s)
Proof
  strip_tac >>
  qpat_assum `valid_horizon cx st0 H locked.storage_trace`
    (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
  mp_tac (Q.INST [`key` |-> `global_nonreentrant_slot`, `trace` |-> `locked.storage_trace`,
     `u` |-> `s`, `ret_count` |-> `ret_count`]
     intcall_callee_intret_post) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  irule intcall_callee_exit_assemble >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexists_tac `out` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_callee_return_from_path[local]:
  body_inv tops ctx cenv cx /\
  body_inv tops ctx ce (cx with stk updated_by CONS (NONE,name)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  intcall_callee_src cx name mut nr ss (es1 with gas_obs := xs) =
    (INL v,ee with gas_obs := []) /\
  valid_horizon cx st0 H ee.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
    MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
    marks (IntRet ir u,G',tn') /\
  ce.ce_returns_count = ret_count /\
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\ view = is_view_mut mut) /\
  valid_horizon cx st0 H locked.storage_trace /\
  (nr /\ ~view ==>
    MEM (StorageLock global_nonreentrant_slot) locked.storage_trace) /\
  storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
  intret_q H callee ce (cx with stk updated_by CONS (NONE,name)) rtv v
    ((ee with gas_obs := []) with scopes := []) (IntRet ir u) /\
  stor_taint_ok_at (DF H) tn' u /\
  (!i. i < lo /\ i IN tn'.t_mem ==>
    imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i) /\
  (!p. rb = SOME p ==> !mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
    val_in_memory rtv v (w2n p) mem) ==>
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv ret_count rb
    sa.cs_next_id sb.cs_next_id t tn (INL v) (ee with gas_obs := []) (G',tn') (IntRet ir u)
Proof
  strip_tac >>
  `!b sz. (cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b) /\
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (mp_tac (Q.INST [`ys` |-> `[]`, `res` |-> `INL v`, `s'` |-> `u`]
       intcall_callee_final_horizon_bytes) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  `!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tn'.t_mem /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      i < off \/ off + asz <= i) ==> i IN tn.t_mem` by
    (mp_tac (Q.INST [`ys` |-> `[]`, `res` |-> `INL v`, `s'` |-> `u`]
       intcall_callee_final_horizon_taint_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  mp_tac (Q.INST [`ee` |-> `ee with gas_obs := []`, `s` |-> `u`,
    `n` |-> `sa.cs_next_id`, `m` |-> `sb.cs_next_id`]
    intcall_callee_return_to_caller) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms]
QED

Theorem contract_inv_singleton_function_mutability[local]:
  contract_inv [(NONE,tops)] [] ctx cenv cx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops ==>
  function_mutability_ok [(NONE,tops)] vis mut nr dflts ss
Proof
  rw[contract_inv_def, optionTheory.FORALL_OPTION] >> res_tac
QED

(* Compilation and concrete cursors of the straight-line entry phases.
   The actual origin path is recorded separately; zero GAS is not used as
   an opcode classification. *)
Definition intcall_callee_prologue_route_def:
  intcall_callee_prologue_route callee ce params has_rb ctor ilen rt
    (entry,prologue) (entered,at_pro) <=>
    ?ce1 caps pc imm ce2 capture reserved materialized at_capture at_reserve at_mat.
      compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
      (if ctor /\ 0 < ilen then
         comp_bind (compile_fixed_region_with_id ilen)
           (\ar. comp_return (SOME (SND ar).buf_operand))
       else comp_return NONE) capture = (imm,reserved) /\
      materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
      (case rt of NONE => comp_return ()
        | SOME ty => if 0 < ce.ce_returns_count then
             comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
               (comp_return ())
           else comp_return ()) materialized = ((),prologue) /\
      fn_has_code entry capture callee /\ fn_has_code capture reserved callee /\
      fn_has_code reserved materialized callee /\ fn_has_code materialized prologue callee /\
      entry.cs_current_insts = [] /\
      entered.vs_current_bb = entry.cs_current_bb /\
      entered.vs_inst_idx = LENGTH entry.cs_current_insts /\
      at_capture.vs_current_bb = capture.cs_current_bb /\
      at_capture.vs_inst_idx = LENGTH capture.cs_current_insts /\
      at_reserve.vs_current_bb = reserved.cs_current_bb /\
      at_reserve.vs_inst_idx = LENGTH reserved.cs_current_insts /\
      at_mat.vs_current_bb = materialized.cs_current_bb /\
      at_mat.vs_inst_idx = LENGTH materialized.cs_current_insts /\
      at_pro.vs_current_bb = prologue.cs_current_bb /\
      at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts
End

(* Keep the callbacks opaque during the shared preparation proof. Each
   branch opens only its own elimination rule. *)
Definition intcall_callee_selected_callbacks_def:
  intcall_callee_selected_callbacks P (DF,lo,ctx,shadow_ctx,callee)
    (tops,cx,st0,name,mut,nr,ret,ss,es1) (entered,G,tn,arg_ops) <=>
      (~storage_trace_domain cx st0 es1.storage_trace ==> P) /\
      (!key. nr /\ cx.nonreentrant_slot = SOME key /\
        ~storage_trace_domain cx st0 (es1.storage_trace ++ [StorageLock key]) ==> P) /\
      (!ce params has_rb ctor ilen rt entry prologue a at_pro Gpro tnpro msg ee ab u j Gl tnl.
        intcall_callee_prologue_route callee ce params has_rb ctor ilen rt
          (entry,prologue) (entered,at_pro) /\
        (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
           MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
           [] (OK at_pro,Gpro,tnpro)) /\
        nr /\ compile_nonreentrant_lock global_nonreentrant_slot T (is_view_mut mut) prologue = ((),a) /\
        fn_has_code prologue a callee /\
        lock_if_nr cx nr (is_view_mut mut) es1 = (INR (Error (RuntimeError msg)),ee) /\
        run_inst_seq (emitted_insts prologue a) at_pro = Abort ab u /\
        (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
           MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
           [] (Abort ab (u with vs_inst_idx := j),Gl,tnl)) ==> P) /\
      (!ce params has_rb ctor ilen rt entry prologue at_pro Gpro tnpro
        a b aS bS final sf body_ce body_out ss_comp dret RetQ locked at_body Gl tnl.
        let pushed = cx with stk updated_by CONS (NONE,name);
            body_ty = case rt of NONE => BaseT BoolT | SOME ty => ty
        in
        intcall_callee_prologue_route callee ce params has_rb ctor ilen rt
          (entry,prologue) (entered,at_pro) /\
        (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
           MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
           [] (OK at_pro,Gpro,tnpro)) /\
        (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (is_view_mut mut)
         else comp_return ()) prologue = ((),a) /\
        fn_has_code prologue a callee /\ fn_has_code b final callee /\
        (?rpc. (if block_is_terminated b then ((),b)
          else comp_ignore_bind
            (if nr then compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View)
             else comp_return ())
            (case rt of NONE => emit_inst RET [rpc] [] | SOME _ => emit_inst INVALID [] []) b) =
          ((),final)) /\
        (?u. run_inst_seq (emitted_insts prologue a) at_pro = OK u /\
             at_body = u with vs_inst_idx := LENGTH a.cs_current_insts) /\
        (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
           MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
           [] (OK at_body,Gl,tnl)) /\
        (!gs. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := gs) =
              (INL (),locked with gas_obs := gs)) /\
        (!K tr. valid_horizon pushed st0 K tr <=> valid_horizon cx st0 K tr) /\
        (!K. valid_horizon cx st0 K locked.storage_trace ==> valid_horizon cx st0 K es1.storage_trace) /\
        at_body.vs_gas_readings = entered.vs_gas_readings /\
        ss_comp = subst_consts_stmts (module_consts_env tops []) ss /\
        intcall_callee_body_inputs tops ctx pushed body_ce ret rt ss locked /\
        frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
          pushed RetQ body_ce ret /\
        stmts_env body_ce NoLoop body_ty ss_comp a = (body_out,b) /\
        stmts_env (gas_shadow_env T body_ce) NoLoop body_ty (MAP gas_shadow_stmt ss_comp) aS =
          (gas_shadow_env T body_out,bS) /\
        gas_shadow_state a aS /\ gas_shadow_state b bS /\
        gas_shadow_function callee sf /\ MEM callee ctx.ctx_functions /\
        MEM sf shadow_ctx.ctx_functions /\ fn_has_code a b callee /\ fn_has_code aS bS sf /\
        (!K. dead_lo_ok K (DF K) lo body_ce pushed) /\
        fn_inst_ids_distinct callee /\ local_ptrs_reserved body_ce a /\ ret_pc_ok body_ce a at_body /\
        (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
        ~block_is_terminated a /\ gas_admissible (eval_stmts pushed ss) (stmt_res_ok NoLoop) locked /\
        return_buf_frame dret body_ce a at_body /\ return_buf_sep dret body_ce locked at_body /\
        alloca_history callee at_body /\ (ctx_has_dalloca ctx ==> allocas_below_fmp at_body) /\
        (!fn inst s. frag_reachable ctx callee at_body fn inst s ==> dalloca_fmp_headroom inst s) /\
        (!K. valid_horizon pushed st0 K locked.storage_trace ==>
          stmt_state_rel K ctx callee body_ce pushed locked at_body /\
          storage_well_formed_on pushed locked (FST K) /\
          ghost_inv_at (DF K) lo dret body_ce pushed locked Gl tnl at_body) /\
        ~at_body.vs_halted /\ at_body.vs_current_bb = a.cs_current_bb /\
        at_body.vs_inst_idx = LENGTH a.cs_current_insts ==> P)
End

(* Early domain failures, an executed lock abort and a successful body
   landing are separate exits from preparation. The ordinary full outcome
   below is retained as a projection, not a second proof of preparation. *)
Theorem intcall_callee_selected_landing:
  !P DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      intcall_callee_selected_callbacks P (DF,lo,ctx,shadow_ctx,callee)
        (tops,cx,st0,name,mut,nr,ret,ss,es1) (entered,G,tn,arg_ops) ==>
      P /\ gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sb.cs_next_id t tn res ee gt r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> disch_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es1.storage_trace`)
  >- (conj_tac >-
        (qhdtm_assum `intcall_callee_selected_callbacks`
           (irule o cj 1 o REWRITE_RULE [intcall_callee_selected_callbacks_def]) >>
         first_assum ACCEPT_TAC) >>
      irule intcall_callee_bad_entry >> simp[] >>
      qexistsl_tac [`func`, `t`] >> fs[]) >>
  drule_all intcall_callee_entry_decode >> strip_tac >>
  `intcall_entry_full (DF, lo, d)
      (storage_trace_horizon es1.storage_trace) tops ctx func cenv cx tenv
      name es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
      es1 t G tn` by
    (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _`
       irule >> fs[storage_trace_domain_def]) >>
  drule_all intcall_entry_full_fmp_room >> strip_tac >>
  drule_all intcall_callee_invoke_label >> strip_tac >>
  `cenv.ce_is_ctor = cx.in_deploy /\ supported_program tops /\
    (cx.in_deploy ==> supported_program_deploy tops)` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       let
         val contract = MATCH_MP bodySimTheory.body_inv_contract inv
         val modul = MATCH_MP bodySimTheory.body_inv_module inv
       in
         ACCEPT_TAC (CONJ (MATCH_MP contract_inv_constructor contract)
           (MATCH_MP contract_inv_module_gate (CONJ contract modul)))
       end)) >>
  `lookup_function
     (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
        cx.in_deploy) ctx.ctx_functions = SOME callee` by
    (qpat_assum `cenv.ce_is_ctor <=> cx.in_deploy`
       (fn th => ONCE_REWRITE_TAC [SYM th]) >>
     qpat_assum `lbl = internal_fn_label _ _ _ _`
       (fn th => ONCE_REWRITE_TAC [SYM th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all bodyFullShadowBodyInvTheory.shadow_body_inv_callee_code >>
  strip_tac >>
  qpat_x_assum `compiled_ss = subst_consts_stmts _ _` (assume_tac o SYM) >>
  qpat_x_assum `set_internal_package_target _ (package_internal_fn _ _ _ _ _ (subst_consts_fn _ _)) = _`
    (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def]) >>
  `label = lbl` by
    (gvs[package_internal_fn_def, set_internal_package_target_def, LET_THM]) >>
  `fn_entry_label callee = SOME lbl` by
    (Cases_on `cx.in_deploy`
     >- (`MEM callee unit.cu_context.ctx_functions` by
           metis_tac[venomInstTheory.lookup_function_MEM] >>
         `callee.fn_name = lbl` by
           metis_tac[vyperCompilerTheory.lookup_function_result_name] >>
         metis_tac[deploy_prefix_member_entry_label]) >>
     `lower_vyper_runtime_unit tops rpolicy = SOME unit` by fs[] >>
     drule_all lower_vyper_runtime_unit_internal_lookup >>
     strip_tac >>
     gvs[vyperCompilerTheory.mk_internal_function_metadata,
         venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
         listTheory.NULL_EQ]) >>
  `setup.vs_current_bb = entry.cs_current_bb /\ entry.cs_current_insts = [] /\
   setup.vs_inst_idx = 0` by
    (drule venomExecPropsTheory.setup_callee_props >> strip_tac >>
     qpat_assum `new_block label before = (old,entry)`
       (strip_assume_tac o MATCH_MP (SPEC_ALL emitHelperPropsTheory.new_block_props)) >>
     (gvs[])) >>
  Cases_on `compile_internal_function_entry ce params has_rb ctor ilen rt entry` >>
  rename1 `_ = (entry_info,prologue)` >>
  PairCases_on `entry_info` >>
  `?prologueS.
     compile_internal_function_entry (gas_shadow_env T ce) params has_rb
       ctor ilen rt entryS = ((gas_shadow_env T entry_info0,entry_info1,entry_info2),prologueS) /\
     gas_shadow_state prologue prologueS` by
    (irule intcall_shadow_entry_cut >> qexists_tac `entry` >> simp[]) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac `lock = if nr' then compile_nonreentrant_lock key trans view
                      else comp_return ()` >>
  Cases_on `lock prologue` >>
  rename1 `_ = (lock_result,a)` >> Cases_on `lock_result` >>
  `?aS. lock prologueS = ((),aS) /\ gas_shadow_state a aS` by
    (`gas_shadow_compiles lock lock` by
       (simp[Abbr `lock`] >> Cases_on `nr'` >>
        simp[gas_shadow_compiles_nonreentrant_lock, gas_shadow_compiles_return]) >>
     qpat_x_assum `gas_shadow_compiles lock lock`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`prologue`, `prologueS`] mp_tac) >>
     Cases_on `lock prologueS` >> simp[]) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac `body_ce = entry_info0 with
    <|ce_imm_alloca := entry_info2; ce_alloca_locals := T|>` >>
  qabbrev_tac `body_ty = case rt of SOME ty => ty | NONE => BaseT BoolT` >>
  Cases_on `stmts_env body_ce NoLoop body_ty compiled_ss a` >>
  rename1 `_ = (body_out,b)` >>
  `?bS. stmts_env (gas_shadow_env T body_ce) NoLoop body_ty (MAP gas_shadow_stmt compiled_ss) aS =
          (gas_shadow_env T body_out,bS) /\ gas_shadow_state b bS` by
    (`gas_shadow_compiles_env T (stmts_env body_ce NoLoop body_ty compiled_ss)
        (stmts_env (gas_shadow_env T body_ce) NoLoop body_ty
           (MAP gas_shadow_stmt compiled_ss))` by irule gas_shadow_stmts_env_env >>
     pop_assum (qspecl_then [`a`,`aS`] mp_tac o
       REWRITE_RULE [gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def]) >>
     Cases_on `stmts_env (gas_shadow_env T body_ce) NoLoop body_ty
       (MAP gas_shadow_stmt compiled_ss) aS` >> simp[]) >>
  pop_assum strip_assume_tac >>
  `cs_appends lock` by
    (simp[Abbr `lock`] >> Cases_on `nr'` >>
     simp[cs_appends_nonreentrant, cs_appends_return]) >>
  qpat_assum `compile_internal_function_entry _ _ _ _ _ _ entry = _`
    (assume_tac o MATCH_MP (SRULE[cs_appends_def]
      cs_appends_internal_function_entry)) >>
  qpat_assum `compile_internal_function_entry _ _ _ _ _ _ entryS = _`
    (assume_tac o MATCH_MP (SRULE[cs_appends_def]
      cs_appends_internal_function_entry)) >>
  `cs_extends prologue a /\ cs_extends prologueS aS` by
    (qpat_assum `cs_appends lock` (mp_tac o REWRITE_RULE[cs_appends_def]) >>
     disch_then (fn th =>
       mp_tac (Q.SPECL [`prologue`, `()`, `a`] th) >>
       mp_tac (Q.SPECL [`prologueS`, `()`, `aS`] th)) >> simp[]) >>
  `cs_extends entry a /\ cs_extends entryS aS` by
    (conj_tac >> irule cs_extends_trans
     >- (qexists_tac `prologue` >> asm_rewrite_tac []) >>
     qexists_tac `prologueS` >> asm_rewrite_tac []) >>
  `cs_extends a final /\ fn_has_code a b callee /\ fn_has_code b final callee /\
   (if block_is_terminated b then ((),b)
    else comp_ignore_bind
      (if nr' then compile_nonreentrant_unlock key trans view else comp_return ())
      (case rt of NONE => emit_inst RET [entry_info1] []
        | SOME _ => emit_inst INVALID [] []) b) = ((),final)` by
    (qspecl_then [`ce`, `params`, `has_rb`, `nr'`, `key`, `trans`, `view`,
       `ctor`, `ilen`, `compiled_ss`, `rt`, `entry`, `final`, `entry_info0`,
       `entry_info1`, `entry_info2`, `prologue`, `a`, `body_out`, `b`,
       `callee`] mp_tac intcall_lowering_suffix >>
     fs[Abbr `lock`, Abbr `body_ce`, Abbr `body_ty`]) >>
  `gas_shadow_env T body_ce = (gas_shadow_env T entry_info0) with
     <|ce_imm_alloca := entry_info2; ce_alloca_locals := T|>` by
    simp[Abbr `body_ce`, gasShadowCompileBaseTheory.gas_shadow_env_def] >>
  `fn_has_code aS bS sf` by
    (`(if nr' then compile_nonreentrant_lock key trans view else comp_return ())
        prologueS = ((),aS)` by fs[Abbr `lock`] >>
     `stmts_env ((gas_shadow_env T entry_info0) with
        <|ce_imm_alloca := entry_info2; ce_alloca_locals := T|>) NoLoop
        (case rt of SOME ty => ty | NONE => BaseT BoolT)
        (MAP gas_shadow_stmt compiled_ss) aS = (gas_shadow_env T body_out,bS)` by
       (qpat_assum `gas_shadow_env T body_ce = _` (rewrite_tac o single o SYM) >>
        qpat_assum `stmts_env _ _ _ (MAP gas_shadow_stmt _) aS = _` mp_tac >>
        simp[Abbr `body_ty`]) >>
     drule_all (Q.SPEC `gas_shadow_env T ce` intcall_lowering_suffix) >> simp[]) >>
  qpat_assum `compile_internal_function_entry _ _ _ _ _ _ entry = _`
    (strip_assume_tac o MATCH_MP (SPEC_ALL intcall_callee_entry_phases)) >>
  drule_then strip_assume_tac intcall_callee_capture_same_blocks >>
  `cs_extends entry capture` by
    (simp[cs_extends_def] >> qexists_tac `[]` >> simp[same_blocks_def] >>
     fs[same_blocks_def]) >>
  `cs_extends capture prologue` by
    metis_tac[cs_extends_trans] >>
  `cs_extends capture final` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code entry capture callee` by
    metis_tac[fn_has_code_split] >>
  drule_all intcall_callee_capture_entry >> strip_tac >>
  `set_internal_package_target rpolicy.rpol_target
     (package_internal_fn tops T (K global_nonreentrant_slot) cenv.ce_is_ctor
       (if cx.in_deploy then
          compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
        else 0)
       (mut,nr,rr,name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,
        subst_consts_stmts (module_consts_env tops []) ss)) =
     (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)` by
    (qpat_assum `cenv.ce_is_ctor = cx.in_deploy` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `set_internal_package_target rpolicy.rpol_target
     (package_internal_fn tops T (K global_nonreentrant_slot) cenv.ce_is_ctor
       (if cx.in_deploy then
          compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
        else 0) (mut,nr,rr,name,args,dflts,ret,ss)) =
     (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,ss,rt)` by
    (qpat_assum `set_internal_package_target _ (package_internal_fn _ _ _
        cenv.ce_is_ctor _ _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[package_internal_fn_def, set_internal_package_target_def,
          entryDispatchPropsTheory.build_compile_env_subst_consts_stmts] >>
     strip_tac >> fs[]) >>
  drule_all intcall_callee_selected_args >> strip_tac >>
  `fresh_vars_wrt entry entered /\ entered.vs_params = argv /\
   ~entered.vs_halted /\ allocas_from lo entered /\ entered.vs_allocas = FEMPTY` by
    (drule intcall_callee_setup_capture >>
     disch_then (qspecl_then [`lo`, `entry`] mp_tac) >> simp[]) >>
  `(if has_rb then 1 else 0) + LENGTH params <= LENGTH entered.vs_params /\
   LENGTH entered.vs_params < dimword (:256)` by
    ((qpat_assum `internal_args_rel ce params _ _ _ _ _`
       (mp_tac o REWRITE_RULE [internal_args_rel_def]) >>
     strip_tac >> simp[] >> (gvs[]))) >>
  `fmp_room ctx callee entered` by
    (qpat_assum `entered = setup` (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entered` by
    (qpat_assum `fmp_room ctx callee entered` mp_tac >>
     qpat_assum `entered.vs_allocas = FEMPTY` (fn empty =>
       simp[NoAsms, fmp_room_def, ptrDisciplineTheory.allocas_below_fmp_def, empty]) >>
     metis_tac[]) >>
  drule_all compile_internal_entry_prefix_joint >>
  disch_then (qspecl_then [`tn with t_var := FEMPTY`, `MAP (op_prov G) arg_ops`, `FEMPTY`]
    (qx_choose_then `captured` (qx_choose_then `Gcap`
      (qx_choose_then `tncap` strip_assume_tac)))) >>
  `entered.vs_current_bb = entry.cs_current_bb` by metis_tac[] >>
  drule_all intcall_callee_capture_cursor >> strip_tac >>
  qabbrev_tac `at_capture = captured with vs_inst_idx :=
    entered.vs_inst_idx + LENGTH (emitted_insts entry capture)` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_capture,Gcap,tncap)` by
    (rpt gen_tac >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `D` (qspec_then `explicit` ACCEPT_TAC o CONJUNCT2))) >>
  `at_capture = captured with vs_inst_idx := LENGTH capture.cs_current_insts` by
    (qpat_assum `Abbrev (at_capture = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `entered.vs_inst_idx + LENGTH (emitted_insts entry capture) = _`
       (rewrite_tac o single)) >>
  `fresh_vars_wrt capture at_capture /\ ~at_capture.vs_halted /\ allocas_from lo at_capture /\
   at_capture.vs_current_bb = capture.cs_current_bb /\
   at_capture.vs_inst_idx = LENGTH capture.cs_current_insts` by
    (qpat_assum `at_capture = captured with vs_inst_idx := _` (rewrite_tac o single) >>
     simp[loweringStateRelDefsTheory.fresh_vars_wrt_def] >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >>
     simp[ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[loweringStateRelDefsTheory.fresh_vars_wrt_def, ptrDisciplineTheory.allocas_from_def]) >>
  `cs_extends reserved final /\ fn_has_code capture reserved callee` by
    (conj_asm1_tac
     >- (irule cs_extends_trans >> qexists_tac `prologue` >>
         reverse conj_tac >- (irule cs_extends_trans >> qexists_tac `a` >> simp[]) >>
         irule cs_extends_trans >> qexists_tac `materialized` >> simp[]) >>
     irule fn_has_code_mid >> reverse conj_tac >- (qexistsl_tac [`final`,`entry`] >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `fmp_room ctx callee at_capture` by
    (qspecl_then [`ctx`,`callee`,`entered`,`at_capture`] mp_tac fmp_room_fields_cong >>
     qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >>
     simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_capture` by
    (qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp entered` mp_tac >>
     simp[NoAsms, ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all intcall_callee_reserve >>
  disch_then (qspecl_then [`tncap`, `MAP (op_prov G) arg_ops`, `Gcap`] strip_assume_tac) >>
  rename1 `at_reserve = at_capture with <|vs_vars := at_reserve.vs_vars; vs_inst_idx := _|>` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,_) (at_capture,Gcap,tncap) []
                       (OK at_reserve,Gres,tnres)` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_reserve,Gres,tnres)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gcap`,`at_capture`,`tncap`] >> simp[]) >>
  `at_reserve.vs_inst_idx = LENGTH reserved.cs_current_insts /\
   at_reserve.vs_params = argv /\ ~at_reserve.vs_halted /\
   at_reserve.vs_allocas = FEMPTY /\
   at_reserve.vs_alloca_next = t.vs_alloca_next /\
   at_reserve.vs_memory = t.vs_memory /\
   at_reserve.vs_call_ctx = t.vs_call_ctx /\
   at_reserve.vs_accounts = t.vs_accounts /\
   at_reserve.vs_transient = t.vs_transient /\
   at_reserve.vs_immutables = t.vs_immutables /\
   at_reserve.vs_tx_ctx = t.vs_tx_ctx /\ at_reserve.vs_block_ctx = t.vs_block_ctx /\
   at_reserve.vs_logs = t.vs_logs /\ at_reserve.vs_outcomes = t.vs_outcomes /\
   at_reserve.vs_requests = t.vs_requests /\
   at_reserve.vs_pending_deletions = t.vs_pending_deletions /\
   at_reserve.vs_data_section = t.vs_data_section /\ at_reserve.vs_code = t.vs_code /\
   at_reserve.vs_labels = t.vs_labels` by
    (qpat_assum `at_reserve = at_capture with <|vs_vars := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >>
     qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >>
     qpat_assum `entered = setup` (once_rewrite_tac o single) >>
     Cases_on `NULL callee.fn_blocks`
     >- fs[venomExecSemanticsTheory.setup_callee_def] >>
     qpat_x_assum `setup_callee callee argv t = SOME setup` mp_tac >>
     simp[venomExecSemanticsTheory.setup_callee_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `DF (storage_trace_horizon es1.storage_trace)` (assume_tac o CONJUNCT1)) >>
  drule_all compile_internal_entry_prefix_ghost_outputs >> strip_tac >>
  drule_then assume_tac compile_internal_entry_prefix_capture_code >>
  drule_all internal_capture_seq_ghost_frame >> strip_tac >>
  drule_then strip_assume_tac compile_internal_entry_prefix_shape >>
  `internal_args_rel ce1 params penv (if has_rb then 1 else 0) argv
      at_reserve.vs_alloca_next at_reserve.vs_memory` by
    (qpat_assum `internal_args_rel ce params penv _ argv _ _`
       (mp_tac o REWRITE_RULE [internal_args_rel_def]) >>
     asm_rewrite_tac [internal_args_rel_def]) >>
  `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
      not_fresh_at reserved p /\
      lookup_var p at_reserve = SOME (EL ((if has_rb then 1 else 0) + i) argv)` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
     qpat_assum `!y. not_fresh_at capture y ==> _` drule >> strip_tac >>
     qexists_tac `p` >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `lookup_var p at_reserve = _` (once_rewrite_tac o single) >>
     qpat_assum `at_capture = captured with vs_inst_idx := _`
       (once_rewrite_tac o single) >>
     qpat_assum `lookup_var p captured = _` mp_tac >>
     qpat_assum `entered.vs_params = argv` (once_rewrite_tac o single) >>
     simp[lookup_var_def, NoAsms]) >>
  drule_all intcall_callee_materialize_pre >>
  disch_then (qspec_then `callee` strip_assume_tac) >>
  `cs_extends materialized final` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code reserved materialized callee` by
    metis_tac[fn_has_code_split] >>
  `fn_inst_ids_distinct callee` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts callee))` by
       (irule allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn >>
        qexists_tac `ctx` >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
     pop_assum mp_tac >>
     simp[venomWfTheory.fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
          venomInstIdsPropsTheory.fn_insts_blocks_map_id, NoAsms]) >>
  `!i. MEM i (DROP (LENGTH reserved.cs_current_insts) materialized.cs_current_insts) ==>
       MEM i (fn_insts callee)` by
    (rpt strip_tac >> irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl_tac [`reserved`, `materialized`] >>
     metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `es1.scopes = [penv] /\
   (!n e. FLOOKUP penv n = SOME e ==> value_has_type e.type e.value)` by
    (qhdtm_assum `intcall_entry_full`
       (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
     drule vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success >>
     simp[vyperTypeInvariantsTheory.scope_well_typed_def, NoAsms] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST caps)` by
    (qpat_assum `internal_args_rel ce1 params penv _ argv _ _`
       (strip_assume_tac o REWRITE_RULE [internal_args_rel_def]) >>
     simp[]) >>
  `internal_stack_size ce1 params = internal_stack_size ce params` by
    (irule internal_stack_size_vars >> simp[]) >>
  `at_reserve.vs_alloca_next +
     internal_stack_size ce1 (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by
    (qpat_assum `at_reserve.vs_alloca_next = _` (once_rewrite_tac o single) >>
     simp[intcall_callee_stack_size_imm]) >>
  `LENGTH argv = LENGTH arg_ops` by
    metis_tac[tupleLoadPropsTheory.eval_operands_length] >>
  `!i. i < (if has_rb then 1 else 0) + LENGTH params ==>
       FLOOKUP Gcap (STRING #"%" (toString (entry.cs_next_var + i))) =
         op_prov G (EL i arg_ops) /\
       op_taint tncap (Var (STRING #"%" (toString (entry.cs_next_var + i)))) = {}` by
    (qx_gen_tac `i` >> disch_tac >>
     `i < LENGTH arg_ops` by
       (qpat_assum `_ + LENGTH params <= LENGTH entered.vs_params` mp_tac >>
        qpat_assum `i < _ + LENGTH params` mp_tac >>
        qpat_assum `entered.vs_params = argv` (once_rewrite_tac o single) >>
        qpat_assum `LENGTH argv = LENGTH arg_ops` (once_rewrite_tac o single) >> decide_tac) >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = (if _ then _ else _) /\ _`
       (qspec_then `i` mp_tac) >> simp[listTheory.EL_MAP]) >>
  `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
     lookup_var p at_reserve = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
     FLOOKUP Gres p = op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) /\
     op_taint tnres (Var p) = {}` by
    (qx_gen_tac `i` >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _ /\ _ /\ lookup_var p captured = _`
       drule >> disch_then (qx_choose_then `p` strip_assume_tac) >>
     `p = STRING #"%" (toString (entry.cs_next_var + ((if has_rb then 1 else 0) + i)))` by
       (qpat_assum `!i. i < LENGTH params ==> SND (SND (EL i caps)) = _` drule >>
        qpat_assum `SND (SND (EL i caps)) = Var p` (rewrite_tac o single) >>
        simp[NoAsms, GSYM arithmeticTheory.ADD_ASSOC]) >>
     qpat_assum `!x. not_fresh_at capture x ==> lookup_var x at_reserve = _ /\ _`
       (qspec_then `p` mp_tac) >>
     qpat_assum `not_fresh_at capture p` (once_rewrite_tac o single) >>
     rewrite_tac[] >> strip_tac >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = op_prov G _ /\ _`
       (qspec_then `(if has_rb then 1 else 0) + i` mp_tac) >>
     impl_tac >- (qpat_assum `i < LENGTH params` mp_tac >> simp[NoAsms]) >>
     strip_tac >> qexists_tac `p` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `lookup_var p at_reserve = lookup_var p at_capture`
           (rewrite_tac o single) >>
         qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
         qpat_assum `lookup_var p captured = _` mp_tac >>
         qpat_assum `entered.vs_params = argv` (rewrite_tac o single) >> simp[NoAsms, lookup_var_def]) >>
     qpat_assum `FLOOKUP Gres p = FLOOKUP Gcap p` (rewrite_tac o single) >>
     qpat_assum `op_taint tnres (Var p) = op_taint tncap (Var p)` (rewrite_tac o single) >>
     qpat_assum `p = STRING #"%" _` (rewrite_tac o single) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `tnres.t_mem = tn.t_mem /\ tnres.t_stor = tn.t_stor /\
   tnres.t_trans = tn.t_trans /\ tnres.t_imm = tn.t_imm` by
    (asm_rewrite_tac[] >> simp[NoAsms]) >>
  `!mem. mem_agree_outside tnres.t_mem at_reserve.vs_memory mem ==>
     internal_args_rel ce1 params penv (if has_rb then 1 else 0) argv t.vs_alloca_next mem` by
    (gen_tac >>
     qpat_assum `tnres.t_mem = tn.t_mem` (rewrite_tac o single) >>
     qpat_assum `at_reserve.vs_memory = t.vs_memory` (rewrite_tac o single) >>
     qpat_assum `!mem. mem_agree_outside tn.t_mem _ mem ==> internal_args_rel ce params _ _ _ _ mem`
       (qspec_then `mem` mp_tac) >>
     rewrite_tac[internal_args_rel_def] >> asm_rewrite_tac[]) >>
  `!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
       FLOOKUP ce1.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
       ?b bsz. op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) = SOME (b,bsz) /\
          b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
          w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz` by
    (qpat_assum `ce1.ce_vars = ce.ce_vars` (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  drule_all intcall_callee_materialize_captures >> strip_tac >>
  `ce1.ce_return_pc = SOME (PtrVar (Var x) 0) /\
   not_fresh_at reserved x /\
   lookup_var x at_reserve = SOME entered.vs_return_pc_token /\
   op_taint tnres (Var x) = {}` by
    (qpat_assum `!x. not_fresh_at capture x ==> lookup_var x at_reserve = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at capture x` (rewrite_tac o single) >>
     strip_tac >>
     qpat_assum `ce1.ce_return_pc = _` (rewrite_tac o single) >>
     qpat_assum `entry_info1 = Var x` (rewrite_tac o single) >>
     qpat_assum `not_fresh_at reserved x` (rewrite_tac o single) >>
     qpat_assum `lookup_var x at_reserve = lookup_var x at_capture` (rewrite_tac o single) >>
     qpat_assum `at_capture = captured with vs_inst_idx := _` (rewrite_tac o single) >>
     qpat_assum `op_taint tnres (Var x) = _` (rewrite_tac o single) >>
     qpat_assum `op_taint tncap entry_info1 = {}` mp_tac >>
     qpat_assum `entry_info1 = Var x` (rewrite_tac o single) >>
     qpat_assum `lookup_var x captured = SOME entered.vs_return_pc_token` mp_tac >>
     simp[NoAsms, lookup_var_def]) >>
  drule_all intcall_callee_package_slots >> strip_tac >>
  qabbrev_tac `ret_dest = if has_rb then SOME (HD argv,type_memory_size rtv) else NONE` >>
  `(!q sz. ce1.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at reserved q) /\
   return_buf_ptr ret_dest ce1 Gres tnres at_reserve` by
    (reverse (Cases_on `has_rb`)
     >- simp[Abbr `ret_dest`, bodyPtrDefsTheory.return_buf_ptr_def] >>
     `0 < LENGTH entered.vs_params` by
       (qpat_assum `_ + LENGTH params <= LENGTH entered.vs_params` mp_tac >>
        simp[NoAsms] >> decide_tac) >>
     drule_all intcall_callee_capture_buffer >> strip_tac >>
     qabbrev_tac `p = STRING #"%" (toString entry.cs_next_var)` >>
     qpat_assum `!q. not_fresh_at capture q ==> lookup_var q at_reserve = _ /\ _`
       (qspec_then `p` mp_tac) >>
     `not_fresh_at capture p` by simp[Abbr `p`] >>
     qpat_assum `not_fresh_at capture p` (rewrite_tac o single) >> strip_tac >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = op_prov G _ /\ _`
       (qspec_then `0` mp_tac) >>
     simp[NoAsms, listTheory.EL] >> strip_tac >>
     `lookup_var p at_reserve = SOME (HD argv)` by
       (qpat_assum `lookup_var p at_reserve = lookup_var p at_capture` (rewrite_tac o single) >>
        qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
        qpat_assum `lookup_var p captured = _` mp_tac >>
        simp[NoAsms, lookup_var_def] >>
        qpat_assum `entered.vs_params = argv` (rewrite_tac o single) >> simp[NoAsms]) >>
     qpat_assum `T ==> ?b bsz. op_prov G (HD arg_ops) = _ /\ _`
       (strip_assume_tac o SRULE []) >>
     simp[Abbr `ret_dest`, bodyPtrDefsTheory.return_buf_ptr_def] >>
     simp[bodyPtrDefsTheory.ptr_covers_def, Abbr `p`]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
        ghost_inv_at (DF H) lo ret_dest ce1 cx es1 Gres tnres at_reserve` by
    ((qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> intcall_entry_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx _ G tn t`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
                 ptrDisciplineTheory.allocas_from_def] >>
     map_every (fn p => qpat_assum p (rewrite_tac o single))
       [`at_reserve.vs_allocas = FEMPTY`, `at_reserve.vs_alloca_next = t.vs_alloca_next`,
        `at_reserve.vs_memory = t.vs_memory`, `at_reserve.vs_call_ctx = t.vs_call_ctx`,
        `at_reserve.vs_accounts = t.vs_accounts`, `at_reserve.vs_transient = t.vs_transient`,
        `at_reserve.vs_immutables = t.vs_immutables`, `tnres.t_stor = tn.t_stor`,
        `tnres.t_trans = tn.t_trans`, `tnres.t_imm = tn.t_imm`, `tnres.t_mem = tn.t_mem`,
        `!n p sz. FLOOKUP ce1.ce_vars n <> SOME (PtrVar p sz)`, `ce1.ce_imm_alloca = NONE`,
        `ce1.ce_return_pc = SOME (PtrVar (Var x) 0)`, `op_taint tnres (Var x) = {}`,
        `return_buf_ptr ret_dest ce1 Gres tnres at_reserve`, `lo <= t.vs_alloca_next`] >>
     qpat_assum `stor_taint_ok_at (DF H) tn t`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` mp_tac >>
     simp[NoAsms, finite_mapTheory.FLOOKUP_EMPTY] >> (metis_tac[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def, ptrDisciplineTheory.allocas_from_def, finite_mapTheory.FLOOKUP_EMPTY]))) >>
  `lo <= t.vs_alloca_next` by
    (qhdtm_assum `intcall_entry_full`
       (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
     qhdtm_assum `ghost_inv_at`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `Ds = {DF H | valid_horizon cx st0 H es1.storage_trace}` >>
  `!D. D IN Ds ==> ghost_inv_at D lo ret_dest ce1 cx es1 Gres tnres at_reserve` by
    simp[Abbr `Ds`, pred_setTheory.GSPECIFICATION, PULL_EXISTS] >>
  `!q sz. ce1.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at reserved q` by simp[] >>
  `!n q sz. FLOOKUP ce1.ce_vars n = SOME (PtrVar (Var q) sz) ==> not_fresh_at reserved q` by simp[] >>
  `!q. ce1.ce_imm_alloca = SOME (Var q) ==> not_fresh_at reserved q` by simp[] >>
  `lo <= at_reserve.vs_alloca_next` by
    (qpat_assum `at_reserve.vs_alloca_next = t.vs_alloca_next` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `!q. entry_info2 = SOME (Var q) ==>
     not_fresh_at reserved q /\ FLOOKUP Gres q = NONE /\ op_taint tnres (Var q) = {}` by
    (qpat_assum `if ctor /\ 0 < ilen then _ else entry_info2 = NONE` mp_tac >>
     IF_CASES_TAC >> simp[NoAsms] >>
     disch_then (qx_choose_then `imm_var` strip_assume_tac) >>
     qpat_assum `entry_info2 = SOME (Var imm_var)` (rewrite_tac o single) >> simp[]) >>
  `!D. D IN Ds ==> ghost_inv_at D lo ret_dest
      (ce1 with ce_imm_alloca := entry_info2) cx es1 Gres tnres at_reserve` by
    (gen_tac >> disch_tac >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at _ _ _ ce1 _ _ _ _ _` drule >>
     qpat_assum `!q. entry_info2 = SOME (Var q) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `materialize_internal_params (ce1 with ce_imm_alloca := entry_info2) caps reserved =
     (entry_info0 with ce_imm_alloca := entry_info2,materialized)` by
    (irule intcall_callee_materialize_imm >> first_assum ACCEPT_TAC) >>
  `fmp_room ctx callee at_reserve` by
    (qspecl_then [`ctx`,`callee`,`at_capture`,`at_reserve`] mp_tac fmp_room_fields_cong >>
     qpat_assum `at_reserve = at_capture with <|vs_vars := _; vs_inst_idx := _|>`
       (once_rewrite_tac o single) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_reserve /\
    at_reserve.vs_alloca_next + pending_alloca_size callee at_reserve <= w2n at_reserve.vs_initial_fmp` by
    (mp_tac (Q.INST [`s` |-> `at_reserve`, `func` |-> `callee`]
       intcall_callee_alloca_room) >> simp[venomMemProofsTheory.alloca_inv_empty_proof]) >>
  qpat_assum `materialize_internal_params (ce1 with ce_imm_alloca := _) _ _ = _`
    (mp_then (Pos hd) mp_tac materialize_params_full) >>
  disch_then (qspecl_then [`callee`, `penv`, `at_reserve`, `at_reserve.vs_alloca_next`,
    `mr`, `ctx`, `lo`, `ret_dest`, `cx`, `es1`, `MAP (op_prov G) arg_ops`,
    `Gres`, `tnres`, `Ds`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  simp[NoAsms] >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choose_then `mat_state` (qx_choose_then `Gmat`
    (qx_choose_then `tnmat` strip_assume_tac))) >>
  `entry_info0.ce_imm_alloca = NONE` by
    (qpat_assum `materialize_internal_params ce1 caps reserved = (entry_info0,materialized)`
       (mp_then (Pos hd) mp_tac intcall_callee_materialize_shape) >> strip_tac >>
     qpat_assum `entry_info0 = ce1 with ce_vars := _` (once_rewrite_tac o single) >> simp[]) >>
  `entry_info0 with ce_imm_alloca := NONE = entry_info0` by
    simp[compile_env_component_equality] >>
  `!D. D IN Ds ==> ghost_inv_at D lo ret_dest body_ce cx es1 Gmat tnmat mat_state` by
    (gen_tac >> disch_tac >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at D _ _ (entry_info0 with ce_imm_alloca := _) _ _ _ _ _` drule >>
     simp[NoAsms, Abbr `body_ce`, bodyPtrDefsTheory.ghost_inv_at_def,
          intcall_callee_return_buf_imm] >> metis_tac[]) >>
  `!D. D IN Ds ==> ghost_inv_at D lo ret_dest entry_info0 cx es1 Gmat tnmat mat_state` by
    (gen_tac >> disch_tac >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at D _ _ body_ce _ _ _ _ _` drule >>
     simp[NoAsms, Abbr `body_ce`, intcall_callee_ghost_imm] >>
     qpat_assum `entry_info0 with ce_imm_alloca := NONE = entry_info0` (rewrite_tac o single) >>
     simp[NoAsms]) >>
  `return_buf_sep ret_dest entry_info0 es1 mat_state` by
    (mp_tac (Q.INST [`ce` |-> `entry_info0`, `env` |-> `penv`,
                `s` |-> `mat_state`, `frontier` |-> `at_reserve.vs_alloca_next`,
                `borrowed` |-> `mr`, `es` |-> `es1`, `d` |-> `ret_dest`]
       intcall_callee_materialized_return_buf_sep) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        Cases_on `has_rb` >> simp[NoAsms, Abbr `ret_dest`] >>
        conj_tac
        >- (qpat_assum `T ==> w2n (HD argv) + type_memory_size rtv <= _` mp_tac >>
            qpat_assum `at_reserve.vs_alloca_next = t.vs_alloca_next`
              (rewrite_tac o single) >> simp[NoAsms, arithmeticTheory.ADD_COMM]) >>
        map_every qx_gen_tac [`borrowed_name`, `borrowed_base`, `borrowed_size`] >>
        disch_tac >>
        qpat_assum `!n b sz. mr n = SOME (b,sz) <=> _`
          (drule_then (qx_choose_then `arg_index`
            (qx_choose_then `arg_offset` strip_assume_tac)) o iffLR) >>
        `FLOOKUP ce.ce_vars (FST (EL arg_index params)) =
          SOME (MemLoc arg_offset borrowed_size)` by
          (qpat_assum `ce1.ce_vars = ce.ce_vars` (pure_rewrite_tac o single o SYM) >>
           qpat_assum `FST (EL arg_index params) = borrowed_name`
             (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
        qpat_assum `T ==> !i off sz. _ ==> regions_disjoint _ _ _ _`
          (mp_tac o SIMP_RULE bool_ss []) >>
        disch_then (qspecl_then [`arg_index`,`arg_offset`,`borrowed_size`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_assum `borrowed_base = _` (rewrite_tac o single) >>
        simp[NoAsms,arithmeticTheory.ADD_COMM]) >> simp[]) >>
  qabbrev_tac `at_mat = mat_state with vs_inst_idx := LENGTH materialized.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_mat,Gmat,tnmat)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gres`,`at_reserve`,`tnres`] >> simp[NoAsms, Abbr `at_mat`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
        ghost_inv_at (DF H) lo ret_dest entry_info0 cx es1 Gmat tnmat at_mat` by
    (rpt strip_tac >>
     simp[NoAsms, Abbr `at_mat`, ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at D lo ret_dest entry_info0 cx es1 Gmat tnmat mat_state`
       irule >>
     simp[Abbr `Ds`, pred_setTheory.GSPECIFICATION, PULL_EXISTS] >> metis_tac[]) >>
  qpat_assum `materialize_internal_params ce1 caps reserved = (entry_info0,materialized)`
    (mp_then (Pos hd) mp_tac intcall_callee_materialize_shape) >> strip_tac >>
  `~at_mat.vs_halted /\ at_mat.vs_current_bb = materialized.cs_current_bb /\
   at_mat.vs_inst_idx = LENGTH materialized.cs_current_insts` by
    (qpat_assum `mat_frame reserved at_reserve mat_state`
       (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     simp[NoAsms, Abbr `at_mat`] >>
     qpat_assum `mat_state = at_reserve with <|vs_vars := _; vs_memory := _;
        vs_allocas := _; vs_alloca_next := _|>` (once_rewrite_tac o single) >>
     simp[]) >>
  `alloca_room ctx callee at_reserve` by
    (irule alloca_room_fields >> qexists_tac `setup` >>
     qpat_assum `at_reserve = at_capture with <|vs_vars := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >>
     qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >>
     qpat_assum `entered = setup` (once_rewrite_tac o single) >> simp[]) >>
  `EVERY (\i. MEM i (fn_insts callee) /\ i.inst_opcode <> INVOKE)
       (DROP (LENGTH reserved.cs_current_insts) materialized.cs_current_insts)` by
    (simp[NoAsms, listTheory.EVERY_MEM] >> gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!i. MEM i (DROP _ materialized.cs_current_insts) ==> _`
           irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE) code`
       (irule o SRULE [listTheory.EVERY_MEM]) >>
     qpat_assum `MEM _ (DROP _ materialized.cs_current_insts)` mp_tac >>
     qpat_assum `materialized.cs_current_insts = reserved.cs_current_insts ++ code`
       (rewrite_tac o single) >>
     simp[NoAsms, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `alloca_room ctx callee mat_state` by
    (irule run_inst_seq_alloca_room >> goal_assum (drule_at Any) >>
     qexists_tac `at_reserve` >> simp[]) >>
  `alloca_room ctx callee at_mat` by
    (irule alloca_room_fields >> qexists_tac `mat_state` >> simp[Abbr `at_mat`]) >>
  `allocas_from lo at_mat /\ lo <= at_mat.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ at_mat`
       (qspec_then `storage_trace_horizon es1.storage_trace` mp_tac) >>
     (impl_tac >- (qpat_assum `storage_trace_domain cx st0 es1.storage_trace` mp_tac >>
                   simp[NoAsms, storage_trace_domain_def])) >>
     disch_then (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `materialized.cs_next_id NOTIN FDOM at_mat.vs_allocas` by
    (simp[NoAsms, Abbr `at_mat`] >>
     qpat_assum `mat_inv callee entry_info0 penv materialized mat_state _ mr`
       (strip_assume_tac o REWRITE_RULE [intcall_callee_materialize_imm_invs,mat_inv_def]) >>
     qpat_assum `!aid. aid IN FDOM mat_state.vs_allocas ==> _`
       (qspec_then `materialized.cs_next_id` mp_tac) >>
     simp[NoAsms]) >>
  `fn_has_code materialized prologue callee` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`final`,`entry`] >> conj_tac
     >- (irule cs_extends_trans >> qexists_tac `a` >> conj_tac >> first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists_tac `reserved` >> conj_tac
     >- (irule cs_extends_trans >> qexists_tac `capture` >> conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `alloca_inv at_mat /\
   (!i w b sz. MEM i (fn_insts callee) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\ FLOOKUP at_mat.vs_allocas i.inst_id = SOME (b,sz) ==>
      sz = w2n w)` by
    (qpat_assum `mat_inv callee entry_info0 penv materialized mat_state _ mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     simp[NoAsms, Abbr `at_mat`] >> conj_tac
     >- simp[venomMemProofsTheory.alloca_inv_set_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN
    `prologue = materialized \/ ?n buf. compile_alloc_buffer n materialized = (buf,prologue)`
    assume_tac
  >- (qpat_assum `(case rt of NONE => _ | SOME _ => _) materialized = _` mp_tac >>
     Cases_on `rt` >> simp[NoAsms, comp_return_def] >>
     IF_CASES_TAC >> simp[NoAsms, comp_return_def, comp_ignore_bind_def, comp_bind_def] >>
     rename1 `compile_alloc_buffer (type_memory_bytes ce ty) _` >>
     Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) materialized` >>
     simp[NoAsms, comp_return_def] >>
     disch_then (rewrite_tac o single o SYM) >> disj2_tac >>
     qexists_tac `type_memory_bytes ce ty` >> goal_assum (drule_at Any)) >>
  `mat_state.vs_fmp = at_reserve.vs_fmp` by
    (qpat_assum `mat_frame reserved at_reserve mat_state`
       (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     qpat_assum `mat_state = at_reserve with <|vs_vars := _; vs_memory := _;
        vs_allocas := _; vs_alloca_next := _|>` (once_rewrite_tac o single) >>
     simp[]) >>
  `fmp_room ctx callee mat_state` by
    (irule run_inst_seq_fmp_room >>
     qexistsl_tac [`DROP (LENGTH reserved.cs_current_insts) materialized.cs_current_insts`,
                    `at_reserve`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `fmp_room ctx callee at_mat` by
    (qspecl_then [`ctx`,`callee`,`mat_state`,`at_mat`] mp_tac fmp_room_fields_cong >>
     simp[Abbr `at_mat`]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_mat` by
    (mp_tac (Q.INST [`s` |-> `at_mat`, `func` |-> `callee`]
       intcall_callee_alloca_room) >> simp[]) >>
  `?at_pro Gpro tnpro.
     alloca_inv at_pro /\
     (!i w b sz. MEM i (fn_insts callee) /\ i.inst_opcode = ALLOCA /\
        i.inst_operands = [Lit w] /\ FLOOKUP at_pro.vs_allocas i.inst_id = SOME (b,sz) ==>
        sz = w2n w) /\
     at_pro with <|vs_vars := at_mat.vs_vars; vs_allocas := at_mat.vs_allocas;
       vs_alloca_next := at_mat.vs_alloca_next; vs_inst_idx := at_mat.vs_inst_idx|> = at_mat /\
     allocas_from lo at_pro /\ at_mat.vs_alloca_next <= at_pro.vs_alloca_next /\
     alloca_room ctx callee at_pro /\ fmp_room ctx callee at_pro /\ ~at_pro.vs_halted /\
     at_pro.vs_current_bb = prologue.cs_current_bb /\
     at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts /\
     (fresh_vars_wrt materialized at_mat ==> fresh_vars_wrt prologue at_pro) /\
     (!aid r. FLOOKUP at_mat.vs_allocas aid = SOME r ==> FLOOKUP at_pro.vs_allocas aid = SOME r) /\
     (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) /\
         FLOOKUP at_mat.vs_allocas aid = NONE ==> at_mat.vs_alloca_next <= b) /\
     (!q. not_fresh_at materialized q ==>
       lookup_var q at_pro = lookup_var q at_mat /\ FLOOKUP Gpro q = FLOOKUP Gmat q /\
       op_taint tnpro (Var q) = op_taint tnmat (Var q)) /\
     tnpro.t_stor = tnmat.t_stor /\ tnpro.t_trans = tnmat.t_trans /\ tnpro.t_imm = tnmat.t_imm /\
     (!i. i IN tnpro.t_mem <=> i IN tnmat.t_mem \/
            (at_mat.vs_alloca_next <= i /\ i < at_pro.vs_alloca_next)) /\
     !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
        (at_mat,Gmat,tnmat) [] (OK at_pro,Gpro,tnpro)` by
    (qpat_assum `prologue = materialized \/ _` strip_assume_tac
     >- (qexistsl_tac [`at_mat`,`Gmat`,`tnmat`] >>
         simp[venom_state_component_equality, fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         rpt gen_tac >> strip_tac >>
         qpat_assum `FLOOKUP at_mat.vs_allocas _ = SOME _` mp_tac >>
         qpat_assum `FLOOKUP at_mat.vs_allocas _ = NONE` (rewrite_tac o single) >> simp[NoAsms]) >>
     irule intcall_callee_scratch_joint >>
     rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
       (qexistsl_tac [`buf`,`n`] >> first_assum ACCEPT_TAC))) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_pro,Gpro,tnpro)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gmat`,`at_mat`,`tnmat`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `EVERY (\c. !q. SND (SND c) = Var q ==> not_fresh_at reserved q) caps` by
    (simp[NoAsms, listTheory.EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
     `LENGTH caps = LENGTH params` by metis_tac[listTheory.LENGTH_MAP] >>
     `i < LENGTH params` by metis_tac[] >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _ /\ not_fresh_at reserved p /\ _`
       (qspec_then `i` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qx_choose_then `pp` strip_assume_tac) >>
     qpat_assum `SND (SND (EL i caps)) = Var pp` (rewrite_tac o single) >>
     simp[]) >>
  `!n p sz. FLOOKUP entry_info0.ce_vars n = SOME (PtrVar (Var p) sz) ==>
           not_fresh_at materialized p` by
    (qpat_assum `EVERY _ caps /\ _ ==> !n p sz. FLOOKUP entry_info0.ce_vars n = _ ==> _`
       mp_tac >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[NoAsms]) >>
  `local_ptrs_rel callee entry_info0 es1.scopes at_mat` by
    (qpat_assum `mat_inv callee entry_info0 penv materialized mat_state _ mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     qpat_assum `es1.scopes = [penv]` (rewrite_tac o single) >>
     simp[NoAsms, Abbr `at_mat`, localPtrsPropsTheory.local_ptrs_rel_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  `entry_info0.ce_imm_alloca = NONE /\
   entry_info0.ce_return_pc = ce1.ce_return_pc /\ entry_info0.ce_return_buf = ce1.ce_return_buf` by
    (qpat_assum `entry_info0 = ce1 with ce_vars := _` (once_rewrite_tac o single) >> simp[]) >>
  `(!q sz. entry_info0.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at materialized q) /\
   (!q sz. entry_info0.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at materialized q)` by
    (conj_tac >> rpt gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `reserved` >> conj_tac >- first_assum ACCEPT_TAC >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
        ghost_inv_at (DF H) lo ret_dest entry_info0 cx es1 Gpro tnpro at_pro` by
    (gen_tac >> disch_tac >>
     `ghost_inv_at (DF H) lo ret_dest entry_info0 cx es1 Gmat tnmat at_mat` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at_vars >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gmat`,`at_pro.vs_alloca_next`,`callee`,`at_mat`,`materialized`,`tnmat`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  `fresh_vars_wrt prologue at_pro` by
    (qpat_assum `fresh_vars_wrt materialized at_mat ==> _` irule >>
     qpat_assum `mat_inv callee entry_info0 penv materialized mat_state _ mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     simp[NoAsms, Abbr `at_mat`, loweringStateRelDefsTheory.fresh_vars_wrt_def] >>
     qpat_assum `fresh_vars_wrt materialized mat_state`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.fresh_vars_wrt_def])) >>
  qpat_assum `at_pro with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = at_mat`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  `local_ptrs_rel callee body_ce es1.scopes at_pro` by
    (irule local_ptrs_rel_cenv_cong >> qexists_tac `entry_info0` >>
     conj_tac >- simp[NoAsms, Abbr `body_ce`] >>
     irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists_tac `at_mat` >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `at_pro.vs_memory = at_mat.vs_memory` (rewrite_tac o single) >> NO_TAC) ORELSE
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!q. not_fresh_at materialized q ==> _`
          (irule o cj 1) >>
        qpat_assum `!n p sz. FLOOKUP entry_info0.ce_vars n = _ ==> _`
          (irule_at Any) >> goal_assum (drule_at Any)))) >>
  `ce.ce_module_vars = body_ce.ce_module_vars /\
   ce.ce_module = body_ce.ce_module /\ ce.ce_is_ctor = body_ce.ce_is_ctor /\
   ce.ce_module_var_type = body_ce.ce_module_var_type` by
    (drule_then assume_tac intcall_callee_capture_env >>
     simp[NoAsms, Abbr `body_ce`] >>
     qpat_assum `entry_info0 = ce1 with ce_vars := _` (once_rewrite_tac o single) >>
     qpat_assum `ce1 = ce with <|ce_return_buf := _; ce_return_pc := _|>`
       (once_rewrite_tac o single) >> simp[NoAsms]) >>
  `return_buf_sep ret_dest body_ce es1 at_pro` by
    (mp_tac (Q.INST [`d` |-> `ret_dest`, `cenv` |-> `entry_info0`,
                `es` |-> `es1`, `s` |-> `mat_state`,
                `cenv'` |-> `body_ce`, `ee` |-> `es1`, `t` |-> `at_pro`]
        bodyFullSharedTheory.return_buf_sep_transport) >>
     impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
        >- (map_every qx_gen_tac [`rb_word`,`rb_capacity`] >> disch_tac >>
            `w2n rb_word + rb_capacity <= at_mat.vs_alloca_next` by
              (qpat_assum `ret_dest = SOME (rb_word,rb_capacity)` mp_tac >>
               Cases_on `has_rb` >> simp[NoAsms, Abbr `ret_dest`] >>
               strip_tac >>
               qpat_assum `T ==> w2n (HD argv) + type_memory_size rtv <= _`
                 (mp_tac o SIMP_RULE bool_ss []) >>
               qpat_assum `mat_state.vs_alloca_next = _` mp_tac >>
               qpat_assum `at_reserve.vs_alloca_next = t.vs_alloca_next` mp_tac >>
               simp[Abbr `at_mat`, arithmeticTheory.ADD_COMM]) >>
            `allocas_from (w2n rb_word + rb_capacity) at_mat` by
              (simp[NoAsms, Abbr `at_mat`, ptrDisciplineTheory.allocas_from_def] >>
               qpat_assum `return_buf_sep ret_dest entry_info0 es1 mat_state` mp_tac >>
               qpat_assum `ret_dest = SOME (rb_word,rb_capacity)` (rewrite_tac o single) >>
               simp[NoAsms, bodySimFullTheory.return_buf_sep_def,
                    ptrDisciplineTheory.allocas_from_def] >>
               strip_tac >> first_assum ACCEPT_TAC) >>
            simp[NoAsms, ptrDisciplineTheory.allocas_from_def] >>
            map_every qx_gen_tac [`new_aid`,`new_base`,`new_size`] >> strip_tac >>
            Cases_on `FLOOKUP at_mat.vs_allocas new_aid`
            >- (qpat_assum `!aid b sz. FLOOKUP at_pro.vs_allocas aid = _ /\ _ ==> _`
                  (drule_all_then assume_tac) >> decide_tac) >>
            rename1 `FLOOKUP at_mat.vs_allocas new_aid = SOME old_slot` >>
            qpat_assum `!aid r. FLOOKUP at_mat.vs_allocas aid = _ ==> _`
              (drule_then assume_tac) >>
            `old_slot = (new_base,new_size)` by
              (qpat_assum `FLOOKUP at_pro.vs_allocas new_aid = SOME old_slot` (mp_tac o SYM) >>
               qpat_assum `FLOOKUP at_pro.vs_allocas new_aid = SOME (new_base,new_size)`
                 (rewrite_tac o single) >> simp[NoAsms]) >>
            qpat_assum `allocas_from (w2n rb_word + rb_capacity) at_mat`
              (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
            disch_then (qspecl_then [`new_aid`,`new_base`,`new_size`] mp_tac) >>
            simp[]) >>
        simp[NoAsms, Abbr `body_ce`, loweringStateRelDefsTheory.local_region_def] >>
        map_every qx_gen_tac [`local_name`,`local_base`,`local_size`] >>
        disch_then (qx_choose_then `local_entry` (qx_choose_then `local_var`
          (qx_choose_then `local_word` strip_assume_tac))) >>
        qexistsl_tac [`local_entry`,`local_var`,`local_word`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        `not_fresh_at materialized local_var` by
          (qpat_assum `!n p sz. FLOOKUP entry_info0.ce_vars n = _ ==> _`
             (drule_then ACCEPT_TAC)) >>
        qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = _ /\ _`
          (drule_then strip_assume_tac) >>
        `lookup_var local_var mat_state = lookup_var local_var at_mat` by
          simp[NoAsms, Abbr `at_mat`, lookup_var_def] >>
        pop_assum (pure_rewrite_tac o single) >>
        qpat_assum `lookup_var local_var at_pro = lookup_var local_var at_mat`
          (pure_rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC) >> simp[]) >>
  `internal_immutable_regions body_ce cx es1 t.vs_alloca_next` by
    (qpat_assum `internal_immutable_regions ce cx es1 t.vs_alloca_next` mp_tac >>
     pure_rewrite_tac [internal_immutable_regions_def] >>
     map_every (fn p => qpat_assum p (rewrite_tac o single))
       [`ce.ce_module_vars = body_ce.ce_module_vars`, `ce.ce_module = body_ce.ce_module`,
        `ce.ce_is_ctor = body_ce.ce_is_ctor`,
        `ce.ce_module_var_type = body_ce.ce_module_var_type`]) >>
  qpat_assum `mat_frame reserved at_reserve mat_state`
    (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
  qpat_assum `mat_state = at_reserve with <|vs_vars := _; vs_memory := _;
        vs_allocas := _; vs_alloca_next := _|>`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  `immutable_base_zero body_ce at_pro` by
    (simp[NoAsms, loweringStateRelDefsTheory.immutable_base_zero_def] >> conj_tac
     >- (simp[NoAsms, Abbr `body_ce`] >> gen_tac >> disch_tac >>
         qpat_assum `if ctor /\ 0 < ilen then _ else entry_info2 = NONE` mp_tac >>
         IF_CASES_TAC >> simp[NoAsms]
         >- (disch_then (qx_choose_then `imm_var` strip_assume_tac) >>
             `not_fresh_at materialized imm_var` by
               (irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `reserved` >> conj_tac >> first_assum ACCEPT_TAC) >>
             qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = _ /\ _`
               (qspec_then `imm_var` mp_tac) >>
             (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
             qpat_assum `!q. not_fresh_at reserved q ==> lookup_var q mat_state = _`
               (qspec_then `imm_var` mp_tac) >>
             (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
             `base' = Var imm_var` by metis_tac[optionTheory.SOME_11] >>
             qpat_assum `base' = Var imm_var` (rewrite_tac o single) >>
             pure_rewrite_tac [eval_operand_def] >>
             qpat_assum `lookup_var imm_var at_pro = lookup_var imm_var at_mat`
               (rewrite_tac o single) >>
             `lookup_var imm_var at_mat = lookup_var imm_var mat_state` by
               simp[NoAsms, Abbr `at_mat`, lookup_var_def] >>
             metis_tac[]) >>
         simp[]) >>
     qpat_assum `ce.ce_is_ctor = body_ce.ce_is_ctor` (rewrite_tac o single o SYM) >>
     simp[Abbr `at_mat`]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
     state_rel H callee ce cx (es1 with scopes := []) t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==>
          intcall_entry_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` drule >>
     disch_tac >> drule_all (cj 1 intcall_callee_selected_args) >> simp[]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
     state_rel H callee body_ce cx es1 at_pro` by
    (gen_tac >> disch_tac >>
     `state_rel H callee ce cx (es1 with scopes := []) t` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     `state_rel H callee body_ce cx (es1 with scopes := []) t` by
       (irule state_rel_cenv_cong >> qexists_tac `ce` >>
        simp[vyperStateTheory.lookup_scopes_def]) >>
     `LENGTH t.vs_memory <= LENGTH at_pro.vs_memory` by
       (simp[Abbr `at_mat`] >> metis_tac[]) >>
     `immutables_rel body_ce cx.txn.target body_ce.ce_module body_ce.ce_is_ctor es1 at_pro` by
       (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `t` >>
        qpat_assum `state_rel H callee body_ce cx _ t`
          (assume_tac o MATCH_MP stateRelProjTheory.state_rel_immutables_rel) >>
        rpt conj_tac >>
        TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        TRY (simp[Abbr `at_mat`] >> NO_TAC) >>
        TRY (qpat_assum `immutables_rel body_ce _ _ _ (es1 with scopes := []) t` mp_tac >>
             simp[NoAsms, loweringStateRelDefsTheory.immutables_rel_def] >> NO_TAC) >>
        qpat_assum `internal_immutable_regions body_ce cx es1 _`
          (mp_tac o REWRITE_RULE [internal_immutable_regions_def]) >>
        simp[Abbr `at_mat`] >> rpt strip_tac >>
        metis_tac[]) >>
     irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es1 with scopes := []`, `t`] >>
     simp[Abbr `at_mat`] >> conj_tac
     >- (qpat_assum `es1.scopes = [penv]` (rewrite_tac o single o SYM) >> simp[]) >>
     qpat_assum `immutables_rel body_ce _ _ _ es1 at_pro` mp_tac >>
     simp[NoAsms, loweringStateRelDefsTheory.immutables_rel_def]) >>
  `entered.vs_allocas = FEMPTY` by
    (qpat_assum `at_reserve.vs_allocas = FEMPTY` mp_tac >>
     qpat_assum `at_reserve = at_capture with <|vs_vars := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >>
     qpat_assum `at_capture = captured with vs_inst_idx := _` (once_rewrite_tac o single) >>
     qpat_assum `captured = entered with vs_vars := _` (once_rewrite_tac o single) >> simp[NoAsms]) >>
  `alloca_history callee at_pro` by
    (`alloca_history callee entered` by simp[allocaHistoryTheory.alloca_history_empty] >>
     `alloca_inv entered` by simp[venomMemProofsTheory.alloca_inv_empty_proof] >>
     irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_pro,Gpro,tnpro)`
       (qspec_then `DF (storage_trace_horizon es1.storage_trace)` (irule_at Any)) >>
     simp[]) >>
  `ret_pc_ok ce1 reserved at_reserve` by
    (simp[loweringPostsTheory.ret_pc_ok_def] >>
     qexists_tac `entered.vs_return_pc_token` >> first_assum ACCEPT_TAC) >>
  `return_buf_frame ret_dest ce1 reserved at_reserve` by
    (reverse (Cases_on `has_rb`) >- simp[Abbr `ret_dest`, loweringPostsTheory.return_buf_frame_def] >>
     `w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next` by
       (qpat_assum `T ==> ?b bsz. op_prov G (HD arg_ops) = _ /\ _`
          (qx_choose_then `buf_base` (qx_choose_then `buf_size` strip_assume_tac) o SRULE []) >>
        irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `buf_base + buf_size` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `return_buf_ptr ret_dest ce1 Gres tnres at_reserve` mp_tac >>
     simp[NoAsms, Abbr `ret_dest`, bodyPtrDefsTheory.return_buf_ptr_def, loweringPostsTheory.return_buf_frame_def] >>
     disch_then (qx_choose_then `rbv` (qx_choose_then `rbsize` strip_assume_tac)) >>
     qexistsl_tac [`rbv`,`rbsize`] >> simp[]) >>
  `immutable_alloca_sep callee body_ce cx es1 at_pro` by
    (`immutable_alloca_sep func cenv cx (es1 with scopes := prev) t` by
       (qhdtm_assum `intcall_entry_full`
          (strip_assume_tac o REWRITE_RULE [intcall_entry_full_def]) >>
        qhdtm_assum `stmt_state_rel`
          (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]) >>
        first_assum ACCEPT_TAC) >>
     `cenv.ce_is_ctor = body_ce.ce_is_ctor /\ cenv.ce_module = body_ce.ce_module /\
      cenv.ce_module_vars = body_ce.ce_module_vars /\
      cenv.ce_module_var_type = body_ce.ce_module_var_type` by
       (qpat_assum `cenv.ce_is_ctor = cx.in_deploy` mp_tac >>
        qpat_assum `ce.ce_module_vars = body_ce.ce_module_vars` mp_tac >>
        qpat_assum `ce.ce_module = body_ce.ce_module` mp_tac >>
        qpat_assum `ce.ce_is_ctor = body_ce.ce_is_ctor` mp_tac >>
        qpat_assum `ce.ce_module_var_type = body_ce.ce_module_var_type` mp_tac >>
        qpat_assum `set_internal_package_target _ (package_internal_fn _ _ _ cx.in_deploy _ _) = _`
          mp_tac >>
        qpat_assum `body_inv tops ctx cenv cx`
          (mp_tac o MATCH_MP intcall_callee_singleton_frame) >>
        POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        simp[package_internal_fn_def, set_internal_package_target_def, update_cenv_nonreentrant_def] >>
        strip_tac >>
        qspecl_then [`tops`,`Internal`,`mut`,`name`,`args`,`ret`,`compiled_ss`,`T`]
          strip_assume_tac
          (SRULE [bodySimTheory.cenv_module_pins_def] bodySimEntryTheory.build_compile_env_module_pins) >>
        qpat_assum `_ with <|ce_target := _; ce_is_ctor := _;
                      ce_nonreentrant := _; ce_raw_return := _|> = ce`
          (once_rewrite_tac o single o SYM) >>
        fs[bodySimTheory.cenv_module_pins_def]) >>
     qpat_assum `mat_inv callee entry_info0 penv materialized mat_state _ mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     `t.vs_alloca_next <= at_mat.vs_alloca_next` by simp[Abbr `at_mat`] >>
     irule intcall_callee_immutable_sep >>
     qexistsl_tac [`func`,`cenv`,`es1 with scopes := prev`,`t`] >>
     simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt gen_tac >> strip_tac >>
     rename1 `local_region body_ce es1.scopes at_pro nm lb lsz` >>
     `local_region entry_info0 [penv] mat_state nm lb lsz` by
       (qpat_assum `local_region body_ce es1.scopes at_pro nm lb lsz` mp_tac >>
        qpat_assum `es1.scopes = [penv]` (rewrite_tac o single) >>
        simp[NoAsms, Abbr `body_ce`, loweringStateRelDefsTheory.local_region_def] >>
        strip_tac >> goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
        `not_fresh_at materialized p` by
          (qpat_assum `!n p sz. FLOOKUP entry_info0.ce_vars n = _ ==> _` drule >> simp[]) >>
        qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = _ /\ _` drule >>
        simp[Abbr `at_mat`, lookup_var_def]) >>
     qpat_assum `!n b sz. local_region entry_info0 [penv] mat_state n b sz ==> _`
       (drule_then strip_assume_tac)
     >- (disj1_tac >> decide_tac) >>
     disj2_tac >>
     qpat_assum `!n b sz. mr n = SOME (b,sz) <=> _` (drule_then strip_assume_tac o iffLR) >>
     `FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off lsz)` by
       metis_tac[] >>
     qpat_assum `!i off sz. i < LENGTH params /\ ~SND (EL i params) /\ _ ==>
       ?inst b cap. MEM inst (fn_insts func) /\ _` (drule_all_then strip_assume_tac) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qpat_assum `lb = w2n _` (pure_rewrite_tac o single) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (map_every qx_gen_tac [`slot_id`,`slot_base`,`slot_size`] >> disch_tac >>
         Cases_on `FLOOKUP at_mat.vs_allocas slot_id`
         >- (qpat_assum `!aid b sz. FLOOKUP at_pro.vs_allocas aid = _ /\ _ ==> _` drule_all >>
             decide_tac) >>
         rename1 `FLOOKUP at_mat.vs_allocas slot_id = SOME slot` >>
         `FLOOKUP at_pro.vs_allocas slot_id = SOME slot` by
           (qpat_assum `!aid r. FLOOKUP at_mat.vs_allocas aid = _ ==> _`
              (qspecl_then [`slot_id`,`slot`] irule) >> first_assum ACCEPT_TAC) >>
         `slot = (slot_base,slot_size)` by metis_tac[optionTheory.SOME_11] >>
         `FLOOKUP mat_state.vs_allocas slot_id = SOME (slot_base,slot_size)` by
           (qpat_assum `FLOOKUP at_mat.vs_allocas slot_id = SOME slot` mp_tac >>
            simp[NoAsms, Abbr `at_mat`] >>
            qpat_assum `slot = (slot_base,slot_size)` (pure_rewrite_tac o single) >> simp[]) >>
         qpat_assum `!aid b sz. FLOOKUP mat_state.vs_allocas aid = _ ==> _`
           (qspecl_then [`slot_id`,`slot_base`,`slot_size`] mp_tac) >> simp[]) >>
     decide_tac) >>
  Q.SUBGOAL_THEN
    `materialized.cs_next_var <= prologue.cs_next_var /\
     (~block_is_terminated materialized ==> ~block_is_terminated prologue)` strip_assume_tac
  >- (irule intcall_callee_scratch_resources >> first_assum ACCEPT_TAC) >>
  `reserved.cs_next_var <= prologue.cs_next_var` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `materialized.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `at_reserve.vs_alloca_next <= at_pro.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `at_mat.vs_alloca_next` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `mat_frame reserved at_reserve mat_state`
       (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     simp[NoAsms, Abbr `at_mat`] >> first_assum ACCEPT_TAC) >>
  `!q. not_fresh_at reserved q ==> lookup_var q at_pro = lookup_var q at_reserve` by
    (gen_tac >> disch_tac >>
     `not_fresh_at materialized q` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `reserved` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!q. not_fresh_at materialized q ==> lookup_var q at_pro = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `mat_frame reserved at_reserve mat_state`
       (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
     qpat_assum `!q. not_fresh_at reserved q ==> lookup_var q mat_state = _`
       (drule_then assume_tac) >>
     qpat_assum `lookup_var q at_pro = lookup_var q at_mat` (rewrite_tac o single) >>
     simp[NoAsms, Abbr `at_mat`, lookup_var_def] >>
     qpat_assum `lookup_var q mat_state = lookup_var q at_reserve`
       (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gmat tnmat at_mat` by
    (gen_tac >> disch_tac >>
     simp[NoAsms, Abbr `at_mat`, ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at D lo ret_dest body_ce cx es1 Gmat tnmat mat_state`
       irule >>
     simp[Abbr `Ds`, pred_setTheory.GSPECIFICATION, PULL_EXISTS] >> metis_tac[]) >>
  `local_ptrs_rel callee body_ce es1.scopes at_mat` by
    (irule local_ptrs_rel_cenv_cong >> qexists_tac `entry_info0` >>
     conj_tac >- simp[NoAsms, Abbr `body_ce`] >> first_assum ACCEPT_TAC) >>
  `!q. body_ce.ce_imm_alloca = SOME (Var q) ==> not_fresh_at materialized q` by
    (simp[NoAsms, Abbr `body_ce`] >> gen_tac >> disch_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `reserved` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!q. entry_info2 = SOME (Var q) ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `~block_is_terminated capture` by
    (qpat_assum `compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,entry_info1),capture)`
       (mp_then (Pos hd) mp_tac intcall_callee_capture_open) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `(if ctor /\ 0 < ilen then _ else _) capture = (entry_info2,reserved)`
    (mp_then (Pos hd) mp_tac intcall_callee_fixed_reserve_resources) >> strip_tac >>
  `~block_is_terminated reserved` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `~block_is_terminated materialized` by
    (irule intcall_callee_open_append >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `LENGTH caps = LENGTH params` by metis_tac[listTheory.LENGTH_MAP] >>
  `ALL_DISTINCT (MAP (SND o SND) caps)` by
    (simp[listTheory.EL_ALL_DISTINCT_EL_EQ, listTheory.EL_MAP,
          combinTheory.o_DEF] >> rpt strip_tac >>
     qpat_assum `!i. i < LENGTH params ==> SND (SND (EL i caps)) = _`
       (fn th => imp_res_tac th) >>
     gvs[ASCIInumbersTheory.toString_inj]) >>
  `!n b op. MEM (n,b,op) caps ==>
       (?off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz)) /\
       (?p. op = Var p /\ not_fresh_at reserved p)` by
    (simp[NoAsms,listTheory.MEM_EL] >> rpt gen_tac >>
     disch_then (qx_choose_then `cap_index` strip_assume_tac) >>
     `cap_index < LENGTH params` by decide_tac >>
     `FST (EL cap_index caps) = FST (EL cap_index params)` by
       (qpat_assum `MAP FST caps = MAP FST params`
          (mp_tac o Q.AP_TERM `EL cap_index`) >>
        simp[listTheory.EL_MAP]) >>
     qpat_assum `internal_args_rel ce1 params penv _ argv _ _`
       (strip_assume_tac o REWRITE_RULE [internal_args_rel_def]) >>
     conj_tac
     >- (qpat_assum `!i. i < LENGTH params ==> ?off sz e. _`
           (qspec_then `cap_index` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then (qx_choose_then `cap_off` (qx_choose_then `cap_size`
           (qx_choose_then `cap_val` strip_assume_tac))) >>
         qpat_assum `(_,_,_) = EL cap_index caps`
           (mp_tac o Q.AP_TERM `FST`) >>
         qpat_assum `FST (EL cap_index caps) = FST (EL cap_index params)` (rewrite_tac o single) >>
         simp[NoAsms] >> disch_then SUBST1_TAC >>
         qexistsl_tac [`cap_off`,`cap_size`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
             not_fresh_at reserved p /\ _` (qspec_then `cap_index` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `(_,_,_) = EL cap_index caps`
       (mp_tac o Q.AP_TERM `SND o SND`) >>
     qpat_assum `SND (SND (EL cap_index caps)) = Var p`
       (simp o cons NoAsms o cons combinTheory.o_DEF o single) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!n off sz. FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz) ==>
    MEM n (MAP FST caps)` by
    (rpt strip_tac >>
     `ce.ce_vars = (build_compile_env tops Internal mut name args ret ss T).ce_vars /\
       MAP FST params = MAP FST args` by
       (qpat_assum `set_internal_package_target _
            (package_internal_fn _ _ _ _ _ (mut,nr,rr,name,args,dflts,ret,ss)) = _`
          (mp_tac o MATCH_MP intcall_callee_package_metadata) >>
        simp[NoAsms]) >>
     qpat_assum `FLOOKUP ce1.ce_vars n = _` mp_tac >>
     simp[] >> metis_tac[bodySimEntryTheory.build_compile_env_bound]) >>
  `local_ptrs_reserved entry_info0 materialized` by
    (irule materialize_internal_params_reserved >>
     qexistsl_tac [`caps`,`ce1`,`reserved`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     simp[]) >>
  `!q. entry_info2 = SOME (Var q) ==> ~MEM (Var q) (MAP (SND o SND) caps)` by
    (qx_gen_tac `imm_var` >> disch_tac >>
     qpat_assum `!p. entry_info2 = SOME (Var p) ==> ~not_fresh_at capture p`
       (drule_then assume_tac) >>
     CCONTR_TAC >>
     qpat_x_assum `~~MEM (Var imm_var) _`
       (qx_choose_then `cap_index` strip_assume_tac o
        REWRITE_RULE [listTheory.MEM_EL, listTheory.LENGTH_MAP] o SIMP_RULE bool_ss []) >>
     qpat_x_assum `Var imm_var = EL cap_index _` mp_tac >>
     qpat_assum `cap_index < LENGTH caps`
       (simp o cons NoAsms o cons listTheory.EL_MAP o single) >>
     disch_tac >>
     `cap_index < LENGTH params` by decide_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
             not_fresh_at capture p /\ _` (qspec_then `cap_index` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `Var imm_var = SND (SND (EL cap_index caps))`
       (simp o cons NoAsms o single o SYM) >>
     qpat_assum `~not_fresh_at capture imm_var`
       (simp o cons NoAsms o single)) >>
  `local_ptrs_reserved body_ce materialized` by
    (qpat_assum `local_ptrs_reserved entry_info0 materialized`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     simp[NoAsms, Abbr `body_ce`,loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> disch_tac >>
     conj_tac
     >- (qpat_assum `!p. body_ce.ce_imm_alloca = SOME (Var p) ==> _`
           (irule o SRULE [NoAsms, Abbr `body_ce`]) >>
         first_assum ACCEPT_TAC) >>
     irule intcall_callee_materialize_avoids >>
     goal_assum (drule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     metis_tac[]) >>
  `local_ptrs_reserved body_ce prologue /\ ~block_is_terminated prologue /\
   ret_pc_ok body_ce prologue at_pro /\ return_buf_frame ret_dest body_ce prologue at_pro /\
   (!q sz. body_ce.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
   (!q sz. body_ce.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
   (!H. valid_horizon cx st0 H es1.storage_trace ==> stmt_state_rel H ctx callee body_ce cx es1 at_pro) /\
   (!H. valid_horizon cx st0 H es1.storage_trace ==>
      ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gpro tnpro at_pro)` by
    (irule intcall_callee_prologue_body_resources >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     (TRY (qexistsl_tac [`Gmat`,`at_mat`,`materialized`,`tnmat`])) >>
     (TRY (qexistsl_tac [`at_reserve`,`ce1`,`reserved`])) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[NoAsms, Abbr `body_ce`] >> first_assum ACCEPT_TAC)) >>
  `nr' = nr /\ key = global_nonreentrant_slot /\ trans = T /\ view = (mut = View)` by
    (qpat_assum `set_internal_package_target _ (package_internal_fn _ _ _ cx.in_deploy _ _) = _`
       mp_tac >>
     simp[NoAsms, package_internal_fn_def, set_internal_package_target_def]) >>
  `nr ==> view = is_view_mut mut /\ cx.nonreentrant_slot = SOME key` by
    (disch_tac >> conj_tac
     >- (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
           qpat_assum `MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops`
             (fn decl => mp_tac (MATCH_MP contract_inv_singleton_function_mutability
               (CONJ (MATCH_MP bodySimTheory.body_inv_contract inv) decl)))) >>
         simp[vyperTypeContractTheory.function_mutability_ok_def]) >>
     qpat_assum `key = global_nonreentrant_slot` (rewrite_tac o single) >>
     metis_tac[bodySimTheory.body_inv_nonreentrant_slot]) >>
  Cases_on `nr /\ ~storage_trace_domain cx st0 (es1.storage_trace ++ [StorageLock key])`
  >- (qpat_assum `nr /\ ~_` strip_assume_tac >>
      conj_tac >-
        (qhdtm_assum `intcall_callee_selected_callbacks`
           (qspec_then `key` mp_tac o cj 2 o REWRITE_RULE [intcall_callee_selected_callbacks_def]) >>
         (impl_tac >-
            (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
             qpat_assum `nr ==> _ /\ cx.nonreentrant_slot = SOME key`
               (drule_then (ACCEPT_TAC o cj 2)))) >>
         simp[NoAsms]) >>
      qpat_assum `nr` (rewrite_tac o single) >> irule intcall_callee_bad_lock >>
      (metis_tac[])) >>
  `nr ==> compile_nonreentrant_lock key T view prologue = ((),a) /\
         key < dimword (:256) /\
         valid_horizon cx st0 (storage_trace_horizon (es1.storage_trace ++ [StorageLock key]))
           (es1.storage_trace ++ [StorageLock key])` by
    (strip_tac >> conj_tac
     >- (qpat_assum `lock prologue = ((),a)` mp_tac >> simp[Abbr `lock`] >> gvs[]) >>
     conj_tac >- simp[contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
     qpat_assum `~(nr /\ ~storage_trace_domain cx st0 _)` mp_tac >>
     simp[storage_trace_domain_def]) >>
  `nr ==> key_taint tnpro.t_trans (n2w key) = {} /\
          lookup_storage (n2w key) (es1.tStorage cx.txn.target) = tload (n2w key) at_pro /\
          at_pro.vs_call_ctx.cc_static = cx.txn.is_static` by
    (strip_tac >>
     qabbrev_tac `K0 = storage_trace_horizon (es1.storage_trace ++ [StorageLock key])` >>
     `valid_horizon cx st0 K0 (es1.storage_trace ++ [StorageLock key])` by simp[Abbr `K0`] >>
     drule_then strip_assume_tac intcall_callee_lock_horizon >>
     `state_rel K0 callee ce cx (es1 with scopes := []) t` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     `ghost_inv_at (DF K0) lo ret_dest entry_info0 cx es1 Gpro tnpro at_pro` by
       (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ at_pro`
          irule >> first_assum ACCEPT_TAC) >>
     `key < dimword (:256)` by simp[] >>
     conj_tac
     >- (qpat_assum `ghost_inv_at (DF K0) _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
         irule intcall_callee_lock_clean >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`DF K0`,`K0`,`cenv`,`cx`,`lo`,`at_pro`] >> simp[]) >>
     irule intcall_callee_lock_read >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`K0`,`ce`,`callee`,`t`] >> simp[Abbr `at_mat`]) >>
  `fn_has_code prologue a callee` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`final`,`entry`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_pro` by
    (mp_tac (Q.INST [`s` |-> `at_pro`, `func` |-> `callee`]
       intcall_callee_alloca_room) >> simp[]) >>
  `nr ==> ?Gl tnl.
     (!D. inst_seq_ptr D lo ctx callee (MAP (op_prov G) arg_ops)
        Gpro tnpro (emitted_insts prologue a) at_pro Gl tnl) /\
     (!u. run_inst_seq (emitted_insts prologue a) at_pro = OK u ==>
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
         (at_pro,Gpro,tnpro) [] (OK (u with vs_inst_idx := LENGTH a.cs_current_insts),Gl,tnl)) /\
     (!ab u. run_inst_seq (emitted_insts prologue a) at_pro = Abort ab u ==>
       ?j. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
         (at_pro,Gpro,tnpro) [] (Abort ab (u with vs_inst_idx := j),Gl,tnl))` by
    (disch_tac >>
     `compile_nonreentrant_lock key T view prologue = ((),a)` by simp[] >>
     drule_then strip_assume_tac intcall_callee_lock_shape >>
     irule intcall_callee_lock_path >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE (qexistsl_tac [`key`,`view`] >> simp[]))) >>
  `intcall_callee_prologue_route callee ce params has_rb ctor ilen rt
      (entry,prologue) (entered,at_pro)` by
    (simp[NoAsms,intcall_callee_prologue_route_def] >>
     qexistsl_tac [`ce1`,`caps`,`entry_info1`,`entry_info2`,`entry_info0`,
                   `capture`,`reserved`,`materialized`,`at_capture`,`at_reserve`,`at_mat`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     simp[NoAsms, Abbr `at_mat`]) >>
  `(if nr then compile_nonreentrant_lock global_nonreentrant_slot T (is_view_mut mut)
     else comp_return ()) prologue = ((),a)` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> view = is_view_mut mut /\ _`
           (strip_assume_tac o SIMP_RULE bool_ss []) >>
         qpat_assum `T ==> compile_nonreentrant_lock _ _ _ _ = _ /\ _`
           (mp_tac o cj 1 o SIMP_RULE bool_ss []) >>
         qpat_assum `key = global_nonreentrant_slot` (pure_rewrite_tac o single) >>
         qpat_assum `view = is_view_mut mut` (pure_rewrite_tac o single) >>
         simp[NoAsms]) >>
     qpat_assum `lock prologue = ((),a)` mp_tac >>
     qpat_assum `nr' = F` (fn eq => simp[NoAsms, Abbr `lock`, eq])) >>
  `~nr ==> a = prologue` by
    (disch_tac >> qpat_x_assum `lock prologue = ((),a)` mp_tac >>
     qpat_assum `nr' = nr` (fn hyp =>
       qpat_assum `~nr` (fn not_nr =>
         simp[NoAsms, Abbr `lock`, hyp, not_nr, comp_return_def])) >>
     disch_then (ACCEPT_TAC o SYM)) >>
  `nr ==> (?e u. lock_if_nr cx T view es1 = (INL (),e) /\
                   run_inst_seq (emitted_insts prologue a) at_pro = OK u) \/
           (?e u. lock_if_nr cx T view es1 = (INR (Error (RuntimeError "nonreentrant lock")),e) /\
                   run_inst_seq (emitted_insts prologue a) at_pro = Abort Revert_abort u) \/
           (?e u. lock_if_nr cx T view es1 = (INR (Error (RuntimeError "write in static context")),e) /\
                   run_inst_seq (emitted_insts prologue a) at_pro = Abort ExHalt_abort u)` by
    (disch_tac >>
     `compile_nonreentrant_lock key T view prologue = ((),a)` by simp[] >>
     irule intcall_callee_lock_run >> conj_tac >- simp[] >>
     qexists_tac `key` >> simp[]) >>
  reverse (Cases_on `?locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked)`)
  >- (`nr` by
        (spose_not_then assume_tac >> qpat_x_assum `~(?locked. _)` mp_tac >>
         simp[lock_if_nr_def, return_def]) >>
      `view = is_view_mut mut` by simp[] >>
      qpat_assum `nr ==> ?Gl tnl. _` drule >> strip_tac >>
      `?msg ee ab u. lock_if_nr cx nr (is_view_mut mut) es1 =
                       (INR (Error (RuntimeError msg)),ee) /\
                     run_inst_seq (emitted_insts prologue a) at_pro = Abort ab u` by
        (qpat_assum `nr ==> (?e u. _) \/ _` drule >>
         qpat_assum `nr` (pure_rewrite_tac o single) >>
         qpat_assum `view = is_view_mut mut` (pure_rewrite_tac o single) >>
         strip_tac
         >- (qpat_assum `~(?l. lock_if_nr cx nr _ es1 = (INL (),l))` mp_tac >>
             qpat_assum `nr` (pure_rewrite_tac o single) >>
             qpat_assum `lock_if_nr cx T _ es1 = (INL (),_)` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
      qpat_assum `!ab u. run_inst_seq _ at_pro = Abort ab u ==> ?j. _` drule >>
      disch_then (qx_choose_then `j` assume_tac) >>
      `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
          MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
          [] (Abort ab (u with vs_inst_idx := j),Gl,tnl)` by
        (gen_tac >> irule gas_origin_ptr_path_trans >>
         qexistsl_tac [`Gpro`,`at_pro`,`tnpro`] >>
         conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      conj_tac >-
        (qhdtm_assum `intcall_callee_selected_callbacks`
           (irule o cj 3 o REWRITE_RULE [intcall_callee_selected_callbacks_def]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (qexistsl_tac [`ee`,`msg`] >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`Gl`,`Gpro`,`a`,`ab`,`at_pro`,`ce`,`ctor`,`entry`,`has_rb`,
                       `ilen`,`j`,`params`,`prologue`,`rt`,`tnl`,`tnpro`,`u`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_assum `(if nr then compile_nonreentrant_lock _ _ _ else _) prologue = ((),a)`
           mp_tac >> qpat_assum `nr` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
      irule intcall_callee_lock_abort >> conj_tac
      >- (qexistsl_tac [`Gl`,`ab`,`tnl`,`u with vs_inst_idx := j`] >>
          gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`ee`,`msg`] >> first_assum ACCEPT_TAC) >>
  pop_assum strip_assume_tac >>
  `~nr ==> locked = es1` by
    (strip_tac >> qpat_x_assum `lock_if_nr _ _ _ es1 = (INL (),locked)` mp_tac >>
     simp[lock_if_nr_def, return_def]) >>
  `nr ==> locked.storage_trace = es1.storage_trace ++ [StorageLock key]` by
    (strip_tac >>
     `cx.nonreentrant_slot = SOME key` by simp[] >>
     drule intcall_callee_lock_trace >>
     disch_then (qspecl_then [`is_view_mut mut`,`es1`] mp_tac) >>
     qpat_assum `lock_if_nr _ _ _ es1 = (INL (),locked)` mp_tac >>
     qpat_assum `nr` (pure_rewrite_tac o single) >>
     disch_then (rewrite_tac o single) >> simp[NoAsms]) >>
  `nr ==> acquire_nonreentrant_lock cx.txn.target key view es1 = (INL (),locked) /\
          (~view ==> ~cx.txn.is_static) /\ tload (n2w key) at_pro <> 1w` by
    (strip_tac >>
     `!c k v s s'. c.nonreentrant_slot = SOME k /\
         lock_if_nr c T v s = (INL (),s') ==>
         acquire_nonreentrant_lock c.txn.target k v s = (INL (),s') /\
         (~v ==> ~c.txn.is_static) /\
         lookup_storage (n2w k) (s.tStorage c.txn.target) <> 1w` by
       (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
        Cases_on `v` >> Cases_on `c.txn.is_static` >>
        Cases_on `lookup_storage (n2w k) (s.tStorage c.txn.target) = 1w` >>
        csimp[lock_if_nr_def, acquire_nonreentrant_lock_execution,
              ignore_bind_def, bind_def, check_not_static_def, check_def,
              assert_def, return_def, raise_def]) >>
     `cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut /\
      lookup_storage (n2w key) (es1.tStorage cx.txn.target) = tload (n2w key) at_pro` by simp[] >>
     `lock_if_nr cx T (is_view_mut mut) es1 = (INL (),locked)` by
       (qpat_assum `lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked)` mp_tac >>
        qpat_assum `nr` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
     qpat_x_assum `!c k v s s'. _` (qspecl_then [`cx`,`key`,`is_view_mut mut`,`es1`,`locked`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[]) >>
  `nr ==> !H. valid_horizon cx st0 H locked.storage_trace ==>
          ?u. run_inst_seq (emitted_insts prologue a) at_pro = OK u /\
              state_rel H callee body_ce cx locked u` by
    (disch_tac >> gen_tac >> disch_tac >>
     `valid_horizon cx st0 H (es1.storage_trace ++ [StorageLock key])` by
       (qpat_assum `nr ==> locked.storage_trace = _` drule >>
        disch_then (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
     drule_then strip_assume_tac intcall_callee_lock_horizon >>
     `state_rel H callee body_ce cx es1 at_pro` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     `?v u. acquire_nonreentrant_lock cx.txn.target key view es1 = (INL (),v) /\
            run_inst_seq (emitted_insts prologue a) at_pro = OK u /\
            state_rel H callee body_ce cx v u` by
       (irule compile_nonreentrant_lock_source_correct >> simp[]) >>
     `v = locked` by
       (qpat_assum `nr ==> acquire_nonreentrant_lock _ _ _ es1 = _ /\ _` drule >>
        strip_tac >> qpat_assum `acquire_nonreentrant_lock _ _ _ es1 = (INL (),v)` mp_tac >>
        qpat_assum `acquire_nonreentrant_lock _ _ _ es1 = (INL (),locked)`
          (simp o cons NoAsms o single) >> metis_tac[]) >>
     qexists_tac `u` >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `v = locked` (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `?u Gl tnl.
     run_inst_seq (emitted_insts prologue a) at_pro = OK u /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
        MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) []
       (OK (u with vs_inst_idx := LENGTH a.cs_current_insts),Gl,tnl)) /\
     (!D. inst_seq_ptr D lo ctx callee (MAP (op_prov G) arg_ops)
        Gpro tnpro (emitted_insts prologue a) at_pro Gl tnl) /\
     (!H. valid_horizon cx st0 H locked.storage_trace ==>
           state_rel H callee body_ce cx locked u)` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> compile_nonreentrant_lock _ _ _ _ = _ /\ _`
           (strip_assume_tac o SIMP_RULE bool_ss []) >>
         `valid_horizon cx st0 (storage_trace_horizon locked.storage_trace) locked.storage_trace` by
           (qpat_assum `T ==> locked.storage_trace = _`
             (pure_rewrite_tac o single o SIMP_RULE bool_ss []) >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `T ==> !H. valid_horizon cx st0 H locked.storage_trace ==> ?u. _`
           (mp_tac o SIMP_RULE bool_ss []) >>
         disch_then (qspec_then `storage_trace_horizon locked.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         qpat_assum `T ==> ?Gl tnl. _` (strip_assume_tac o SIMP_RULE bool_ss []) >>
         qexistsl_tac [`u`,`Gl`,`tnl`] >> conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (qx_gen_tac `Dlock` >> irule gas_origin_ptr_path_trans >>
             qexistsl_tac [`Gpro`,`at_pro`,`tnpro`] >> conj_tac
             >- (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_pro,Gpro,tnpro)`
                   (qspec_then `Dlock` ACCEPT_TAC)) >>
             qpat_assum `!u. run_inst_seq _ at_pro = OK u ==> !D explicit. _` drule >>
             disch_then (qspecl_then [`Dlock`,`gas_explicit_sites ctx shadow_ctx`] ACCEPT_TAC)) >>
         conj_tac >- first_assum MATCH_ACCEPT_TAC >>
         gen_tac >> disch_tac >>
         qpat_assum `T ==> !H. valid_horizon cx st0 H locked.storage_trace ==> ?u. _`
           (mp_tac o SIMP_RULE bool_ss []) >>
         disch_then (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `run_inst_seq _ at_pro = OK u` (simp o cons NoAsms o single)) >>
     `a = prologue /\ locked = es1` by simp[] >>
     qexistsl_tac [`at_pro`,`Gpro`,`tnpro`] >>
     qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
     qpat_assum `locked = es1` (pure_rewrite_tac o single) >>
     simp[NoAsms, emitted_insts_def, fragGasSeqPtrTheory.inst_seq_ptr_def,
          exprLoweringPropsTheory.run_inst_seq_def] >>
     `at_pro with vs_inst_idx := LENGTH prologue.cs_current_insts = at_pro` by
       simp[venom_state_component_equality] >>
     pop_assum (rewrite_tac o single) >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qabbrev_tac `at_body = u with vs_inst_idx := LENGTH a.cs_current_insts` >>
  qpat_assum `lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked)`
    (strip_assume_tac o MATCH_MP intcall_callee_lock_fields) >>
  `!H. valid_horizon cx st0 H locked.storage_trace ==>
      valid_horizon cx st0 H es1.storage_trace` by
    (gen_tac >> Cases_on `nr`
     >- (qpat_assum `T ==> locked.storage_trace = _`
           (pure_rewrite_tac o single o SIMP_RULE bool_ss []) >>
         metis_tac[intcall_callee_lock_horizon]) >>
     simp[]) >>
  qabbrev_tac `Hlock = storage_trace_horizon locked.storage_trace` >>
  `valid_horizon cx st0 Hlock locked.storage_trace` by
    (simp[NoAsms, Abbr `Hlock`] >> Cases_on `nr`
     >- (qpat_assum `T ==> compile_nonreentrant_lock _ _ _ _ = _ /\ _`
           (strip_assume_tac o SRULE []) >>
         qpat_assum `T ==> locked.storage_trace = _`
           (pure_rewrite_tac o single o SRULE []) >> first_assum ACCEPT_TAC) >>
     simp[GSYM storage_trace_domain_def]) >>
  `fresh_vars_wrt a at_body /\ local_ptrs_reserved body_ce a /\
   ret_pc_ok body_ce a at_body /\ return_buf_frame ret_dest body_ce a at_body /\
   (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
   ~block_is_terminated a /\ ~at_body.vs_halted /\
   at_body.vs_current_bb = a.cs_current_bb /\
   at_body.vs_inst_idx = LENGTH a.cs_current_insts /\
   at_body.vs_allocas = at_pro.vs_allocas /\
   (!x. not_fresh_at prologue x ==> lookup_var x at_body = lookup_var x at_pro) /\
   (!H. valid_horizon cx st0 H locked.storage_trace ==>
     stmt_state_rel H ctx callee body_ce cx locked at_body)` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> compile_nonreentrant_lock _ _ _ _ = _ /\ _`
           (strip_assume_tac o SIMP_RULE bool_ss []) >>
         drule_all intcall_callee_lock_concrete_fields >>
         rewrite_tac[LET_THM] >> BETA_TAC >>
         qpat_assum `Abbrev (at_body = _)`
           (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         strip_tac >>
         `!H. valid_horizon cx st0 H locked.storage_trace ==>
           stmt_state_rel H ctx callee body_ce cx locked at_body /\
           fresh_vars_wrt a at_body /\ local_ptrs_reserved body_ce a /\
           ret_pc_ok body_ce a at_body /\
           (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
                not_fresh_at a x) /\
           return_buf_frame ret_dest body_ce a at_body /\
           ~block_is_terminated a /\ ~at_body.vs_halted /\
           at_body.vs_current_bb = a.cs_current_bb /\
           at_body.vs_inst_idx = LENGTH a.cs_current_insts` by
           (gen_tac >> disch_tac >>
            `valid_horizon cx st0 H es1.storage_trace` by
              (first_assum irule >> first_assum ACCEPT_TAC) >>
            `stmt_state_rel H ctx callee body_ce cx es1 at_pro /\
             state_rel H callee body_ce cx locked u` by
              (conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
            mp_tac (Q.INST [`key` |-> `key`, `view` |-> `view`,
              `pro` |-> `prologue`, `a` |-> `a`, `s` |-> `at_pro`, `u` |-> `u`,
              `H` |-> `H`, `ctx` |-> `ctx`, `fn` |-> `callee`,
              `ce` |-> `body_ce`, `cx` |-> `cx`, `es` |-> `es1`,
              `locked` |-> `locked`, `dret` |-> `ret_dest`]
              (INST_TYPE [Type.alpha |-> ``:256``]
                intcall_callee_lock_landing_concrete)) >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
            rewrite_tac[LET_THM] >> BETA_TAC >>
            qpat_assum `Abbrev (at_body = _)`
              (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            simp[NoAsms]) >>
         qpat_assum `!H. valid_horizon cx st0 H locked.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
           (qspec_then `Hlock` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         strip_tac >> simp[] >> rpt strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H locked.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
           drule >> simp[])
     >- (`a = prologue /\ locked = es1` by simp[] >>
         `u = at_pro` by
           (qpat_assum `run_inst_seq (emitted_insts prologue a) at_pro = OK u` mp_tac >>
            qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
            simp[NoAsms, exprLoweringPropsTheory.emitted_insts_refl,
                 exprLoweringPropsTheory.run_inst_seq_nil]) >>
         `at_body = at_pro` by
           simp[Abbr `at_body`, venom_state_component_equality] >>
         qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
         qpat_assum `locked = es1` (pure_rewrite_tac o single) >>
         qpat_assum `at_body = at_pro` (pure_rewrite_tac o single) >>
         rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >> simp[])) >>
  `return_buf_sep ret_dest body_ce locked at_body` by
    (mp_tac (Q.INST [`d` |-> `ret_dest`, `cenv` |-> `body_ce`,
               `es` |-> `es1`, `s` |-> `at_pro`, `cenv'` |-> `body_ce`,
               `ee` |-> `locked`, `t` |-> `at_body`]
            bodyFullSharedTheory.return_buf_sep_transport) >>
     impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
        >- (simp[ptrDisciplineTheory.allocas_from_def] >> rpt strip_tac >>
            qpat_assum `return_buf_sep ret_dest body_ce es1 at_pro` mp_tac >>
            qpat_assum `ret_dest = SOME _` (pure_rewrite_tac o single) >>
            simp[NoAsms, bodySimFullTheory.return_buf_sep_def,
                 ptrDisciplineTheory.allocas_from_def] >> strip_tac >>
            qpat_assum `!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) ==> _`
              (qspecl_then [`aid`,`b'`,`sz`] mp_tac) >>
            simp[]) >>
        map_every qx_gen_tac [`region_name`,`region_base`,`region_sz`] >>
        qpat_assum `locked.scopes = es1.scopes` (pure_rewrite_tac o single) >>
        mp_tac (Q.INST [`cenv` |-> `body_ce`, `scopes` |-> `es1.scopes`,
                         `s` |-> `at_pro`, `t` |-> `at_body`,
                         `name:string` |-> `region_name`, `lo:num` |-> `region_base`, `sz:num` |-> `region_sz`]
                loweringStateRelDefsTheory.local_region_lookup_cong) >>
        impl_tac >-
          (map_every qx_gen_tac [`local_name'`,`entry_value`,`ptr_var`,`sz`] >>
           strip_tac >>
           qpat_assum `!x. not_fresh_at prologue x ==> lookup_var x at_body = _` irule >>
           qpat_assum `local_ptrs_reserved body_ce prologue`
             (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
           strip_tac >>
           qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP body_ce.ce_vars n1 = _ ==> _`
             (qspecl_then [`local_name'`,`local_name'`,`ptr_var`,`sz`,`sz`] mp_tac) >>
           impl_tac >- first_assum ACCEPT_TAC >>
           simp[NoAsms]) >>
        simp[NoAsms]) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H locked.storage_trace ==>
     ghost_inv_at (DF H) lo ret_dest body_ce cx locked Gl tnl at_body` by
    (gen_tac >> disch_tac >>
     Cases_on `nr`
     >- (qpat_assum `T ==> compile_nonreentrant_lock _ _ _ _ = _ /\ _`
           (strip_assume_tac o SIMP_RULE bool_ss []) >>
         `valid_horizon cx st0 H (es1.storage_trace ++ [StorageLock key])` by
           (qpat_assum `T ==> locked.storage_trace = _`
              (pure_rewrite_tac o single o SYM o SIMP_RULE bool_ss []) >>
            first_assum ACCEPT_TAC) >>
         drule_then strip_assume_tac intcall_callee_lock_horizon >>
         `ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gpro tnpro at_pro` by
           (first_assum irule >> first_assum ACCEPT_TAC) >>
         drule_then assume_tac transientLockPropsTheory.compile_nonreentrant_lock_transient_code >>
         `inst_seq_ptr (DF H) lo ctx callee (MAP (op_prov G) arg_ops)
           Gpro tnpro (transient_lock_code key view prologue) at_pro Gl tnl` by
           (qpat_assum `emitted_insts prologue a = transient_lock_code _ _ _`
              (pure_rewrite_tac o single o SYM) >>
            first_assum MATCH_ACCEPT_TAC) >>
         `tload (n2w key) at_pro <> 1w /\ (~view ==> ~at_pro.vs_call_ctx.cc_static)` by
           (qpat_assum `T ==> acquire_nonreentrant_lock _ _ _ _ = _ /\ _`
              (strip_assume_tac o SIMP_RULE bool_ss []) >>
            conj_tac >- first_assum ACCEPT_TAC >> disch_tac >>
            qpat_assum `T ==> key_taint tnpro.t_trans (n2w key) = {} /\ _ /\
                         (at_pro.vs_call_ctx.cc_static <=> cx.txn.is_static)`
              (pure_rewrite_tac o single o cj 3 o SIMP_RULE bool_ss []) >>
            qpat_assum `~view ==> ~cx.txn.is_static` irule >> first_assum ACCEPT_TAC) >>
         drule_all intcall_callee_lock_success_ghost_fields >> strip_tac >>
         `at_pro.vs_call_ctx.cc_address = cx.txn.target` by
           (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> state_rel H callee body_ce cx es1 at_pro`
              (qspec_then `H` mp_tac) >>
            impl_tac >- first_assum ACCEPT_TAC >>
            disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
            simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
         `body_ce.ce_is_ctor = cenv.ce_is_ctor` by
           (qpat_assum `ce.ce_is_ctor <=> body_ce.ce_is_ctor`
              (pure_rewrite_tac o single o SYM) >>
            qpat_assum `set_internal_package_target rpolicy.rpol_target (package_internal_fn tops T _ cenv.ce_is_ctor _ _) = _`
              (mp_tac o cj 1 o MATCH_MP intcall_callee_package_metadata) >>
            simp[NoAsms]) >>
         `dead_lo_ok H (DF H) lo body_ce cx` by
           (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H` mp_tac) >>
            simp[NoAsms, bodyPtrDefsTheory.dead_lo_ok_def,
                 sourceUnitExecutionTheory.cx_dead_def] >>
            qpat_assum `body_ce.ce_is_ctor <=> cenv.ce_is_ctor`
              (pure_rewrite_tac o single) >> simp[NoAsms]) >>
         simp[NoAsms, Abbr `at_body`] >>
         irule intcall_callee_lock_landing_ghost >>
         qexistsl_tac [`Gpro`,`H`,`a`,`es1`,`key`,`at_pro`,`prologue`,`tnpro`,`view`] >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))
     >- (`a = prologue /\ locked = es1` by simp[] >>
         `u = at_pro` by
           (qpat_assum `run_inst_seq (emitted_insts prologue a) at_pro = OK u` mp_tac >>
            qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
            simp[NoAsms, exprLoweringPropsTheory.emitted_insts_refl,
                 exprLoweringPropsTheory.run_inst_seq_nil]) >>
         `at_body = at_pro` by
           (simp[NoAsms, Abbr `at_body`] >>
            qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
            qpat_assum `u = at_pro` (pure_rewrite_tac o single) >>
            qpat_assum `at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts`
              (pure_rewrite_tac o single o SYM) >>
            simp[NoAsms, venom_state_component_equality]) >>
         `Gl = Gpro /\ tnl = tnpro` by
           (qpat_assum `!D. inst_seq_ptr D _ _ _ _ Gpro tnpro _ at_pro Gl tnl`
              (qspec_then `DF H` mp_tac) >>
            qpat_assum `a = prologue` (pure_rewrite_tac o single) >>
            simp[NoAsms, exprLoweringPropsTheory.emitted_insts_refl,
                 fragGasSeqPtrTheory.inst_seq_ptr_def]) >>
         qpat_assum `locked = es1` (pure_rewrite_tac o single) >>
         qpat_assum `at_body = at_pro` (pure_rewrite_tac o single) >>
         qpat_assum `Gl = Gpro` (pure_rewrite_tac o single) >>
         qpat_assum `tnl = tnpro` (pure_rewrite_tac o single) >>
         qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==>
              ghost_inv_at (DF H) lo ret_dest body_ce cx es1 Gpro tnpro at_pro` irule >>
         qpat_assum `locked = es1` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC)) >>
  `MEM callee ctx.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
      MAP (op_prov G) arg_ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_body,Gl,tnl)` by
    simp[Abbr `at_body`] >>
  `alloca_history callee at_body` by
    (`alloca_history callee entered` by simp[allocaHistoryTheory.alloca_history_empty] >>
     `alloca_inv entered` by simp[venomMemProofsTheory.alloca_inv_empty_proof] >>
     irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_body,Gl,tnl)`
       (qspec_then `DF Hlock` (irule_at Any)) >>
     simp[]) >>
  `!i. active_inst callee i entered ==> frag_reachable ctx func s0 callee i entered` by
    (qx_gen_tac `i` >> disch_tac >>
     `active_inst func inst t` by
       (rewrite_tac[active_inst_def] >> qexists_tac `bb` >>
        qpat_assum `lookup_block t.vs_current_bb func.fn_blocks = SOME bb`
          (fn th => assume_tac (MATCH_MP lookup_block_MEM th) >>
                    assume_tac (MATCH_MP lookup_block_label th)) >>
        simp[] >>
        qpat_assum `get_instruction bb t.vs_inst_idx = SOME inst` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        Cases_on `t.vs_inst_idx < LENGTH bb.bb_instructions` >>
        simp[get_instruction_def]) >>
     `enters_block callee setup entered` by
       (rewrite_tac[enters_block_def] >> qexistsl_tac [`first`,`phi_state`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qspecl_then [`ctx`,`func`,`s0`,`func`,`inst`,`t`,`lbl`,`arg_ops`,
                   `callee`,`argv`,`setup`,`entered`,`i`]
       mp_tac (cj 4 frag_reachable_rules) >>
     impl_tac >-
       (rpt conj_tac >-
          (qpat_assum `!i. active_inst func i t ==> frag_reachable ctx func s0 func i t`
             irule >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!fn inst s. frag_reachable ctx callee entered fn inst s ==> dalloca_fmp_headroom inst s` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s` irule >>
     qexists_tac `fn` >>
     qpat_assum `frag_reachable ctx callee entered fn _ _`
       (fn reach => qspecl_then [`func`,`s0`] irule (MATCH_MP frag_reachable_trans reach)) >>
     first_assum ACCEPT_TAC) >>
  `!fn inst s. frag_reachable ctx callee at_body fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_body,Gl,tnl)`
       (qspec_then `DF Hlock` assume_tac) >>
     `!bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `gas_origin_ptr_path _ _ [] (OK at_body,Gl,tnl)` (fn path =>
       qpat_assum `!bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
         (fn phi =>
           qpat_assum `!fn inst s. frag_reachable ctx callee entered fn inst s ==> dalloca_fmp_headroom inst s`
             (fn nowrap => ACCEPT_TAC (MATCH_MP
               bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
               (LIST_CONJ [path,phi,nowrap])))))) >>
  qabbrev_tac `pushed = cx with stk updated_by CONS (NONE,name)` >>
  `!H. valid_horizon pushed st0 H locked.storage_trace ==>
     stmt_state_rel H ctx callee body_ce pushed locked at_body /\
     storage_well_formed_on pushed locked (FST H) /\
     ghost_inv_at (DF H) lo ret_dest body_ce pushed locked Gl tnl at_body` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H locked.storage_trace` by
       (qpat_assum `valid_horizon pushed _ _ _` mp_tac >>
        simp[NoAsms, Abbr `pushed`, valid_horizon_def,
             vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
             vyperFiniteStoragePreservationTheory.storage_observations_ok_stk]) >>
     `valid_horizon cx st0 H es1.storage_trace` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     `stmt_state_rel H ctx callee body_ce cx locked at_body /\
      ghost_inv_at (DF H) lo ret_dest body_ce cx locked Gl tnl at_body` by
       (conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
     `storage_well_formed_on cx es1 (FST H)` by
       (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==>
            intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv
              name es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr)
              prev penv rtv es1 t G tn`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        simp[NoAsms, bodyFullIntCallDefsTheory.intcall_entry_full_def]) >>
     rpt conj_tac
     >- (`stmt_state_rel H ctx callee body_ce pushed locked at_body <=>
           stmt_state_rel H ctx callee body_ce cx locked at_body` by
           simp[NoAsms, Abbr `pushed`, stmt_state_rel_def,
                loweringStateRelDefsTheory.state_rel_def, immutable_alloca_sep_def,
                loweringStateRelDefsTheory.storage_vars_rel_def,
                loweringStateRelDefsTheory.transient_vars_rel_def,
                loweringStateRelDefsTheory.accounts_rel_def, lookup_var_slot_from_layout_def,
                immutable_decl_sep_def, get_module_code_stk_irrelevant, get_tenv_stk_irrelevant] >>
         qpat_assum `stmt_state_rel H _ _ _ pushed _ _ <=> _`
           (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)
     >- (simp[Abbr `pushed`,vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk] >>
         mp_tac (Q.INST [`cx` |-> `cx`,`H` |-> `H`,`st` |-> `es1`,
                         `u` |-> `locked`,`nr` |-> `nr`,`view` |-> `is_view_mut mut`,
                         `res` |-> `INL ()`]
                  vyperExternalEntryStorageFrameTheory.lock_if_nr_preserves_storage_well_formed_on) >>
         qpat_assum `valid_horizon cx st0 H locked.storage_trace`
           (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[NoAsms]) >>
     `ghost_inv_at (DF H) lo ret_dest body_ce pushed locked Gl tnl at_body <=>
      ghost_inv_at (DF H) lo ret_dest body_ce cx locked Gl tnl at_body` by
       simp[NoAsms, Abbr `pushed`, bodyPtrDefsTheory.ghost_inv_at_def,
            cx_tops_def, get_module_code_stk_irrelevant] >>
     qpat_assum `ghost_inv_at (DF H) _ _ _ pushed _ _ _ _ <=> _`
       (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `get_module_code cx NONE = SOME tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP body_inv_main_code)) >>
  `stmt_state_rel (storage_trace_horizon es1.storage_trace)
       ctx func cenv cx (es1 with scopes := prev) t /\
    expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
    evaluate_type (get_tenv cx) ret = SOME rtv` by
    (qhdtm_assum `intcall_entry_full`
       (fn th => map_every STRIP_ASSUME_TAC
          (List.take (CONJUNCTS (REWRITE_RULE [intcall_entry_full_def] th), 8))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ce = (build_compile_env tops Internal mut name args ret ss T) with
      <|ce_is_ctor := cx.in_deploy; ce_raw_return := rr;
        ce_nonreentrant := (nr,global_nonreentrant_slot,T,mut = View);
        ce_target := rpolicy.rpol_target|> /\
    rt = (if ret = NoneT then NONE else SOME ret)` by
    (qpat_assum `set_internal_package_target rpolicy.rpol_target
         (package_internal_fn tops T _ cx.in_deploy _ _) = _`
       (strip_assume_tac o REWRITE_RULE [entryDispatchPropsTheory.build_compile_env_subst_consts_stmts] o
        MATCH_MP intcall_callee_package_metadata) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `body_ce = ce with <|ce_vars := entry_info0.ce_vars;
        ce_return_buf := entry_info0.ce_return_buf; ce_return_pc := entry_info0.ce_return_pc;
        ce_imm_alloca := entry_info2; ce_alloca_locals := T|>` by
    (qpat_assum `compile_internal_entry_prefix ce params has_rb entry =
         ((ce1,caps,entry_info1),capture)`
       (fn prefix => qpat_assum `materialize_internal_params ce1 caps reserved =
            (entry_info0,materialized)`
          (mp_tac o (fn mat => MATCH_MP
             (Q.INST [`imm` |-> `entry_info2`] intcall_callee_body_env)
             (CONJ prefix mat)))) >>
     simp[NoAsms, Abbr `body_ce`]) >>
  `body_inv tops ctx body_ce pushed` by
    (simp[NoAsms, Abbr `pushed`] >>
     mp_tac (Q.INST [`caller` |-> `cenv`,`policy` |-> `rpolicy`,`unit` |-> `unit`,
         `mut` |-> `mut`,`rr` |-> `rr`,`args` |-> `args`,`ret` |-> `ret`,`ss` |-> `ss`,
         `nrinfo` |-> `(nr,global_nonreentrant_slot,T,mut = View)`,`name` |-> `name`,
         `vars` |-> `entry_info0.ce_vars`,`rb` |-> `entry_info0.ce_return_buf`,
         `rpc` |-> `entry_info0.ce_return_pc`,`imm` |-> `entry_info2`]
       (cj 1 intcall_callee_body_metadata)) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_assum `body_ce = ce with <|ce_vars := _; ce_return_buf := _;
              ce_return_pc := _; ce_imm_alloca := _; ce_alloca_locals := _|>`
       (pure_rewrite_tac o single) >>
     qpat_assum `ce = (build_compile_env tops Internal mut name args ret ss T) with
         <|ce_is_ctor := cx.in_deploy; ce_raw_return := rr;
           ce_nonreentrant := (nr,global_nonreentrant_slot,T,mut = View);
           ce_target := rpolicy.rpol_target|>`
       (pure_rewrite_tac o single) >> simp[compile_env_component_equality]) >>
     simp[NoAsms]) >>
  `body_ce.ce_is_ctor = cenv.ce_is_ctor /\
   body_ce.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (assume_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
     qpat_assum `body_inv tops ctx body_ce pushed`
       (assume_tac o MATCH_MP bodySimTheory.body_inv_contract) >>
     `pushed.in_deploy = cx.in_deploy` by simp[Abbr `pushed`] >>
     drule_all intcall_callee_compile_tables_mods >> simp[]) >>
  `!H. dead_lo_ok H (DF H) lo body_ce pushed` by
    (gen_tac >> simp[NoAsms, Abbr `pushed`] >>
     irule intcall_callee_dead_lo >> qexists_tac `cenv` >> simp[]) >>
  `(has_rb <=> ce.ce_returns_count = 0 /\ ret <> NoneT)` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[package_internal_fn_def, set_internal_package_target_def] >>
     strip_tac >>
     qpat_x_assum `_ = ce` (SUBST1_TAC o SYM) >>
     simp[update_cenv_nonreentrant_def, build_compile_env_returns_count] >>
     metis_tac[]) >>
  `body_ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
   body_ce.ce_returns_count = returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields body_ce.ce_struct_fields n)) ret /\
   (has_rb <=> body_ce.ce_returns_count = 0 /\ ret <> NoneT) /\
   (~has_rb ==> body_ce.ce_return_buf = NONE)` by
    (qpat_assum `body_ce = ce with <|ce_vars := _; ce_return_buf := _;
             ce_return_pc := _; ce_imm_alloca := _; ce_alloca_locals := _|>`
        (once_rewrite_tac o single) >>
     qpat_assum `entry_info0.ce_return_buf = ce1.ce_return_buf` (rewrite_tac o single) >>
     qpat_assum `ce1.ce_return_buf = if has_rb then _ else NONE` (rewrite_tac o single) >>
     qpat_assum `has_rb <=> ce.ce_returns_count = 0 /\ ret <> NoneT` mp_tac >>
     qpat_assum `ce = (build_compile_env tops Internal mut name args ret ss T) with
         <|ce_is_ctor := cx.in_deploy; ce_raw_return := rr;
           ce_nonreentrant := (nr,global_nonreentrant_slot,T,mut = View);
           ce_target := rpolicy.rpol_target|>` (rewrite_tac o single) >>
     simp[NoAsms, build_compile_env_returns_count, build_compile_env_ce_struct_fields]) >>
  `body_ce.ce_return_pc = SOME (PtrVar (Var x) 0)` by
    (simp[NoAsms, Abbr `body_ce`] >>
     qpat_assum `entry_info0.ce_return_pc = ce1.ce_return_pc`
       (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `has_rb ==> lo <= w2n (HD argv) /\ 0 < type_memory_size rtv /\
                 type_memory_size rtv + 64 < dimword (:256)` by
    (disch_tac >>
     conj_tac >-
       (qpat_assum `has_rb ==> ?b bsz. op_prov _ (HD _) = _ /\ _`
          (drule_then strip_assume_tac) >> decide_tac) >>
     `ret <> NoneT` by
       (qpat_assum `has_rb <=> body_ce.ce_returns_count = 0 /\ ret <> NoneT`
          (fn buf => qpat_assum `has_rb` (ACCEPT_TAC o cj 2 o EQ_MP buf))) >>
     conj_tac >-
       (`functions_well_typed cx /\ env_context_consistent tenv cx` by
          (qpat_assum `expr_sim_inv cenv cx tenv _`
             (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def,env_consistent_def]) >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        `context_function_live cx (NONE,name)` by
          (qpat_assum `body_inv tops ctx cenv cx`
             (fn inv => qpat_assum `stmt_state_rel
                   (storage_trace_horizon es1.storage_trace) ctx func cenv cx
                   (es1 with scopes := prev) t`
                (MATCH_ACCEPT_TAC o (fn rel => MATCH_MP intcall_callee_live (CONJ inv rel))))) >>
        mp_tac (Q.INST [`env` |-> `tenv`,`src` |-> `NONE`,`tv` |-> `rtv`]
           internalReturnMemoryInputsTheory.callable_return_memory_size_pos) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[NoAsms]) >>
     irule memoryLocalRhsPropsTheory.allocation_limit_word_room >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
       (qpat_assum `body_inv tops ctx cenv cx`
          (ACCEPT_TAC o MATCH_MP intcall_callee_singleton_keys)) >>
     `fn_allocs_ok tops (subst_consts_fn (module_consts_env tops [])
       (mut,nr,rr,name,args,dflts,ret,ss))` by
       (irule intcall_callee_allocs >> simp[] >>
        qexistsl_tac [`cx.in_deploy`,`rpolicy`,`unit`] >> first_assum ACCEPT_TAC) >>
     drule_then assume_tac intcall_callee_subst_return_alloc >>
     `type_memory_bytes (build_compile_env tops Internal mut name args ret ss F) ret =
          type_memory_size rtv` by
       (`type_memory_bytes cenv ret = type_memory_size rtv` by
           (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
            qexistsl_tac [`cx`,`tenv`,`es1 with scopes := prev`] >> simp[]) >>
        `cenv.ce_struct_fields = (build_compile_env tops Internal mut name args ret ss F).ce_struct_fields` by
          (qpat_assum `body_inv tops ctx cenv cx`
             (mp_tac o MATCH_MP contract_inv_struct_fields o
              MATCH_MP bodySimTheory.body_inv_contract) >>
           simp[build_compile_env_ce_struct_fields, make_struct_fields_map_mods_singleton]) >>
        metis_tac[type_memory_bytes_struct_fields]) >>
     qpat_assum `type_memory_bytes (build_compile_env tops Internal mut name args ret ss F) ret =
          type_memory_size rtv` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `body_ce.ce_returns_count = rc' /\ (has_rb <=> rc' = 0 /\ 0 < rbs)` by
    (`has_rb ==> 0 < type_memory_bytes cenv ret` by
       (disch_tac >>
        `type_memory_bytes cenv ret = type_memory_size rtv` by
          (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
           qexistsl_tac [`cx`,`tenv`,`es1 with scopes := prev`] >> simp[]) >>
        qpat_assum `has_rb ==> _ /\ 0 < type_memory_size rtv /\ _`
          (drule_then strip_assume_tac) >> simp[]) >>
     mp_tac (Q.INST [`ret_count` |-> `rc'`] intcall_callee_return_count) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[NoAsms]) >>
  qabbrev_tac `RetQ = \H v ee (gt : (string |-> num # num) # taint) r.
    intret_q H callee body_ce pushed rtv v ee r /\
    !ir u. r = IntRet ir u ==>
      (has_rb ==> !mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
         val_in_memory rtv v (w2n (HD argv)) mem) /\
      stor_taint_ok_at (DF H) (SND gt) u /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
         imm_section_dead (cx_tops pushed) (mem_bytes_at 0 lo u.vs_memory) i)` >>
  `frame_ret_ok_full (DF,lo,ret_dest,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
    pushed RetQ body_ce ret` by
    (simp[NoAsms, Abbr `ret_dest`, Abbr `RetQ`] >>
     irule intcall_callee_frame_return >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qexists_tac `tops` >> first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qexistsl_tac [`x`,`0`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
     simp[Abbr `pushed`, get_tenv_stk_irrelevant] >>
     Cases_on `nr` >> simp[] >> Cases_on `mut = View` >> fs[]) >>
  `!K tr. valid_horizon pushed st0 K tr <=> valid_horizon cx st0 K tr` by
    simp[Abbr `pushed`, valid_horizon_def,
         vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
         vyperFiniteStoragePreservationTheory.storage_observations_ok_stk] >>
  `cx_tops pushed = cx_tops cx` by simp[Abbr `pushed`, cx_tops_def, get_module_code_stk_irrelevant] >>
  `gas_path_mem ctx callee entered 0 (OK at_body)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_body,Gl,tnl)`
       (qspec_then `DF Hlock` assume_tac) >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `at_body.vs_gas_readings = entered.vs_gas_readings` by
    (drule fragGasPathMemTheory.gas_path_mem_ok_suffix >> simp[]) >>
  `!gs. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := gs) =
     (INL (),locked with gas_obs := gs)` by
    (gen_tac >> irule externalCallSelectedTheory.lock_if_nr_with_gas_obs >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_body` by
    (qpat_assum `!H. valid_horizon cx st0 H locked.storage_trace ==>
                   stmt_state_rel H ctx callee body_ce cx locked at_body`
       (qspec_then `Hlock` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  mp_tac (Q.INST [`caller` |-> `cenv`, `ds` |-> `dflts`,
    `H` |-> `storage_trace_horizon es1.storage_trace`, `dret` |-> `ret_dest`,
    `ce2` |-> `entry_info0`, `imm` |-> `entry_info2`, `rpc` |-> `entry_info1`,
    `body_ce` |-> `body_ce`,
    `ss'` |-> `compiled_ss`, `ss_comp` |-> `compiled_ss`,
    `ds_comp` |-> `subst_consts_exprs (module_consts_env tops []) dflts`,
    `policy` |-> `rpolicy`,
    `ilen` |-> `if cx.in_deploy then
          compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
        else 0`, `ilen'` |-> `ilen`,
    `body_start` |-> `a`, `body_end` |-> `b`, `shadow_start` |-> `aS`,
    `shadow_end` |-> `bS`, `env_end` |-> `body_out`,
    `Gbody` |-> `Gl`, `tnbody` |-> `tnl`, `RetQ` |-> `RetQ`,
    `PG` |-> `MAP (op_prov G) arg_ops`]
    intcall_callee_locked_body_outcome) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qpat_assum `Abbrev (pushed = _)`
            (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          qpat_assum `subst_consts_stmts _ _ = compiled_ss`
            (pure_rewrite_tac o single o SYM) >>
          first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (REFL_TAC >> NO_TAC) >>
     TRY (qpat_assum `subst_consts_stmts _ _ = compiled_ss` (ACCEPT_TAC o SYM) >> NO_TAC) >>
     TRY (qpat_assum `subst_consts_stmts _ _ = compiled_ss` (fn body =>
            qpat_assum `set_internal_package_target _
              (package_internal_fn _ _ _ cx.in_deploy _ _) = _`
              (ACCEPT_TAC o PURE_REWRITE_RULE [body])) >> NO_TAC) >>
     qpat_assum `Abbrev (body_ce = _)`
       (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (pushed = cx with stk updated_by CONS (NONE,name))`
    (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (body_ty = case rt of NONE => BaseT BoolT | SOME ty => ty)`
    (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  conj_tac >-
    (qhdtm_assum `intcall_callee_selected_callbacks`
       (irule o SIMP_RULE bool_ss [LET_THM,pairTheory.UNCURRY_DEF] o cj 4 o
        REWRITE_RULE [intcall_callee_selected_callbacks_def]) >>
     qpat_assum `Abbrev (pushed = _)`
       (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gl`,`Gpro`,`RetQ`,`a`,`aS`,`at_body`,`at_pro`,`b`,`bS`,
       `body_ce`,`body_out`,`ce`,`ctor`,`ret_dest`,`entry`,`final`,`has_rb`,`ilen`,
       `locked`,`params`,`prologue`,`rt`,`sf`,`tnl`,`tnpro`] >>
     qpat_assum `Abbrev (body_ty = _)`
       (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `subst_consts_stmts _ _ = compiled_ss` (pure_rewrite_tac o single) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qexists_tac `u` >> simp[NoAsms, Abbr `at_body`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
     qexists_tac `entry_info1` >>
     qpat_assum `(if block_is_terminated b then ((),b) else _) = ((),final)` mp_tac >>
     qpat_assum `nr' = nr` (pure_rewrite_tac o single) >>
     qpat_assum `key = global_nonreentrant_slot` (pure_rewrite_tac o single) >>
     qpat_assum `trans = T` (pure_rewrite_tac o single) >>
     qpat_assum `view = (mut = View)` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  `!K. gas_origin_ptr_path (DF K,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
      MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY)
      [] (OK at_body,Gl,tnl)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK at_body,Gl,tnl)`
       MATCH_ACCEPT_TAC) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ (locked,at_body,Gl,tnl) _ _`
    (fn body =>
      qpat_assum `!K. gas_origin_ptr_path (DF K,_,_,_,_,_) _ [] (OK at_body,Gl,tnl)`
        (mp_tac o MATCH_MP gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix o
         C CONJ body)) >>
  `storage_trace_domain pushed st0 locked.storage_trace` by
    (rewrite_tac[storage_trace_domain_def] >>
     qpat_assum `!K tr. valid_horizon pushed st0 K tr <=> _`
       (pure_rewrite_tac o single) >>
     qpat_assum `Abbrev (Hlock = _)`
       (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  `!J. (storage_trace_domain pushed st0 locked.storage_trace ==>
         valid_horizon pushed st0 J locked.storage_trace) ==>
         valid_horizon cx st0 J es1.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H locked.storage_trace ==> _` irule >>
     qpat_assum `!H tr. valid_horizon pushed st0 H tr <=> _`
       (pure_rewrite_tac o single o GSYM) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> reverse conj_tac
      >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
          conj_tac >- (disch_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
          first_assum ACCEPT_TAC) >>
      qpat_x_assum `gas_bad_storage_at pushed _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_bad_storage_at_def, storage_trace_domain_def] >>
      disch_tac >> qx_gen_tac `rest_gas` >>
      qpat_assum `lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked)`
        (qspec_then `gas_explicit marks entered.vs_gas_readings ++ rest_gas`
          mp_tac o MATCH_MP intcall_callee_body_gas_trace) >>
      qpat_assum `Abbrev (pushed = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      disch_then (pure_rewrite_tac o single) >>
      qpat_assum `!K tr. valid_horizon pushed _ K tr <=> _`
        (pure_rewrite_tac o single o GSYM) >>
      first_assum MATCH_ACCEPT_TAC)
  >- (
      qabbrev_tac `gs = gas_explicit marks entered.vs_gas_readings` >>
      mp_tac (Q.INST [`pushed` |-> `pushed`, `gs` |-> `gs`]
        intcall_callee_source_frame) >>
      (impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `Abbrev (pushed = _)`
                (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >> NO_TAC) >>
         qpat_assum `Abbrev (gs = _)`
           (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         first_assum ACCEPT_TAC)) >>
      qabbrev_tac `vres = case res of INL _ => INL NoneV
        | INR err => FST (handle_function err ee)` >>
      qpat_assum `Abbrev (vres = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        (qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
           (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
      `!H. valid_horizon cx st0 H locked.storage_trace ==>
          storage_well_formed_on cx locked (FST H)` by
        (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon pushed st0 H locked.storage_trace ==> _ /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >-
           (qpat_assum `!K tr. valid_horizon pushed st0 K tr <=> _`
              (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)) >>
         disch_then (mp_tac o cj 1 o cj 2) >>
         simp[NoAsms, Abbr `pushed`,
              vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk]) >>
      `eval_stmts pushed ss (locked with gas_obs := gs) = (res,ee with gas_obs := [])` by
        (qpat_assum `!tail. eval_stmts pushed ss _ = (res,ee with gas_obs := tail)`
           (qspec_then `[]` mp_tac) >>
         simp[NoAsms, Abbr `gs`]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
           storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
        (qx_gen_tac `Hfinal` >> disch_tac >>
         irule (INST_TYPE [Type.alpha |-> ``:256``] intcall_callee_source_storage) >>
         qexistsl_tac [`DF`,`G`,`G0`,`storage_trace_horizon es1.storage_trace`,
           `args`,`cenv`,`ctx`,`d`,`dflts`,`es`,`es0`,`es1`,`func`,
           `gs`,`lo`,`locked`,`mut`,`name`,`nr`,`penv`,`prev`,`res`,
           `ret`,`rr`,`rtv`,`s0`,`sa`,`sb`,`ss`,`st0`,`t`,`tenv`,
           `tn`,`tn0`,`tops`,`vv`] >>
         qpat_assum `Abbrev (pushed = _)`
           (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         disch_tac >>
         qpat_assum `!H. valid_horizon cx st0 H locked.storage_trace ==> _`
           (qspec_then `Hfinal` irule) >>
         first_assum ACCEPT_TAC) >>
      `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\ view = is_view_mut mut` by
        (disch_tac >>
         qpat_assum `nr ==> _ /\ cx.nonreentrant_slot = SOME key`
           (drule_then mp_tac) >>
         qpat_assum `key = global_nonreentrant_slot` (pure_rewrite_tac o single) >>
         simp[NoAsms]) >>
      `nr /\ ~view ==> MEM (StorageLock global_nonreentrant_slot) locked.storage_trace` by
        (strip_tac >>
         qpat_assum `nr ==> locked.storage_trace = _` (drule_then (pure_rewrite_tac o single)) >>
         qpat_assum `key = global_nonreentrant_slot` (pure_rewrite_tac o single) >>
         simp[NoAsms]) >>
      qpat_assum `!H. valid_horizon pushed st0 H ee.storage_trace ==> _ /\ _`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      (impl_tac >-
        (qpat_assum `!K tr. valid_horizon pushed st0 K tr <=> _`
           (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)) >>
      reverse (disch_then (strip_assume_tac o BETA_RULE))
      >- (
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`vres`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (qpat_assum `Abbrev (gs = _)`
                     (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
                   first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `Hfinal` >> disch_tac >>
      qpat_assum `!H. valid_horizon pushed st0 H ee.storage_trace ==> _ /\ _`
        (qspec_then `Hfinal` mp_tac) >>
      (impl_tac >- (qpat_assum `!K tr. valid_horizon pushed _ K tr <=> _`
                      (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)) >>
      disch_then (strip_assume_tac o BETA_RULE)
      >- (qpat_assum `r = OK _` (fn eq => qpat_assum `exit_result r`
            (mp_tac o REWRITE_RULE [eq,exit_result_def])) >> simp[NoAsms]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!tail. stmt_exit_ptr (RetQ Hfinal) _ res _ r`
        (qspec_then `[]` mp_tac) >>
      pure_rewrite_tac[bodyPtrDefsTheory.stmt_exit_ptr_def] >> strip_tac
      >- (mp_tac (Q.INST [`n` |-> `sa.cs_next_id`, `m` |-> `sb.cs_next_id`,
             `ret_count` |-> `rc'`, `rb` |-> `if rc' = 0 /\ 0 < rbs then SOME (HD argv) else NONE`,
             `H` |-> `Hfinal`, `gt` |-> `(G',tn')`] (INST_TYPE [Type.alpha |-> ``:256``] intcall_callee_body_error_exit)) >>
          impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                       TRY (qpat_assum `Abbrev (pushed = _)`
                              (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >> NO_TAC) >>
                       simp[NoAsms, Abbr `vres`]) >>
          simp[NoAsms]) >>
      `vres = INL v` by
        (qpat_assum `Abbrev (vres = _)`
           (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         qpat_assum `res = INR (ReturnException v)` (pure_rewrite_tac o single) >>
         simp[NoAsms, handle_function_def, return_def]) >>
      qpat_assum `RetQ Hfinal v _ _ r` mp_tac >>
      simp[NoAsms, Abbr `RetQ`] >>
      strip_tac >>
      `?ir sret. r = IntRet ir sret` by
        (qpat_assum `intret_q Hfinal callee body_ce pushed rtv v _ r`
          (mp_tac o REWRITE_RULE [intret_q_def]) >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
      rename1 `r = IntRet ir sret` >>
      `intcall_callee_src cx name mut nr ss (es1 with gas_obs := gs) =
         (INL v,ee with gas_obs := [])` by
        (qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = (vres,_)`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `vres = INL v` (pure_rewrite_tac o single) >>
         simp[NoAsms]) >>
      qpat_assum `!ir u. r = IntRet ir u ==> _`
        (qspecl_then [`ir`,`sret`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `r = IntRet ir sret` (pure_rewrite_tac o single) >>
      qpat_assum `vres = INL v` (pure_rewrite_tac o single) >>
      mp_tac (Q.INST [`ret_count` |-> `rc'`, `ce` |-> `body_ce`,
        `H` |-> `Hfinal`, `xs` |-> `gs`, `u` |-> `sret`, `view` |-> `view`, `rb` |->
          `if rc' = 0 /\ 0 < rbs then SOME (HD argv) else NONE`]
        (INST_TYPE [Type.alpha |-> ``:256``] intcall_callee_return_from_path)) >>
      qpat_assum `Abbrev (pushed = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `r = IntRet ir sret` (pure_rewrite_tac o single o SYM) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `cx_tops pushed = cx_tops cx` (pure_rewrite_tac o single o SYM) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (first_assum irule >> first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (simp[NoAsms] >> NO_TAC) >>
         TRY (qpat_assum `view <=> mut = View` (pure_rewrite_tac o single) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_assum `has_rb <=> rc' = 0 /\ 0 < rbs` (pure_rewrite_tac o single o GSYM) >>
         Cases_on `has_rb` >> simp[NoAsms] >>
         qpat_assum `T ==> !mem. mem_agree_outside tn'.t_mem sret.vs_memory mem ==> _`
           (ACCEPT_TAC o SIMP_RULE bool_ss [])) >>
      simp[NoAsms])
      >- (
      rename1 `r = OK body_state` >>
      rename1 `cenv_top_ext body_ce body_end_env (ee with gas_obs := []).scopes` >>
      `res = INL ()` by
        (qpat_assum `stmt_lands NoLoop b res body_state`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [loweringPostsTheory.stmt_lands_def]) >>
         first_assum ACCEPT_TAC) >>
      `~block_is_terminated b /\ body_end_env = body_out` by
        (qpat_assum `res = INL () ==> ~block_is_terminated b /\ body_end_env = body_out`
           (drule_then ACCEPT_TAC)) >>
      `cenv_top_ext body_ce body_out (ee with gas_obs := []).scopes` by
        (qpat_assum `body_end_env = body_out` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
      `body_inv tops ctx body_out pushed /\
       body_out.ce_return_pc = body_ce.ce_return_pc /\
       body_out.ce_nonreentrant = body_ce.ce_nonreentrant /\
       body_out.ce_returns_count = body_ce.ce_returns_count /\
       body_out.ce_is_ctor = body_ce.ce_is_ctor` by
        (mp_tac (Q.INST [`ce` |-> `body_ce`, `ce'` |-> `body_out`, `cx` |-> `pushed`,
                            `scopes` |-> `(ee with gas_obs := []).scopes`]
            intcall_callee_fallthrough_metadata) >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
      `a.cs_next_var <= b.cs_next_var` by
        (qpat_assum `stmts_env body_ce NoLoop body_ty _ a = (body_out,b)`
           (ACCEPT_TAC o cj 2 o MATCH_MP (REWRITE_RULE [cs_mono_def] stmts_env_cs_mono))) >>
      `ret_pc_ok body_out b body_state` by
        (irule ret_pc_ok_frame >>
         qexistsl_tac [`body_ce`,`at_body`,`a`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         rpt strip_tac >>
         qpat_assum `!x w. not_fresh_at a x /\ lookup_var x at_body = SOME w ==> _` irule >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      `gas_admissible (intcall_rest cx name mut nr ss prev rtv)
          expr_vv_res_ok (es1 with gas_obs := gs)` by
        (qhdtm_assum `intcall_entry_full`
           (mp_tac o cj 6 o REWRITE_RULE [intcall_entry_full_def]) >>
         simp[NoAsms]) >>
      `lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := gs) =
          (INL (),locked with gas_obs := gs)` by
        (qpat_assum `!gs. lock_if_nr cx nr _ _ = _` (qspec_then `gs` ACCEPT_TAC)) >>
      `eval_stmts pushed ss (locked with gas_obs := gs) = (INL (),ee with gas_obs := [])` by
        (qpat_assum `res = INL ()` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
      `nr /\ ~view ==> ~cx.txn.is_static` by
        (strip_tac >>
         qpat_assum `nr ==> _ /\ (~view ==> ~cx.txn.is_static) /\ _`
           (drule_then (irule o cj 1 o cj 2)) >>
         first_assum ACCEPT_TAC) >>
      `ret = NoneT` by
        (mp_tac (Q.INST [`ret_tv` |-> `rtv`, `es` |-> `es1 with gas_obs := gs`,
             `locked` |-> `locked with gas_obs := gs`,
             `ee` |-> `ee with gas_obs := []`] intcall_callable_fallthrough_void) >>
         qpat_assum `Abbrev (pushed = _)`
           (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
      `body_out.ce_returns_count = 0 /\ rc' = 0 /\ ~has_rb /\ ~(0 < rbs)` by
        (qpat_assum `body_ce.ce_returns_count = returns_stack_count _ ret` mp_tac >>
         qpat_assum `has_rb <=> rc' = 0 /\ 0 < rbs` mp_tac >>
         qpat_assum `has_rb <=> body_ce.ce_returns_count = 0 /\ ret <> NoneT` mp_tac >>
         qpat_assum `body_out.ce_returns_count = body_ce.ce_returns_count` (pure_rewrite_tac o single) >>
         qpat_assum `body_ce.ce_returns_count = rc'` (pure_rewrite_tac o single) >>
         qpat_assum `ret = NoneT` (pure_rewrite_tac o single) >>
         simp[NoAsms, returns_stack_count_def] >> decide_tac) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
            MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY) marks
            (OK body_state,G',tn') /\
         dead_lo_ok H (DF H) lo body_out pushed /\
         state_rel H callee body_out pushed (ee with gas_obs := []) body_state /\
         ghost_inv_at (DF H) lo ret_dest body_out pushed
           (ee with gas_obs := []) G' tn' body_state` by
        (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon pushed st0 H ee.storage_trace ==> _ /\ _`
           (qspec_then `H` mp_tac) >>
         impl_tac >-
           (qpat_assum `!K tr. valid_horizon pushed st0 K tr <=> _`
              (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
         qpat_assum `r = OK body_state` (pure_rewrite_tac o single) >>
         simp[NoAsms, exit_result_def] >> strip_tac >>
         rename1 `cenv_top_ext body_ce end_env ee.scopes` >>
         `end_env = body_out` by
           (qpat_assum `res = INL () ==> ~block_is_terminated b /\ end_env = body_out`
              (drule_then (ACCEPT_TAC o cj 2))) >>
         qpat_assum `end_env = body_out` SUBST_ALL_TAC >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (simp[NoAsms, Abbr `pushed`] >> first_assum ACCEPT_TAC >> NO_TAC)
         >- (simp[NoAsms, Abbr `pushed`] >> irule intcall_callee_dead_lo >>
             qexists_tac `cenv` >> reverse conj_tac
             >- (qpat_assum `!K. dead_lo_ok K (DF K) lo cenv cx` MATCH_ACCEPT_TAC) >>
             qpat_assum `body_out.ce_is_ctor = body_ce.ce_is_ctor`
               (pure_rewrite_tac o single) >>
             first_assum ACCEPT_TAC) >>
         qpat_assum `stmt_state_rel H ctx callee body_out _ _ body_state`
           (mp_tac o cj 1 o REWRITE_RULE [stmt_state_rel_def]) >>
         simp[NoAsms, Abbr `pushed`, loweringStateRelDefsTheory.state_rel_gas_obs]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp body_state` by
        (qpat_assum `!H. valid_horizon pushed st0 H ee.storage_trace ==> _ /\ _`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         (impl_tac >-
           (qpat_assum `!K tr. valid_horizon pushed st0 K tr <=> _`
              (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)) >>
         qpat_assum `r = OK body_state` (pure_rewrite_tac o single) >>
         simp[NoAsms, exit_result_def] >> strip_tac >>
         qpat_assum `stmt_state_rel _ ctx callee _ _ _ body_state`
           (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
      mp_tac (Q.INST [`ce` |-> `body_out`, `d` |-> `ret_dest`,
          `es` |-> `es1 with gas_obs := gs`, `locked` |-> `locked with gas_obs := gs`,
          `ee` |-> `ee with gas_obs := []`, `rpc` |-> `x`, `sz` |-> `0`,
          `s` |-> `body_state`, `tn` |-> `tn'`, `G` |-> `G'`, `ret_tv` |-> `rtv`,
          `PG` |-> `MAP (op_prov G) arg_ops`,
          `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
        (INST_TYPE [Type.alpha |-> ``:256``] intcall_callee_fallthrough_exit)) >>
      qpat_assum `Abbrev (pushed = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `body_out.ce_return_pc = body_ce.ce_return_pc`
                (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `body_out.ce_nonreentrant = body_ce.ce_nonreentrant`
                (pure_rewrite_tac o single) >>
              qpat_assum `key = global_nonreentrant_slot` (pure_rewrite_tac o single) >>
              qpat_assum `view <=> mut = View` (pure_rewrite_tac o single) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `(if block_is_terminated b then ((),b) else _) = ((),final)`
                mp_tac >>
              qpat_assum `nr' <=> nr` (pure_rewrite_tac o single) >>
              qpat_assum `trans <=> T` (pure_rewrite_tac o single) >>
              qpat_assum `entry_info1 = Var x` (pure_rewrite_tac o single) >>
              simp[NoAsms] >> NO_TAC) >>
         TRY (qpat_assum `ret = NoneT` (pure_rewrite_tac o single) >>
              simp[NoAsms] >> first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `res = INL ()` (pure_rewrite_tac o single o SYM) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (gen_tac >> simp[NoAsms] >> disch_tac >>
              qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ _ /\ _ /\ _`
                (qspec_then `H` mp_tac) >>
              impl_tac >- first_assum ACCEPT_TAC >>
              qpat_assum `Abbrev (pushed = _)`
                (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
              simp[NoAsms] >> NO_TAC) >>
         FAIL_TAC "fallthrough RET input") >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `Gend` (qx_choose_then `tnend` strip_assume_tac))) >>
      qabbrev_tac `iret = <|iret_values := []; iret_adopt_fmp := NONE|>` >>
      qabbrev_tac `ret_state = return_unlock_state body_out body_state` >>
      `intcall_callee_src cx name mut nr ss (es1 with gas_obs := gs) =
         (INL NoneV,ee with gas_obs := [])` by first_assum ACCEPT_TAC >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL NoneV`,`ee`,`IntRet iret ret_state`,`Gend`,`tnend`] >>
      conj_tac
      >- (qx_gen_tac `tail` >>
          qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = (vres,_)`
            (qspec_then `tail` mp_tac) >>
          qpat_assum `Abbrev (vres = _)`
            (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          qpat_assum `res = INL ()` (pure_rewrite_tac o single) >>
          simp[NoAsms]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `Hfinal` >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H _ ==>
        gas_origin_ptr_path _ (body_state,G',tn') [] _ /\ _`
        (qspec_then `Hfinal` mp_tac) >>
      impl_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      qpat_assum `Abbrev (iret = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qpat_assum `Abbrev (ret_state = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path _ (entered,_,_) marks (OK body_state,G',tn') /\ _`
        (qspec_then `Hfinal` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      `gas_origin_ptr_path (DF Hfinal,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
        MAP (op_prov G) arg_ops) (entered,FEMPTY,tn with t_var := FEMPTY) marks
        (IntRet iret ret_state,Gend,tnend)` by
        (qpat_assum `gas_origin_ptr_path _ _ marks (OK body_state,_,_)`
            (fn prefix =>
              qpat_assum `gas_origin_ptr_path _ (body_state,_,_) [] _`
                (fn suffix => mp_tac (MATCH_MP
                  (MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append prefix)
                  (CONJ (REFL (rand (concl prefix))) suffix)))) >>
          simp[NoAsms]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >> conj_tac >- simp[exit_result_def] >>
      qpat_assum `intret_q Hfinal callee body_out pushed rtv NoneV _ (IntRet iret ret_state)`
        (assume_tac o MATCH_MP intcall_callee_intret_clear_scopes) >>
      mp_tac (Q.INST [`ce` |-> `body_out`, `xs` |-> `gs`, `H` |-> `Hfinal`,
        `ret_count` |-> `rc'`, `ir` |-> `iret`, `u` |-> `ret_state`, `v` |-> `NoneV`,
        `G'` |-> `Gend`, `tn'` |-> `tnend`, `rb` |->
          `if rc' = 0 /\ 0 < rbs then SOME (HD argv) else NONE`]
        (INST_TYPE [Type.alpha |-> ``:256``] intcall_callee_return_from_path)) >>
      qpat_assum `Abbrev (pushed = _)`
        (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (first_assum irule >> first_assum ACCEPT_TAC >> NO_TAC) >>
         TRY (qpat_assum `body_out.ce_nonreentrant = body_ce.ce_nonreentrant`
                (pure_rewrite_tac o single) >>
              qpat_assum `view <=> mut = View` (pure_rewrite_tac o single) >>
              first_assum ACCEPT_TAC >> NO_TAC) >>
         simp[]) >>
      simp[NoAsms]))
  >- (disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac
      >- (irule intcall_callee_body_exempt >> qexistsl_tac [`locked`,`entered`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          TRY (simp[fragGasPathMemTheory.gas_path_mem_rules] >> NO_TAC) >>
          qpat_assum `Abbrev (pushed = _)`
            (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          qpat_assum `cx_tops pushed = cx_tops cx` (pure_rewrite_tac o single o SYM) >>
          first_assum ACCEPT_TAC) >>
      qexists_tac `H` >>
      conj_tac >- (disch_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC)
QED

Theorem intcall_callee_full:
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sb.cs_next_id t tn res ee gt r)
Proof
  MATCH_ACCEPT_TAC
    (SIMP_RULE bool_ss [intcall_callee_selected_callbacks_def, LET_THM, pairTheory.UNCURRY_DEF]
       (Q.SPEC `T` intcall_callee_selected_landing))
QED
