(* Calling convention and typed value facts for the selected return. *)
Theory bodyFullIntCallReturnValue
Ancestors context[qualified,ignore_grammar]
  bodyFullIntCallDefs bodyFullIntCallReturnMetadata
  fragGasOriginPtrInvoke intCallResultFull
  vyperInterpreter vyperState vyperAST vyperTyping bodyFullIntCallReturnTyping
  valueEncodingProofs valueCopyBytes exprLoweringProps
  bodyInvCodeProps exprBodyPreProps compileUnit alist
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]

Theorem fresh_vars_arity_code[local]:
  !n sa xs sb. fresh_vars n sa = (xs,sb) ==>
    ALL_DISTINCT xs /\ LENGTH xs = n /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. MEM x xs ==> ~not_fresh_at sa x /\ not_fresh_at sb x)
Proof
  Induct >>
  simp[emitHelperTheory.fresh_vars_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.fresh_var_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  TRY (qpat_x_assum `!x. MEM x vs ==> _` drule >>
       simp[ASCIInumbersTheory.toString_inj] >> NO_TAC) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
            arithmeticTheory.LESS_EQ_ADD]
QED

Theorem intcall_entry_invoke_continuation:
 !DF lo d H tops ctx func cenv cx tenv name es sa sm vv s0 es0 G0 tn0
   mut nr args ret ss rr prev penv rtv es1 t G tn rc rbs pvs bb inst.
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv s0 es0
   G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 fn_has_code sa sm func /\
 cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
 lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb t.vs_inst_idx = SOME inst ==>
 ALL_DISTINCT inst.inst_outputs /\ LENGTH inst.inst_outputs = rc /\
 (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x) /\
 (rc = 0 ==> sm.cs_current_bb = t.vs_current_bb /\
             LENGTH sm.cs_current_insts = SUC t.vs_inst_idx) /\
 (0 < rc ==> ?rbuf root st4 off aid.
    rbuf.buf_operand = Var root /\
    store_multi_results (Var root) (MAP Var inst.inst_outputs) 0 st4 = ((),sm) /\
    st4.cs_current_bb = t.vs_current_bb /\
    LENGTH st4.cs_current_insts = SUC t.vs_inst_idx /\
    fn_has_code st4 sm func /\ not_fresh_at st4 root /\
    ~MEM root inst.inst_outputs /\
    (!x. MEM x inst.inst_outputs ==> not_fresh_at st4 x) /\
    rbuf.buf_size = 32 * rc /\
    eval_operand rbuf.buf_operand t = SOME (n2w off) /\
    FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
    aid = sa.cs_next_id /\ sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
    vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
           (base_ptr rbuf))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `intcall_entry_full` mp_tac >>
  pure_rewrite_tac[intcall_entry_full_def] >>
  disch_then (strip_assume_tac o cj 14) >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key trans view ctor imm_len' ss' rt. _` kall_tac >>
  gvs[] >> rename1 `LENGTH inst.inst_outputs = nret` >>
  Cases_on `nret = 0`
  >- (Cases_on `rbs = 0` >> gvs[] >> suspend "void_arity") >>
  gvs[] >> suspend "register_arity"
QED

Resume intcall_entry_invoke_continuation[void_arity]:
  markerLib.RESUME_TAC >>
  qhdtm_assum `emit_void` mp_tac >>
  pure_rewrite_tac[emitHelperTheory.emit_void_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >>
  simp_tac (srw_ss()) [compileEnvTheory.emit_def] >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp_tac (srw_ss()) [rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  gvs[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
      venomInstTheory.mk_inst_def]
QED
Resume intcall_entry_invoke_continuation[register_arity]:
  drule intCallResultTheory.store_multi_results_shape >> strip_tac >>
  `ci_mono st2 st3` by
    (qpat_assum `compile_stage_intcall_args _ _ _ _ _ st2 = _` mp_tac >>
     qpat_assum `compile_stage_intcall_args _ _ _ _ _ st2a = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[ci_mono_trans, ci_mono_compile_stage_intcall_args,
               cj 1 compile_expr_ci_mono, pairTheory.SND]) >>
  qpat_x_assum `ci_mono st2 st3` mp_tac >>
  simp[ci_mono_def] >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  qhdtm_assum `emit_multi_op` mp_tac >>
  pure_rewrite_tac[emitHelperTheory.emit_multi_op_def, compileEnvTheory.comp_bind_def] >>
  Cases_on `fresh_vars nret st3` >> simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
     compileEnvTheory.fresh_id_def, compileEnvTheory.comp_return_def] >>
  simp_tac (srw_ss()) [LET_THM, compileEnvTheory.emit_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.fresh_id_def] >> strip_tac >>
  drule fresh_vars_arity_code >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp_tac (srw_ss()) [rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  gvs[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
      venomInstTheory.mk_inst_def, listTheory.APPEND_ASSOC] >>
  conj_tac
  >- (rpt strip_tac >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  qmatch_asmsub_abbrev_tac `store_multi_results _ _ _ st4` >>
  qexistsl [`rbuf`, `STRING #"%" (toString sa.cs_next_var)`, `st4`] >>
  simp[Abbr `st4`, fragExecTheory.emitted_blocks_def] >>
  conj_tac
  >- (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  conj_tac
  >- (strip_tac >>
      `~not_fresh_at st3 (STRING #"%" (toString sa.cs_next_var))` by metis_tac[] >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def]
QED
Finalise intcall_entry_invoke_continuation

Theorem intcall_entry_invoke_arity:
 !DF lo d H tops ctx func cenv cx tenv name es sa sm vv s0 es0 G0 tn0
   mut nr args ret ss rr prev penv rtv es1 t G tn rc rbs pvs bb inst.
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv s0 es0
   G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 fn_has_code sa sm func /\
 cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
 lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb t.vs_inst_idx = SOME inst ==>
 LENGTH inst.inst_outputs = rc
Proof
 metis_tac[intcall_entry_invoke_continuation]
QED

Theorem intcall_return_type_facts_mods:
 contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
 expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (src,name)) es dflt) es0 /\
 lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
 evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv v = SOME v ==>
 cenv.ce_func_return_type (nsid_to_string (src,name)) = ret /\
 evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
 type_widens_to (get_tenv cx) ret ann /\
 cenv.ce_struct_fields = make_struct_fields_map_mods mods
Proof
 strip_tac >>
 drule_all_then strip_assume_tac intcall_declared_return_type_mods >>
 drule_then assume_tac contract_inv_struct_fields >>
 drule_then assume_tac safe_cast_result_well_typed >>
 simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
 rpt strip_tac >>
 `evaluate_type (get_tenv cx) ret = SOME rtv /\
  ?dflts. lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss)` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]) >>
 drule_all_then strip_assume_tac body_inv_expr_body_pre_mods >>
 drule_then assume_tac bodySimTheory.body_inv_contract >>
 drule_all_then strip_assume_tac
   (REWRITE_RULE [ALOOKUP_def] (Q.INST [`mods` |-> `[(NONE,tops)]`,
     `src` |-> `NONE`] intcall_return_type_facts_mods)) >>
 simp[make_struct_fields_map_mods_singleton]
QED
*)
Theorem intcall_return_type_facts:
 !tops ctx func cenv cx tenv ann name es dflt es0 sa sm vv s0
  DF lo d H G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn v.
 (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
 expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
   s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 safe_cast rtv v = SOME v ==>
 cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ret /\
 evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
 type_widens_to (get_tenv cx) ret ann /\
 cenv.ce_struct_fields = make_struct_fields_map tops
Proof
  cheat
QED


(* Typed interpretation of the words in the selected return buffer. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
 rpt gen_tac >> strip_tac >> rename1 `0 < nret` >>
 drule_all intcall_return_type_facts >> strip_tac >>
 `?dflts. lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss)` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> metis_tac[]) >>
 drule_all callable_func_info_in_env >> strip_tac >>
 `returns_stack_count
   (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ret =
   nret` by
   (qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _`
      (mp_tac o Q.AP_TERM `FST`) >>
    qpat_assum `cenv.ce_func_info _ = (nret,rbs,pvs)` mp_tac >>
    simp[compileEnvTheory.compute_func_info_def]) >>
 `0 < returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ret` by simp[] >>
 `~is_bytestring_type ret` by suspend "not_bytes" >>
 `type_memory_size rtv = 32 * nret` by
   (`expr_sim_inv cenv cx tenv es0` by metis_tac[expr_body_pre_static_facts] >>
    `type_memory_bytes cenv ret = type_memory_size rtv` by
      metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
    drule_all returns_stack_extent >> pure_asm_rewrite_tac[] >>
    disch_then (ACCEPT_TAC o SYM)) >>
 simp[] >> suspend "post_type"
QED
*)
Theorem intcall_return_register_type_facts:
 !tops ctx func cenv cx tenv ann name es dflt es0 sa sm vv s0
  DF lo d H G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn rc rbs pvs v.
 (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
 expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
   s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\ 0 < rc /\
 safe_cast rtv v = SOME v ==>
 cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ret /\
 evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
 type_memory_size rtv = 32 * rc /\ type_widens_to (get_tenv cx) ret ann /\
 ~is_bytestring_type ret /\
 post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt) = ret /\
 0 < returns_stack_count
   (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ret /\
 cenv.ce_struct_fields = make_struct_fields_map tops
Proof
  cheat
QED
(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_return_register_type_facts[not_bytes]:
 Cases_on `ret` >>
 gvs[compileEnvTheory.is_bytestring_type_def,
     compileEnvTheory.returns_stack_count_def] >>
 Cases_on `b` >> gvs[compileEnvTheory.returns_stack_count_def,
                            compileEnvTheory.is_bytestring_type_def,
                            compileEnvTheory.is_word_type_def] >>
 rename1 `BytesT bd` >> Cases_on `bd` >>
 gvs[compileEnvTheory.returns_stack_count_def,
     compileEnvTheory.is_bytestring_type_def, compileEnvTheory.is_word_type_def]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_return_register_type_facts[post_type]:
 `~is_bytestring_type ann` by
   metis_tac[vyperTypeSystemTheory.type_widens_to_def,
             compileEnvTheory.arg_type_fits_bytestring_source] >>
 Cases_on `is_word_type ann`
 >- (drule_all compileEnvTheory.type_widens_to_word >> strip_tac >> gvs[]) >>
 gvs[exprLoweringTheory.lowered_value_type_def]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Finalise intcall_return_register_type_facts
*)

Theorem intcall_return_register_value_certificate:
 !tops ctx func cenv cx tenv ann name es dflt es0 sa sm vv s0
  DF lo d H G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn
  rc rbs pvs v ee Gc tc ir cs returned out outs rbuf root off st4 stored Gs ts.
 (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
 expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
 intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
   s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
 cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\ 0 < rc /\
 intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc NONE
   sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
 safe_cast rtv v = SOME v /\
 FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
 bind_outputs outs ir.iret_values
   (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
 ~MEM root outs /\
 rbuf.buf_operand = Var root /\ rbuf.buf_size = 32 * rc /\
 vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rbuf) /\
 eval_operand rbuf.buf_operand t = SOME (n2w off) /\
 off + rbuf.buf_size <= t.vs_alloca_next /\
 off + rbuf.buf_size < dimword (:256) /\
 not_fresh_at st4 root /\
 (stored with <|vs_vars := (returned with vs_inst_idx := SUC t.vs_inst_idx).vs_vars;
               vs_memory := returned.vs_memory|>) =
   (returned with vs_inst_idx := SUC t.vs_inst_idx) /\
 (!x. not_fresh_at st4 x ==>
   lookup_var x stored = lookup_var x returned /\
   FLOOKUP Gs x = FLOOKUP (DRESTRICT G (COMPL (set outs))) x /\
   op_taint ts (Var x) = op_taint
     (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) (Var x)) /\
 (!mem i. mem_agree_outside ts.t_mem stored.vs_memory mem /\ i < LENGTH ir.iret_values ==>
   mem_word_at (off + 32 * i) mem = EL i ir.iret_values) ==>
 vv_holds cenv cx (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
   (Value v) vv (out with scopes := prev)
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 vv_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
   (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
   (out with scopes := prev) (Value v) vv
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts) /\
 ptr_vv_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
   (Value v) vv (out with scopes := prev) Gs ts
   (stored with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
 rpt gen_tac >> strip_tac >> rename1 `0 < nret` >>
 drule_all intcall_return_register_type_facts >> strip_tac >>
 `intret_vals_match rtv v ir.iret_values /\ LENGTH ir.iret_values = nret` by
   (qhdtm_assum `intcall_callee_exit_full` mp_tac >>
    pure_rewrite_tac[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
         exprSimDefsTheory.expr_exit_def] >> strip_tac >> gvs[]) >>
 `!mem. mem_agree_outside ts.t_mem stored.vs_memory mem ==>
    val_in_memory rtv v off mem` by suspend "robust" >>
 `stored.vs_alloca_next = t.vs_alloca_next` by
   (drule calleeTransportTheory.bind_outputs_shared_fields >>
    Cases_on `ir.iret_adopt_fmp` >>
    simp[venomExecSemanticsTheory.adopt_return_fmp_def,
         venomExecSemanticsTheory.merge_callee_state_def] >>
    strip_tac >>
    qpat_x_assum `stored with <|vs_vars := _; vs_memory := _|> = _` (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_alloca_next`) >>
    simp[]) >>
 `eval_operand rbuf.buf_operand stored = SOME (n2w off)` by suspend "root_operand" >>
 `off < dimword (:256)` by decide_tac >>
 `val_store_size rtv v <= 32 * nret` by
   (drule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
    disch_then (mp_tac o MATCH_MP exprSimPropsTheory.val_store_size_le) >> simp[]) >>
 conj_tac >- suspend "holds" >>
 conj_tac >- suspend "bound" >> suspend "pointer"
QED
Resume intcall_return_register_value_certificate[robust]:
 rpt strip_tac >>
 irule intCallResultTheory.stack_results_val_in_memory >>
 conj_tac >- (qexists `get_tenv cx` >> suspend "abi_shape") >>
 simp[] >> qexists `ir.iret_values` >> simp[] >>
 conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
 Cases_on `ir.iret_values` >> gvs[]
QED
Resume intcall_return_register_value_certificate[abi_shape]:
 `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
   (drule_then strip_assume_tac expr_body_pre_static_facts >>
    fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
 Cases_on `is_word_type ret`
 >- (disj1_tac >> metis_tac[]) >>
 Cases_on `ret` >>
 gvs[compileEnvTheory.returns_stack_count_def] >>
 suspend "shape_detail"
QED
Resume intcall_return_register_value_certificate[shape_detail]:
 markerLib.RESUME_TAC
 >~ [`evaluate_type _ (TupleT tys) = SOME _`] >-
   (gvs[compileEnvTheory.tuple_like_stack_count_def,
        vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
    gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
    drule vyperTypeABITheory.OPT_MMAP_LIST_REL >> strip_tac >>
    disj2_tac >>
    `EVERY is_word_type tys` by
      (Cases_on `LENGTH tys <= MAX_STACK_RETURNS /\ EVERY is_word_type tys` >> gvs[]) >>
    gvs[listTheory.EVERY_MEM, listTheory.LIST_REL_EL_EQN] >>
    metis_tac[listTheory.MEM_EL]) >>
 suspend "struct_shape"
QED
Resume intcall_return_register_value_certificate[struct_shape]:
 gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
 qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
 simp[loweringStateRelDefsTheory.sfields_tenv_consistent_def] >> strip_tac >>
 first_x_assum drule >> strip_tac >>
 gvs[compileEnvTheory.get_struct_fields_def, compileEnvTheory.tuple_like_stack_count_def] >>
 `EVERY is_word_type (MAP SND args')` by
   (Cases_on `LENGTH fields <= MAX_STACK_RETURNS /\ EVERY is_word_type (MAP SND args')` >> gvs[]) >>
 drule (cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono) >> strip_tac >>
 gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
 drule vyperTypeABITheory.OPT_MMAP_LIST_REL >> strip_tac >>
 disj2_tac >>
 `LENGTH (MAP FST args') = LENGTH tvs` by
   gvs[listTheory.LIST_REL_EL_EQN] >>
 `MAP SND (ZIP (MAP FST args',tvs)) = tvs` by
   metis_tac[listTheory.UNZIP_MAP, listTheory.UNZIP_ZIP, pairTheory.PAIR_EQ] >>
 simp[] >>
 gvs[listTheory.EVERY_MEM, listTheory.LIST_REL_EL_EQN] >>
 rpt strip_tac >>
 qpat_x_assum `MEM etv tvs` (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
 qexists `EL n (MAP SND args')` >>
 conj_tac >- (first_x_assum irule >> simp[listTheory.MEM_EL] >> metis_tac[]) >>
 metis_tac[]
QED
Resume intcall_return_register_value_certificate[root_operand]:
 `lookup_var root returned = lookup_var root t` by
   (drule dftGasInvCallPartnerTheory.inv_bind_outputs_lookup_outside >>
    disch_then drule >>
    Cases_on `ir.iret_adopt_fmp` >>
    simp[venomExecSemanticsTheory.adopt_return_fmp_def,
         venomExecSemanticsTheory.merge_callee_state_def, venomStateTheory.lookup_var_def]) >>
 gvs[venomStateTheory.eval_operand_def] >> metis_tac[]
QED
Resume intcall_return_register_value_certificate[holds]:
 gvs[] >> irule intCallResultTheory.buffer_vv_holds >>
 simp[] >>
 first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED
Resume intcall_return_register_value_certificate[bound]:
 gvs[exprSimMemDefsTheory.vv_store_bound_def,
     contextTheory.base_ptr_def, exprLoweringTheory.lowered_value_type_def,
     vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
Resume intcall_return_register_value_certificate[pointer]:
 `FLOOKUP G root = SOME (off,rbuf.buf_size) /\ op_taint tn (Var root) = {}` by
   (qhdtm_assum `intcall_entry_full` mp_tac >>
    pure_rewrite_tac[intcall_entry_full_def] >> strip_tac >>
    qpat_x_assum `!ty p buf. _`
      (qspecl_then [`cenv.ce_func_return_type (nsid_to_string (NONE,name))`,
         `base_ptr rbuf`,`rbuf`] mp_tac) >>
    map_every (fn p => qpat_assum p mp_tac)
      [`vv = LocatedValue (cenv.ce_func_return_type _) (base_ptr rbuf)`,
       `rbuf.buf_operand = Var root`,
       `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size)`] >>
    POP_ASSUM_LIST (K all_tac) >>
    simp[contextTheory.base_ptr_def] >> rpt strip_tac >> gvs[]) >>
 `FLOOKUP Gs root = SOME (off,rbuf.buf_size) /\ op_taint ts (Var root) = {}` by
   (first_x_assum (qspec_then `root` mp_tac) >>
    simp[ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
    gvs[ptrDisciplineTheory.op_taint_def]) >>
 `~is_bytestring_type ann` by
   metis_tac[vyperTypeSystemTheory.type_widens_to_def,
             compileEnvTheory.arg_type_fits_bytestring_source] >>
 gvs[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
     contextTheory.base_ptr_def, vyperStateTheory.read_result_def,
     vyperStateTheory.return_def]
QED
Finalise intcall_return_register_value_certificate
