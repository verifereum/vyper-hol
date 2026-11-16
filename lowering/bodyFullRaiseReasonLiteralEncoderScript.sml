(* Literal reason encoding keeps the annotated capacity distinct from its tag. *)
Theory bodyFullRaiseReasonLiteralEncoder
Ancestors
  bodyFullRaiseReasonLiteralLayout bodyFullRaiseReasonContinuation
  exprSimPtrLiteralBuffer exprSimUnwrapProps loweringPosts exprLowering
  vyperInterpreter vyperState context compileEnv
  bodyFullRaiseReasonHeadFrame bodyFullRaiseReasonHead bodyFullRaiseReasonHeadValue
  bodyFullRaiseReasonHeadGhost bodyPtrDefs loweringStateRelDefs exprLoweringProps
  revertReasonLayout stmtReasonMemory vyperStorageFootprint fragExec
  venomInst venomState venomMemDefs rich_list list arithmetic finite_map
  revertAllocationPtr stmtReasonLitFragMemory abiPathAllocInv
  vyperTypeSystem vyperTypeValues valueEncoding vyperValue vyperTyping
  valueEncodingDefs exprSimSource

Theorem reason_literal_annotated_vv_post[local]:
  expr_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
    es sa sm s0 es (StringV str) (Var p) s ==>
  vv_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
    es sa sm s0 es (Value (StringV str))
    (LocatedValue (BaseT (StringT ml)) (mk_ptr (Var p) LocMemory)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def, read_result_def,
      vyperStateTheory.return_def, is_word_type_def,
      vyperASTTheory.expr_type_def] >>
  fs[expr_val_rel_def, expr_val_at_def, is_word_type_def] >>
  rpt strip_tac >> gvs[is_word_type_def] >> metis_tac[]
QED

Theorem reason_literal_encoder_origin_ptr:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sm) /\
  compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) M sm = ((),sf) /\
  M = type_memory_bytes cenv (BaseT (StringT ml)) /\
  64+M < dimword(:256) /\
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es /\
  buf.buf_operand = Var p /\ not_fresh_at sm p /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
      es sa sm s0 es (StringV str) (Var p) s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  expr_store_bound cx (BaseT (StringT (LENGTH str))) (StringV str) (Var p) s /\
  ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) G tn s /\
  ptr_buf_ok cenv (Literal (BaseT (StringT ml)) (StringL str)) (Var p) G s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z Gf tnf. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort z,Gf,tnf)
Proof
  strip_tac >>
  drule reason_literal_encoder_memory_layout >>
  disch_then (qx_choose_then `sb` strip_assume_tac) >>
  `cs_extends sm sb /\ cs_extends sb sf` by
    simp[cs_extends_def, IS_PREFIX_APPEND] >>
  `fn_has_code sm sb func /\ fn_has_code sb sf func` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    fs[expr_post_def] >>
  `alloca_room ctx func s /\ alloca_next_valid s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, alloca_inv_def] >> metis_tac[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ reason_head sm.cs_next_id sm.cs_next_var M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (64+M))]
      ["%" ++ toString sm.cs_next_var]) (fn_insts func) /\
   MEM (mk_inst (sm.cs_next_id+3) ALLOCA [Lit (n2w M)]
      ["%" ++ toString (sm.cs_next_var+2)]) (fn_insts func)` by
    (conj_tac >> first_x_assum irule >> simp[reason_head_def]) >>
  `M < dimword(:256)` by decide_tac >>
  `(!x. FLOOKUP s.vs_allocas sm.cs_next_id = SOME x ==> SND x = 64+M) /\
   (!x. FLOOKUP s.vs_allocas (sm.cs_next_id+3) = SOME x ==> SND x = M)` by
    (drule_all (Q.INST [`id` |-> `sm.cs_next_id`, `n` |-> `64+M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     drule_all (Q.INST [`id` |-> `sm.cs_next_id+3`, `n` |-> `M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     conj_tac >> gen_tac >> PairCases_on `x` >> simp[NoAsms] >>
     strip_tac >> metis_tac[ADD_COMM]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (reason_head sm.cs_next_id sm.cs_next_var M)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all reason_head_origin_ptr_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`th`,`Gh`,`thn`,`B`,`TP`] strip_assume_tac)) >>
  suspend "resources"
QED

Resume reason_literal_encoder_origin_ptr[resources]:
  `vv_post (storage_trace_horizon es.storage_trace) ctx func cenv cx
    (Literal (BaseT (StringT ml)) (StringL str)) es sa sm s0 es
    (Value (StringV str)) (LocatedValue (BaseT (StringT ml)) (mk_ptr (Var p) LocMemory)) s` by
    (irule reason_literal_annotated_vv_post >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (StringT ml)) = SOME (BaseTV (StringT ml)) /\
   value_has_type (BaseTV (StringT ml)) (StringV str)` by
    (drule expr_body_pre_runtime_typed >>
     simp[evaluate_def, vyperValueOperationTheory.evaluate_literal_def, return_def, read_result_def,
       vyperASTTheory.expr_type_def] >>
     strip_tac >> gvs[evaluate_type_def, AllCaseEqs()]) >>
  `val_wf (BaseTV (StringT ml)) (StringV str)` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `alloca_inv s /\ alloca_inv th` by
    metis_tac[stmt_state_rel_def, run_inst_seq_alloca_inv] >>
  `!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `!x k. not_fresh_at sa x /\ k < 3 ==>
    x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> first_x_assum irule >> decide_tac) >>
  `!x k. (mk_ptr (Var p) LocMemory).ptr_operand = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (simp[mk_ptr_def] >> rpt strip_tac >> fs[not_fresh_at_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
    (reason_head sm.cs_next_id sm.cs_next_var M) s Gh thn` by metis_tac[] >>
  `vv_post (storage_trace_horizon es.storage_trace) ctx func cenv cx
    (Literal (BaseT (StringT ml)) (StringL str)) es sa sm s0 es
    (Value (StringV str)) (LocatedValue (BaseT (StringT ml)) (mk_ptr (Var p) LocMemory)) th` by
    (irule reason_head_vv_post >>
     conj_tac >- simp[vyperASTTheory.expr_type_def, read_result_def, return_def] >>
     simp[] >>
     qexistsl_tac [`ARB`,`G`,`Gh`,`M`,`PG`,`sm.cs_next_id`,`lo`,`s`,`tn`,`thn`,`sm.cs_next_var`] >>
     simp[vv_operand_def, mk_ptr_def, read_result_def, return_def,
       vyperASTTheory.expr_type_def, evaluate_type_def, GSYM ADD_ASSOC] >>
     rpt conj_tac >- (rpt strip_tac >> fs[mk_ptr_def] >> metis_tac[ADD_COMM])
     >- (rpt strip_tac >> metis_tac[ADD_COMM])
     >- (once_rewrite_tac[ADD_COMM] >> simp[]) >> gvs[ADD_COMM]) >>
  suspend "pointer"
QED

Resume reason_literal_encoder_origin_ptr[pointer]:
  `ptr_vv_ok cx (BaseT (StringT ml)) (Value (StringV str))
    (LocatedValue (BaseT (StringT ml)) (mk_ptr (Var p) LocMemory)) es Gh thn th` by
    (irule (INST_TYPE [alpha |-> ``:256``] reason_head_ptr_vv_ok) >> simp[] >>
     qexistsl_tac [`ARB`,`G`,`storage_trace_horizon es.storage_trace`,`M`,`PG`,
       `cenv`,`ctx`,`func`,`sm.cs_next_id`,`lo`,`s`,`sa`,`sm`,`tn`,`sm.cs_next_var`] >>
     simp[vv_operand_def, mk_ptr_def, ptr_vv_ok_def, read_result_def, return_def] >>
     conj_tac >- (rpt strip_tac >> fs[mk_ptr_def] >> metis_tac[ADD_COMM]) >>
     gvs[vv_post_def, ptr_val_ok_def, mk_ptr_def, vyperASTTheory.expr_type_def,
       is_word_type_def, ADD_COMM]) >>
  suspend "tail"
QED

Resume reason_literal_encoder_origin_ptr[tail]:
  `LENGTH str <= ml` by fs[value_has_type_def] >>
  `evaluate_type (get_tenv cx) (BaseT (StringT (LENGTH str))) =
    SOME (BaseTV (StringT (LENGTH str)))` by
    (drule exprSimPropsTheory.word_size_monotone >> strip_tac >>
     fs[evaluate_type_def, type_slot_size_def] >> gvs[AllCaseEqs()] >> decide_tac) >>
  `expr_store_bound cx (BaseT (StringT ml)) (StringV str) (Var p) th` by
    (drule_all reason_head_operand_frame >> strip_tac >>
     qpat_x_assum `expr_store_bound _ _ _ _ s` mp_tac >>
     simp[exprSimMemDefsTheory.expr_store_bound_def, exprSimPropsTheory.val_store_size_def,
       is_word_type_def] >>
     strip_tac >> rpt strip_tac >>
     fs[mk_ptr_def] >>
     qpat_x_assum `!w. eval_operand (Var p) s = SOME w ==> _`
       (qspec_then `w` mp_tac) >> simp[] >> decide_tac) >>
  `allocas_from lo th /\ lo <= th.vs_alloca_next` by
    metis_tac[reason_head_allocas_from] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es th /\
   expr_val_rel cx (BaseT (StringT ml)) (StringV str) (Var p) th` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ th` mp_tac >>
     simp[NoAsms, vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def,
       read_result_def, return_def, vyperASTTheory.expr_type_def,
       is_word_type_def] >> strip_tac >>
     gvs[expr_val_rel_def, expr_val_at_def, is_word_type_def]) >>
  `ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) Gh thn th` by
    fs[ptr_vv_ok_def, ptr_val_ok_def, is_word_type_def, mk_ptr_def, read_result_def, return_def] >>
  `sf.cs_current_bb = sb.cs_current_bb /\
   sf.cs_current_insts = sb.cs_current_insts ++
     reason_tail sb.cs_next_id sb.cs_next_var sm.cs_next_var (Var p)` by
    simp[reason_tail_def, revert_reason_copy_def, revert_reason_suffix_def] >>
  mp_tac (Q.INST [`sa` |-> `sb`, `sb` |-> `sf`,
    `code` |-> `reason_tail sb.cs_next_id sb.cs_next_var sm.cs_next_var (Var p)`]
    (SPEC_ALL fn_has_code_code)) >>
  impl_tac >- simp[] >> strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by simp[] >>
  qpat_assum `fn_inst_ids_distinct func /\ _ ==> _` mp_tac >>
  impl_tac >- (conj_tac >- simp[] >>
    qpat_assum `!k. k < 2 ==> _` mp_tac >>
    simp[NoAsms, ADD_COMM]) >> strip_tac >>
  suspend "apply_tail"
QED

Resume reason_literal_encoder_origin_ptr[apply_tail]:
  qmatch_asmsub_abbrev_tac `OK sh` >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es sh` by
    simp[Abbr `sh`, stmt_state_rel_inst_idx] >>
  `wb_frame cenv es es sb sh sh` by
    simp[wb_frame_def] >>
  `ghost_kept_at lo cenv es sb Gh thn sh Gh thn` by
    simp[ghost_kept_at_def] >>
  `expr_val_rel cx (BaseT (StringT ml)) (StringV str) (Var p) sh` by
    fs[Abbr `sh`, expr_val_rel_def, eval_operand_def, lookup_var_def] >>
  `isPREFIX (reason_tail sb.cs_next_id sb.cs_next_var sm.cs_next_var (Var p))
    (DROP sh.vs_inst_idx bb'.bb_instructions)` by
    (qpat_x_assum `isPREFIX (reason_tail _ _ _ _) _` mp_tac >>
     simp[Abbr `sh`, reason_head_def, revert_reason_prefix_def]) >>
  `!x. Var p = Var x ==> not_fresh_at sb x` by
    (simp[] >> fs[not_fresh_at_def]) >>
  `sb.cs_next_id = sm.cs_next_id+4 /\ sb.cs_next_var = sm.cs_next_var+3` by simp[] >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var)) sh = SOME (n2w B) /\
   lookup_var (STRING #"%" (toString (sm.cs_next_var+1))) sh = SOME (n2w (B+32)) /\
   lookup_var (STRING #"%" (toString (sm.cs_next_var+2))) sh = SOME (n2w TP) /\
   ptr_covers Gh thn (STRING #"%" (toString sm.cs_next_var)) sh (64+M) /\
   ptr_covers Gh thn (STRING #"%" (toString (sm.cs_next_var+1))) sh (32+M) /\
   ptr_covers Gh thn (STRING #"%" (toString (sm.cs_next_var+2))) sh M` by
    gvs[Abbr `sh`, ptr_covers_def, lookup_var_def] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ sh`
    (mp_then Any mp_tac reason_normalized_tail_origin_ptr) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`explicit`,`TP`,`PG`,`M`,`B`] mp_tac) >>
  impl_tac >- (simp[Abbr `sh`, ptr_val_ok_def, exprSimMemDefsTheory.expr_store_bound_def,
    eval_operand_def, lookup_var_def, ptrDisciplineTheory.allocas_from_def] >>
    gvs[ptr_val_ok_def, ptr_mem_ok_def, exprSimMemDefsTheory.expr_store_bound_def,
      eval_operand_def, lookup_var_def]) >>
  strip_tac >> qexistsl_tac [`z`,`Gf`,`tnf`] >> rpt strip_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gh`,`sh`,`thn`] >> conj_tac >- metis_tac[] >>
  metis_tac[]
QED

Finalise reason_literal_encoder_origin_ptr
