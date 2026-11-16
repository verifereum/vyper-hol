(* Full source/capture/start/length composition for ordinary Slice. *)
Theory bodyFullBuiltinSliceOrdinary
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose gasOutcomeFullStmts
  exprSimSliceOrdinary exprSimSliceSource
  bodyPtrSignedConvertSourceFixed exprSimSliceMemory builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs venomState venomExecSemantics
  bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost stmtSimLogArgs
  loweringPosts exprSimWordArgs logTopicFramePtr stmtSimLogTopics abiEncodeOwnership
  exprSimHashBoundary exprSimConvertBytes valueEncodingProofs valueEncodingDefs
  compileEnv vyperValue supportedTypes vyperTypeSystem vyperTyping ptrDiscipline
  bodyPtrBytestringBuiltinsAllocation bodyInvNoDalloca
  exprSimSliceOrdinaryContext exprSimSliceOrdinaryFrame exprSimSliceOrdinaryEntry
  exprSimSliceOrdinaryContinue exprSimHypsDefs exprSimSource exprLowering
  gasShadowCompileBuiltinBytes gasShadowCompileContext
  gasShadowCompileStmtHelpers gasShadowCompilePure
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr exprLoweringProps
  bodyPtrBytestringBuiltinsCalldataReserved loweringStateRelDefs
  exprSimSliceCaptureControl bodyFullUnwrapRun
  bodyFullGhostFrame bodyFullBuiltinWordPowCompose
  exprSimSliceCapture exprOperandVar vyperTypeExprResult
  vyperTypeExprSoundness vyperTypeInvariants
  vyperInterpreter vyperAST list

Theorem slice_dynamic_capture_source_post_from_run:
  (!sa src len data sb func s p G tn capacity bs lo ctx explicit PG.
    compile_bytestring_src (Var src) sa = ((len,data),sb) /\
    fn_has_code sa sb func /\ not_fresh_at sa src /\
    lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
    32 <= capacity /\ w2n p + 32 < dimword (:256) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    w2n p + 32 <= s.vs_alloca_next /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
      eval_operand len u = SOME (n2w (LENGTH bs)) /\
      eval_operand data u = SOME (p+32w) /\
      op_taint tn' len = {} /\ op_prov G' len = NONE /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
      (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      u = s with vs_vars := u.vs_vars /\
      (!x. not_fresh_at sa x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!n. 32+n <= capacity ==>
         ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
      (?lp dp. len = Var lp /\ data = Var dp /\
         not_fresh_at sb lp /\ not_fresh_at sb dp)) ==>
  !H ctx func cenv cx e es0 sa sm s0 es v srcop s bt vt env G tn
    ghost_D floor d len data sc lo explicit PG.
  expr_post (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx e es0 sa sm s0 es v srcop s /\
  post_value_type cenv e = BaseT bt /\
  (?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\ value_has_type vt v /\
  expr_sim_inv cenv cx env es /\
  ptr_val_ok cx (BaseT bt) v srcop G tn s /\
  ghost_inv_at ghost_D floor d cenv cx es G tn s /\
  compile_bytestring_src srcop sm = ((len,data),sc) /\ fn_has_code sm sc func /\
  (!z. srcop = Var z ==> not_fresh_at sm z) /\ (!l. srcop <> Label l) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u G' tn' src p bs.
    srcop = Var src /\ eval_operand srcop s = SOME p /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    val_footprint vt v = 32 + LENGTH bs /\
    run_inst_seq (emitted_insts sm sc) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sm x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. n <= LENGTH bs ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
    expr_post H ctx func cenv cx e es0 sa sc s0 es v srcop u /\
    ghost_inv_at ghost_D floor d cenv cx es G' tn' u /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ptr_covers G' tn' src u (32+LENGTH bs) /\
    (?dp. data = Var dp /\ ptr_covers G' tn' dp u (LENGTH bs)) /\
    (?lp dp. len = Var lp /\ data = Var dp /\
       not_fresh_at sc lp /\ not_fresh_at sc dp)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   expr_val_rel cx (BaseT bt) v srcop s /\
   expr_val_at cenv cx (BaseT bt) sa sm es v srcop s` by
    gvs[expr_post_def] >>
  `~is_word_type (BaseT bt) /\ supported_scalar_type (BaseT bt) /\
   is_bytestring_type (BaseT bt)` by
    gvs[supported_scalar_type_def, supported_word_type_def,
        supported_string_type_def, is_word_type_def, is_bytestring_type_def] >>
  `log_arg_rel cenv cx sa sm es s (srcop,BaseT bt) v` by
    (simp[log_arg_rel_def] >> irule log_arg_clear_base >>
     goal_assum (drule_at Any)) >>
  `?p. eval_operand srcop s = SOME p` by gvs[expr_val_rel_def] >>
  drule_all expr_val_rel_memory >> strip_tac >>
  `?bs. (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
        val_footprint vt v = 32 + LENGTH bs /\
        mem_word_at (w2n p) s.vs_memory = n2w (LENGTH bs) /\
        mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs` by
    (gvs[] >> Cases_on `v` >>
     gvs[evaluate_type_def, value_has_type_def, val_footprint_def,
         val_in_memory_def] >> metis_tac[]) >>
  drule_all log_arg_footprint_bound >> strip_tac >>
  `LENGTH bs < dimword (:256) /\ w2n p + 32 < dimword (:256)` by decide_tac >>
  drule_all ptr_val_ok_log_bytestring_window >> strip_tac >>
  `w2n p + 32 <= s.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >> decide_tac) >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    metis_tac[mem_word_at_eq_mload_proof] >>
  `lookup_var src s = SOME p` by gvs[eval_operand_def] >>
  `32 <= 32 + LENGTH bs` by simp[] >>
  `not_fresh_at sm src` by metis_tac[] >>
  qpat_x_assum `srcop = Var src` SUBST_ALL_TAC >>
  qpat_x_assum `!sa src len data sb func s p G tn capacity bs lo ctx explicit PG. _`
    (drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac)) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (irule stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
  `stor_taint_ok_at ghost_D tn' u /\
   allocas_from floor u /\ floor <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at ghost_D floor _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `u = s with vs_vars := _` mp_tac >>
     qpat_assum `tn'.t_stor = tn.t_stor` mp_tac >>
     qpat_assum `tn'.t_trans = tn.t_trans` mp_tac >>
     qpat_assum `tn'.t_imm = tn.t_imm` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ghost_inv_at_def,stor_taint_ok_at_def,allocas_from_def,
       venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv_at ghost_D floor d cenv cx es G' tn' u` by
    (irule ghost_inv_at_local_window_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`G`,`es`,`func`,`s`,`sm`,`tn`] >>
     simp[] >> gvs[venom_state_component_equality] >> metis_tac[]) >>
  `sm.cs_next_id <= sc.cs_next_id` by
    (qspec_then `sm` mp_tac (Q.SPEC `Var src` ci_mono_compile_bytestring_src) >>
     simp[ci_mono_def]) >>
  `eval_operand (Var src) u = SOME p` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx e es0 sa sc s0 es v (Var src) u` by
    (irule convert_readonly_expr_post >> simp[] >>
     qexistsl_tac [`s`,`sm`,`Var src`] >> simp[] >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`u`,`G'`,`tn'`,`src`,`p`,`bs`] >> simp[] >>
  gvs[allocas_from_def, venom_state_component_equality,
      ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem slice_builtin_none_vv_full_from_runs:
  (!sa src len data sb func s p G tn capacity bs lo ctx explicit PG.
    compile_bytestring_src (Var src) sa = ((len,data),sb) /\
    fn_has_code sa sb func /\ not_fresh_at sa src /\
    lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
    32 <= capacity /\ w2n p + 32 < dimword (:256) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    w2n p + 32 <= s.vs_alloca_next /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
      eval_operand len u = SOME (n2w (LENGTH bs)) /\
      eval_operand data u = SOME (p+32w) /\
      op_taint tn' len = {} /\ op_prov G' len = NONE /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
      (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      u = s with vs_vars := u.vs_vars /\
      (!x. not_fresh_at sa x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!n. 32+n <= capacity ==>
         ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
      (?lp dp. len = Var lp /\ data = Var dp /\
         not_fresh_at sb lp /\ not_fresh_at sb dp)) /\
  (!sa buf sm src sb func cenv H ctx cx es s w tn lo explicit PG G.
    compile_alloc_buffer 32 sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand;src] sm = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\ alloca_history func s /\
    eval_operand src s = SOME w /\ op_taint tn src = {} /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?root p u t G' tn'.
      buf.buf_operand = Var root /\ not_fresh_at sb root /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G',tn')) /\
      t = mstore (w2n p) w u with vs_inst_idx := LENGTH sb.cs_current_insts /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      lookup_var root t = SOME p /\ ptr_covers G' tn' root t 32 /\
      mem_word_at (w2n p) t.vs_memory = w /\
      mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T /\
      (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn'.t_mem) /\
      alloca_history func t /\ allocas_from lo t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,32) /\
      w2n p+32 < dimword (:256) /\ w2n p+32 <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      u with <|vs_vars := s.vs_vars;vs_allocas := s.vs_allocas;
        vs_alloca_next := s.vs_alloca_next;vs_inst_idx := s.vs_inst_idx|> = s /\
      (!H':(bool # bytes32 # type_value) list # num list.
        stmt_state_rel H' ctx func cenv cx es s ==>
        stmt_state_rel H' ctx func cenv cx es u) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n p) 32 b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n p) 32 b len) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!j. j < s.vs_alloca_next /\ j IN tn'.t_mem ==> j IN tn.t_mem)) /\
  (!limit src start cnt N sa out sb func cenv ctx s bs p G tn i k n a result
    e args cx st0 es DF lo d explicit tops source PG.
    compile_slice_data limit (Var src) start cnt N sa = (out,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    eval_operand limit s = SOME (n2w (LENGTH bs)) /\
    lookup_var src s = SOME p /\ ptr_covers G tn src s (LENGTH bs) /\
    op_prov G limit = NONE /\ op_taint tn limit = {} /\
    eval_operand start s = SOME (n2w i) /\
    eval_operand cnt s = SOME (n2w k) /\
    op_prov G start = NONE /\ op_taint tn start = {} /\
    op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
    (!op x. MEM op [limit;Var src;start;cnt] /\ op = Var x ==>
      not_fresh_at sa x) /\
    (!l. limit <> Label l /\ start <> Label l /\ cnt <> Label l) /\
    mem_bytes_at (w2n p) (LENGTH bs) s.vs_memory = bs /\
    (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN tn.t_mem) /\
    w2n p + LENGTH bs < dimword (:256) /\
    w2n p + LENGTH bs <= s.vs_alloca_next /\
    i < dimword (:256) /\ k < dimword (:256) /\
    (i+k <= LENGTH bs ==> k <= n) /\
    ((a = BaseT (BytesT (Dynamic n)) /\
        result = BytesV (TAKE k (DROP i bs))) \/
     (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
        result = StringV (TAKE k (DROP i str)))) /\
    e = Builtin a (Slice n) args /\
    N = type_memory_bytes cenv a /\ 32+n <= N /\ N < dimword (:256) /\
    storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    (!tail. source (es with gas_obs := tail) =
      ((if i+k <= LENGTH bs then INL (Value result)
        else INR (Error (RuntimeError "evaluate_slice range"))),
       es with gas_obs := tail)) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
      (es,s,G,tn)
      (\H res ee HG tm t.
        res = INL (Value result) /\
        vv_post H ctx func cenv cx e es sa sb s ee (Value result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        vv_store_bound cx a a ee (Value result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
        ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
        ptr_buf_ok cenv e out HG t /\ ghost_kept_at lo cenv es sa G tn s HG tm)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)) ==>

  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = NONE ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "dynamic_run")
    (CONJUNCTS_THEN2 (mk_asm "fixed_run") (mk_asm "tail_run"))) >>
  asm "dynamic_run" (mp_then Any (mk_asm "dynamic_source_post")
    slice_dynamic_capture_source_post_from_run) >>
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by
    (irule body_inv_no_dalloca >> goal_assum (drule_at Any)) >>
  `well_typed_expr env (Builtin a (Slice n) args)` by fs[expr_body_pre_def] >>
  drule slice_typed_args >>
  disch_then (qx_choosel_then [`src`,`start`,`len`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `args = _` SUBST_ALL_TAC >>
  `body_exprs_full_ok cx [src;start;len]` by
    fs[vyperContextTheory.builtin_args_length_ok_def] >>
  `~is_extcode src` by
    (qpat_assum `code_slice_source (Slice n) [src;start;len] = NONE` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_extcode_ind >> simp[is_extcode_def]) >>
  `~is_self_code src` by
    (qpat_assum `~is_extcode src` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_self_code_ind >>
     simp[is_self_code_def,is_extcode_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env src es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type src) src es` by
    (`body_expr_full_ok cx src` by fs[body_exprs_full_ok_def] >>
     qpat_assum `body_expr_full_ok cx src`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`expr_type src`,`es`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  pure_rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by
    (qpat_assum `!bt xs. names_builtin bt xs ==> _`
      (qspec_then `Slice n` mp_tac) >> simp[]) >>
  qpat_x_assum `!bt xs. names_builtin bt xs ==> _` kall_tac >>
  reverse (Cases_on `is_bytestring_type (expr_type src)`)
  >- suspend "fixed_source" >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprSimSliceSourceTheory.slice_dispatch_bytestring,
    exprBopLoweringTheory.lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac
    `compile_bytestring_src src_op st1 = ((src_len,src_data),sc)` >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty start sc = (start_op,sd)` >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty len sd = (len_op,se)` >>
  `ci_mono st1 sc` by
    (qspecl_then [`src_op`,`st1`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_bytestring_src >> simp[]) >>
  drule_all exprSimSliceOrdinaryContextTheory.slice_ordinary_pipeline_context >>
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,
    compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv (expr_type src) (gas_shadow_expr src)
       shadow_sa = (shadow_src,shadow_s1)` >>
  qmatch_asmsub_rename_tac
    `compile_bytestring_src shadow_src shadow_s1 = ((shadow_len,shadow_data),shadow_sc)` >>
  `shadow_src = src_op /\ gas_shadow_state st1 shadow_s1` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_src = src_op` SUBST_ALL_TAC >>
  `shadow_len = src_len /\ shadow_data = src_data /\
   gas_shadow_state sc shadow_sc` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileBuiltinBytesTheory.gas_shadow_compiles_bytestring_src,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND,
       pairTheory.PAIR_EQ]) >>
  qpat_assum `shadow_len = src_len` SUBST_ALL_TAC >>
  qpat_assum `shadow_data = src_data` SUBST_ALL_TAC >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty (gas_shadow_expr start) shadow_sc =
       (shadow_start,shadow_sd)` >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty (gas_shadow_expr len) shadow_sd =
       (shadow_count,shadow_se)` >>
  `shadow_start = start_op /\ gas_shadow_state sd shadow_sd` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_start = start_op` SUBST_ALL_TAC >>
  `shadow_count = len_op /\ gas_shadow_state se shadow_se` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_count = len_op` SUBST_ALL_TAC >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  `ci_mono shadow_s1 shadow_sc` by
    (qspecl_then [`src_op`,`shadow_s1`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_bytestring_src >> simp[]) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_data _ _ _ _ _ shadow_se) = (_,shadow_sb)`
    (mp_then Any mp_tac exprSimSliceOrdinaryContextTheory.slice_ordinary_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`st1`,`shadow_sa`,`shadow_s1`,
    `src_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ source_post _` >>
  simp[Once slice_eval_ordinary] >>
  simp[eval_exprs_cons_action,vyperStateTheory.bind_assoc] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,vyperStateTheory.return_def] >>
  simp[vyperStateTheory.bind_return,vyperStateTheory.bind_assoc] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      (reverse conj_tac >-
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_state_reads,
          vyperStorageTraceTheory.storage_trace_frame_lifts,
          exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
      gen_tac >> BETA_TAC) >>
    simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists_tac `\H res ee G tn t. source_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
  rpt gen_tac >> strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> source_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `source_post`, NoAsms] >> strip_tac >>
  qpat_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- REFL_TAC >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
   expr_result_typed env src (Value v)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env src
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qspecl_then [`cenv`,`cx`,`env`,`src`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `INL v`,`mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `?vt. evaluate_type (get_tenv cx) (expr_type src) = SOME vt /\
        value_has_type vt v` by
    fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >>
  `?bt. expr_type src = BaseT bt` by
    (qpat_assum `_ \/ _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `post_value_type cenv src = BaseT bt` by
    (irule EQ_TRANS >> qexists_tac `expr_type src` >> simp[] >>
     irule loweringPostsTheory.post_value_type_bytestring >> simp[]) >>
  `(?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap)` by
    (qpat_assum `is_bytestring_type (expr_type src)` mp_tac >>
     qpat_assum `expr_type src = BaseT bt` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bt` >>
     simp[compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  `!z. src_op = Var z ==> not_fresh_at st1 z` by
    (qpat_assum `lower_value compile_expr cenv (expr_type src) src sa = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `!l. src_op <> Label l` by
    (drule_all exprSimSliceCaptureTheory.slice_source_operand_not_label >> simp[]) >>
  `sa.cs_next_var <= st1.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `(?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap) /\
   evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\
   ptr_val_ok cx (BaseT bt) v src_op G1 tn1 t /\
   expr_sim_inv cenv cx env mid` by fs[] >>
  asm "dynamic_source_post" drule >>
  simp[] >>
  disch_then (qspecl_then [`vt`,`env`,`G1`,`tn1`,
    `DF (storage_trace_horizon mid.storage_trace)`,`lo`,`d`,`lo`,
    `gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choose_then `captured` (qx_choose_then `capture_G`
    (qx_choose_then `capture_tn` (qx_choose_then `src_name`
      (qx_choose_then `src_ptr` (qx_choose_then `source_bytes`
        (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 assume_tac
            (CONJUNCTS_THEN2 assume_tac strip_assume_tac))))))))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx src es sa st1 s0 mid v src_op t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> source_post _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> simp[NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid captured` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx mid t` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- simp[]) >> simp[loweringPostsTheory.expr_post_def,NoAsms] >>
        strip_tac >> asm_rewrite_tac[]) >>
     irule stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> qexists_tac `st1` >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid capture_G capture_tn captured` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `local_ptrs_rel func cenv mid.scopes t` by
       fs[loweringPostsTheory.expr_post_def,exprLoweringPropsTheory.stmt_state_rel_def,
          loweringStateRelDefsTheory.state_rel_def] >>
     `stor_taint_ok_at (DF H) capture_tn captured` by
       (qpat_assum `ghost_inv_at (DF H) lo _ _ _ _ _ _ _` mp_tac >>
        qpat_assum `captured = t with vs_vars := _` mp_tac >>
        qpat_assum `capture_tn.t_stor = tn1.t_stor` mp_tac >>
        qpat_assum `capture_tn.t_trans = tn1.t_trans` mp_tac >>
        qpat_assum `capture_tn.t_imm = tn1.t_imm` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[bodyPtrDefsTheory.ghost_inv_at_def,
          bodyPtrDefsTheory.stor_taint_ok_at_def,venomStateTheory.venom_state_component_equality]) >>
     irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` (irule_at Any) >>
     qexistsl_tac [`st1`,`func`] >> simp[] >>
     qpat_assum `captured = t with vs_vars := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand src_op captured = SOME src_ptr` by
    (asm_x "dynamic_run" kall_tac >> asm_x "fixed_run" kall_tac >>
     asm_x "tail_run" kall_tac >> asm_x "dynamic_source_post" kall_tac >>
     gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `st1.cs_next_id <= sc.cs_next_id` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx src es sa sc s0 mid v src_op captured` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule exprSimConvertBytesTheory.convert_readonly_expr_post >> simp[] >>
     qexistsl_tac [`t`,`st1`,`src_op`] >> simp[] >>
     qpat_assum `captured = t with vs_vars := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  qabbrev_tac `capture_state = captured with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid capture_state /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid capture_G capture_tn capture_state` by
    (gen_tac >> disch_tac >>
     `expr_post H ctx func cenv cx src es sa sc s0 mid v src_op captured` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     `ghost_inv_at (DF H) lo d cenv cx mid capture_G capture_tn captured` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     conj_tac >- fs[Abbr `capture_state`,exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       loweringPostsTheory.expr_post_def] >>
     conj_tac >- fs[loweringPostsTheory.expr_post_def] >>
     qspecl_then [`DF (H:(bool # bytes32 # type_value) list # num list)`,
       `lo`,`d`,`cenv`,`cx`,`mid`,`mid`,`capture_G`,`capture_G`,
       `capture_tn`,`capture_tn`,`captured`,`capture_state`,`st1`]
       mp_tac ghost_inv_at_exterior_frame >>
     (impl_tac >- (simp[Abbr `capture_state`,venomStateTheory.lookup_var_def,NoAsms] >>
                   asm_rewrite_tac[])) >> simp[]) >>
  qpat_assum `compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`
    (mp_then Any strip_assume_tac slice_bytestring_src_control) >>
  `alloca_history func capture_state` by
    (qunabbrev_tac `capture_state` >>
     irule emitted_alloca_history >>
     qpat_assum `run_inst_seq (emitted_insts st1 sc) t = OK captured`
       (irule_at Any) >>
     qexists_tac `st1` >> simp[] >> reverse conj_tac >-
       (qpat_assum `compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`
          (mp_then Any mp_tac slice_bytestring_src_zero_code) >>
        simp[listTheory.EVERY_MEM]) >>
     fs[loweringPostsTheory.expr_post_def,exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `body_exprs_full_ok cx [start;len]` by
    (qpat_assum `body_exprs_full_ok cx [src;start;len]`
       (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
     disch_then irule >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env start mid` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`mid`] mp_tac) >> fs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty start mid` by
    (`body_expr_full_ok cx start` by fs[body_exprs_full_ok_def] >>
     qpat_assum `body_expr_full_ok cx start`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`ty`,`mid`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `sa.cs_next_var <= sc.cs_next_var /\ st1.cs_next_var <= sc.cs_next_var` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `s0.vs_alloca_next <= captured.vs_alloca_next` by
    (qpat_assum `captured = t with vs_vars := _`
       (mp_tac o AP_TERM ``\ss:venom_state. ss.vs_alloca_next``) >>
     simp[NoAsms] >> disch_then SUBST1_TAC >> simp[]) >>
  `return_buf_frame d cenv sc captured` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ captured`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sc capture_state` by
    (simp[Abbr `capture_state`] >>
     qpat_assum `return_buf_frame d cenv sc captured` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `d` >- simp[loweringPostsTheory.return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME buf) _ _ _` >> PairCases_on `buf` >>
     simp[loweringPostsTheory.return_buf_frame_def,venomStateTheory.lookup_var_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> simp[]) >>
  `~capture_state.vs_halted /\
   capture_state.vs_current_bb = sc.cs_current_bb /\
   capture_state.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (fs[Abbr `capture_state`,venomStateTheory.venom_state_component_equality]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok mid` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     first_assum (irule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sc`,`sd`,`shadow_sc`,`shadow_sd`,
    `start_op`,`capture_state`,`capture_G`,`capture_tn`] mp_tac) >>
  (impl_tac >- (simp[] >>
    asm_x "dynamic_run" kall_tac >> asm_x "fixed_run" kall_tac >>
    asm_x "tail_run" kall_tac >> asm_x "dynamic_source_post" kall_tac >>
    qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
    qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ (mid,capture_state,capture_G,capture_tn) start_post _` >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`capture_G`,`capture_state`,`capture_tn`] >>
  simp[] >>
  BETA_TAC >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  (irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      (reverse conj_tac >-
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_state_reads,
          vyperStorageTraceTheory.storage_trace_frame_lifts,
          exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
      gen_tac >> BETA_TAC) >>
    simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists_tac `\H res ee G tn t. start_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx start) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> pop_assum (mp_tac o BETA_RULE) >>
          POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `res` >>
          simp[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
  qx_genl_tac [`start_marks`,`start_res`,`start_mid`,`start_G`,`start_tn`,`start_state`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon start_mid.storage_trace)
      start_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon start_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `start_post`,NoAsms] >> strip_tac >>
  rename1 `start_res = INL start_v` >>
  qpat_assum `start_res = INL start_v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `start_v` >> conj_tac >- REFL_TAC >>
  `start_mid with gas_obs := [] = start_mid` by
    (qpat_assum `start_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (start_mid with gas_obs := [])` by
    (qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` mp_tac) >> strip_tac >>
     qspecl_then [`cenv`,`cx`,`env`,`start`,
       `mid with gas_obs := gas_explicit start_marks capture_state.vs_gas_readings ++ []`,
       `INL start_v`,`start_mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `body_exprs_full_ok cx [len]` by
    (qpat_assum `body_exprs_full_ok cx [start;len]`
       (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
     disch_then irule >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env len start_mid` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`len`,`start_mid`] mp_tac) >> fs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty len start_mid` by
    (`body_expr_full_ok cx len` by fs[body_exprs_full_ok_def] >>
     qpat_assum `body_expr_full_ok cx len`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`ty`,`start_mid`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `return_buf_frame d cenv sd start_state` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`capture_state`,`sc`] >> simp[] >>
     conj_tac
     >- (qpat_assum `expr_post _ _ _ _ _ start mid sc sd capture_state start_mid start_v start_op start_state`
           (ACCEPT_TAC o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def)))) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    (qpat_assum `ci_mono sc sd` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sc` >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!H. valid_horizon cx st0 H start_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx start_mid start_state /\
     storage_well_formed_on cx start_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx start_mid start_G start_tn start_state` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok start_mid` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     first_assum (irule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sd`,`se`,`shadow_sd`,`shadow_se`,
    `len_op`,`start_state`,`start_G`,`start_tn`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
    qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ (start_mid,start_state,start_G,start_tn) length_post _` >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  (irule gas_outcome_full_bind_all >>
   conj_tac >- (rpt gen_tac >> BETA_TAC >>
     rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
       simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
         vyperStorageTraceTheory.storage_trace_frame_lifts,
         vyperStorageTraceTheory.storage_trace_frame_return,
         exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
   conj_tac >- (rpt strip_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
     goal_assum (drule_at Any) >> fs[]) >>
   conj_tac >- (rpt strip_tac >>
     qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
   conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
   qexists_tac `\H res ee G tn t. length_post H res ee G tn t /\
     ee.gas_obs = [] /\ ~t.vs_halted` >>
   reverse conj_tac
   >- (irule gas_outcome_full_post_source >>
       qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx len) _) _ _ _`
         (irule_at Any) >>
       reverse conj_tac
       >- (rpt strip_tac >> pop_assum (mp_tac o BETA_RULE) >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `res` >>
           simp[exprSimDefsTheory.expr_exit_INL] >>
           rename1 `expr_exit (INR exc) r` >>
           qspec_then `Value` (qspec_then `INR exc`
             (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
             exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
   qx_genl_tac [`length_marks`,`length_res`,`length_mid`,`length_G`,`length_tn`,`length_state`] >>
   strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
   `valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       length_mid.storage_trace` by
     fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
   qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==> _`
     (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
   (impl_tac >- simp[]) >>
   simp[Abbr `length_post`,NoAsms] >> strip_tac >>
   rename1 `length_res = INL length_v` >>
   qpat_assum `length_res = INL length_v` SUBST_ALL_TAC >>
   disj1_tac >> qexists_tac `length_v` >> conj_tac >- REFL_TAC >>
   `length_mid with gas_obs := [] = length_mid` by
     (qpat_assum `length_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `expr_sim_inv cenv cx env (length_mid with gas_obs := [])` by
     (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]` mp_tac) >> strip_tac >>
      qspecl_then [`cenv`,`cx`,`env`,`len`,
        `start_mid with gas_obs := gas_explicit length_marks start_state.vs_gas_readings ++ []`,
        `INL length_v`,`length_mid with gas_obs := []`] mp_tac
        exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
   `MAP FDOM mid.scopes = MAP FDOM start_mid.scopes /\
    ?i. start_v = IntV (&i) /\ i < dimword (:256) /\
        eval_operand start_op start_state = SOME (n2w i)` by
     (qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ start_mid start_v start_op start_state`
        (mp_then (Pos (el 4)) mp_tac (INST_TYPE [alpha |-> ``:256``]
          exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
      disch_then (qspecl_then [`gas_explicit start_marks capture_state.vs_gas_readings`,`env`] mp_tac) >>
      `start_mid with gas_obs := [] = start_mid` by
        (qpat_assum `start_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
   rename1 `start_v = IntV (&i)` >>
   qpat_assum `start_v = IntV (&i)` SUBST_ALL_TAC >>
   `MAP FDOM start_mid.scopes = MAP FDOM length_mid.scopes /\
    ?k. length_v = IntV (&k) /\ k < dimword (:256) /\
        eval_operand len_op length_state = SOME (n2w k)` by
     (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      qpat_assum `expr_post _ _ _ _ _ len _ _ _ _ length_mid length_v len_op length_state`
        (mp_then (Pos (el 4)) mp_tac (INST_TYPE [alpha |-> ``:256``]
          exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
      disch_then (qspecl_then [`gas_explicit length_marks start_state.vs_gas_readings`,`env`] mp_tac) >> simp[]) >>
   rename1 `length_v = IntV (&k)` >>
   qpat_assum `length_v = IntV (&k)` SUBST_ALL_TAC >>
   `!H. valid_horizon cx st0 H length_mid.storage_trace ==>
        valid_horizon cx st0 H start_mid.storage_trace` by
     (rpt strip_tac >>
      qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   `!H. valid_horizon cx st0 H start_mid.storage_trace ==>
        valid_horizon cx st0 H mid.storage_trace` by
     (rpt strip_tac >>
      qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   `valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       start_mid.storage_trace /\
    valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       mid.storage_trace` by
     (conj_asm1_tac >> first_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
   qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _ /\ start_mid.gas_obs = [] /\ _`
     (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
   (impl_tac >- simp[]) >> simp[NoAsms] >> strip_tac >>
   `stmt_state_rel (storage_trace_horizon length_mid.storage_trace)
       ctx func cenv cx mid capture_state` by
     (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ capture_state /\ _`
        (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >> simp[]) >>
   `expr_val_at cenv cx (BaseT bt) sa sc mid v src_op capture_state` by
     (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post _ _ _ _ _ src es sa sc s0 mid v src_op captured`
        (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (mp_tac o MATCH_MP (cj 4 (iffLR loweringPostsTheory.expr_post_def))) >>
      simp[Abbr `capture_state`,slice_capture_value_index]) >>
   `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
    sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id` by
     fs[exprLoweringPropsTheory.ci_mono_def] >>
   `!x. src_op = Var x ==> not_fresh_at sc x` by
     (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `st1` >> simp[]) >>
   `~is_word_type (BaseT bt)` by fs[compileEnvTheory.is_word_type_def] >>
   `eval_operand src_op capture_state = SOME src_ptr /\
    mem_bytes_at (w2n src_ptr + 32) (LENGTH source_bytes)
      capture_state.vs_memory = source_bytes` by
     (simp[Abbr `capture_state`,instIdxIndepTheory.eval_op_inst_idx,NoAsms] >>
      asm_rewrite_tac[]) >>
   `!j. w2n src_ptr + 32 <= j /\
        j < w2n src_ptr + 32 + LENGTH source_bytes ==> j NOTIN capture_tn.t_mem` by
     (gen_tac >> disch_tac >>
      qpat_assum `!j. w2n src_ptr <= j /\ _ ==> _` irule >> decide_tac) >>
   `wb_frame cenv mid start_mid sc capture_state start_state` by
     (qpat_assum `expr_post _ _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state`
        (mp_then Any MATCH_ACCEPT_TAC expr_post_frame)) >>
   `!n b sz. local_region cenv start_mid.scopes start_state n b sz <=>
              local_region cenv mid.scopes capture_state n b sz` by
     (rpt gen_tac >> drule_all log_frame_local_region >> simp[]) >>
   `ghost_kept_at lo cenv mid sc capture_G capture_tn capture_state length_G length_tn` by
     (irule ghost_kept_at_trans >> goal_assum (drule_at Any) >>
      qexistsl_tac [`start_G`,`sd`,`start_tn`] >> simp[] >>
      qpat_assum `expr_post _ _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_post_def]) >>
   `ghost_kept cenv mid sc capture_G capture_tn capture_state length_G length_tn` by
     (qpat_assum `ghost_kept_at lo cenv mid sc capture_G capture_tn capture_state length_G length_tn`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
       simp[ghost_kept_def,ghost_kept_at_def] >> metis_tac[]) >>
   `log_arg_clear cenv cx (BaseT bt) v` by
     (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
   `mem_bytes_at (w2n src_ptr + 32) (LENGTH source_bytes) length_state.vs_memory = source_bytes` by
     (qpat_assum `expr_post _ _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state`
        (mp_then (Pos (el 15)) mp_tac (cj 2 slice_dynamic_payload_two_operands)) >>
      disch_then (fn th =>
        qpat_assum `expr_post _ _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
          (mp_then Any mp_tac th)) >>
      disch_then (fn th =>
        qpat_assum `expr_val_at cenv cx (BaseT bt) sa sc mid v src_op capture_state`
          (mp_then Any mp_tac th)) >>
      disch_then irule >> simp[] >>
      conj_tac >> qexists_tac `env`
      >- first_assum MATCH_ACCEPT_TAC >>
      qpat_assum `expr_sim_inv cenv cx env (start_mid with gas_obs := [])`
        (MATCH_ACCEPT_TAC o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_gas_obs])) >>
   `!j. w2n src_ptr + 32 <= j /\ j < w2n src_ptr + 32 + LENGTH source_bytes ==>
        j NOTIN length_tn.t_mem` by
     (rpt strip_tac >> spose_not_then assume_tac >>
      `w2n src_ptr <= j /\ j < w2n src_ptr + val_footprint vt v` by decide_tac >>
      drule_all bop_argument_taint_kept >> disch_tac >>
      qpat_assum `!j. w2n src_ptr + 32 <= j /\ _ ==> j NOTIN capture_tn.t_mem`
        (qspec_then `j` mp_tac) >> simp[]) >>
   `!op w. (!z. op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
           (!l. op <> Label l) /\ eval_operand op capture_state = SOME w ==>
           eval_operand op length_state = SOME w` by
     (qpat_assum `expr_post _ _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state` mp_tac >>
      qpat_assum `expr_post _ _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[slice_two_posts_operands]) >>
   `!dp n. not_fresh_at sc dp /\ not_fresh_at sd dp /\
           ptr_covers capture_G capture_tn dp capture_state n ==>
           ptr_covers length_G length_tn dp length_state n` by
     (qx_genl_tac [`kept_dp`,`kept_n`] >> strip_tac >>
      `?kept_w. eval_operand (Var kept_dp) capture_state = SOME kept_w` by
        (qpat_assum `ptr_covers capture_G capture_tn kept_dp capture_state kept_n` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[ptr_covers_def,eval_operand_def] >> metis_tac[]) >>
      `eval_operand (Var kept_dp) length_state = SOME kept_w` by
        (qpat_assum `!op w. (!z. op = Var z ==> _ /\ _) /\ _ /\ _ ==> _` irule >> simp[]) >>
      irule ghost_kept_ptr_covers >>
      goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
      qexists_tac `kept_w` >> simp[]) >>
   `(!x. start_op = Var x ==> not_fresh_at sd x) /\
    (!l. start_op <> Label l)` by
     (qspecl_then [`cenv`,`cx`,`env`,`start`,`mid`,`ty`,`sc`,`start_op`,`sd`]
        mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
      (impl_tac >- simp[compileEnvTheory.is_word_type_def]) >> strip_tac >> simp[]) >>
   `(!x. len_op = Var x ==> not_fresh_at se x) /\
    (!l. len_op <> Label l)` by
     (qspecl_then [`cenv`,`cx`,`env`,`len`,`start_mid`,`ty`,`sd`,`len_op`,`se`]
        mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
      (impl_tac >- simp[compileEnvTheory.is_word_type_def]) >> strip_tac >> simp[]) >>
   `op_prov start_G start_op = NONE /\ op_taint start_tn start_op = {} /\
    op_prov length_G len_op = NONE /\ op_taint length_tn len_op = {}` by
     (qpat_assum `ptr_val_ok _ _ _ start_op start_G start_tn start_state` mp_tac >>
      qpat_assum `ptr_val_ok _ _ _ len_op length_G length_tn length_state` mp_tac >>
      fs[bodyPtrDefsTheory.ptr_val_ok_def,loweringPostsTheory.post_value_type_def,
         compileEnvTheory.is_word_type_def]) >>
   `eval_operand start_op length_state = SOME (n2w i)` by
     (qpat_assum `expr_post _ _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
        (mp_then Any mp_tac exprSimSliceOrdinaryFrameTheory.slice_post_operands) >>
      disch_then (qspecl_then [`start_op`,`n2w i`] mp_tac) >> simp[]) >>
   `op_prov length_G start_op = NONE /\ op_taint length_tn start_op = {}` by
     (qpat_assum `ghost_kept_at lo cenv start_mid sd start_G start_tn start_state length_G length_tn`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
      qpat_assum `!x. start_op = Var x ==> not_fresh_at sd x` mp_tac >>
      qpat_assum `op_prov start_G start_op = NONE` mp_tac >>
      qpat_assum `op_taint start_tn start_op = {}` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_op` >>
      simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
   rename1 `src_len = Var limit_name` >>
   rename1 `src_data = Var data_name` >>
   `not_fresh_at sd limit_name /\ not_fresh_at sd data_name` by
     (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sc` >> simp[]) >>
   `eval_operand src_len capture_state = SOME (n2w (LENGTH source_bytes)) /\
    eval_operand src_data capture_state = SOME (src_ptr+32w)` by
     simp[Abbr `capture_state`,instIdxIndepTheory.eval_op_inst_idx] >>
   `eval_operand src_len length_state = SOME (n2w (LENGTH source_bytes)) /\
    eval_operand src_data length_state = SOME (src_ptr+32w)` by
     (conj_tac >>
      qpat_assum `!op w. (!z. op = Var z ==> _ /\ _) /\ _ /\ _ ==> _` irule >>
      simp[] >> metis_tac[]) >>
   `ptr_covers capture_G capture_tn data_name captured (LENGTH source_bytes)` by
     (qpat_assum `ptr_covers capture_G capture_tn _ captured (LENGTH source_bytes)` mp_tac >>
      qpat_x_assum `src_data = Var data_name` mp_tac >>
      qpat_assum `src_data = Var _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
   `ptr_covers capture_G capture_tn data_name capture_state (LENGTH source_bytes)` by
     simp[Abbr `capture_state`] >>
   `ptr_covers length_G length_tn data_name length_state (LENGTH source_bytes)` by
     (qpat_assum `!dp n. not_fresh_at sc dp /\ not_fresh_at sd dp /\ _ ==> _`
        (qspecl_then [`data_name`,`LENGTH source_bytes`] mp_tac) >> simp[]) >>
   `op_prov length_G src_len = NONE /\ op_taint length_tn src_len = {}` by
     (qpat_assum `ghost_kept_at lo cenv mid sc capture_G capture_tn capture_state start_G start_tn`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
      qpat_assum `ghost_kept_at lo cenv start_mid sd start_G start_tn start_state length_G length_tn`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
      qpat_assum `op_prov capture_G src_len = NONE` mp_tac >>
      qpat_assum `op_taint capture_tn src_len = {}` mp_tac >>
      qpat_assum `src_len = Var limit_name` mp_tac >>
      qpat_assum `not_fresh_at sc limit_name` mp_tac >>
      qpat_assum `not_fresh_at sd limit_name` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
   `not_fresh_at se limit_name /\ not_fresh_at se data_name` by
     (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sd` >> simp[]) >>
   `!x. start_op = Var x ==> not_fresh_at se x` by
     (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sd` >> simp[]) >>
   `w2n src_ptr + 32 + LENGTH source_bytes <= capture_state.vs_alloca_next` by
     (qpat_assum `stmt_state_rel _ ctx func cenv cx mid capture_state`
        (mp_then Any mp_tac abiEncodeOwnershipTheory.abi_encode_owned_footprint_frontier) >>
      disch_then drule >> disch_then drule >>
      disch_then (qspec_then `src_ptr` mp_tac) >>
      (impl_tac >- fs[]) >> fs[]) >>
   `expr_val_rel cx (BaseT bt) v src_op capture_state` by
     (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post _ _ _ _ _ src es sa sc s0 mid v src_op captured`
        (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (mp_tac o cj 3 o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
      qpat_assum `post_value_type cenv src = BaseT bt` mp_tac >>
      qunabbrev_tac `capture_state` >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[loweringPostsTheory.expr_val_rel_def,
           instIdxIndepTheory.eval_op_inst_idx]) >>
   `log_arg_rel cenv cx sa sc mid capture_state (src_op,BaseT bt) v` by
     (fs[stmtSimLogArgsTheory.log_arg_rel_def] >>
      irule stmtSimLogArgsTheory.log_arg_clear_base >> goal_assum (drule_at Any)) >>
   `w2n src_ptr + 32 + LENGTH source_bytes < dimword (:256)` by
     (mp_tac (Q.INST [`H` |-> `storage_trace_horizon length_mid.storage_trace`,
        `es` |-> `mid`,`s` |-> `capture_state`,`ty` |-> `BaseT bt`,
        `sb` |-> `sc`,`tv` |-> `vt`,`p` |-> `src_ptr`,`op` |-> `src_op`]
        (INST_TYPE [alpha |-> ``:256``]
          stmtSimLogTopicsTheory.log_arg_footprint_bound)) >>
      (impl_tac >- fs[]) >> fs[]) >>
   `w2n (src_ptr+32w) = w2n src_ptr+32` by
     (simp[wordsTheory.w2n_add_2,wordsTheory.w2n_n2w] >> decide_tac) >>
   `w2n (src_ptr+32w) + LENGTH source_bytes <= length_state.vs_alloca_next` by
     (qpat_assum `w2n src_ptr + 32 + LENGTH source_bytes <= capture_state.vs_alloca_next` mp_tac >>
      qpat_assum `capture_state.vs_alloca_next <= start_state.vs_alloca_next` mp_tac >>
      qpat_assum `start_state.vs_alloca_next <= length_state.vs_alloca_next` mp_tac >>
      qpat_assum `w2n (src_ptr+32w) = w2n src_ptr+32` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
   `LENGTH source_bytes <= bytelike_type_bound (expr_type src)` by
     (qpat_assum `evaluate_type (get_tenv cx) (expr_type src) = SOME vt` mp_tac >>
      qpat_assum `value_has_type vt v` mp_tac >>
      qpat_assum `expr_type src = BaseT bt` mp_tac >>
      qpat_assum `bt = _` mp_tac >>
      qpat_assum `v = BytesV source_bytes \/
        (?str. v = StringV str /\ source_bytes = MAP (n2w o ORD) str)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def,
        vyperTypingTheory.value_has_type_def,
        vyperTypeSystemTheory.bytelike_type_bound_def]) >>
   `(i+k <= LENGTH source_bytes ==> k <= n)` by
     (drule slice_capacity_alternatives >> strip_tac
      >- (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
            (qspec_then `[]` mp_tac) >>
          qpat_assum `len = Literal _ (IntL _)` mp_tac >>
          qpat_assum `_ <= &n` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
          gvs[vyperInterpreterTheory.evaluate_def,
            vyperStateTheory.bind_def,vyperStateTheory.return_def,
            vyperStateTheory.lift_sum_def,vyperStateTheory.read_result_def,
            vyperValueOperationTheory.evaluate_literal_def] >> intLib.ARITH_TAC) >>
      decide_tac) >>
   `?slice_result.
      ((a = BaseT (BytesT (Dynamic n)) /\
         slice_result = BytesV (TAKE k (DROP i source_bytes))) \/
       (?str. a = BaseT (StringT n) /\
         source_bytes = MAP (n2w o ORD) str /\
         slice_result = StringV (TAKE k (DROP i str)))) /\
      !acc. evaluate_builtin cx acc a (Slice n)
        (MAP expr_type [src;start;len]) [v;IntV (&i);IntV (&k)] =
        if i+k <= LENGTH source_bytes then INL slice_result
        else INR (RuntimeError "evaluate_slice range")` by
     (qpat_assum `(a = BaseT (BytesT (Dynamic n)) /\ _) \/ _` mp_tac >>
      qpat_assum `expr_type src = BaseT bt` mp_tac >>
      qpat_assum `bt = _` mp_tac >>
      qpat_assum `evaluate_type (get_tenv cx) (expr_type src) = SOME vt` mp_tac >>
      qpat_assum `value_has_type vt v` mp_tac >>
      qpat_assum `v = BytesV source_bytes \/
        (?str. v = StringV str /\ source_bytes = MAP (n2w o ORD) str)` mp_tac >>
      qpat_assum `i+k <= LENGTH source_bytes ==> k <= n` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def,vyperTypingTheory.value_has_type_def] >>
      simp[vyperContextTheory.evaluate_builtin_def,slice_bytes_nat,slice_string_nat] >>
       Cases_on `i+k <= LENGTH source_bytes` >> fs[] >>
       qmatch_goalsub_rename_tac `StringV (TAKE k (DROP i chars))` >>
       qexists_tac `StringV (TAKE k (DROP i chars))` >> simp[] >>
       qexists_tac `chars` >> simp[]) >>
   `32+n <= type_memory_bytes cenv a` by
     (qpat_assum `a = BaseT _` mp_tac >>
      qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      fs[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def]) >>
   `type_memory_bytes cenv a < dimword (:256)` by
     (qpat_assum `expr_body_pre cenv cx env (Builtin a (Slice n) _) es` mp_tac >>
      qpat_assum `a = BaseT _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def] >>
      simp[wordsTheory.dimword_def] >> decide_tac) >>
   `?out. compile_slice_data src_len src_data start_op len_op
       (type_memory_bytes cenv a) se = (out,sb) /\
     vv = LocatedValue a (mk_ptr out LocMemory)` by
     (qpat_assum `as_ptr_val a LocMemory _ = (vv,sb)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      Cases_on `compile_slice_data src_len src_data start_op len_op
        (type_memory_bytes cenv a) se` >>
      simp[as_ptr_val_def] >> strip_tac >> gvs[]) >>
   `!H. valid_horizon cx st0 H length_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx length_mid length_state /\
     storage_well_formed_on cx length_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx length_mid length_G length_tn length_state` by
     (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
        _ H (INL _) length_mid length_G length_tn length_state /\ _`
        (qspec_then `H` mp_tac) >>
      qpat_assum `valid_horizon cx st0 H length_mid.storage_trace` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
   `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at se x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at se x)` by
     (`sa.cs_next_var <= se.cs_next_var` by
        (qpat_assum `ci_mono sa st1` mp_tac >>
         qpat_assum `ci_mono st1 sc` mp_tac >>
         qpat_assum `ci_mono sc sd` mp_tac >>
         qpat_assum `ci_mono sd se` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
      qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sa x` mp_tac >>
      qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sa x` mp_tac >>
      qpat_assum `sa.cs_next_var <= se.cs_next_var` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      metis_tac[]) >>
   `evaluate_slice v (IntV (&i)) (IntV (&k)) n =
      if i+k <= LENGTH source_bytes then INL slice_result
      else INR (RuntimeError "evaluate_slice range")` by
     (qpat_assum `!acc. evaluate_builtin _ _ _ _ _ _ = _`
        (qspec_then `length_mid.accounts` mp_tac) >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[vyperContextTheory.evaluate_builtin_def]) >>
   `compile_slice_data src_len (Var data_name) start_op len_op
       (type_memory_bytes cenv a) se = (out,sb)` by
     (qpat_assum `compile_slice_data _ _ _ _ _ se = (out,sb)` mp_tac >>
      qpat_assum `src_data = Var data_name` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
   qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ tail_source _ _ _` >>
   `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 tail_source (length_mid,length_state,length_G,length_tn)
      (\H res ee HG tm t.
        res = INL (Value slice_result) /\
        vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
          length_mid se sb length_state ee (Value slice_result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        vv_store_bound cx a a ee (Value slice_result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ length_state.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
        ptr_vv_ok cx a (Value slice_result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
        ptr_buf_ok cenv (Builtin a (Slice n) [src;start;len]) out HG t /\
        ghost_kept_at lo cenv length_mid se length_G length_tn length_state HG tm)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)` by
    (qpat_assum `a = BaseT _` SUBST_ALL_TAC >>
     asm "tail_run" irule >>
     qpat_assum `compile_slice_data src_len (Var data_name) _ _ _ se = (out,sb)`
       (irule_at Any) >>
     qexistsl_tac [`src_ptr+32w`,`n`,`k`,`i`,`source_bytes`,`[src;start;len]`] >>
     simp[IgnAsm `source_bytes = _`,arithmeticTheory.ADD_COMM,
        venomStateTheory.eval_operand_def] >>
     conj_tac
     >- (qpat_assum `not_fresh_at se limit_name` mp_tac >>
         qpat_assum `not_fresh_at se data_name` mp_tac >>
         qpat_assum `!x. start_op = Var x ==> not_fresh_at se x` mp_tac >>
         qpat_assum `!x. len_op = Var x ==> not_fresh_at se x` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     reverse conj_tac
     >- (qpat_assum `eval_operand src_data length_state = SOME (src_ptr+32w)` mp_tac >>
         qpat_assum `src_data = Var data_name` mp_tac >>
         rpt (qpat_x_assum `source_bytes = _` mp_tac) >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
     qunabbrev_tac `tail_source` >>
     qpat_assum `!acc. evaluate_builtin _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `slice_result = _` mp_tac >>
     rpt (qpat_x_assum `expr_type src = _` mp_tac) >>
     qpat_assum `bt = _` mp_tac >>
     qpat_assum `expr_type start = _` mp_tac >>
     qpat_assum `expr_type len = _` mp_tac >>
     rpt (qpat_x_assum `source_bytes = _` mp_tac) >>
     qpat_assum `eval_operand src_data length_state = SOME (src_ptr+32w)` mp_tac >>
     qpat_assum `src_data = Var data_name` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[] >>
     simp[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
       vyperStateTheory.lift_sum_def] >>
     IF_CASES_TAC >>
     simp[vyperStateTheory.return_def,vyperStateTheory.raise_def,
       venomStateTheory.eval_operand_def] >> metis_tac[]) >>
   qunabbrev_tac `tail_source` >>
   (irule gas_outcome_full_post_source >>
   qpat_assum `gas_outcome_full _ _ _ _ _
     (length_mid,length_state,length_G,length_tn) _ _` (irule_at Any) >>
   reverse conj_tac >- simp[] >>
   qx_genl_tac [`H`,`res`,`ee`,`HG`,`tm`,`target`] >> strip_tac >>
   RULE_ASSUM_TAC BETA_RULE >>
   qpat_x_assum `res = INL _ /\ _` strip_assume_tac >>
   qpat_assum `res = INL _` SUBST_ALL_TAC >>
   `ee with gas_obs := [] = ee` by
     (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `length_mid with gas_obs := [] = length_mid` by
     (qpat_assum `length_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `ee = length_mid` by
     (qpat_assum `!tail. bind get_accounts _ _ = _` (qspec_then `[]` mp_tac) >>
      qpat_assum `evaluate_slice v (IntV (&i)) (IntV (&k)) n = _` mp_tac >>
      qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
      qpat_assum `length_mid with gas_obs := [] = length_mid` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      Cases_on `i+k <= LENGTH source_bytes` >>
      fs[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
         vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
         vyperStateTheory.raise_def,vyperContextTheory.evaluate_builtin_def] >>
      qpat_assum `evaluate_slice v (IntV (&i)) (IntV (&k)) n = _`
        (fn eq => full_simp_tac (srw_ss())
          [eq,vyperStateTheory.return_def,vyperStateTheory.raise_def]) >>
      qpat_assum `length_mid with gas_obs := _ = ee with gas_obs := []`
        (mp_tac o Q.AP_TERM `\st:evaluation_state. st with gas_obs := []`) >> simp[]) >>
   qpat_assum `ee = length_mid` SUBST_ALL_TAC >>
   `valid_horizon cx st0 H start_mid.storage_trace` by
     (qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
        valid_horizon _ _ H start_mid.storage_trace` irule >> simp[]) >>
   `valid_horizon cx st0 H mid.storage_trace` by
     (qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==>
        valid_horizon _ _ H mid.storage_trace` irule >> simp[]) >>
   qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==>
     (?v. INL _ = INL v /\ expr_post H _ _ _ _ start _ _ _ _ _ _ _ _ /\ _) /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
   simp[NoAsms] >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
     (?v. INL _ = INL v /\ expr_post H _ _ _ _ len _ _ _ _ _ _ _ _ /\ _) /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
   simp[NoAsms] >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     stmt_state_rel H _ _ _ _ mid capture_state /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
    sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id` by
     (qpat_assum `ci_mono sc sd` mp_tac >>
      qpat_assum `ci_mono sd se` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
   `vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
      mid sc sb capture_state length_mid (Value slice_result)
      (LocatedValue a (mk_ptr out LocMemory)) target` by
     (irule exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase >>
      qpat_assum `vv_post H _ _ _ _ _ length_mid se sb length_state length_mid _ _ target`
        (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
        (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state`
        (irule_at Any) >>
      simp[NoAsms,loweringPostsTheory.expr_has_effect_thm] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
   `valid_horizon cx st0 H es.storage_trace` by
     (qpat_assum `!tail. bind (eval_expr cx src) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     expr_post H _ _ _ _ src es sa st1 s0 mid v src_op t /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   `sa.cs_next_id <= st1.cs_next_id` by
     (qpat_assum `ci_mono sa st1` mp_tac >>
      simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
   `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
     (qpat_assum `!tail. bind (eval_expr cx src) _ _ = _`
        (qspec_then `[]` mp_tac) >>
      POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
      drule (SRULE [SF ETA_ss]
        exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
   `capture_state = captured with vs_inst_idx := LENGTH sc.cs_current_insts` by
     simp[Abbr `capture_state`] >>
   `vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
      es sa sb s0 length_mid (Value slice_result)
      (LocatedValue a (mk_ptr out LocMemory)) target` by
     (irule exprSimSliceOrdinaryEntryTheory.slice_bytestring_source_post_rebase >>
      qpat_assum `expr_post H _ _ _ _ src es sa st1 s0 mid v src_op t`
        (irule_at Any) >>
      qpat_assum `compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`
        (irule_at Any) >>
      qpat_assum `run_inst_seq (emitted_insts st1 sc) t = OK captured`
        (irule_at Any) >>
      qpat_assum `eval_operand src_op t = SOME src_ptr` (irule_at Any) >>
      qpat_assum `capture_state = captured with vs_inst_idx := _`
        (fn eq => pure_rewrite_tac[GSYM eq]) >>
      simp[NoAsms,loweringPostsTheory.expr_has_effect_thm] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 capture_G capture_tn` by
     (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
      qpat_assum `!x. not_fresh_at st1 x ==> _ /\ _ /\ _` mp_tac >>
      qpat_assum `capture_tn.t_mem = tn1.t_mem` mp_tac >>
      qpat_assum `sa.cs_next_var <= st1.cs_next_var` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      fs[bodyPtrDefsTheory.ghost_kept_at_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
   `wb_frame cenv es mid sa s0 capture_state` by
     (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post H _ _ _ _ src es sa sc s0 mid v src_op captured`
        (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
      qpat_assum `capture_state = captured with vs_inst_idx := _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[loweringPostsTheory.expr_post_def,loweringPostsTheory.wb_frame_def,
        venomStateTheory.lookup_var_def,exprSimPropsTheory.locals_kept_inst_idx] >>
      metis_tac[]) >>
   `sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 start_G start_tn` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`capture_G`,`capture_tn`,
          `mid`,`sc`,`start_G`,`start_tn`,`capture_state`,`mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `wb_frame cenv mid start_mid sc capture_state start_state` by
     (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
        (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
   `wb_frame cenv start_mid length_mid sd start_state length_state` by
     (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
        (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
   `wb_frame cenv es start_mid sa s0 start_state` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`sa`,`mid`,`start_mid`,`sc`,
          `capture_state`,`start_state`] mp_tac)
          exprSimWordArgsTheory.wb_frame_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
    sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by decide_tac >>
   `wb_frame cenv es length_mid sa s0 length_state` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`sa`,`start_mid`,`length_mid`,`sd`,
          `start_state`,`length_state`] mp_tac)
          exprSimWordArgsTheory.wb_frame_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 length_G length_tn` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`start_G`,`start_tn`,
          `start_mid`,`sd`,`length_G`,`length_tn`,`start_state`,`start_mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`length_G`,`length_tn`,
          `length_mid`,`se`,`HG`,`tm`,`length_state`,`length_mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `s0.vs_alloca_next <= target.vs_alloca_next` by
     (`s0.vs_alloca_next <= capture_state.vs_alloca_next` by
        (qpat_assum `s0.vs_alloca_next <= captured.vs_alloca_next` mp_tac >>
         qpat_assum `capture_state = captured with vs_inst_idx := _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >> decide_tac) >>
   qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 length_mid _ _ target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   qpat_assum `vv_store_bound cx _ _ length_mid _ _ target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   qpat_assum `ptr_vv_ok cx _ _ _ length_mid HG tm target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   simp[vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
     contextTheory.mk_ptr_def,contextTheory.vv_location_def] >>
   qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 length_mid _ _ target` mp_tac >>
   qpat_assum `vv_store_bound cx _ _ length_mid _ _ target` mp_tac >>
   qpat_assum `ptr_vv_ok cx _ _ _ length_mid HG tm target` mp_tac >>
   qpat_assum `ptr_buf_ok cenv _ out HG target` mp_tac >>
   qpat_assum `a = BaseT _` mp_tac >>
   qpat_assum `slice_result = _` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
   gvs[contextTheory.mk_ptr_def])))
QED

Resume slice_builtin_none_vv_full_from_runs[fixed_source]:
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprSimSliceSourceTheory.slice_dispatch_fixed,
    exprBopLoweringTheory.lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv (expr_type src) src sa = (src_op,st1)` >>
  qmatch_asmsub_rename_tac `compile_alloc_buffer 32 st1 = (buf,sm)` >>
  qmatch_asmsub_rename_tac `emit_void MSTORE [buf.buf_operand;src_op] sm = (ignored,sc)` >>
  Cases_on `ignored` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty start sc = (start_op,sd)` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty len sd = (len_op,se)` >>
  `ci_mono st1 sc` by
    (irule exprSimSliceOrdinaryContextTheory.slice_fixed_capture_ci_mono >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule_all exprSimSliceOrdinaryContextTheory.slice_ordinary_pipeline_context >> strip_tac >>
  `?m. expr_type src = BaseT (BytesT (Fixed m)) /\
       a = BaseT (BytesT (Dynamic n))` by
    (qpat_assum `(a = BaseT (BytesT (Dynamic n)) /\ _) \/ _` mp_tac >>
     qpat_assum `~is_bytestring_type (expr_type src)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[compileEnvTheory.is_bytestring_type_def] >>
     Cases_on `bd` >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  rename1 `expr_type src = BaseT (BytesT (Fixed m))` >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,
    compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call,
    compileEnvTheory.is_bytestring_type_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv (BaseT (BytesT (Fixed m))) (gas_shadow_expr src)
       shadow_sa = (shadow_src,shadow_s1)` >>
  qmatch_asmsub_rename_tac `compile_alloc_buffer 32 shadow_s1 = (shadow_buf,shadow_sm)` >>
  `shadow_src = src_op /\ gas_shadow_state st1 shadow_s1` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_src = src_op` SUBST_ALL_TAC >>
  `shadow_buf = buf /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `compile_alloc_buffer 32 st1 = (buf,sm)` mp_tac >>
     qpat_assum `compile_alloc_buffer 32 shadow_s1 = (shadow_buf,shadow_sm)` mp_tac >>
     qpat_assum `gas_shadow_state st1 shadow_s1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_buf = buf` SUBST_ALL_TAC >>
  qmatch_asmsub_rename_tac
    `emit_void MSTORE [buf.buf_operand;src_op] shadow_sm = (ignored_shadow,shadow_sc)` >>
  Cases_on `ignored_shadow` >>
  `gas_shadow_state sc shadow_sc` by
    (qpat_assum `emit_void MSTORE _ sm = ((),sc)` mp_tac >>
     qpat_assum `emit_void MSTORE _ shadow_sm = ((),shadow_sc)` mp_tac >>
     qpat_assum `gas_shadow_state sm shadow_sm` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gasShadowStateTheory.gas_shadow_compiles_emit_void,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty (gas_shadow_expr start) shadow_sc =
       (shadow_start,shadow_sd)` >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv ty (gas_shadow_expr len) shadow_sd =
       (shadow_count,shadow_se)` >>
  `shadow_start = start_op /\ gas_shadow_state sd shadow_sd` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_start = start_op` SUBST_ALL_TAC >>
  `shadow_count = len_op /\ gas_shadow_state se shadow_se` by
    (map_every (fn label => asm_x label kall_tac)
       ["dynamic_run","fixed_run","tail_run","dynamic_source_post"] >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `shadow_count = len_op` SUBST_ALL_TAC >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  `ci_mono shadow_s1 shadow_sc` by
    (irule exprSimSliceOrdinaryContextTheory.slice_fixed_capture_ci_mono >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_data _ _ _ _ _ shadow_se) = (_,shadow_sb)`
    (mp_then Any mp_tac exprSimSliceOrdinaryContextTheory.slice_ordinary_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`st1`,`shadow_sa`,`shadow_s1`,
    `src_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ source_post _` >>
  simp[Once slice_eval_ordinary] >>
  simp[eval_exprs_cons_action,vyperStateTheory.bind_assoc] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,vyperStateTheory.return_def] >>
  simp[vyperStateTheory.bind_return,vyperStateTheory.bind_assoc] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      (reverse conj_tac >-
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_state_reads,
          vyperStorageTraceTheory.storage_trace_frame_lifts,
          exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
      gen_tac >> BETA_TAC) >>
    simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists_tac `\H res ee G tn t. source_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
  rpt gen_tac >> strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> source_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `source_post`, NoAsms] >> strip_tac >>
  qpat_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- REFL_TAC >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
   expr_result_typed env src (Value v)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env src
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qspecl_then [`cenv`,`cx`,`env`,`src`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `INL v`,`mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `?vt. evaluate_type (get_tenv cx) (expr_type src) = SOME vt /\
        value_has_type vt v` by
    fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >>
  `?bs. v = BytesV bs /\ LENGTH bs = m /\ m <= 32` by
    (qpat_assum `expr_type src = BaseT (BytesT (Fixed m))` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (expr_type src) = SOME vt` mp_tac >>
     qpat_assum `value_has_type vt v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `v` >>
     gvs[vyperValueTheory.evaluate_type_def,vyperTypingTheory.value_has_type_def]) >>
  rename1 `v = BytesV source_bytes` >>
  qpat_assum `v = BytesV source_bytes` SUBST_ALL_TAC >>
  `post_value_type cenv src = BaseT (BytesT (Fixed m))` by
    (qpat_assum `expr_type src = BaseT (BytesT (Fixed m))` mp_tac >>
     qpat_assum `m <= 32` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[loweringPostsTheory.post_value_type_word,compileEnvTheory.is_word_type_def]) >>
  `value_has_type (BaseTV (BytesT (Fixed m))) (BytesV source_bytes)` by
    fs[vyperTypingTheory.value_has_type_def] >>
  qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) _ _ _ _ src _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac exprSimHashTheory.hash_fixed_post_view) >>
  disch_then (qspec_then `m` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `src_word` strip_assume_tac) >>
  `op_taint tn1 src_op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!x. src_op = Var x ==> not_fresh_at st1 x` by
    (qpat_assum `lower_value compile_expr cenv (expr_type src) src sa = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx mid t` by fs[loweringPostsTheory.expr_post_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  asm "fixed_run" drule_all >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`] mp_tac) >>
  disch_then (qx_choosel_then [`data_name`,`src_ptr`,`allocated`,`captured`,
    `capture_G`,`capture_tn`] (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx src es sa st1 s0 mid
       (BytesV source_bytes) src_op t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> source_post _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> simp[NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `allocated.vs_memory = t.vs_memory /\
   allocated.vs_call_ctx = t.vs_call_ctx /\
   allocated.vs_accounts = t.vs_accounts /\
   allocated.vs_transient = t.vs_transient /\
   allocated.vs_immutables = t.vs_immutables /\
   captured.vs_vars = allocated.vs_vars /\
   captured.vs_allocas = allocated.vs_allocas /\
   captured.vs_alloca_next = allocated.vs_alloca_next /\
   captured.vs_call_ctx = t.vs_call_ctx /\
   captured.vs_accounts = t.vs_accounts /\
   captured.vs_transient = t.vs_transient /\
   captured.vs_immutables = t.vs_immutables` by
    (qpat_assum `allocated with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = t` mp_tac >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[venomStateTheory.mstore_def,venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.venom_state_component_equality]) >>
  `cs_extends st1 sm /\ cs_extends sm sc` by
    (conj_tac
     >- (qpat_assum `compile_alloc_buffer 32 st1 = (buf,sm)`
           (ACCEPT_TAC o MATCH_MP loweringHaltTheory.compile_alloc_buffer_extends)) >>
     `ci_mono sm sc` by
       (qspecl_then [`MSTORE`,`[buf.buf_operand;src_op]`,`sm`] mp_tac
          exprLoweringPropsTheory.ci_mono_emit_void >> simp[]) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code st1 sm func` by
    (qpat_assum `fn_has_code st1 sc func` mp_tac >>
     qpat_assum `cs_extends st1 sm` mp_tac >>
     qpat_assum `cs_extends sm sc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func)` by
    (irule exprSimHashTheory.hash_emitted_inst_mem >>
     qexistsl_tac [`st1`,`sm`] >> simp[] >>
     qpat_assum `compile_alloc_buffer 32 st1 = (buf,sm)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[contextTheory.compile_alloc_buffer_def,emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def,compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def,compileEnvTheory.emit_def] >>
     strip_tac >> gvs[exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid captured /\
     storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx mid t` by
       fs[loweringPostsTheory.expr_post_def] >>
     `stmt_state_rel H ctx func cenv cx mid allocated` by
       (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ mid t ==> _`
          (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
     reverse conj_tac >- fs[loweringPostsTheory.expr_post_def] >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     irule exprSimAllocTheory.literal_mstore_state_rel >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w2n src_ptr`,
       `mk_inst st1.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString st1.cs_next_var)]`,`32`] >>
     fs[venomInstTheory.mk_inst_def] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `lo <= w2n src_ptr` by
    (qpat_assum `allocas_from lo captured` mp_tac >>
     qpat_assum `FLOOKUP captured.vs_allocas st1.cs_next_id = SOME (w2n src_ptr,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `!off sz. regions_disjoint (w2n src_ptr) 32 off sz ==>
     mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[] >> irule EQ_TRANS >>
     qexists_tac `mem_bytes_at off sz allocated.vs_memory` >>
     reverse conj_tac >- simp[] >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!x. not_fresh_at st1 x ==> lookup_var x allocated = lookup_var x t` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     qpat_assum `captured.vs_vars = allocated.vs_vars` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venomStateTheory.lookup_var_def]) >>
  `!name b sz. local_region cenv mid.scopes t name b sz ==>
     local_region cenv mid.scopes allocated name b sz` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`t`,`st1`,`mid.scopes`] >> simp[]) >>
  `!name b sz. local_region cenv mid.scopes t name b sz ==>
     mem_bytes_at b sz captured.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!j. b <= j /\ j < b+sz /\ j IN capture_tn.t_mem ==> j IN tn1.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!off sz. regions_disjoint _ _ _ _ ==> _` irule >>
         qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
           (qspecl_then [`name`,`b`,`sz`] match_mp_tac) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!j. j < t.vs_alloca_next /\ j IN capture_tn.t_mem ==> _` irule >>
     simp[] >>
     `b+sz <= t.vs_alloca_next` by
       (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >> decide_tac) >>
  `mem_bytes_at 0 lo captured.vs_memory = mem_bytes_at 0 lo t.vs_memory /\
   (!j. j < lo /\ j IN capture_tn.t_mem ==> j IN tn1.t_mem)` by
    (conj_tac
     >- (qpat_assum `!off sz. regions_disjoint _ _ _ _ ==> _` irule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     rpt strip_tac >>
     qpat_assum `!j. j < t.vs_alloca_next /\ j IN capture_tn.t_mem ==> _` irule >>
     simp[] >> decide_tac) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x w. not_fresh_at st1 x /\ lookup_var x t = SOME w ==>
     lookup_var x captured = SOME w` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!x. not_fresh_at st1 x ==>
     FLOOKUP capture_G x = FLOOKUP G1 x /\
     op_taint capture_tn (Var x) = op_taint tn1 (Var x)` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `lo <= captured.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid capture_G capture_tn captured` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     `local_ptrs_rel func cenv mid.scopes t` by
       (qpat_assum `expr_post H _ _ _ _ src _ _ _ _ mid _ _ t` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[loweringPostsTheory.expr_post_def,
          exprLoweringPropsTheory.stmt_state_rel_def,
          loweringStateRelDefsTheory.state_rel_def]) >>
     `stor_taint_ok_at (DF H) capture_tn captured` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
        qpat_assum `capture_tn.t_stor = tn1.t_stor` mp_tac >>
        qpat_assum `capture_tn.t_trans = tn1.t_trans` mp_tac >>
        qpat_assum `capture_tn.t_imm = tn1.t_imm` mp_tac >>
        qpat_assum `captured.vs_call_ctx = t.vs_call_ctx` mp_tac >>
        qpat_assum `captured.vs_accounts = t.vs_accounts` mp_tac >>
        qpat_assum `captured.vs_transient = t.vs_transient` mp_tac >>
        qpat_assum `captured.vs_immutables = t.vs_immutables` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[bodyPtrDefsTheory.ghost_inv_at_def,bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` (irule_at Any) >>
     qexistsl_tac [`st1`,`func`] >> simp[NoAsms] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qabbrev_tac `fixed_capture_shape =
    (captured = mstore (w2n src_ptr) src_word allocated with
       vs_inst_idx := LENGTH sc.cs_current_insts)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid captured /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid capture_G capture_tn captured` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ captured /\ _` mp_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ captured` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `body_exprs_full_ok cx [start;len]` by
    (qpat_assum `body_exprs_full_ok cx [src;start;len]`
       (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
     disch_then irule >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env start mid` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`mid`] mp_tac) >> fs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty start mid` by
    (`body_expr_full_ok cx start` by fs[body_exprs_full_ok_def] >>
     qpat_assum `body_expr_full_ok cx start`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`ty`,`mid`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `sa.cs_next_var <= st1.cs_next_var /\ st1.cs_next_var <= sc.cs_next_var /\
   sa.cs_next_var <= sc.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `s0.vs_alloca_next <= captured.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv st1 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) _ _ _ _ src _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def)))) >>
  `return_buf_frame d cenv sc captured` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t`,`st1`] >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> simp[]) >>
  `~captured.vs_halted /\
   captured.vs_current_bb = sc.cs_current_bb /\
   captured.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (fs[venomStateTheory.venom_state_component_equality]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok mid` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     first_assum (irule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sc`,`sd`,`shadow_sc`,`shadow_sd`,
    `start_op`,`captured`,`capture_G`,`capture_tn`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
    qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ (mid,captured,capture_G,capture_tn) start_post _` >>
  irule gas_outcome_full_zero_prefix >>
  qexistsl_tac [`capture_G`,`captured`,`capture_tn`] >>
  conj_tac >- (gen_tac >> first_assum (MATCH_ACCEPT_TAC o SPEC_ALL)) >>
  BETA_TAC >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  (irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      (reverse conj_tac >-
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_state_reads,
          vyperStorageTraceTheory.storage_trace_frame_lifts,
          exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
      gen_tac >> BETA_TAC) >>
    simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists_tac `\H res ee G tn t. start_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx start) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> pop_assum (mp_tac o BETA_RULE) >>
          POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `res` >>
          simp[exprSimDefsTheory.expr_exit_INL] >>
          rename1 `expr_exit (INR exc) r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
  qx_genl_tac [`start_marks`,`start_res`,`start_mid`,`start_G`,`start_tn`,`start_state`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon start_mid.storage_trace)
      start_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon start_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `start_post`,NoAsms] >> strip_tac >>
  rename1 `start_res = INL start_v` >>
  qpat_assum `start_res = INL start_v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `start_v` >> conj_tac >- REFL_TAC >>
  `start_mid with gas_obs := [] = start_mid` by
    (qpat_assum `start_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (start_mid with gas_obs := [])` by
    (qpat_assum `expr_body_pre cenv cx env start mid` mp_tac >>
     qpat_assum `start_mid with gas_obs := [] = start_mid` mp_tac >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` mp_tac) >> strip_tac >>
     qspecl_then [`cenv`,`cx`,`env`,`start`,
       `mid with gas_obs := gas_explicit start_marks captured.vs_gas_readings ++ []`,
       `INL start_v`,`start_mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `body_exprs_full_ok cx [len]` by
    (qpat_assum `body_exprs_full_ok cx [start;len]`
       (mp_tac o CONJUNCT2 o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
     disch_then irule >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env len start_mid` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`len`,`start_mid`] mp_tac) >> fs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty len start_mid` by
    (`body_expr_full_ok cx len` by fs[body_exprs_full_ok_def] >>
     qpat_assum `body_expr_full_ok cx len`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`ty`,`start_mid`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `return_buf_frame d cenv sd start_state` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`captured`,`sc`] >> simp[] >>
     conj_tac
     >- (qpat_assum `expr_post _ _ _ _ _ start mid sc sd captured start_mid start_v start_op start_state`
           (ACCEPT_TAC o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def)))) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!H. valid_horizon cx st0 H start_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx start_mid start_state /\
     storage_well_formed_on cx start_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx start_mid start_G start_tn start_state` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok start_mid` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     first_assum (irule_at Any)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sd`,`se`,`shadow_sd`,`shadow_se`,
    `len_op`,`start_state`,`start_G`,`start_tn`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
    qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ (start_mid,start_state,start_G,start_tn) length_post _` >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  (irule gas_outcome_full_bind_all >>
   conj_tac >- (rpt gen_tac >> BETA_TAC >>
     rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
       simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
         vyperStorageTraceTheory.storage_trace_frame_lifts,
         vyperStorageTraceTheory.storage_trace_frame_return,
         exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
   conj_tac >- (rpt strip_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
     goal_assum (drule_at Any) >> fs[]) >>
   conj_tac >- (rpt strip_tac >>
     qpat_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[]) >>
   conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
   qexists_tac `\H res ee G tn t. length_post H res ee G tn t /\
     ee.gas_obs = [] /\ ~t.vs_halted` >>
   reverse conj_tac
   >- (irule gas_outcome_full_post_source >>
       qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx len) _) _ _ _`
         (irule_at Any) >>
       reverse conj_tac
       >- (rpt strip_tac >> pop_assum (mp_tac o BETA_RULE) >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `res` >>
           simp[exprSimDefsTheory.expr_exit_INL] >>
           rename1 `expr_exit (INR exc) r` >>
           qspec_then `Value` (qspec_then `INR exc`
             (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
             exprSimDefsTheory.expr_exit_success_map >>
          gvs[exprSimDefsTheory.halt_exit_def]) >> simp[]) >>
   qx_genl_tac [`length_marks`,`length_res`,`length_mid`,`length_G`,`length_tn`,`length_state`] >>
   strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
   `valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       length_mid.storage_trace` by
     fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
   qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==> _`
     (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
   (impl_tac >- simp[]) >>
   simp[Abbr `length_post`,NoAsms] >> strip_tac >>
   rename1 `length_res = INL length_v` >>
   qpat_assum `length_res = INL length_v` SUBST_ALL_TAC >>
   disj1_tac >> qexists_tac `length_v` >> conj_tac >- REFL_TAC >>
   `length_mid with gas_obs := [] = length_mid` by
     (qpat_assum `length_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `expr_sim_inv cenv cx env (length_mid with gas_obs := [])` by
     (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]` mp_tac) >> strip_tac >>
      qspecl_then [`cenv`,`cx`,`env`,`len`,
        `start_mid with gas_obs := gas_explicit length_marks start_state.vs_gas_readings ++ []`,
        `INL length_v`,`length_mid with gas_obs := []`] mp_tac
        exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
   `MAP FDOM mid.scopes = MAP FDOM start_mid.scopes /\
    ?i. start_v = IntV (&i) /\ i < dimword (:256) /\
        eval_operand start_op start_state = SOME (n2w i)` by
     (qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ start_mid start_v start_op start_state`
        (mp_then (Pos (el 4)) mp_tac (INST_TYPE [alpha |-> ``:256``]
          exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
      disch_then (qspecl_then [`gas_explicit start_marks captured.vs_gas_readings`,`env`] mp_tac) >>
      `start_mid with gas_obs := [] = start_mid` by
        (qpat_assum `start_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
   rename1 `start_v = IntV (&i)` >>
   qpat_assum `start_v = IntV (&i)` SUBST_ALL_TAC >>
   `MAP FDOM start_mid.scopes = MAP FDOM length_mid.scopes /\
    ?k. length_v = IntV (&k) /\ k < dimword (:256) /\
        eval_operand len_op length_state = SOME (n2w k)` by
     (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      qpat_assum `expr_post _ _ _ _ _ len _ _ _ _ length_mid length_v len_op length_state`
        (mp_then (Pos (el 4)) mp_tac (INST_TYPE [alpha |-> ``:256``]
          exprSimSliceOrdinaryContinueTheory.slice_uint_read_post)) >>
      disch_then (qspecl_then [`gas_explicit length_marks start_state.vs_gas_readings`,`env`] mp_tac) >> simp[]) >>
   rename1 `length_v = IntV (&k)` >>
   qpat_assum `length_v = IntV (&k)` SUBST_ALL_TAC >>
   `!H. valid_horizon cx st0 H length_mid.storage_trace ==>
        valid_horizon cx st0 H start_mid.storage_trace` by
     (rpt strip_tac >>
      qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   `!H. valid_horizon cx st0 H start_mid.storage_trace ==>
        valid_horizon cx st0 H mid.storage_trace` by
     (rpt strip_tac >>
      qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   `valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       start_mid.storage_trace /\
    valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace)
       mid.storage_trace` by
     (qpat_assum `!H. valid_horizon cx st0 H length_mid.storage_trace ==> valid_horizon cx st0 H start_mid.storage_trace` mp_tac >>
      qpat_assum `!H. valid_horizon cx st0 H start_mid.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` mp_tac >>
      qpat_assum `valid_horizon cx st0 (storage_trace_horizon length_mid.storage_trace) length_mid.storage_trace` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
   qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==> _ /\ start_mid.gas_obs = [] /\ _`
     (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >>
   (impl_tac >- simp[]) >> simp[NoAsms] >> strip_tac >>
   `stmt_state_rel (storage_trace_horizon length_mid.storage_trace)
       ctx func cenv cx mid captured` by
     (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ captured /\ _`
        (qspec_then `storage_trace_horizon length_mid.storage_trace` mp_tac) >> simp[]) >>
   `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
    sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id` by
     fs[exprLoweringPropsTheory.ci_mono_def] >>
   `st1.cs_next_id < sc.cs_next_id /\ st1.cs_next_id < sd.cs_next_id` by
     (`sm.cs_next_id < sc.cs_next_id` by
        (qpat_assum `emit_void MSTORE _ sm = ((),sc)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[emitHelperTheory.emit_void_def,compileEnvTheory.comp_bind_def,
           compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.comp_return_def,
           compileEnvTheory.fresh_id_def,compileEnvTheory.emit_def] >>
         strip_tac >> gvs[]) >>
      `ci_mono st1 sm` by
        (qspecl_then [`32`,`st1`] mp_tac exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >>
         simp[]) >>
      fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
   `!name off sz. local_region cenv mid.scopes captured name off sz ==>
      w2n src_ptr + 32 <= off \/ off + sz <= w2n src_ptr` by
     (rpt strip_tac >>
      `local_region cenv mid.scopes allocated name off sz` by
        (qpat_assum `local_region cenv mid.scopes captured name off sz` mp_tac >>
         qpat_assum `captured.vs_vars = allocated.vs_vars` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[loweringStateRelDefsTheory.local_region_def,venomStateTheory.lookup_var_def]) >>
      qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
        (qspecl_then [`name`,`off`,`sz`] mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
   `mem_bytes_at (w2n src_ptr) (LENGTH source_bytes) captured.vs_memory = source_bytes` by
     (qunabbrev_tac `fixed_capture_shape` >>
      qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
      simp[NoAsms] >> irule exprSimHashTheory.hash_mstore_prefix >> simp[]) >>
   `mem_bytes_at (w2n src_ptr) (LENGTH source_bytes) length_state.vs_memory = source_bytes` by
     (irule (INST_TYPE [alpha |-> ``:256``] slice_fixed_payload_two_operands) >>
      qpat_assum `expr_post _ _ _ _ _ start mid sc sd captured start_mid _ start_op start_state`
        (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
        (irule_at Any) >>
      qexists_tac `st1.cs_next_id` >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
   `wb_frame cenv mid start_mid sc captured start_state` by
     (qpat_assum `expr_post _ _ _ _ _ start mid sc sd captured start_mid _ start_op start_state`
        (ACCEPT_TAC o MATCH_MP exprSimWordArgsTheory.expr_post_frame)) >>
   `!name off sz. local_region cenv start_mid.scopes start_state name off sz <=>
      local_region cenv mid.scopes captured name off sz` by
     (rpt gen_tac >> drule_all stmtSimLogArgsTheory.log_frame_local_region >> simp[]) >>
   `!aid entry. FLOOKUP captured.vs_allocas aid = SOME entry ==>
      FLOOKUP start_state.vs_allocas aid = SOME entry` by
     (qpat_assum `wb_frame cenv mid start_mid sc captured start_state`
        (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
          REWRITE_RULE [loweringPostsTheory.wb_frame_def])) >>
   `ghost_kept_at lo cenv mid sc capture_G capture_tn captured length_G length_tn` by
     (irule wordArgsPtrTheory.ghost_kept_at_trans >>
      qexistsl_tac [`start_G`,`start_mid`,`start_state`,`sd`,`start_tn`] >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
   `ghost_kept cenv mid sc capture_G capture_tn captured length_G length_tn` by
     (qpat_assum `ghost_kept_at lo cenv mid sc capture_G capture_tn captured length_G length_tn`
        mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[bodyPtrDefsTheory.ghost_kept_def,bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
   `!j. w2n src_ptr <= j /\ j < w2n src_ptr + LENGTH source_bytes ==>
      j NOTIN length_tn.t_mem` by
     (`w2n src_ptr + LENGTH source_bytes <= w2n src_ptr + 32` by decide_tac >>
      `!j. w2n src_ptr <= j /\ j < w2n src_ptr + LENGTH source_bytes ==>
         j NOTIN capture_tn.t_mem` by
        (gen_tac >> disch_tac >>
         qpat_assum `!i. w2n src_ptr <= i /\ i < w2n src_ptr + 32 ==> _` irule >>
         decide_tac) >>
      gen_tac >> disch_tac >>
      irule (INST_TYPE [alpha |-> ``:num # num``]
        bodyPtrPrecompileBuiltinsGhostTheory.ghost_kept_alloca_clean) >>
      qpat_assum `ghost_kept cenv mid sc capture_G capture_tn captured length_G length_tn`
        (irule_at Any) >>
      qpat_assum `FLOOKUP captured.vs_allocas st1.cs_next_id = SOME (w2n src_ptr,32)`
        (irule_at Any) >>
      qexistsl_tac [`LENGTH source_bytes`,`w2n src_ptr`] >>
      simp[] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
   `not_fresh_at sd data_name` by
     (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
   `eval_operand (Var data_name) captured = SOME src_ptr` by
     simp[venomStateTheory.eval_operand_def] >>
   `eval_operand (Var data_name) length_state = SOME src_ptr` by
     (qpat_assum `expr_post _ _ _ _ _ start mid sc sd captured start_mid _ start_op start_state`
        (mp_then Any mp_tac slice_two_posts_operands) >>
      disch_then drule >>
      disch_then (qspecl_then [`Var data_name`,`src_ptr`] mp_tac) >> simp[]) >>
   `ptr_covers length_G length_tn data_name length_state 32` by
     (irule bodyPtrPrecompileBuiltinsGhostTheory.ghost_kept_ptr_covers >>
      goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
      qexists_tac `src_ptr` >> simp[]) >>
   `(!x. start_op = Var x ==> not_fresh_at sd x) /\
    (!l. start_op <> Label l)` by
     (qspecl_then [`cenv`,`cx`,`env`,`start`,`mid`,`ty`,`sc`,`start_op`,`sd`]
        mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
      (impl_tac >- simp[compileEnvTheory.is_word_type_def]) >> strip_tac >> simp[]) >>
   `(!x. len_op = Var x ==> not_fresh_at se x) /\
    (!l. len_op <> Label l)` by
     (qspecl_then [`cenv`,`cx`,`env`,`len`,`start_mid`,`ty`,`sd`,`len_op`,`se`]
        mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
      (impl_tac >- simp[compileEnvTheory.is_word_type_def]) >> strip_tac >> simp[]) >>
   `op_prov start_G start_op = NONE /\ op_taint start_tn start_op = {} /\
    op_prov length_G len_op = NONE /\ op_taint length_tn len_op = {}` by
     (qpat_assum `ptr_val_ok _ _ _ start_op start_G start_tn start_state` mp_tac >>
      qpat_assum `ptr_val_ok _ _ _ len_op length_G length_tn length_state` mp_tac >>
      fs[bodyPtrDefsTheory.ptr_val_ok_def,loweringPostsTheory.post_value_type_def,
         compileEnvTheory.is_word_type_def]) >>
   `eval_operand start_op length_state = SOME (n2w i)` by
     (qpat_assum `expr_post _ _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
        (mp_then Any mp_tac exprSimSliceOrdinaryFrameTheory.slice_post_operands) >>
      disch_then (qspecl_then [`start_op`,`n2w i`] mp_tac) >> simp[]) >>
   `op_prov length_G start_op = NONE /\ op_taint length_tn start_op = {}` by
     (qpat_assum `ghost_kept_at lo cenv start_mid sd start_G start_tn start_state length_G length_tn`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
      qpat_assum `!x. start_op = Var x ==> not_fresh_at sd x` mp_tac >>
      qpat_assum `op_prov start_G start_op = NONE` mp_tac >>
      qpat_assum `op_taint start_tn start_op = {}` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_op` >>
      simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
   `not_fresh_at se data_name` by
     (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sd` >> simp[]) >>
   `!x. start_op = Var x ==> not_fresh_at se x` by
     (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sd` >> simp[]) >>
   `!x. x = data_name \/ Var x = start_op \/ Var x = len_op ==>
      not_fresh_at se x` by
     (qpat_assum `not_fresh_at se data_name` mp_tac >>
      qpat_assum `!x. start_op = Var x ==> not_fresh_at se x` mp_tac >>
      qpat_assum `!x. len_op = Var x ==> not_fresh_at se x` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
   `ptr_covers length_G length_tn data_name length_state (LENGTH source_bytes)` by
     (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `32` >> simp[]) >>
   `lookup_var data_name length_state = SOME src_ptr` by
     (qpat_assum `eval_operand (Var data_name) length_state = SOME src_ptr`
        (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.eval_operand_def])) >>
   `w2n src_ptr + LENGTH source_bytes < dimword (:256)` by decide_tac >>
   `w2n src_ptr + LENGTH source_bytes <= length_state.vs_alloca_next` by
     (qpat_assum `w2n src_ptr + 32 <= captured.vs_alloca_next` mp_tac >>
      qpat_assum `captured.vs_alloca_next <= start_state.vs_alloca_next` mp_tac >>
      qpat_assum `start_state.vs_alloca_next <= length_state.vs_alloca_next` mp_tac >>
      qpat_assum `LENGTH source_bytes = m` mp_tac >>
      qpat_assum `m <= 32` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
   `LENGTH source_bytes <= bytelike_type_bound (expr_type src)` by
     simp[vyperTypeSystemTheory.bytelike_type_bound_def] >>
   `(i+k <= LENGTH source_bytes ==> k <= n)` by
     (drule slice_capacity_alternatives >> strip_tac
      >- (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
            (qspec_then `[]` mp_tac) >>
          qpat_assum `len = Literal _ (IntL _)` mp_tac >>
          qpat_assum `_ <= &n` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
          gvs[vyperInterpreterTheory.evaluate_def,
            vyperStateTheory.bind_def,vyperStateTheory.return_def,
            vyperStateTheory.lift_sum_def,vyperStateTheory.read_result_def,
            vyperValueOperationTheory.evaluate_literal_def] >> intLib.ARITH_TAC) >>
      decide_tac) >>
   qabbrev_tac `slice_result = BytesV (TAKE k (DROP i source_bytes))` >>
   `evaluate_slice (BytesV source_bytes) (IntV (&i)) (IntV (&k)) n =
      if i+k <= LENGTH source_bytes then INL slice_result
      else INR (RuntimeError "evaluate_slice range")` by
     (simp[slice_bytes_nat,Abbr `slice_result`] >>
      Cases_on `i+k <= LENGTH source_bytes` >> fs[]) >>
   `32+n <= type_memory_bytes cenv a` by
     (qpat_assum `a = BaseT _` mp_tac >>
      qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      fs[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def]) >>
   `type_memory_bytes cenv a < dimword (:256)` by
     (qpat_assum `expr_body_pre cenv cx env (Builtin a (Slice n) _) es` mp_tac >>
      qpat_assum `a = BaseT _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def] >>
      simp[wordsTheory.dimword_def] >> decide_tac) >>
   `?out. compile_slice_data (Lit (n2w m)) (Var data_name) start_op len_op
       (type_memory_bytes cenv a) se = (out,sb) /\
     vv = LocatedValue a (mk_ptr out LocMemory)` by
     (qpat_assum `as_ptr_val a LocMemory _ = (vv,sb)` mp_tac >>
      qpat_assum `buf.buf_operand = Var data_name` mp_tac >>
      qpat_assum `expr_type src = BaseT (BytesT (Fixed m))` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      Cases_on `compile_slice_data (Lit (n2w m)) (Var data_name) start_op len_op
        (type_memory_bytes cenv a) se` >>
      gvs[as_ptr_val_def,exprLoweringTheory.fixed_bytes_size_def]) >>
   `!H. valid_horizon cx st0 H length_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx length_mid length_state /\
     storage_well_formed_on cx length_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx length_mid length_G length_tn length_state` by
     (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
        _ H (INL _) length_mid length_G length_tn length_state /\ _`
        (qspec_then `H` mp_tac) >>
      qpat_assum `valid_horizon cx st0 H length_mid.storage_trace` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
   `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at se x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at se x)` by
     (conj_tac >> rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
   qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ tail_source _ _ _` >>
   `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 tail_source (length_mid,length_state,length_G,length_tn)
      (\H res ee HG tm t.
        res = INL (Value slice_result) /\
        vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
          length_mid se sb length_state ee (Value slice_result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        vv_store_bound cx a a ee (Value slice_result)
          (LocatedValue a (mk_ptr out LocMemory)) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ length_state.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
        ptr_vv_ok cx a (Value slice_result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
        ptr_buf_ok cenv (Builtin a (Slice n) [src;start;len]) out HG t /\
        ghost_kept_at lo cenv length_mid se length_G length_tn length_state HG tm)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)` by
     (qpat_assum `a = BaseT _` SUBST_ALL_TAC >>
      asm "tail_run" irule >>
      qpat_assum `compile_slice_data (Lit (n2w m)) (Var data_name) _ _ _ se = (out,sb)`
        (irule_at Any) >>
      qexistsl_tac [`src_ptr`,`n`,`k`,`i`,`source_bytes`,`[src;start;len]`] >>
      simp[MEM,venomStateTheory.eval_operand_def,
        ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def,
        Abbr `tail_source`,vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
        vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
        vyperStateTheory.raise_def,vyperContextTheory.evaluate_builtin_def,
        Abbr `slice_result`] >>
      Cases_on `i+k <= LENGTH source_bytes` >>
      simp[slice_bytes_nat,vyperStateTheory.return_def,vyperStateTheory.raise_def] >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
   qunabbrev_tac `tail_source` >>
   irule gas_outcome_full_post_source >>
   qpat_assum `gas_outcome_full _ _ _ _ _
     (length_mid,length_state,length_G,length_tn) _ _` (irule_at Any) >>
   reverse conj_tac >- simp[] >>
   qx_genl_tac [`H`,`res`,`ee`,`HG`,`tm`,`target`] >> strip_tac >>
   RULE_ASSUM_TAC BETA_RULE >>
   qpat_x_assum `res = INL _ /\ _` strip_assume_tac >>
   qpat_assum `res = INL _` SUBST_ALL_TAC >>
   `ee with gas_obs := [] = ee` by
     (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `length_mid with gas_obs := [] = length_mid` by
     (qpat_assum `length_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
   `ee = length_mid` by
     (qpat_assum `!tail. bind get_accounts _ _ = _` (qspec_then `[]` mp_tac) >>
      qpat_assum `evaluate_slice (BytesV source_bytes) (IntV (&i)) (IntV (&k)) n = _` mp_tac >>
      qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
      qpat_assum `length_mid with gas_obs := [] = length_mid` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      Cases_on `i+k <= LENGTH source_bytes` >>
      fs[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
         vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
         vyperStateTheory.raise_def,vyperContextTheory.evaluate_builtin_def] >>
      qpat_assum `evaluate_slice (BytesV source_bytes) (IntV (&i)) (IntV (&k)) n = _`
        (fn eq => full_simp_tac (srw_ss())
          [eq,vyperStateTheory.return_def,vyperStateTheory.raise_def]) >>
      qpat_assum `length_mid with gas_obs := _ = ee with gas_obs := []`
        (mp_tac o Q.AP_TERM `\st:evaluation_state. st with gas_obs := []`) >> simp[]) >>
   qpat_assum `ee = length_mid` SUBST_ALL_TAC >>
   `valid_horizon cx st0 H start_mid.storage_trace` by
     (qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
        valid_horizon _ _ H start_mid.storage_trace` irule >> simp[]) >>
   `valid_horizon cx st0 H mid.storage_trace` by
     (qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==>
        valid_horizon _ _ H mid.storage_trace` irule >> simp[]) >>
   qpat_assum `!H. valid_horizon _ _ H start_mid.storage_trace ==>
     (?v. INL _ = INL v /\ expr_post H _ _ _ _ start _ _ _ _ _ _ _ _ /\ _) /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
   simp[NoAsms] >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H length_mid.storage_trace ==>
     (?v. INL _ = INL v /\ expr_post H _ _ _ _ len _ _ _ _ _ _ _ _ /\ _) /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
   simp[NoAsms] >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     stmt_state_rel H _ _ _ _ mid captured /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
    sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id` by
     (qpat_assum `ci_mono sc sd` mp_tac >>
      qpat_assum `ci_mono sd se` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
   `vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
      mid sc sb captured length_mid (Value slice_result)
      (LocatedValue a (mk_ptr out LocMemory)) target` by
     (irule exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase >>
      qpat_assum `vv_post H _ _ _ _ _ length_mid se sb length_state length_mid _ _ target`
        (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ len start_mid sd se start_state length_mid _ len_op length_state`
        (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ start mid sc sd capture_state start_mid _ start_op start_state`
        (irule_at Any) >>
      simp[NoAsms,loweringPostsTheory.expr_has_effect_thm] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
   `valid_horizon cx st0 H es.storage_trace` by
     (qpat_assum `!tail. bind (eval_expr cx src) _ _ = _`
        (qspec_then `[]`
          (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
      simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
   qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     expr_post H _ _ _ _ src es sa st1 s0 mid (BytesV source_bytes) src_op t /\ _`
     (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
   `sa.cs_next_id <= st1.cs_next_id` by
     (qpat_assum `ci_mono sa st1` mp_tac >>
      simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
   `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
     (qpat_assum `!tail. bind (eval_expr cx src) _ _ = _`
        (qspec_then `[]` mp_tac) >>
      POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
      drule (SRULE [SF ETA_ss]
        exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
   `!name off sz. local_region cenv mid.scopes t name off sz ==>
      mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory` by
     (qpat_assum `!name b sz. local_region cenv mid.scopes t name b sz ==> _ /\ _`
        mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
   `!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\
      aid < st1.cs_next_id ==>
      mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory` by
     (rpt gen_tac >> strip_tac >>
      qpat_assum `!off sz. regions_disjoint (w2n src_ptr) 32 off sz ==> _` irule >>
      qpat_assum `!aid b len. aid < st1.cs_next_id /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
   `wb_frame cenv mid mid st1 t captured` by
     (simp[NoAsms,loweringPostsTheory.wb_frame_def] >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC
      >- first_assum MATCH_ACCEPT_TAC
      >- (rpt strip_tac >>
          qpat_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _` irule >>
          qexists_tac `aid` >> simp[]) >>
      irule exprSimPropsTheory.locals_kept_regions >> first_assum MATCH_ACCEPT_TAC) >>
   `!off sz. regions_disjoint off sz (w2n src_ptr) 32 ==>
      mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory` by
     (rpt strip_tac >>
      qpat_assum `!off sz. regions_disjoint (w2n src_ptr) 32 off sz ==> _` irule >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
   `st1.cs_next_id <= sc.cs_next_id` by decide_tac >>
   `pure_frame cenv func mid st1 t captured` by
     (qspecl_then [`cenv`,`func`,`mid`,`st1`,`t`,`captured`,
        `st1.cs_next_id`,`[Lit 32w]`,
        `[STRING #"%" (toString st1.cs_next_var)]`,`w2n src_ptr`,`32`]
        match_mp_tac exprSimPropsTheory.pure_frame_fresh_alloca >>
      simp[NoAsms] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
   `vv_post H ctx func cenv cx (Builtin a (Slice n) [src;start;len])
      es sa sb s0 length_mid (Value slice_result)
      (LocatedValue a (mk_ptr out LocMemory)) target` by
     (irule exprSimSliceOrdinaryEntryTheory.slice_source_capture_post_rebase >>
      qpat_assum `vv_post H _ _ _ _ _ mid sc sb captured length_mid _ _ target`
        (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ src es sa st1 s0 mid _ src_op t`
        (irule_at Any) >>
      simp[loweringPostsTheory.expr_has_effect_thm]) >>
   `!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
      off+sz <= t.vs_alloca_next` by
     (qpat_assum `expr_post H _ _ _ _ src es sa st1 s0 mid _ src_op t` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[loweringPostsTheory.expr_post_def,
        exprLoweringPropsTheory.stmt_state_rel_def,
        venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
      metis_tac[]) >>
   `ghost_kept_at lo cenv mid st1 G1 tn1 t capture_G capture_tn` by
     (qpat_assum `!x. not_fresh_at st1 x ==> FLOOKUP capture_G x = _ /\ _` mp_tac >>
      qpat_assum `!j. j < t.vs_alloca_next /\ j IN capture_tn.t_mem ==> _` mp_tac >>
      qpat_assum `!name b sz. local_region cenv mid.scopes t name b sz ==> _ /\ _` mp_tac >>
      qpat_assum `!j. j < lo /\ j IN capture_tn.t_mem ==> _` mp_tac >>
      qpat_assum `!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
      rpt strip_tac >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
   `wb_frame cenv es mid sa s0 t` by
     (qpat_assum `expr_post H _ _ _ _ src es sa st1 s0 mid _ src_op t`
        (ACCEPT_TAC o MATCH_MP exprSimWordArgsTheory.expr_post_frame)) >>
   `wb_frame cenv es mid sa s0 captured` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`sa`,`mid`,`mid`,`st1`,`t`,`captured`] mp_tac)
          exprSimWordArgsTheory.wb_frame_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 capture_G capture_tn` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`G1`,`tn1`,
          `mid`,`st1`,`capture_G`,`capture_tn`,`t`,`mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 start_G start_tn` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`capture_G`,`capture_tn`,
          `mid`,`sc`,`start_G`,`start_tn`,`captured`,`mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `wb_frame cenv mid start_mid sc captured start_state` by
     (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
        (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
   `wb_frame cenv start_mid length_mid sd start_state length_state` by
     (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
        (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
   `wb_frame cenv es start_mid sa s0 start_state` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`sa`,`mid`,`start_mid`,`sc`,
          `captured`,`start_state`] mp_tac)
          exprSimWordArgsTheory.wb_frame_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
    sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by decide_tac >>
   `wb_frame cenv es length_mid sa s0 length_state` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`sa`,`start_mid`,`length_mid`,`sd`,
          `start_state`,`length_state`] mp_tac)
          exprSimWordArgsTheory.wb_frame_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 length_G length_tn` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`start_G`,`start_tn`,
          `start_mid`,`sd`,`length_G`,`length_tn`,`start_state`,`start_mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
     (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then Any (qspecl_then [`lo`,`sa`,`G0`,`tn0`,`length_G`,`length_tn`,
          `length_mid`,`se`,`HG`,`tm`,`length_state`,`length_mid`] mp_tac)
          wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
   `s0.vs_alloca_next <= target.vs_alloca_next` by decide_tac >>
   qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 length_mid _ _ target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   qpat_assum `vv_store_bound cx _ _ length_mid _ _ target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   qpat_assum `ptr_vv_ok cx _ _ _ length_mid HG tm target`
     (assume_tac o REWRITE_RULE[contextTheory.mk_ptr_def]) >>
   simp[vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
     contextTheory.mk_ptr_def,contextTheory.vv_location_def] >>
   qpat_assum `vv_post H ctx func cenv cx _ es sa sb s0 length_mid _ _ target` mp_tac >>
   qpat_assum `vv_store_bound cx _ _ length_mid _ _ target` mp_tac >>
   qpat_assum `ptr_vv_ok cx _ _ _ length_mid HG tm target` mp_tac >>
   qpat_assum `ptr_buf_ok cenv _ out HG target` mp_tac >>
   qpat_assum `a = BaseT _` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
   gvs[contextTheory.mk_ptr_def]))
QED

Finalise slice_builtin_none_vv_full_from_runs
