Theory createSizeRawPayloadReplay
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  venomExecSemantics venomInst venomState vyperCreate vyperState relation list words
  createMarkedPath pair arithmetic exprLowering stmtLoweringMono vfmConstants compileEnv
  exprLoweringProps vyperStorageTrace rich_list exprSimHypsDefs gasCount bodyPtrDefs
  loweringPosts context fragGasPath vyperAST vyperStorageFootprint integer_word
  createCtorSegmentArrival loweringStateRelDefs ptrDiscipline createCtorObservedSilence
  bodySim createExprSizeExitDefs createSizePrefixReplay createSizeBlueprintKeywordReplay
  createSizeRawReplay createSizeCtorRowsReplay createSizeRawEncoderReplay createSizeRawTotal
  createSizeBlueprintAbiKeywords createSizeOperandPre

Theorem raw_payload_silent_readings[local]:
  gas_origin_edge F explicit ctx func s [] (OK t) ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP gas_origin_edge_erase) >>
  disch_then (mp_tac o MATCH_MP gas_path_edge_suffix) >> simp[gas_count_suffix_def]
QED

(* This law is scoped to the constructor list of the current call. A
   client supplies it from the guarded constructor walker, not from a
   claim that the source has already encoded its arguments. *)
Definition raw_ctor_rows_law_def:
  raw_ctor_rows_law A (DF,lo,d,ctx,shctx,func,shfunc) tops ce cx env st0 args <=>
  !C V M Sh SM svs St R Chunk Snap Mid (k : value list -> evaluation_state ->
                                            (eval_result + exception) # evaluation_state)
    p0 H tail res out G0 tn0.
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!i p. i < LENGTH args /\ expr_sim_inv ce cx env p ==>
    expr_body_pre ce cx env (EL i args) p) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_expr (gas_shadow_env T ce) (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
        (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i ++ Snap i) (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
      create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i) (Mid i) /\
      (Mid i).vs_current_bb = (M i).cs_current_bb /\
      (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
      create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (Mid i) (Snap i) (St (SUC i)) /\
      (exprs_can_mutate ce (DROP (SUC i) args) ==>
        fn_has_code (M i) (C (SUC i)) func /\
        (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
             (C (SUC i)).cs_next_id <= j.inst_id) /\
        (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func (Mid i) [] (OK (St (SUC i))) ==>
          Snap i = [])))) /\
  bind (eval_exprs cx args) k p0 = (res,out) /\ (!vs. storage_trace_frame (k vs)) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  A p0 /\ expr_sim_inv ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?vs E Gf tf. E 0 = p0 /\ LENGTH vs = LENGTH args /\
    eval_exprs cx args p0 = (INL vs,E (LENGTH args)) /\
    k vs (E (LENGTH args)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH args)).storage_trace /\ A (E (LENGTH args)) /\
    (!i. i <= LENGTH args ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv ce cx env (E i) /\ return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      storage_well_formed_on cx (E (LENGTH args)) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E (LENGTH args)) Gf tf (St (LENGTH args))) /\
    (!i. i < LENGTH args ==>
      bind (eval_expr cx (EL i args)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
      expr_body_pre ce cx env (EL i args) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h' raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
            (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
              ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
            (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
            (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
              ?val. read_result cx raw ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem)))))
End

Theorem raw_ctor_rows_law_completed[local]:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  (!i. i < LENGTH args ==> create_operand_completed_ok cx (EL i args)) ==>
  raw_ctor_rows_law (K T) (DF,lo,d,ctx,shctx,func,shfunc) tops ce cx env st0 args
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[raw_ctor_rows_law_def, combinTheory.K_THM, AND_CLAUSES] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] create_ctor_rows_at_cuts)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Theorem create_raw_payload_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env
    (Call ann (CreateTarget RawCreate hs rof ks) (e::av::(args ++ (if hs then [saltE] else []))) df) entry /\
  raw_ctor_rows_law A (DF,lo,d,ctx,shctx,func,shfunc) tops ce cx env st0 args /\ A p0 /\
  tys = MAP expr_type (e::av::(args ++ (if hs then [saltE] else []))) /\
  lit = blueprint_literal_offset cx hs (e::av::(args ++ (if hs then [saltE] else []))) /\
  bind (eval_exprs cx (args ++ av::(if hs then [saltE] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\ local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  explicit = gas_explicit_sites ctx shctx /\
  lenop = Var lvar /\ not_fresh_at (C 0) lvar /\
  lookup_var lvar (St 0) = SOME (n2w (LENGTH code)) /\
  uval.vs_current_bb = cv.cs_current_bb /\ uval.vs_inst_idx = LENGTH cv.cs_current_insts /\
  (if args = [] then
     cv = C 0 /\ uval = St 0 /\ size_op = lenop /\ R 0 = kwmarks
   else
     LENGTH svs = LENGTH args /\
     compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
     EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs args) /\
     sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ fn_inst_ids_distinct func /\
     (!i. i < LENGTH args ==>
       compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
       compile_expr (gas_shadow_env T ce) (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
           (EL i svs,C (SUC i)) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
           (EL i svs,Sh (SUC i)) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
       (C 0).cs_next_var <= (C i).cs_next_var /\
       (St (SUC i)).vs_labels = (St i).vs_labels /\
       ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
       (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
       R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
       create_expr_prefix (C i) (C (SUC i)) explicit ctx func
         (St i) (Chunk i ++ Snap i) (St (SUC i)) /\
       create_expr_prefix (C i) (M i) explicit ctx func (St i) (Chunk i) (Mid i) /\
       ~(Mid i).vs_halted /\ (Mid i).vs_current_bb = (M i).cs_current_bb /\
       (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
       create_expr_prefix (M i) (C (SUC i)) explicit ctx func (Mid i) (Snap i) (St (SUC i)) /\
       (if exprs_can_mutate ce (DROP (SUC i) args) then
          fn_has_code (M i) (C (SUC i)) func /\
          RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
                  ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
                 ?j ms. ctor_segment_fetch func p = SOME j /\
                   (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
                   gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
          (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
               (C (SUC i)).cs_next_id <= j.inst_id)
        else ~is_word_type (lowered_value_type ce (EL i args)) ==> Mid i = St (SUC i))) /\
     se = C (LENGTH args) /\ s = St (LENGTH args) /\
     capacity = prefix_bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
     capacity < dimword (:256) /\ w2n (n2w (LENGTH code):bytes32) <= prefix_bound /\
     not_fresh_at (C 0) src /\ lookup_var src (St 0) = SOME p /\
     ptr_covers G0 tn0 src (St 0) (w2n (n2w (LENGTH code):bytes32)) /\
     op_taint tn0 (Var lvar) = {} /\ w2n p + w2n (n2w (LENGTH code):bytes32) <= (St 0).vs_alloca_next /\
     compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
     gas_origin_edge F explicit ctx func s am (OK su) /\
     compile_copy_memory_dynamic buf.buf_operand (Var src) (Var lvar) a = ((),b) /\ fn_has_code a b func /\
     emit_op ADD [buf.buf_operand;Var lvar] b = (dst_op,st) /\ fn_has_code b st func /\
     gas_origin_edge F explicit ctx func su bm (OK sv) /\ gas_origin_edge F explicit ctx func sv cm (OK u) /\
     compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
       st = (alen,en) /\ fn_has_code st en func /\
     create_expr_prefix st en explicit ctx func u encmarks t /\
     (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
     emit_op ADD [lenop;alen] en = (size_op,cv) /\ fn_has_code en cv func /\
     create_expr_prefix en cv explicit ctx func t dm uval /\
     R (LENGTH args) = am ++ bm ++ cm ++ encmarks ++ dm ++ kwmarks /\
     c 0 = en /\ r 0 = t /\ r n = bad /\
     (!k. k < n ==>
       (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
       create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
     lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
     get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
     ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
      (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
     eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs payload ee G tn.
    A ee /\ LENGTH cvs = LENGTH args /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) cvs = SOME payload /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(cvs ++ kvs))) ee = (res,out) /\
    valid_horizon cx st0 H ee.storage_trace /\
    ee.gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env ee /\ return_buf_frame d ce cv uval /\ alloca_history func uval /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp uval) /\
    (!f i z. frag_reachable ctx func uval f i z ==> dalloca_fmp_headroom i z) /\
    ~uval.vs_halted /\ uval.vs_current_bb = cv.cs_current_bb /\
    uval.vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved ce cv /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee uval /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at (DF K) lo d ce cx ee G tn uval) /\
    (if args = [] then payload = [] /\ size_op = lenop /\ cv = C 0 /\ uval = St 0
     else (!x v. not_fresh_at (C 0) x /\ lookup_var x (St 0) = SOME v ==> lookup_var x t = SOME v) /\
       eval_operand alen t = SOME (n2w (LENGTH payload)) /\
       eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH payload)) /\
       (!x. size_op = Var x ==> not_fresh_at cv x) /\ dm = [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `args = []`
  >- (qpat_assum `args = []` (fn h =>
        qpat_x_assum `if args = [] then _ else _`
          (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
      fs[] >> suspend "empty") >>
  qpat_assum `args <> []` (fn h =>
    qpat_x_assum `if args = [] then _ else _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  suspend "rows"
QED

Resume create_raw_payload_from_replay[empty]:
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind (eval_exprs cx _) _ p0 = _`
       (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_create_operands,
          storage_trace_frame_bind_all]) >>
  disj2_tac >> qexistsl_tac [`p0`,`G0`,`tn0`] >>
  qpat_assum `tys = _` (pure_once_rewrite_tac o single o SYM) >>
  qpat_assum `lit = _` (pure_once_rewrite_tac o single o SYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_raw_payload_from_replay[rows]:
  qabbrev_tac `k = \vs. bind (eval_exprs cx (av::(if hs then [saltE] else [])))
    (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(vs ++ kvs)))` >>
  `bind (eval_exprs cx args) k p0 = (res,out)` by
    (qpat_assum `bind (eval_exprs cx (args ++ _)) _ p0 = _`
       (mp_tac o REWRITE_RULE [blueprint_abi_bind_append]) >> simp[Abbr `k`]) >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  qhdtm_assum `raw_ctor_rows_law`
    (mp_tac o SPEC_ALL o REWRITE_RULE [raw_ctor_rows_law_def]) >>
  (impl_tac >- suspend "rows_premises") >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  suspend "encoder"
QED

Resume create_raw_payload_from_replay[rows_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (rpt strip_tac >> irule create_call_operand_body_pre >> simp[EL_MEM] >>
      goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  qpat_assum `explicit = _` (fn he => rule_assum_tac (PURE_REWRITE_RULE[he])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> fs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  disch_tac >> irule ctor_observed_cut_silent >>
  qexistsl_tac [`ctx`,`((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts)`,
    `gas_explicit_sites ctx shctx`,`func`,`St (SUC i)`,`Mid i`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  irule RTC_MONOTONE >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _`
    (irule_at Any o REWRITE_RULE [create_expr_prefix_marked]) >>
  simp[create_marked_edge_def,create_prefix_step_def,FORALL_PROD,PAIR_EQ] >> metis_tac[]
QED

Resume create_raw_payload_from_replay[encoder]:
  `ci_mono (C 0) se` by
    (qpat_assum `se = _` (pure_rewrite_tac o single) >>
     qspecl_then [`compile_expr`,`ce`,`args`,`C 0`] mp_tac ci_mono_compile_create_ctor_args >>
     (impl_tac >- simp_tac bool_ss [cj 1 ci_mono_compile_expr_sa]) >>
     qpat_assum `compile_create_ctor_args _ _ _ _ = _` (pure_rewrite_tac o single) >>
     simp[]) >>
  `local_ptrs_reserved ce se /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (qpat_assum `ci_mono (C 0) se`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     drule_all blueprint_keyword_mono >> simp[]) >>
  mp_tac (Q.INST [`len` |-> `lvar`,`nword` |-> `n2w (LENGTH (code:word8 list)):bytes32`,
                   `ee` |-> `E (LENGTH args)`] (SPEC_ALL create_raw_encoder_at_cuts)) >>
  (impl_tac >- suspend "encoder_premises") >> strip_tac >>
  rename1 `encode_create_ctor_args _ _ vs = SOME bytes` >>
  rename1 `op_taint tt alen = {}` >>
  suspend "add"
QED

Resume create_raw_payload_from_replay[encoder_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (sym_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexists_tac `H` >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (REFL_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac[] >> NO_TAC) >>
  TRY (qpat_assum `E 0 = p0` (fn h => pure_rewrite_tac[h]) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `s = St _` (pure_rewrite_tac o single) >>
       qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
         (qspec_then `LENGTH args` (map_every assume_tac o CONJUNCTS o REWRITE_RULE[LESS_EQ_REFL])) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (map_every qx_gen_tac [`i`,`g`,`h`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
       qpat_assum `!i. i < LENGTH args ==> bind _ _ (E i) = _ /\ _`
         (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
       first_assum (qspecl_then [`g`,`h`] mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then ACCEPT_TAC >> NO_TAC) >>
  qx_gen_tac `i` >> disch_tac >> suspend "encoder_rows"
QED

Resume create_raw_payload_from_replay[encoder_rows]:
  `i <= LENGTH args` by decide_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH args ==> bind _ _ (E i) = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (disch_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >>
  qpat_x_assum `if exprs_can_mutate ce (DROP (SUC i) args) then _ else _` mp_tac >>
  Cases_on `exprs_can_mutate ce (DROP (SUC i) args)`
  >- (qpat_assum `exprs_can_mutate ce (DROP (SUC i) args)` (simp_tac bool_ss o single) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `~exprs_can_mutate ce (DROP (SUC i) args)` (simp_tac bool_ss o single) >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume create_raw_payload_from_replay[add]:
  drule_all (Q.INST [`a` |-> `en`,`b` |-> `cv`,`s` |-> `t`,`t` |-> `uval`,
                     `PG` |-> `[]:(num # num) option list`]
              create_raw_total_add_entry_at_cuts) >> strip_tac >>
  rename1 `size_op = Var sumvar` >>
  rename1 `Gv = step_prov _ _ _ _` >>
  rename1 `tv = step_taint _ _ _ _` >>
  suspend "finish"
QED

Resume create_raw_payload_from_replay[finish]:
  qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH args` (map_every assume_tac o CONJUNCTS o REWRITE_RULE[LESS_EQ_REFL])) >>
  map_every (fn (mark, edge) =>
    qpat_assum mark (fn h => qpat_assum edge
      (assume_tac o MATCH_MP raw_payload_silent_readings o PURE_REWRITE_RULE[h])))
    [(`am = []`,`gas_origin_edge F explicit ctx func s am (OK su)`),
     (`bm = []`,`gas_origin_edge F explicit ctx func su bm (OK sv)`),
     (`cm = []`,`gas_origin_edge F explicit ctx func sv cm (OK u)`)] >>
  qpat_assum `create_expr_prefix st en explicit ctx func u encmarks t`
    (assume_tac o MATCH_MP create_prefix_readings) >>
  `(E (LENGTH args)).gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail` by
    asm_rewrite_tac[APPEND,LENGTH,DROP] >>
  `eval_operand lenop t = SOME (n2w (LENGTH code))` by
    (qpat_assum `lenop = Var lvar` (pure_rewrite_tac o single) >>
     rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH bytes))` by
    (qpat_assum `eval_operand size_op uval = SOME (_ + _)` mp_tac >>
     rpt (qpat_x_assum `eval_operand size_op uval = _` kall_tac) >>
     metis_tac[word_add_n2w,optionTheory.SOME_11]) >>
  qunabbrev_tac `k` >> disj2_tac >>
  qexistsl_tac [`vs`,`bytes`,`E (LENGTH args)`,`Gv`,`tv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qpat_assum `(\vs. _) vs (E (LENGTH args)) = (res,out)`
        (ACCEPT_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)))
  >- (qpat_assum `wb_frame ce (E 0) _ _ _ _`
        (ACCEPT_TAC o cj 1 o REWRITE_RULE[wb_frame_def])) >>
  rpt strip_tac >> gvs[]
QED
Finalise create_raw_payload_from_replay

Theorem create_raw_payload_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env
    (Call ann (CreateTarget RawCreate hs rof ks) (e::av::(args ++ (if hs then [saltE] else []))) df) entry /\
  EVERY (create_operand_completed_ok cx)
    (create_operand_order RawCreate hs (e::av::(args ++ (if hs then [saltE] else [])))) /\
  tys = MAP expr_type (e::av::(args ++ (if hs then [saltE] else []))) /\
  lit = blueprint_literal_offset cx hs (e::av::(args ++ (if hs then [saltE] else []))) /\
  bind (eval_exprs cx (args ++ av::(if hs then [saltE] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\ local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  explicit = gas_explicit_sites ctx shctx /\
  lenop = Var lvar /\ not_fresh_at (C 0) lvar /\
  lookup_var lvar (St 0) = SOME (n2w (LENGTH code)) /\
  uval.vs_current_bb = cv.cs_current_bb /\ uval.vs_inst_idx = LENGTH cv.cs_current_insts /\
  (if args = [] then
     cv = C 0 /\ uval = St 0 /\ size_op = lenop /\ R 0 = kwmarks
   else
     LENGTH svs = LENGTH args /\
     compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
     EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs args) /\
     sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ fn_inst_ids_distinct func /\
     (!i. i < LENGTH args ==>
       compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
       compile_expr (gas_shadow_env T ce) (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
           (EL i svs,C (SUC i)) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
           (EL i svs,Sh (SUC i)) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
       (C 0).cs_next_var <= (C i).cs_next_var /\
       (St (SUC i)).vs_labels = (St i).vs_labels /\
       ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
       (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
       R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
       create_expr_prefix (C i) (C (SUC i)) explicit ctx func
         (St i) (Chunk i ++ Snap i) (St (SUC i)) /\
       create_expr_prefix (C i) (M i) explicit ctx func (St i) (Chunk i) (Mid i) /\
       ~(Mid i).vs_halted /\ (Mid i).vs_current_bb = (M i).cs_current_bb /\
       (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
       create_expr_prefix (M i) (C (SUC i)) explicit ctx func (Mid i) (Snap i) (St (SUC i)) /\
       (if exprs_can_mutate ce (DROP (SUC i) args) then
          fn_has_code (M i) (C (SUC i)) func /\
          RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
                  ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
                 ?j ms. ctor_segment_fetch func p = SOME j /\
                   (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
                   gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
          (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
               (C (SUC i)).cs_next_id <= j.inst_id)
        else ~is_word_type (lowered_value_type ce (EL i args)) ==> Mid i = St (SUC i))) /\
     se = C (LENGTH args) /\ s = St (LENGTH args) /\
     capacity = prefix_bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
     capacity < dimword (:256) /\ w2n (n2w (LENGTH code):bytes32) <= prefix_bound /\
     not_fresh_at (C 0) src /\ lookup_var src (St 0) = SOME p /\
     ptr_covers G0 tn0 src (St 0) (w2n (n2w (LENGTH code):bytes32)) /\
     op_taint tn0 (Var lvar) = {} /\ w2n p + w2n (n2w (LENGTH code):bytes32) <= (St 0).vs_alloca_next /\
     compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
     gas_origin_edge F explicit ctx func s am (OK su) /\
     compile_copy_memory_dynamic buf.buf_operand (Var src) (Var lvar) a = ((),b) /\ fn_has_code a b func /\
     emit_op ADD [buf.buf_operand;Var lvar] b = (dst_op,st) /\ fn_has_code b st func /\
     gas_origin_edge F explicit ctx func su bm (OK sv) /\ gas_origin_edge F explicit ctx func sv cm (OK u) /\
     compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
       st = (alen,en) /\ fn_has_code st en func /\
     create_expr_prefix st en explicit ctx func u encmarks t /\
     (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
     emit_op ADD [lenop;alen] en = (size_op,cv) /\ fn_has_code en cv func /\
     create_expr_prefix en cv explicit ctx func t dm uval /\
     R (LENGTH args) = am ++ bm ++ cm ++ encmarks ++ dm ++ kwmarks /\
     c 0 = en /\ r 0 = t /\ r n = bad /\
     (!k. k < n ==>
       (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
       create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
     lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
     get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
     ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
      (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
     eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs payload ee G tn.
    LENGTH cvs = LENGTH args /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) cvs = SOME payload /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(cvs ++ kvs))) ee = (res,out) /\
    valid_horizon cx st0 H ee.storage_trace /\
    ee.gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env ee /\ return_buf_frame d ce cv uval /\ alloca_history func uval /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp uval) /\
    (!f i z. frag_reachable ctx func uval f i z ==> dalloca_fmp_headroom i z) /\
    ~uval.vs_halted /\ uval.vs_current_bb = cv.cs_current_bb /\
    uval.vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved ce cv /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee uval /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at (DF K) lo d ce cx ee G tn uval) /\
    (if args = [] then payload = [] /\ size_op = lenop /\ cv = C 0 /\ uval = St 0
     else (!x v. not_fresh_at (C 0) x /\ lookup_var x (St 0) = SOME v ==> lookup_var x t = SOME v) /\
       eval_operand alen t = SOME (n2w (LENGTH payload)) /\
       eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH payload)) /\
       (!x. size_op = Var x ==> not_fresh_at cv x) /\ dm = [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. i < LENGTH args ==> create_operand_completed_ok cx (EL i args)` by
    (qpat_x_assum `EVERY (create_operand_completed_ok cx) _` mp_tac >>
     Cases_on `hs` >>
     simp[create_operand_order_def,EVERY_APPEND,DROP_PREFIX,TAKE_APPEND1] >>
     strip_tac >>
     qpat_x_assum `EVERY (create_operand_completed_ok cx) args`
       (mp_tac o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
  mp_tac (Q.INST [`A` |-> `K T`] (SPEC_ALL create_raw_payload_from_replay)) >>
  pure_rewrite_tac[combinTheory.K_THM, AND_CLAUSES] >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                irule raw_ctor_rows_law_completed >> simp[])) >>
  disch_then ACCEPT_TAC
QED
