(* Composition of the fixed RawLog data continuation. *)
Theory bodyFullRawLogFixedCompose
Ancestors
  bodyFullRawLogFixedBoundary bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasOutcomeFullStmts gasShadowState gasShadow bodyFullShared
  exprLoweringProps exprOperandVar exprSimProps exprSimWordArgs
  stmtSimDefs exprSimMemDefs exprSimDefs gasExemptCert
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyPtrDefs
  loweringShapeDefs vyperInterpreter vyperState vyperValue vyperEvent
  venomState words list rich_list arithmetic finite_map pred_set

(* Reanchor the scalar child's frame across the scratch allocation. *)
Theorem raw_log_fixed_data_reanchor:
  compile_alloc_buffer 32 sa = (buf,sd) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  expr_post H ctx func cenv cx data es sd sm u ee v op t /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) ==>
  expr_post H ctx func cenv cx data es sa sm s ee v op t
Proof
  strip_tac >>
  `wb_frame cenv es es sa s u` by
    simp[wb_frame_def, locals_kept_mem] >>
  `wb_frame cenv es ee sa s t` by
    (irule wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`es`, `sd`, `u`] >> simp[] >>
         metis_tac[expr_post_frame]) >>
     metis_tac[]) >>
  `~expr_has_effect data ==> pure_frame cenv func es sa s t` by
    (strip_tac >> irule pure_frame_trans >> simp[] >>
     qexistsl [`es`, `sd`, `u`] >>
     fs[expr_post_def, pure_frame_def] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  fs[expr_post_def, wb_frame_def, expr_val_at_def,
     compileEnvTheory.is_word_type_def] >> first_assum MATCH_ACCEPT_TAC
QED

(* Endpoint hypotheses are universally closed: this proof does not depend on
   the independent concrete allocation or MSTORE/LOG publications. *)
Theorem raw_log_fixed_data_full_from_endpoints:
  (!data cenv ret_ty ty topics dflt call_sa vv call_sb sm buf sd func ctx
      cx st0 ee DF lo explicit PG s G tn d.
    expr_type data = BaseT (BytesT (Fixed 32)) /\
    compile_call compile_expr cenv ret_ty ty RawLog [topics;data] dflt call_sa = (vv,call_sb) /\
    compile_alloc_buffer 32 sm = (buf,sd) /\ fn_has_code sm sd func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\ return_buf_frame d cenv sm s /\
      alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
      s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u Gu tnu p w. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u /\ return_buf_frame d cenv sd u /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
      u.vs_inst_idx = LENGTH sd.cs_current_insts /\ buf.buf_operand = Var p /\
      not_fresh_at sd p /\ eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      u.vs_memory = s.vs_memory /\ tnu.t_mem = tn.t_mem UNION new_site_bytes s u /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b n. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      (!name b n. local_region cenv ee.scopes u name b n ==> regions_disjoint (w2n w) 32 b n) /\
      ghost_kept_at lo cenv ee sm G tn s Gu tnu) ==>
  (!buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2) ==>
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx data es sd data_op sm
      shadow_sd shadow_sm sa shadow_sa s0 G0 tn0 st0 vals ops ann es_call dflt
      buf s1 sb ret_ty ty topics call_sa vv call_sb.
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type data) data es /\
    lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
    lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)
      shadow_sd = (data_op,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_state sd shadow_sd /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sd func /\ fn_has_code sd sm func /\
    fn_has_code shadow_sa shadow_sd shadow_func /\ fn_has_code shadow_sd shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_admissible
      (bind (bind (eval_expr cx data) (read_result cx))
        (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
                type_check (LENGTH vals <= 4) "raw_log too many topics";
                push_log (encode_raw_event_values cx.txn.target vals bs);
                return NoneV od)) expr_res_ok es /\
    LENGTH vals <= 4 /\ LENGTH ops = LENGTH vals /\ LENGTH ops < dimword (:256) /\
    EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn0 op = {}) ops) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\
    post_value_type cenv data = expr_type data /\
    evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    compile_alloc_buffer 32 sa = (buf,sd) /\
    compile_alloc_buffer 32 shadow_sa = (buf,shadow_sd) /\
    emit_inst MSTORE [buf.buf_operand;data_op] [] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    fn_has_code sm sb func /\
    compile_call compile_expr cenv ret_ty ty RawLog [topics;data] dflt call_sa = (vv,call_sb) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (bind (eval_expr cx data) (read_result cx))
        (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
                type_check (LENGTH vals <= 4) "raw_log too many topics";
                push_log (encode_raw_event_values cx.txn.target vals bs);
                return NoneV od)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post H ctx func cenv cx (Call ann RawLog es_call dflt)
          es sa sb s0 ee v (Lit 0w) t /\
        expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) v (Lit 0w) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) v (Lit 0w) G tn t /\
        (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
          ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r))
Proof
  disch_then (mk_asm "alloc_endpoint") >>
  disch_then (mk_asm "tail_endpoint") >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- suspend "source_frame" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\ return_buf_frame d cenv sa s0 /\
    alloca_history func s0 /\ ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `?u Gu tnu p w. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx es u /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es Gu tnu u /\ return_buf_frame d cenv sd u /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
      u.vs_inst_idx = LENGTH sd.cs_current_insts /\ buf.buf_operand = Var p /\
      not_fresh_at sd p /\ eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      u.vs_memory = s0.vs_memory /\ tnu.t_mem = tn0.t_mem UNION new_site_bytes s0 u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
         regions_disjoint (w2n w) 32 b n) /\
      (!name b n. local_region cenv es.scopes u name b n ==>
         regions_disjoint (w2n w) 32 b n) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu` by
    (asm "alloc_endpoint" irule >> simp[] >>
     qexistsl [`call_sa`, `call_sb`, `data`, `ARB`, `ret_ty`, `topics`, `ARB`, `vv`] >>
     simp[] >>
     qpat_x_assum `compile_call _ _ _ _ RawLog _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_call_def]) >>
  FAIL_TAC "allocation prefix"
QED

Resume raw_log_fixed_data_full_from_endpoints[source_frame]:
  irule storage_trace_frame_bind_all >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  reverse conj_tac >- simp[storage_trace_frame_lifts] >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED
Finalise raw_log_fixed_data_full_from_endpoints
