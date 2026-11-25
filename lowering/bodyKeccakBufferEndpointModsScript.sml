(* The read-only Keccak suffix, with one endpoint at every valid horizon. *)
Theory bodyKeccakBufferEndpointMods
Ancestors
  bodyMethodIdHashDynamicMods exprSimHashBoundary exprSimVVFrame
  allocasBelowFmpUpdatesProps exprSimHash bodyFullPostsMods loweringPosts
  compileEnv vyperTypeSystem vyperTyping vyperStorageTrace venomState words
  venomExecSemantics list finite_map

val buffer_layout = ``
  ((?k. expr_type e = BaseT (BytesT (Dynamic k)) /\ v = BytesV payload) \/
   (?k str. expr_type e = BaseT (StringT k) /\ v = StringV str /\
           payload = MAP (n2w o ORD) str))``;

Theorem keccak_buffer_payload_view[local]:
  ^buffer_layout /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  expr_type e = BaseT bty /\
  expr_post H ctx func cenv cx e es sa sm s0 mid v x s ==>
  ?b. eval_operand x s = SOME (n2w b) /\
      mem_word_at b s.vs_memory = n2w (LENGTH payload) /\
      mem_bytes_at (b + 32) (LENGTH payload) s.vs_memory = payload /\
      b + 32 < dimword (:256) /\ LENGTH payload < dimword (:256)
Proof
  strip_tac >> gvs[]
  >- (drule_at (Pos hd) hash_dynamic_post_view >> simp[]) >>
  drule_at (Pos hd) hash_string_post_view >> simp[]
QED

Theorem keccak_buffer_endpoint_mods:
  expr_type e = BaseT bty /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\ ^buffer_layout /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytes x sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sm s /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
     (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (post_value_type cenv e) v x s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?raw u Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK raw /\
    u = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
      vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
        es sa sb s0 mid (Value (BytesV (Keccak_256_w64 payload)))
        (StackValue (BaseT (BytesT (Fixed 32))) op) u /\
      immutable_frame_mods func cenv cx mid u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gf tf u /\
      ghost_kept_at lo cenv mid sm G tn s Gf tf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type (expr_type e) /\ is_bytes_or_string_type (expr_type e)` by
    (qpat_assum `(?k. expr_type e = _ /\ _) \/ _` mp_tac >>
     strip_tac >> simp[is_bytestring_type_def, is_bytes_or_string_type_def]) >>
  `compile_method_id_hash (expr_type e) x sm = (op,sb)` by
    (simp[method_id_hash_as_keccak]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (expr_type e) v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     gvs[post_value_type_bytestring]) >>
  drule_all method_id_hash_dynamic_mods >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `u = (_ with vs_inst_idx := _)` SUBST1_TAC >>
     qpat_assum `(_ with vs_vars := _) = s`
       (mp_tac o Q.AP_TERM `allocas_below_fmp`) >>
     simp[NoAsms, allocas_below_fmp_updates] >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rename1 `run_inst_seq (emitted_insts sm sb) s = OK raw` >>
  qexistsl [`raw`, `u`, `Gh`, `tnh`] >> simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_all_then strip_assume_tac keccak_buffer_payload_view >>
  drule_all_then (qx_choose_then `raw'` strip_assume_tac) keccak_memory_post_run >>
  `raw' = raw` by metis_tac[exec_result_11] >>
  qpat_x_assum `raw' = raw` SUBST_ALL_TAC >>
  qpat_assum `u = (_ with vs_inst_idx := _)` SUBST_ALL_TAC >>
  simp[vv_post_inst_idx]
QED
