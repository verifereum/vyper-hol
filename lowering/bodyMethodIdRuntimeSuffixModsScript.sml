(* Compose the linked hash, selector, and optional output allocation. *)
Theory bodyMethodIdRuntimeSuffixMods
Ancestors
  bodyMethodIdRuntimeInputMods bodyMethodIdHashDynamicMods bodyMethodIdHashFixedMods
  bodyMethodIdScratchFrameMods bodyMethodIdSelectorMods bodyMethodIdOutputBufferMods
  bodyMethodIdRuntimePostsMods bodyMemBiMethodIdEndpoint bodyFullUnwrapRun
  builtinHashing bodyMemoryDefs
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit bodyPtrDefs exprSimHash
  exprSimMemDefs exprSimVVFrame exprLowering exprLoweringProps emitHelperProps valueEncoding context
  fragGasOriginPtrLoop storageCopyBodyPtr loweringPosts stateRelProj compileEnv freshWrites rich_list
  vyperAST vyperTypeSystem vyperValue vyperState vyperInterpreter vyperStorageTrace
  vyperStorageFootprint venomMemDefs venomState venomInst list finite_map pred_set words arithmetic
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem method_horizon_extract[local]:
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> P H) ==>
  P (storage_trace_horizon mid.storage_trace)
Proof
  simp[storage_trace_domain_def]
QED

Theorem method_clean_keep[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sk.cs_next_var /\
  (!q. not_fresh_at sk q ==> lookup_var q z = lookup_var q s /\
       FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem method_cursor_join[local]:
  k1.cs_current_insts = k0.cs_current_insts ++ emitted_insts k0 k1 /\
  k2.cs_current_insts = k1.cs_current_insts ++ emitted_insts k1 k2 /\
  run_inst_seq (emitted_insts k0 k1) s = OK raw /\
  u = (raw with vs_inst_idx := LENGTH k1.cs_current_insts) /\
  run_inst_seq (emitted_insts k1 k2) u = OK raw' /\
  z = (raw' with vs_inst_idx := LENGTH k2.cs_current_insts) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts k1 k2) ==>
  ?t. run_inst_seq (emitted_insts k0 k2) s = OK t /\
      z = (t with vs_inst_idx := LENGTH k2.cs_current_insts)
Proof
  strip_tac >> drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
  irule run_inst_seq_cursor_append >> metis_tac[]
QED

Theorem method_selector_layout[local]:
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (word,sp) ==>
  sp.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sp /\
  sh.cs_next_var <= sp.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sp)
Proof
  strip_tac >>
  qpat_assum `emit_op SHR _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op SHL _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `?xs ys. sn.cs_current_insts = sh.cs_current_insts ++ [xs] /\
    sp.cs_current_insts = sn.cs_current_insts ++ [ys] /\
    ~is_terminator xs.inst_opcode /\ ~is_terminator ys.inst_opcode` by
    (qexistsl_tac [`mk_inst sh.cs_next_id SHR [Lit 224w;hash] [STRING #"%" (toString sh.cs_next_var)]`,
                   `mk_inst sn.cs_next_id SHL [Lit 224w;sel] [STRING #"%" (toString sn.cs_next_var)]`] >>
     asm_rewrite_tac[] >> simp[mk_inst_def, is_terminator_def]) >>
  `sh.cs_next_var <= sp.cs_next_var` by decide_tac >>
  `sp.cs_current_insts = sh.cs_current_insts ++ [xs;ys]` by
    (qpat_assum `sp.cs_current_insts = sn.cs_current_insts ++ [ys]`
       (once_rewrite_tac o single) >>
     qpat_assum `sn.cs_current_insts = sh.cs_current_insts ++ [xs]`
       (once_rewrite_tac o single) >>
     pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  `emitted_insts sh sp = [xs;ys]` by
    (pure_rewrite_tac[emitted_insts_def] >> pop_assum (once_rewrite_tac o single) >>
     simp[DROP_LENGTH_APPEND]) >>
  asm_rewrite_tac[EVERY_DEF] >> BETA_TAC >> asm_rewrite_tac[]
QED

(* Normalize the two hash implementations to the same linked landing. *)
Theorem method_id_linked_hash_landing[local]:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sm s /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ storage_trace_domain cx st0 mid.storage_trace /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (expr_type e) v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?bs t h Gh tnh.
    LENGTH bs = 32 /\
    (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL (BytesV (TAKE 4 bs))) /\
    run_inst_seq (emitted_insts sm sh) s = OK t /\
    h = (t with vs_inst_idx := LENGTH sh.cs_current_insts) /\
    eval_operand hash h = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
    op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
    ~h.vs_halted /\ h.vs_current_bb = sh.cs_current_bb /\
    h.vs_inst_idx = LENGTH sh.cs_current_insts /\ alloca_history func h /\
    local_ptrs_reserved cenv sh /\ return_buf_frame d cenv sh h /\
    s.vs_alloca_next <= h.vs_alloca_next /\ immutable_frame_mods func cenv cx mid h /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gh tnh /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK h,Gh,tnh) /\
      stmt_state_rel H ctx func cenv cx mid h /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gh tnh h)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- suspend "dynamic" >>
  suspend "fixed"
QED

Resume method_id_linked_hash_landing[dynamic]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (expr_type e) v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s)` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all method_id_hash_dynamic_mods >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gh tnh` by
    (irule method_clean_keep >> qexistsl [`G`, `s`, `sm`, `tn`, `u`] >> simp[]) >>
  qexistsl [`bs`, `t`, `u`, `Gh`, `tnh`] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume method_id_linked_hash_landing[fixed]:
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
    ghost_inv_at (DF H) 0 d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     gvs[expr_post_mods_def] >> irule method_id_ghost_at_zero >> goal_assum (drule_at Any)) >>
  drule_all method_id_hash_fixed_scratch_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gh tnh` by
    (irule method_clean_keep >> qexistsl [`G`, `s`, `sm`, `tn`, `u`] >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gh,tnh) /\
    stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gh tnh u /\
    immutable_frame_mods func cenv cx mid u` by suspend "restore" >>
  `immutable_frame_mods func cenv cx mid u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _ /\ _ /\ _ /\ immutable_frame_mods _ _ _ _ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl [`bs`, `t`, `u`, `Gh`, `tnh`] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _ /\ _ /\ _ /\ immutable_frame_mods _ _ _ _ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume method_id_linked_hash_landing[restore]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `immutable_frame_mods func cenv cx mid s` by fs[expr_post_mods_def] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  irule method_id_scratch_frame_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G`, `b`,
    `mk_inst sm.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sm.cs_next_var)]`,
    `sm`, `32`, `s`, `tn`] >>
  qpat_x_assum `u = t with vs_inst_idx := _` kall_tac >>
  `!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s /\
       FLOOKUP Gh p = FLOOKUP G p /\ FLOOKUP tnh.t_var p = FLOOKUP tn.t_var p` by
    (gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at sm p ==> lookup_var p u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED

Finalise method_id_linked_hash_landing[local]

Theorem method_id_selected_word_landing_mods[local]:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
  fn_has_code sm sh func /\ fn_has_code sh sp func /\ fn_inst_ids_distinct func /\
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (word,sp) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sm s /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ storage_trace_domain cx st0 mid.storage_trace /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (expr_type e) v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?bs raw u Gu tnu.
    LENGTH bs = 4 /\
    (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL (BytesV bs)) /\
    run_inst_seq (emitted_insts sm sp) s = OK raw /\
    sp.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sp /\
    u = (raw with vs_inst_idx := LENGTH sp.cs_current_insts) /\
    eval_operand word u = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV bs)) /\
    TAKE 4 (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV bs))) = bs /\
    op_taint tnu word = {} /\ op_prov Gu word = NONE /\
    (!p. word = Var p ==> not_fresh_at sp p) /\
    ~u.vs_halted /\ u.vs_current_bb = sp.cs_current_bb /\
    u.vs_inst_idx = LENGTH sp.cs_current_insts /\ alloca_history func u /\
    s.vs_alloca_next <= u.vs_alloca_next /\ sa.cs_next_var <= sp.cs_next_var /\
    local_ptrs_reserved cenv sp /\ return_buf_frame d cenv sp u /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p) /\
    immutable_frame_mods func cenv cx mid u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tnu u)
Proof
  strip_tac >>
  drule_all method_id_linked_hash_landing >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh` by suspend "hash_layout" >>
  drule_all method_id_hash_grows >> strip_tac >>
  drule_all method_selector_layout >> strip_tac >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sh p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sh p)` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid h /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gh tnh h` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `!ann. builtin_result _ _ ann _ _ _ = _`
    (qspec_then `BaseT (BytesT (Fixed 4))` assume_tac) >>
  drule_all method_id_selector_run_mods >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `eval_operand word u = SOME _` >>
  suspend "package"
QED

Resume method_id_selected_word_landing_mods[hash_layout]:
  `compile_keccak256_bytes x sm = (hash,sh) \/ ?m. compile_keccak256_bytesm x m sm = (hash,sh)` by
    (qpat_x_assum `compile_method_id_hash _ _ _ = _` mp_tac >>
     qpat_x_assum `expr_type e = BaseT bty` SUBST_ALL_TAC >>
     qpat_x_assum `is_bytes_or_string_type (BaseT bty)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `bty` >> simp[is_bytes_or_string_type_def, compile_method_id_hash_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[compile_method_id_hash_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> metis_tac[keccak_suffix_shape]
QED

Resume method_id_selected_word_landing_mods[package]:
  `u.vs_alloca_next = h.vs_alloca_next` by
    (qpat_assum `u with <|vs_vars := _; vs_inst_idx := _|> = h` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sa.cs_next_var <= sp.cs_next_var /\ s.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv sp u` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `h`, `sh`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!p. not_fresh_at sh p ==> lookup_var p u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sp p)` by
    metis_tac[not_fresh_at_mono] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule method_clean_keep >> qexistsl [`Gh`, `h`, `sh`, `tnh`, `u`] >>
     `sa.cs_next_var <= sh.cs_next_var` by decide_tac >> simp[]) >>
  `LENGTH (TAKE 4 bs) = 4` by simp[LENGTH_TAKE] >>
  `eval_operand word u = SOME
    (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs)))` by
    fs[hash_full_bytes_roundtrip] >>
  `TAKE 4 (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs)))) =
    TAKE 4 bs` by
    (mp_tac (Q.INST [`bd` |-> `Fixed 4`, `bs` |-> `TAKE 4 bs`] typed_bytes_prefix) >> simp[]) >>
  suspend "compose"
QED

Resume method_id_selected_word_landing_mods[compose]:
  `sp.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sp` by
    (drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
     qpat_assum `sp.cs_current_insts = sh.cs_current_insts ++ _` (once_rewrite_tac o single) >>
     qpat_assum `sh.cs_current_insts = sm.cs_current_insts ++ _` (once_rewrite_tac o single) >>
     simp[APPEND_ASSOC]) >>
  `u = raw with vs_inst_idx := LENGTH sp.cs_current_insts` by
    (qpat_assum `raw with vs_inst_idx := _ = u` mp_tac >>
     qpat_assum `h.vs_inst_idx = _` (once_rewrite_tac o single) >>
     qpat_assum `sp.cs_current_insts = sh.cs_current_insts ++ _` (once_rewrite_tac o single) >>
     simp[NoAsms]) >>
  drule_all method_cursor_join >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sp) s = OK whole` >>
  qexistsl [`TAKE 4 bs`, `whole`, `u`, `G'`, `tn'`] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (h,Gh,tnh) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  reverse conj_tac >- simp[] >>
  irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
QED

Finalise method_id_selected_word_landing_mods[local]


val method_arg_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx e es sa sm s0 mid v x t /\
  expr_store_bound cx (expr_type e) v x t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx mid G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val method_expr = ``Builtin ann MethodId [e]``;
val method_vv = ``if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)``;
val method_value_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ^method_expr es sa sb s0 mid r op z /\
  expr_store_bound cx ann r op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\
  s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx mid G' tn' z /\
  ptr_val_ok cx ann r op G' tn' z /\ (~fixed ==> ptr_buf_ok cenv ^method_expr op G' z) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'``;
val method_vv_post = ``
  vv_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ^method_expr es sa sb s0 mid (Value r) ^method_vv z /\
  vv_store_bound cx ann (lowered_value_type cenv ^method_expr) mid (Value r) ^method_vv z /\
  ptr_vv_ok cx ann (Value r) ^method_vv mid G' tn' z``;
val method_tail = ``\v (mid:evaluation_state).
  ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
    INL r => INL ((encode:value -> 'a) r) | INR ex => INR ex),mid)``;
val method_suffix = ``
  !DF lo d explicit ctx func PG exps src tops cenv cx env ann e es sa sm sb s0 st0
     mid v x t G0 tn0 G tn fixed op.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    expr_body_pre_mods mods cenv cx env ^method_expr es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok_mods (H : (bool # 256 word # type_value) list # num list) (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> ^method_arg_post) ==>
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
        ^method_value_post /\ ^method_vv_post)``;

(* Typed posts observe the location and operand, not the ptr_buf field. *)
Theorem method_typed_memory_posts[local]:
  (vv_post H ctx func cenv cx e es sa sb s0 mid v
     (if fixed then StackValue ft op else LocatedValue dt
       <|ptr_location := LocMemory; ptr_operand := op|>) z <=>
   vv_post H ctx func cenv cx e es sa sb s0 mid v
     (if fixed then StackValue ft op else LocatedValue dt (mk_ptr op LocMemory)) z) /\
  (vv_store_bound cx ty lty mid v
     (if fixed then StackValue ft op else LocatedValue dt
       <|ptr_location := LocMemory; ptr_operand := op|>) z <=>
   vv_store_bound cx ty lty mid v
     (if fixed then StackValue ft op else LocatedValue dt (mk_ptr op LocMemory)) z)
Proof
  Cases_on `fixed` >>
  simp[mk_ptr_def, vv_post_def, vv_holds_def, vv_at_def, vv_place_ptr_def,
       vv_own_def, vv_storage_live_def, vv_store_bound_def]
QED

Theorem method_cursor_posts[local]:
  vv_post H ctx func cenv cx e es sa sb s0 mid v vv raw /\
  vv_store_bound cx ty lty mid v vv raw /\
  z = (raw with vs_inst_idx := idx) ==>
  vv_post H ctx func cenv cx e es sa sb s0 mid v vv z /\
  vv_store_bound cx ty lty mid v vv z
Proof
  strip_tac >> gvs[vv_post_inst_idx, vv_store_bound_def,
                   ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
QED

Theorem method_id_runtime_suffix_mods:
  ^method_suffix
Proof
  rpt gen_tac >> disch_tac >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
    s0.vs_alloca_next <= t.vs_alloca_next` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then strip_assume_tac method_id_runtime_input_mods >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  `alloca_history func t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
    expr_store_bound cx (expr_type e) v x t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_store_bound _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all method_id_selected_word_landing_mods >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `?raw' z Gz tnz.
     run_inst_seq (emitted_insts sm sb) t = OK raw' /\
     z = (raw' with vs_inst_idx := LENGTH sb.cs_current_insts) /\
     z.vs_current_bb = sb.cs_current_bb /\
     z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
     expr_store_bound cx ann (BytesV bs) op z /\
     ptr_val_ok cx ann (BytesV bs) op Gz tnz z /\
     ptr_vv_ok cx ann (Value (BytesV bs)) ^method_vv mid Gz tnz z /\
     (~fixed ==> ptr_buf_ok cenv ^method_expr op Gz z) /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,Gz,tnz) /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid Gz tnz z /\
       immutable_frame_mods func cenv cx mid z)` by
    (Cases_on `fixed` >- suspend "fixed" >> suspend "dynamic") >>
  suspend "posts"
QED

Resume method_id_runtime_suffix_mods[fixed]:
  rule_assum_tac (REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `op = word /\ sb = sp` strip_assume_tac >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`ann = _`, `op = word`, `sb = sp`] >>
  pure_rewrite_tac[COND_CLAUSES, NOT_CLAUSES, F_IMP, AND_CLAUSES] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ s0.vs_alloca_next <= _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  qexistsl [`raw`, `u`, `Gu`, `tnu`] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  (conj_tac >- simp[expr_store_bound_def, is_word_type_def]) >>
  (conj_tac >- (irule ptr_val_ok_word >> simp[is_word_type_def])) >>
  (conj_tac >- simp[ptr_vv_ok_def, read_result_def, return_def, ptr_val_ok_def, is_word_type_def]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume method_id_runtime_suffix_mods[dynamic]:
  rule_assum_tac (REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `?buf su data sd st. compile_alloc_buffer 64 _ = _ /\ _` strip_assume_tac >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC) [`ann = _`, `op = _`] >>
  pure_rewrite_tac[COND_CLAUSES, NOT_CLAUSES, AND_CLAUSES] >>
  rename1 `compile_alloc_buffer 64 sp = (buf,sbuf)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\
    ghost_inv_at (DF H) 0 d cenv cx mid Gu tnu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     imp_res_tac method_id_ghost_at_zero >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (disch_tac >> conj_tac
     >- (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
     drule stmt_state_rel_fmp_room >>
     qpat_assum `ctx_has_dalloca ctx` (fn th => simp_tac bool_ss [fmp_room_def, th]) >>
     disch_then (assume_tac o CONJUNCT1) >>
     irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx mid u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> ghost_inv_at (DF H) 0 d cenv cx mid Gu tnu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all method_id_output_buffer_scratch_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sp sb) u = OK rawbuf` >>
  rename1 `z = rawbuf with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  rename1 `ptr_mem_ok cx _ _ buf.buf_operand Gz tnz z` >>
  `sb.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sb /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sp sb)` by
    suspend "output_layout" >>
  drule_all method_cursor_join >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK whole` >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz` by
    (irule method_clean_keep >> qexistsl [`Gu`, `u`, `sp`, `tnu`, `z`] >> asm_rewrite_tac[]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ s0.vs_alloca_next <= _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  suspend "output_frame"
QED

Resume method_id_runtime_suffix_mods[output_layout]:
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  qpat_assum `emit_void MSTORE _ sbuf = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_void MSTORE _ sd = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  pure_rewrite_tac[emitted_insts_def] >>
  map_every (fn q => qpat_assum q (pure_once_rewrite_tac o single))
    [`sb.cs_current_insts = _`, `sd.cs_current_insts = _`,
     `st.cs_current_insts = _`, `sbuf.cs_current_insts = _`] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[NoAsms, mk_inst_def, is_terminator_def]
QED

Resume method_id_runtime_suffix_mods[output_frame]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,Gz,tnz) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gz tnz z /\
    immutable_frame_mods func cenv cx mid z` by suspend "output_linked" >>
  `w2n p + 64 <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `sp.cs_next_id` >> asm_rewrite_tac[]) >>
  qexistsl [`whole`, `z`, `Gz`, `tnz`] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  (conj_tac >-
     (map_every (fn q => qpat_assum q mp_tac)
        [`w2n p + 64 <= z.vs_alloca_next`, `LENGTH bs = 4`,
         `eval_operand buf.buf_operand z = SOME p`] >>
      simp[NoAsms, expr_store_bound_def, is_word_type_def, evaluate_type_def,
           exprSimPropsTheory.val_store_size_def, vfmConstantsTheory.word_size_def,
           vyperValueTheory.type_slot_size_def, dimword_def])) >>
  (conj_tac >- simp[ptr_val_ok_def, is_word_type_def]) >>
  (conj_tac >-
     (simp[NoAsms, ptr_vv_ok_def, mk_ptr_def, read_result_def, return_def] >>
      conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC)) >>
  (conj_tac >-
     (map_every (fn q => qpat_assum q mp_tac)
        [`eval_operand buf.buf_operand z = SOME p`, `buf.buf_operand = Var q`,
         `FLOOKUP Gz q = SOME (w2n p,64)`] >>
      simp[NoAsms, ptr_buf_ok_def, lowered_value_type_def, expr_type_def,
           type_memory_bytes_def])) >>
  conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
QED

Resume method_id_runtime_suffix_mods[output_linked]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK u,_,_) /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  irule method_id_scratch_frame_op_taint_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`, `w2n p`, `mk_inst sp.cs_next_id ALLOCA [Lit 64w] [q]`,
            `sp`, `64`, `u`, `tnu`] >>
  rpt (qpat_x_assum `z = _ with vs_inst_idx := _` kall_tac) >>
  asm_rewrite_tac[] >> simp[NoAsms, mk_inst_def] >> first_assum ACCEPT_TAC
QED

Resume method_id_runtime_suffix_mods[posts]:
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK raw'` >>
  rename1 `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz` >>
  rename1 `z = raw' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl [`BytesV bs`, `z`, `Gz`, `tnz`] >>
  conj_tac >- simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK z,_,_) /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_store_bound _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid v x t` by fs[expr_post_mods_def] >>
  drule_all_then strip_assume_tac method_id_runtime_typed_post_run_mem_any_block >>
  rename1 `vv_post H ctx func cenv cx _ es sa sb s0 mid (Value r) _ raw_t` >>
  `raw_t = raw'` by
    (qpat_assum `run_inst_seq (emitted_insts sm sb) t = OK raw_t` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm sb) t = OK raw'`
       (fn th => simp_tac bool_ss [th, venomExecSemanticsTheory.exec_result_11])) >>
  pop_assum SUBST_ALL_TAC >>
  `r = BytesV bs` by
    (qpat_assum `builtin_result _ _ _ MethodId _ _ = INL r` mp_tac >>
     qpat_assum `!ann. builtin_result _ _ ann MethodId _ _ = _`
       (qspec_then `BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))`
         (fn th => simp_tac (srw_ss()) [th]))) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [method_typed_memory_posts]) >>
  suspend "post_transport"
QED

Resume method_id_runtime_suffix_mods[post_transport]:
  drule_all_then strip_assume_tac method_cursor_posts >>
  `if fixed then ptr_vv_ok cx (BaseT (BytesT (Fixed 4))) (Value (BytesV bs))
      (StackValue (BaseT (BytesT (Fixed 4))) op) mid Gz tnz z
   else ptr_vv_ok cx (BaseT (BytesT (Dynamic 4))) (Value (BytesV bs))
      (LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) mid Gz tnz z /\
      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op Gz z` by
    (Cases_on `fixed` >>
     qpat_assum `ptr_vv_ok cx _ _ _ mid Gz tnz z` mp_tac >>
     qpat_assum `~_ ==> ptr_buf_ok cenv _ op Gz z` mp_tac >> simp[NoAsms]) >>
  drule_all_then strip_assume_tac method_id_runtime_endpoint_posts_mods >>
  Cases_on `fixed` >>
  rule_assum_tac (REWRITE_RULE [COND_CLAUSES]) >>
  simp[NoAsms, lowered_value_type_def, expr_type_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise method_id_runtime_suffix_mods
