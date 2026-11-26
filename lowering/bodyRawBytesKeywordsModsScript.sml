(* The reached word-list run retains the byte input at the same endpoint. *)
Theory bodyRawBytesKeywordsMods
Ancestors
  bodyRequestWordResultPrefixMods bodyRawRequestInputsMods
  bodyRawLocalBytesLayoutMods bodyRawKwargsBytesFrameMods bodyRawBytesKeywordSavedMods
  bodyFullPredsMods bodyFullPostsMods vyperStorageFootprint vyperStorageTrace
  exprSimPrecompiles exprSimDefs exprLoweringProps gasOutcomeFullMods gasContext
  gasShadow exprSimWordArgs combin list compileEnv

val _ = Parse.hide "base";
val _ = Parse.hide "size";

val entry_at = ``\(H : (bool # 256 word # type_value) list # num list).
  stmt_state_rel H ctx func cenv cx esD t4 /\
  immutable_frame_mods func cenv cx esD t4 /\
  storage_well_formed_on cx esD (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx esD G4 tn4 t4``;

val outcome = ``\(action : evaluation_state -> eval_result evaluation_result) entry Q R.
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 action entry Q R``;

val kw_at = ``\(H : (bool # 256 word # type_value) list # num list).
  typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
  immutable_frame_mods func cenv cx esK tk /\
  ghost_inv_at_mods (DF H) lo d cenv cx esK GK tnK tk /\
  ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK``;

val kw_reached = ``
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) kws kvs /\
  EVERY (\op. op_prov GK op = NONE /\ op_taint tnK op = {}) xs /\
  EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at s5 z)) xs /\
  expr_sim_inv_mods mods cenv cx env esK /\ body_const_cells_agree_mods mods cx env esK /\
  tk.vs_current_bb = s5.cs_current_bb /\ tk.vs_inst_idx = LENGTH s5.cs_current_insts /\
  alloca_history func tk /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tk) /\
  t4.vs_alloca_next <= tk.vs_alloca_next /\ ~tk.vs_halted /\
  (!fn inst u. frag_reachable ctx func tk fn inst u ==> dalloca_fmp_headroom inst u)``;

val kw_saved = ``
  expr_val_rel cx (BaseT AddressT) av addr tk /\
  eval_operand len tk = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) tk = SOME (n2w (b+32)) /\
  EVERY (safe_operand s5) [addr; len; Var p] /\
  EVERY (\op. op_taint tnK op = {}) [addr; len; Var p] /\
  op_prov GK addr = NONE /\ op_prov GK len = NONE /\
  op_prov GK (Var p) = SOME (base,size) /\
  base <= b+32 /\ b+32+LENGTH bs <= base+size /\
  (bs <> [] ==> ptr_covers GK tnK p tk (LENGTH bs)) /\
  (!aid entry. FLOOKUP t4.vs_allocas aid = SOME entry ==>
     FLOOKUP tk.vs_allocas aid = SOME entry) /\
  b+32+LENGTH (bs : word8 list) <= tk.vs_alloca_next /\ s0.vs_alloca_next <= tk.vs_alloca_next /\
  wb_frame cenv es esK sa s0 tk /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK /\
  return_buf_frame d cenv sa tk /\ return_buf_frame d cenv s5 tk``;

val payload_at = ``\t tn. !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
  mem_bytes_at (b+32) (LENGTH bs) mem = bs``;

Theorem raw_bytes_keywords_mods:
  !kws (next : value list -> evaluation_state -> eval_result evaluation_result).
  body_exprs_full_ok_mods mods exps cx kws /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::e::kws) dflt) es /\
  expr_sim_inv_mods mods cenv cx env esD /\ body_const_cells_agree_mods mods cx env esD /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
    (MAP gas_shadow_expr kws) shadow_s4 = (xs,shadow_s5) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s4,s5,shadow_s4,shadow_s5) /\
  local_ptrs_reserved cenv s4 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
  gas_admissible (bind (eval_exprs cx kws) next) expr_vv_res_ok esD /\
  return_buf_frame d cenv s4 t4 /\ alloca_history func t4 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t4) /\
  (!fn inst u. frag_reachable ctx func t4 fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 esD.storage_trace /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==> (^entry_at) H) /\
  ~t4.vs_halted /\ t4.vs_current_bb = s4.cs_current_bb /\
  t4.vs_inst_idx = LENGTH s4.cs_current_insts /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM esD.scopes /\
  ci_mono sa s4 /\ ci_mono s2 s4 /\ ci_mono s4 s5 /\
  wb_frame cenv es esD sa s0 t4 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4 /\
  return_buf_frame d cenv sa t4 /\ s0.vs_alloca_next <= t4.vs_alloca_next /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data t4 /\
  eval_operand data t4 = SOME (n2w b) /\ (^payload_at) t4 tn4 /\
  EVERY (safe_operand s4) [addr; len; Var p] /\
  expr_val_rel cx (BaseT AddressT) av addr t4 /\
  eval_operand len t4 = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) t4 = SOME (n2w (b+32)) /\
  EVERY (\op. op_taint tn4 op = {}) [addr; len; Var p] /\
  op_prov G4 addr = NONE /\ op_prov G4 len = NONE /\
  op_prov G4 (Var p) = SOME (base,size) /\
  base <= b+32 /\ b+32+LENGTH bs <= base+size /\
  (bs <> [] ==> ptr_covers G4 tn4 p t4 (LENGTH bs)) /\
  b+32+LENGTH bs <= t4.vs_alloca_next /\ b+32+LENGTH bs < dimword (:256) /\
  (!vs. storage_trace_frame (next vs)) /\
  (!H (res : eval_result + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r) /\
  (!reads kvs esK GK tnK tk.
    (!tail. eval_exprs cx kws (esD with gas_obs := reads ++ tail) =
            (INL kvs, esK with gas_obs := tail)) /\
    storage_trace_domain cx st0 esK.storage_trace /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==> (^kw_at) H) /\
    ^kw_reached /\ ^kw_saved /\ (^payload_at) tk tnK /\
    b+32+LENGTH bs < dimword (:256) /\ gas_admissible (next kvs) expr_vv_res_ok esK ==>
    (^outcome) (next kvs) (esK,tk,GK,tnK) Q R) ==>
  (^outcome) (bind (eval_exprs cx kws) next) (esD,t4,G4,tn4) Q R
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `!e' mid. MEM e' kws /\ expr_sim_inv_mods mods cenv cx env mid /\
     body_const_cells_agree_mods mods cx env mid ==>
     expr_body_pre_mods mods cenv cx env e' mid` by
    (rpt strip_tac >> irule request_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >> simp[]) >>
  `EVERY (is_word_type o expr_type) kws` by
    fs[EVERY_MEM,is_word_type_def] >>
  `!exc. expr_vv_res_ok (INR exc) ==> expr_res_ok (INR exc)` by
    simp[expr_vv_res_ok_def,expr_res_ok_def] >>
  irule (BETA_RULE request_word_result_prefix_mods) >>
  qpat_assum `gas_admissible (bind (eval_exprs cx kws) next) _ esD` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_word_args cenv _ kws s4 = _` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (s4,s5,_,_)` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ esD` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv s4 t4` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[] >>
  qx_genl_tac [`reads`,`kvs`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!n k k'. local_val_at cenv cx n k (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
      val_wf (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\ dynarray_len_at cenv n k' ==>
      k + val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= k' \/ k'+32 <= k`
    by (rpt strip_tac >> irule local_bytes_dynarray_apart_mods >>
        qpat_assum `expr_sim_inv_mods _ _ _ _ esD` (irule_at Any) >>
        qpat_assum `local_val_at _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `b < dimword (:256)` by decide_tac >>
  `s2.cs_next_id <= s4.cs_next_id` by fs[ci_mono_def] >>
  `(^payload_at) tk tnK` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:num # num``]
                      raw_kwargs_bytes_frame_from_apart) >>
     qpat_assum `expr_val_at _ _ _ _ _ esD _ _ t4` (irule_at Any) >>
     qpat_assum `typed_args_post _ _ _ _ _ esD s4 t4 esK kws xs kvs tk` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ esD s4 G4 tn4 t4 GK tnK` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id` by fs[ci_mono_def] >>
  `^kw_saved` by
    (irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
                      raw_bytes_keyword_saved_mods) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `typed_args_post _ _ _ _ _ esD s4 t4 esK kws xs kvs tk` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ esD s4 G4 tn4 t4 GK tnK` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!reads kvs esK GK tnK tk. _ ==> gas_outcome_full_mods _ _ _ _ (next kvs) _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum (ACCEPT_TAC o BETA_RULE)) >>
  qexists_tac `reads` >> first_assum ACCEPT_TAC
QED
