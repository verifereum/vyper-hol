(* Run the forced ABI-decode operand before opening the linked decoder. *)
Theory bodyAbiDecodeBindMods
Ancestors
  bodyAbiDecodeCutsMods bodyTypeBuiltinAbiMods bodyBopBytestringBindMods
  bodyForcedStorageFrameMods
  bodyFullPredsMods bodyFullPostsMods exprSimAbiDecodeBodySuccess exprSimDefs
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods haltExitProj stmtSimProps
  exprSimSliceCompose vyperStorageTrace vyperStorageFootprint vyperState
  vyperTypeExprSoundness vyperValue vyperTyping vyperInterpreter vyperAST
  loweringPosts compileEnv gasShadow gasExplicitSites context

val forced = ``bind (eval_expr cx e) (read_result cx)``;
val whole = ``TypeBuiltin ty (AbiDecode unwrap) ty [e]``;
val next = ``\v. bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty
    [expr_type e] [v])) (\w. return (Value w))``;
val result = ``LocatedValue ty (mk_ptr out LocMemory)``;
val child_post = ``\(H:(bool # 256 word # type_value) list # num list) v ee G tn t.
   expr_post_mods H ctx func ce cx e es sa start s0 ee v data t /\
   expr_store_bound cx (post_value_type ce e) v data t /\
   t.vs_current_bb = start.cs_current_bb /\ t.vs_inst_idx = LENGTH start.cs_current_insts /\
   alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   s0.vs_alloca_next <= t.vs_alloca_next /\
   ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
   ptr_val_ok cx (post_value_type ce e) v data G tn t /\
   (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e data G t) /\
   ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;
val exit = ``\(H:(bool # 256 word # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
   expr_exit res r /\ halt_exit H cx ee res r /\
   (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;
val post = ``\(H:(bool # 256 word # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee G tn t. ?tv. res = INL tv /\
   vv_post_mods H ctx func ce cx ^whole es sa sb s0 ee tv ^result t /\
   vv_store_bound cx (post_value_type ce ^whole) (lowered_value_type ce ^whole)
     ee tv ^result t /\
   t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   s0.vs_alloca_next <= t.vs_alloca_next /\
   ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
   ptr_vv_ok cx (post_value_type ce ^whole) tv ^result ee G tn t /\
   (!v. tv = Value v /\ ~is_word_type (post_value_type ce ^whole) /\
      ~is_bytestring_type (post_value_type ce ^whole) ==>
      vv_own ce cx (post_value_type ce ^whole) sa sb ee tv ^result t /\
      (!rt p. ^result = LocatedValue rt p ==> p.ptr_location = LocMemory)) /\
   (ce.ce_is_ctor /\ vv_location ^result = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce ^whole) = SOME rt /\
               eval_operand (vv_operand ^result) t = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem) /\
   (!rt op. ^result = StackValue rt op /\ ~is_word_type (post_value_type ce ^whole) ==>
            ptr_buf_ok ce ^whole op G t) /\
   (!rt p. ^result = LocatedValue rt p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok ce ^whole p.ptr_operand G t) /\
   ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;

(* The source success is a Value even when the input read started from a Place. *)
Theorem abi_decode_source_value_mods:
  eval_expr cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es = (INL raw,ee) ==>
  ?v. raw = Value v
Proof
  simp[abi_decode_singleton_source, bind_def, lift_sum_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >> qexists_tac `w` >> simp[]
QED

Theorem abi_decode_operand_sim_mods[local]:
  body_exprs_full_ok_mods mods exps cx [e] /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e) e es
Proof
  strip_tac >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ [_]`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e) e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e) e es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem abi_decode_forced_bytes_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ ee.gas_obs = [] /\
  (!tail. (^forced) (es with gas_obs := obs ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  (?bs. v = BytesV bs) /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace)
Proof
  strip_tac >> drule_all bop_bytestring_operand_source_mods >>
  disch_then (qspec_then `st0` strip_assume_tac) >> simp[] >>
  conj_tac
  >- (qpat_x_assum `value_runtime_typed _ _ v` mp_tac >>
      Cases_on `v` >> simp[value_runtime_typed_def,evaluate_type_def,value_has_type_def,AllCaseEqs()]) >>
  drule_then ACCEPT_TAC abi_decode_observed_scopes_dom
QED

Theorem abi_decode_vv_from_stages_mods:
  body_exprs_full_ok_mods mods exps cx [e] /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env ^whole es /\
  (!st0 sa sb shsa shsb s0 G0 tn0 data start shstart out bs ee t G tn marks.
     let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
     lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
     lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shsa = (data,shstart) /\
     lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
       (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
       (type_memory_bytes ce wty) start = (out,sb) /\
     lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
       (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
       (type_memory_bytes ce wty) shstart = (out,shsb) /\
     gas_shadow_state start shstart /\
     fn_has_code sa start func /\ fn_has_code start sb func /\
     fn_has_code shsa shstart shadow_func /\ fn_has_code shstart shsb shadow_func /\
     MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
     (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
     (!tail. (^forced) (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL (BytesV bs),ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~t.vs_halted /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> (^child_post) H (BytesV bs) ee G tn t) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       ce.ce_modules cx st0 ((^next) (BytesV bs)) (ee,t,G,tn)
       ^post ^exit) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx cty ^whole es
Proof
  simp_tac bool_ss [LET_THM] >> BETA_TAC >> strip_tac >>
  drule_then strip_assume_tac abi_decode_entry_inputs_mods >> gvs[] >>
  rewrite_tac[expr_vv_sim_full_mods_def,abi_decode_singleton_source] >> rpt gen_tac >> strip_tac >>
  rename1 `compile_expr ce cty _ sa = (vv,sb)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) shsa = (_,shsb)` >>
  rename1 `s0.vs_current_bb = sa.cs_current_bb` >>
  drule_all abi_decode_paired_cuts_mods >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `gas_admissible (^forced) expr_res_ok es` by
    (irule (INST_TYPE [alpha |-> ``:eval_result``] slice_gas_admissible_bind_head) >>
     conj_tac >- simp[expr_res_ok_def] >>
     qexistsl_tac [`expr_vv_res_ok`,`^next`] >> simp[expr_res_ok_def,expr_vv_res_ok_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e) e es` by
    (irule abi_decode_operand_sim_mods >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `body_exprs_full_ok_mods _ _ _ [_]` (irule_at Any) >>
     qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`start`,`shsa`,`shstart`,`data`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (^forced)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`!v:value. storage_trace_frame ((^next) v)`]
  >- simp[storage_trace_frame_bind_all,storage_trace_frame_lifts,storage_trace_frame_return]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> gvs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  conj_tac >- suspend "continuation" >> suspend "operand_post"
QED

Resume abi_decode_vv_from_stages_mods[operand_post]:
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> gvs[expr_exit_INR_type,halt_exit_INR_type,expr_exit_def]
QED

Resume abi_decode_vv_from_stages_mods[continuation]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> childQ H _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `(\H res ee G tn t. ?v. res = INL v /\ _) _ res ee G tn t`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  drule_all abi_decode_forced_bytes_mods >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> valid_horizon _ _ H es.storage_trace`
       (drule_then assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac)) >>
  disj1_tac >> qexists_tac `BytesV bs` >> simp[] >>
  qpat_assum `!st0 sa sb shsa shsb s0 G0 tn0 data start shstart out bs ee t G tn marks. _`
    irule >>
  simp[] >> conj_tac
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`data`,`shsa`,`shsb`,`shstart`,`start`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (\H res ee G tn t. ?v. res = INL v /\ _) H _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  gvs[]
QED

Finalise abi_decode_vv_from_stages_mods
