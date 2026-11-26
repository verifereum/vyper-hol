(* The guarded address and the shared code suffix of linked external Slice. *)
Theory bodySliceExternalRouteMods
Ancestors
  bodySliceCodeTailMods bodySliceSelfRouteMods bodySliceExternalSourceMods
  bodySliceExternalCompileMods bodySliceExternalAddressBindMods
  bodySliceExternalSavedMods bodySliceExternalLaunchMods bodySliceExternalPrefixPostMods
  gasOutcomeFullPostMods exprSimSliceExtcodeTyped exprSimFullBundleProps
  exprLoweringProps loweringPosts vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperContext bodyFullPostsMods words exprLowering
  context compileEnv valueEncoding vyperAST bodyPtrDefs bodyInvCodeProps venomInst
Libs monadsyntax

val finish = ``\v1 v2 av. do
  code_acc <- get_accounts;
  code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type addr] [av]);
  slice_acc <- get_accounts;
  v <- lift_sum (evaluate_builtin cx slice_acc (BaseT (BytesT (Dynamic n))) (Slice n)
         (MAP expr_type [Builtin ct (Acc Code) [addr];start;len]) [code_v;v1;v2]);
  return (Value v)
  od``;
val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;

Theorem slice_external_from_tail_mods:
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
   case code_slice_source (Slice n) args of
     NONE => body_exprs_full_ok_mods mods exps cx args
   | SOME (ct,ad) => body_exprs_full_ok_mods mods exps cx (TL args) /\
       (!s vs t. eval_exprs cx (TL args) s = (INL vs,t) ==>
                 body_exprs_full_ok_mods mods exps cx [ad])) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es /\
  code_slice_source (Slice n) args = SOME (ct,addr) /\
  ~is_self_code (Builtin ct (Acc Code) [addr]) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Slice n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >> gvs[] >>
  qpat_x_assum `builtin_args_length_ok _ _ ==> _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [builtin_args_length_ok_def]) >>
  drule_then strip_assume_tac slice_external_source_mods >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  qabbrev_tac `sliceFinish = ^finish` >>
  `!v1 v2 av. storage_trace_frame (sliceFinish v1 v2 av)` by
    simp[Abbr `sliceFinish`, storage_trace_frame_bind_all, storage_trace_frame_state_reads,
         storage_trace_frame_lifts, storage_trace_frame_return] >>
  qabbrev_tac `sliceNext = \v1 v2. bind (^forced addr) (sliceFinish v1 v2)` >>
  `!v1 v2. storage_trace_frame (sliceNext v1 v2)` by
    simp[Abbr `sliceNext`, storage_trace_frame_bind_all, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `eval_expr cx (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
        [Builtin ct (Acc Code) [addr];start;len]) =
     bind (^forced start) (\v1. bind (^forced len) (sliceNext v1))` by
    (drule_then (fn th => simp[th,Abbr `sliceFinish`,Abbr `sliceNext`]) slice_extcode_actions) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`vv`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb)` by
    simp[expr_sim_full_code_def] >>
  qmatch_asmsub_rename_tac `compile_expr cenv ty _ sa = (vv,sb)` >>
  mp_tac (BETA_RULE slice_external_compile_mods |> Q.INST
    [`e` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
                  [Builtin ct (Acc Code) [addr];start;len]`,
     `ann` |-> `BaseT (BytesT (Dynamic n))`,
     `N` |-> `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
     `hvv` |-> `vv`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then
    [`s1`,`s2`,`s3`,`sh1`,`sh2`,`sh3`,`x`,`y`,`aop`,`out`,
     `sc`,`sd`,`se`,`sf`,`src_len`,`dst`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "tail"
QED

Resume slice_external_from_tail_mods[tail]:
  qpat_assum `eval_expr _ (Builtin _ _ _) = _` (fn th =>
    PURE_ONCE_REWRITE_TAC [th] >> RULE_ASSUM_TAC (PURE_ONCE_REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  irule (BETA_RULE slice_code_tail_mods) >> BETA_TAC >> asm_rewrite_tac[] >>
  qexistsl_tac [`addr`,`BaseT (BytesT (Dynamic n))`,`ct`,`d`,`env`,`exps`,`mods`,
    `n`,`s1`,`s2`,`sa`,`sh1`,`sh2`,`sha`,`shadow_func`,`src`,`tops`,`ty`,`ty`,`x`,`y`] >>
  asm_rewrite_tac[] >>
  qx_genl_tac [`marks1`,`v1`,`mid`,`G1`,`tn1`,`t1`,`marks2`,`v2`,`fin`,`G2`,`tn2`,`t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_full_ok_mods mods exps cx [addr]` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_assum `!s vs t. eval_exprs _ _ s = _ ==> _` (drule_then ACCEPT_TAC)) >>
  `expr_body_pre_mods mods cenv cx env addr fin` by
    (qpat_assum `!fin. expr_sim_inv_mods _ _ _ _ fin ==> _` (drule_then ACCEPT_TAC)) >>
  suspend "address"
QED

Resume slice_external_from_tail_mods[address]:
  qpat_assum `Abbrev (sliceNext = _)` (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `sliceNext = _` (fn th =>
    PURE_ONCE_REWRITE_TAC [th] >>
    qpat_x_assum `gas_admissible (sliceNext _ _) _ _` (assume_tac o BETA_RULE o REWRITE_RULE [th])) >>
  BETA_TAC >>
  qpat_x_assum `v1 = IntV _` (markerLib.mk_asm "start_word") >>
  qpat_x_assum `v2 = IntV _` (markerLib.mk_asm "len_word") >>
  irule (BETA_RULE slice_external_address_bind_mods) >> BETA_TAC >> asm_rewrite_tac[] >>
  qexistsl_tac [`aop`,`d`,`env`,`exps`,`mods`,`s2`,`s3`,`sh2`,`sh3`,`shadow_func`,
                `src`,`tops`,`ty`] >>
  asm_rewrite_tac[] >>
  qx_genl_tac [`marks3`,`bs`,`ae`,`G3`,`tn3`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ae.storage_trace) ae.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ae.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H ae.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post_mods _ ctx func cenv cx addr fin s2 s3 t2 ae _ aop z`
    (mp_then Any (qspecl_then [`y`,`x`,`v2`,`v1`,`tn3`,`tn2`,`lo`,`G3`,`G2`] mp_tac)
       (BETA_RULE slice_external_saved_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "launch"
QED

Resume slice_external_from_tail_mods[launch]:
  qabbrev_tac `i = w2n (val_to_w256 v1)` >>
  qabbrev_tac `k = w2n (val_to_w256 v2)` >>
  `i < dimword (:256) /\ k < dimword (:256)` by simp[Abbr `i`,Abbr `k`,w2n_lt] >>
  `0 < k /\ k <= n` by
    (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _` (qspec_then `[]` mp_tac) >>
     asm "len_word" (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     disch_then (fn th => qpat_assum `!st ee k. _ ==> 0 < k /\ _`
       (mp_tac o C MATCH_MP (REWRITE_RULE [listTheory.APPEND_NIL] th))) >>
     simp[Abbr `k`]) >>
  `eval_operand x z = SOME (n2w i) /\ eval_operand y z = SOME (n2w k)` by
    simp[Abbr `i`,Abbr `k`] >>
  `!H. valid_horizon cx st0 H ae.storage_trace ==> stmt_state_rel H ctx func cenv cx ae z` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H ae.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (slice_external_launch_mods |> Q.INST [`ann` |-> `BaseT (BytesT (Dynamic n))`]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "suffix"
QED

Resume slice_external_from_tail_mods[suffix]:
  qpat_x_assum `ct = BaseT _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `LENGTH sliceCode < dimword (:256)` >>
  `!tail. sliceFinish v1 v2 (BytesV bs) (ae with gas_obs := tail) =
    ((case evaluate_slice (BytesV sliceCode) (IntV (&i)) (IntV (&k)) n of
        INL v => INL (Value v) | INR err => INR (Error err)), ae with gas_obs := tail)` by
    (qx_gen_tac `tail` >> simp_tac bool_ss [Abbr `sliceFinish`] >>
     asm "start_word" (PURE_ONCE_REWRITE_TAC o single) >>
     asm "len_word" (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `!tail. _ = ((case evaluate_slice _ _ _ _ of _ => _ | _ => _),_)`
       (qspec_then `tail` ACCEPT_TAC)) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) slice_self_suffix_mods >>
  BETA_TAC >>
  qexistsl_tac [`tops`,`x`,`src`,`shadow_ctx`,`sf`,`se`,`sd`,`sc`,`sb`,`s3`,
    `[aop]`,`EXTCODESIZE`,`out`,`n`,`src_len`,`k`,`i`,`exps`,`env`,
    `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
       [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len]`,
    `dst`,`d`,`[aop;dst;x;y]`,`EXTCODECOPY`,`sliceCode`,`y`,`cenv`,
    `[Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [addr];start;len]`,
    `aop`,`type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`] >>
  drule_then (fn th => PURE_REWRITE_TAC [th]) contract_inv_cenv_modules >>
  asm_rewrite_tac[] >>
  simp[listTheory.MEM, DISJ_IMP_THM] >>
  qx_genl_tac [`H`,`ee`,`HG`,`tm`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee.storage_trace = ae.storage_trace` by
    (qpat_x_assum `?xs. !tail. _ /\ ae with gas_obs := _ = ee with gas_obs := tail`
       (qx_choose_then `xs` (qspec_then `[]` (mp_tac o cj 2))) >>
     disch_then (mp_tac o AP_TERM ``\e:evaluation_state. e.storage_trace``) >> simp[]) >>
  suspend "rebase"
QED

Resume slice_external_from_tail_mods[rebase]:
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (BETA_RULE slice_external_prefix_post_mods |> Q.INST
    [`ct` |-> `BaseT (BytesT (Dynamic 24576))`, `code` |-> `sliceCode`, `av` |-> `BytesV bs`]) >>
  simp_tac bool_ss [LET_THM] >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]) >>
     rpt strip_tac >> first_assum (drule_then ACCEPT_TAC))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `vv_store_bound _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [mk_ptr_def]) >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [mk_ptr_def]) >>
  simp[expr_type_def, lowered_value_type_def, is_bytestring_type_def, vv_location_def, mk_ptr_def]
QED

Finalise slice_external_from_tail_mods
