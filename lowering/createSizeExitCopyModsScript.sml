Theory createSizeExitCopyMods
Ancestors
  createSizeExitCopy createExprSizeExitDefsMods
  abiEncoderProps e2eDefs fragExec fragGasOrigin gasExplicitSites s1PrefixDefs venomInst
  venomState vyperCreate relation list words createMarkedPath pair builtinCreate arithmetic
  createSizeDispatch exprLowering vfmConstants externalEntryShape compileEnv
  createSizeItinerary exprLoweringProps exprBodyPreProps rich_list vyperTypeSystem vyperAST
  createSizeStraightPrefix createSizeIndexedRun createSizeCopyLength createSizeCopyScalarCode ghostPcTransportPtr
  exprSimSend integer_word loweringStateRelDefs createExprSizeExitDefs
  createSizePrefixReplayMods createSizeCopyReplayMods createSizePrefixCutsMods

Theorem create_size_exit_copy_mods:
  !mods exps cx ann has_salt rof ks args dflt.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order CreateCopyOf has_salt args) ==>
    create_expr_size_exit_mods mods exps cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
Proof
  rewrite_tac[create_expr_size_exit_mods_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_mods_def]) >>
  drule_then strip_assume_tac exprSimFullBundlePropsTheory.expr_sim_full_code_fields >>
  `?result. compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by (simp[] >> metis_tac[]) >>
  drule_all create_size_prefix_cuts_mods >> strip_tac >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [create_call_itinerary_def, create_kind_case_def, create_copy_itinerary_def]) >>
  rename1 `lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `lower_value compile_expr cenv (expr_type value_e) value_e a = (value_op,b)` >>
  rename1 `create_itinerary_salt _ _ b salt_op c` >>
  rename1 `create_size_dispatch_tail rof dispatch sd created bufop len value_op salt_op result sb` >>
  `well_typed_expr env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)` by
    (drule expr_body_pre_mods_well_typed >> simp[]) >>
  qabbrev_tac `salt_e = if has_salt then SOME (HD rest) else NONE` >>
  `has_salt = IS_SOME salt_e /\
   args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e])` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     qpat_assum `args = target_e::value_e::rest` (fn th => PURE_REWRITE_TAC[th]) >>
     Cases_on `has_salt` >> simp[Abbr `salt_e`, well_typed_expr_def, create_arg_types_ok_def] >>
     Cases_on `rest` >> simp[] >> rename1 `MAP expr_type rs = _ ==> _` >> Cases_on `rs` >> simp[]) >>
  `compile_create_salt compile_expr cenv salt_e b = (salt_op,c)` by
    (qpat_x_assum `create_itinerary_salt _ _ b salt_op c` mp_tac >>
     qpat_assum `Abbrev (salt_e = _)` (fn th => PURE_REWRITE_TAC[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
     Cases_on `salt_e` >> simp[create_itinerary_salt_def, compile_create_salt_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  rename1 `emit_op ADD [code; Lit 11w] _ = (len,sc)` >>
  rename1 `marks = FLAT chunk_rows` >>
  drule_all create_copy_preparation_code >>
  disch_then (strip_assume_tac o Q.SPEC `value_op`) >>
  `dispatch = sc` by
    (qpat_assum `LAST (sa::cuts) = dispatch` mp_tac >>
     qpat_assum `cuts = _` (fn th => PURE_REWRITE_TAC[th]) >> simp[]) >>
  qpat_x_assum `dispatch = sc` SUBST_ALL_TAC >>
  `compile_create_dispatch bufop len value_op salt_op rof sc = (result,sb)` by
    (Cases_on `salt_op` >>
     qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
     qpat_x_assum `created = Var out` SUBST_ALL_TAC >>
     simp[compile_create_dispatch_def, comp_bind_def]) >>
  `compile_create_copy target value_op salt_op rof c = (result,sb)` by
    (first_x_assum irule >> simp[]) >>
  drule_all create_copy_scalar_code >> strip_tac >>
  suspend "replay_operands"
QED

Resume create_size_exit_copy_mods[replay_operands]:
  qpat_assum `LIST_REL _ _ _` (strip_assume_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  `EL 0 states = s0` by (Cases_on `states` >> fs[LENGTH]) >>
  `create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 (EL 0 chunk_rows) (EL 1 states) /\
   create_expr_prefix a b (gas_explicit_sites ctx shadow_ctx) ctx func (EL 1 states) (EL 1 chunk_rows) (EL 2 states) /\
   create_expr_prefix b c (gas_explicit_sites ctx shadow_ctx) ctx func (EL 2 states) (EL 2 chunk_rows) (EL 3 states) /\
   (EL 1 states).vs_current_bb = a.cs_current_bb /\ (EL 1 states).vs_inst_idx = LENGTH a.cs_current_insts /\
   (EL 2 states).vs_current_bb = b.cs_current_bb /\ (EL 2 states).vs_inst_idx = LENGTH b.cs_current_insts /\
   (EL 3 states).vs_current_bb = c.cs_current_bb /\ (EL 3 states).vs_inst_idx = LENGTH c.cs_current_insts` by
    (qpat_assum `!i. _ ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (fn th => map_every (fn k => qspec_then k mp_tac th) [`0`,`1`,`2`]) >>
     qpat_assum `!i. i < LENGTH (sa::cuts) ==> _`
       (fn th => map_every (fn k => qspec_then k mp_tac th) [`1`,`2`,`3`]) >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `EL 0 states = s0` (pure_rewrite_tac o single) >>
     simp[NoAsms, EL_CONS] >> rpt strip_tac >> simp[]) >>
  `marks = EL 0 chunk_rows ++ (EL 1 chunk_rows ++ (EL 2 chunk_rows ++ FLAT (DROP 3 chunk_rows)))` by
    (`2 < LENGTH chunk_rows` by simp[] >>
     `TAKE 3 chunk_rows = [EL 0 chunk_rows; EL 1 chunk_rows; EL 2 chunk_rows]` by
       (map_every (fn k => qspecl_then [`chunk_rows:bool list list`,k] mp_tac TAKE_EL_SNOC) [`2`,`1`] >>
        `chunk_rows <> []` by (Cases_on `chunk_rows` >> fs[]) >>
        simp[TAKE1, SNOC] >> decide_tac) >>
     qspecl_then [`3`,`chunk_rows:bool list list`] (mp_tac o Q.AP_TERM `FLAT`) TAKE_DROP >>
     qpat_assum `TAKE 3 _ = _` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[FLAT_APPEND, FLAT, APPEND_NIL, GSYM APPEND_ASSOC] >>
     qpat_assum `marks = FLAT _` (pure_rewrite_tac o single) >>
     disch_then (ACCEPT_TAC o SYM)) >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
   ?acc. accounts_agree H cx.txn.target acc (EL 3 states).vs_accounts /\ accounts_well_typed acc` by
    (qpat_assum `marks = EL 0 _ ++ _`
       (fn eq => qpat_assum `eval_expr _ _ _ = (res,ee)` (assume_tac o SUBS [eq])) >>
     irule create_copy_replay_accounts_at_cuts_mods >>
     qpat_assum `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e])`
       (irule_at Any) >>
     qpat_assum `lower_value _ _ _ target_e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ value_e a = _` (irule_at Any) >>
     qpat_assum `compile_create_salt _ _ salt_e b = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr target_e) shadow_sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr value_e) b1 = _` (irule_at Any) >>
     qpat_assum `compile_create_salt _ _ (OPTION_MAP gas_shadow_expr salt_e) b2 = _` (irule_at Any) >>
     qpat_assum `create_expr_prefix sa a _ _ _ s0 _ _` (irule_at Any) >>
     qpat_assum `create_expr_prefix a b _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `create_expr_prefix b c _ _ _ _ _ _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[])
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "bound_length"
QED

Resume create_size_exit_copy_mods[bound_length]:
  `cs_extends sa c` by
    (`!ce ty e u. cs_extends u (SND (lower_value compile_expr ce ty e u))` by
       simp[lower_value_labels, compile_expr_labels] >>
     `cs_extends sa a /\ cs_extends a b` by metis_tac[SND] >>
     `cs_extends b c` by metis_tac[compile_create_salt_labels, compile_expr_labels, SND] >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends sc sb` by metis_tac[compile_create_dispatch_labels, SND] >>
  `fn_has_code c sc func` by metis_tac[fn_has_code_mid] >>
  `inst.inst_id = sc.cs_next_id /\ sz = len` by
    (qpat_assum `inst = case _ of NONE => _ | SOME _ => _` (pure_rewrite_tac o single) >>
     qpat_x_assum `inst.inst_opcode = _ /\ _ \/ _` mp_tac >>
     qpat_assum `inst = case _ of NONE => _ | SOME _ => _` (pure_rewrite_tac o single) >>
     Cases_on `salt_op` >> simp[mk_inst_def]) >>
  `EL 14 states = s` by
    (`LENGTH states = 15` by fs[LENGTH] >>
     `states <> []` by (Cases_on `states` >> fs[]) >>
     drule LAST_EL >> simp[]) >>
  `!j. 3 <= j /\ j < LENGTH (sa::cuts) ==>
    c.cs_next_id <= (EL j (sa::cuts)).cs_next_id /\
    (EL j (sa::cuts)).cs_next_id <= sc.cs_next_id` by
    (`EVERY (\z. c.cs_next_id <= z.cs_next_id /\ z.cs_next_id <= sc.cs_next_id)
            (DROP 3 (sa::cuts))` by simp[] >>
     rpt strip_tac >>
     `j - 3 + 3 = j /\ j - 3 < LENGTH (DROP 3 (sa::cuts))` by
       (simp[LENGTH_DROP] >> decide_tac) >>
     qpat_x_assum `EVERY _ (DROP 3 _)`
       (qspec_then `j-3` mp_tac o REWRITE_RULE[EVERY_EL]) >>
     simp[EL_DROP]) >>
  `run_inst_seq (emitted_insts c sc) (EL 3 states) =
   OK (s with vs_inst_idx := (EL 3 states).vs_inst_idx)` by
    (qpat_assum `EL 14 states = s` (pure_rewrite_tac o single o SYM) >>
     irule (BETA_RULE (Q.INST [`i` |-> `3`, `k` |-> `14`,
       `C` |-> `\j. EL j (sa::cuts)`, `Obs` |-> `\j. EL j states`,
       `marks` |-> `\j. EL j chunk_rows`] create_indexed_straight_run)) >>
     qpat_assum `EL 14 states = s` (pure_rewrite_tac o single) >>
     `!j. 3 <= j /\ j < 14 ==>
        c.cs_next_id <= (EL j (sa::cuts)).cs_next_id /\
        (EL (SUC j) (sa::cuts)).cs_next_id <= sc.cs_next_id /\
        create_expr_prefix (EL j (sa::cuts)) (EL (SUC j) (sa::cuts))
          (gas_explicit_sites ctx shadow_ctx) ctx func
          (EL j states) (EL j chunk_rows) (EL (SUC j) states)` by
       (gen_tac >> strip_tac >>
        `j < LENGTH cuts /\ SUC j < LENGTH (sa::cuts)` by
          (qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
           simp[NoAsms] >> decide_tac) >>
        qpat_assum `!j. 3 <= j /\ _ ==> _ /\ _`
          (fn th => qspec_then `j` mp_tac th >> qspec_then `SUC j` mp_tac th) >>
        qpat_assum `!i. i < LENGTH cuts ==> create_expr_prefix _ _ _ _ _ _ _ _`
          (qspec_then `j` mp_tac) >>
        simp[NoAsms, EL] >> rpt strip_tac >> simp[] >> decide_tac) >>
     conj_tac >- simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `eval_operand len (s with vs_inst_idx := (EL 3 states).vs_inst_idx) = SOME w` by
    (qpat_assum `sz = len` (pure_rewrite_tac o single o SYM) >>
     simp[ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  drule_all create_copy_pre_dispatch_length_bound >> simp[GSYM NOT_LESS_EQUAL]
QED

Finalise create_size_exit_copy_mods
