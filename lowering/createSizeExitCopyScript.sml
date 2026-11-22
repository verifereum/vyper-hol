Theory createSizeExitCopy
Ancestors
  abiEncoderProps e2eDefs fragExec fragGasOrigin gasExplicitSites s1PrefixDefs venomInst
  venomState vyperCreate relation list words createMarkedPath pair builtinCreate arithmetic
  createSizeDispatch exprLowering vfmConstants externalEntryShape compileEnv
  createSizeItinerary exprLoweringProps exprBodyPreProps rich_list vyperTypeSystem vyperAST
  createSizeStraightPrefix createSizeCopyLength createSizeCopyScalarCode ghostPcTransportPtr
  exprSimSend integer_word loweringStateRelDefs createExprSizeExitDefs
  createSizePrefixReplay createSizeCopyReplay createSizePrefixCuts

Theorem create_prefix_band_rtc:
  lo <= a.cs_next_id /\ b.cs_next_id <= hi /\
  create_expr_prefix a b explicit ctx fn u marks v ==>
  RTC (\p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ lo <= i.inst_id /\ i.inst_id < hi /\
    gas_origin_edge F explicit ctx fn p ms (OK q)) u v
Proof
  strip_tac >> drule_then irule create_expr_prefix_rtc_project >>
  simp[create_prefix_step_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> fs[frag_ids_def] >> decide_tac
QED

Theorem create_indexed_rtc_join:
  !n k (states:'a list) R.
    (!i. k <= i /\ i < k+n ==> RTC R (EL i states) (EL (SUC i) states)) ==>
    RTC R (EL k states) (EL (k+n) states)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `RTC R (EL k states) (EL (k+n) states)` by (first_x_assum irule >> simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `RTC R (EL (k+n) states) (EL (SUC (k+n)) states)` by (first_x_assum irule >> decide_tac) >>
  simp[ADD_CLAUSES] >> metis_tac[RTC_TRANS]
QED

Theorem create_copy_fixed_run[local]:
  cuts = ac::bc::c::prep /\ LAST (c::prep) = sc /\
  EVERY (\z. c.cs_next_id <= z.cs_next_id /\ z.cs_next_id <= sc.cs_next_id) (c::prep) /\
  LIST_REL (\z u. u.vs_current_bb = z.cs_current_bb /\ u.vs_inst_idx = LENGTH z.cs_current_insts)
    (sa::cuts) states /\ LAST states = s /\
  (!i. i < LENGTH cuts ==> create_expr_prefix (EL i (sa::cuts)) (EL i cuts)
    explicit ctx fn (EL i states) (EL i chunk_rows) (EL (SUC i) states)) /\
  fn_has_code c sc fn /\ sc.cs_current_bb = c.cs_current_bb /\
  sc.cs_current_insts = c.cs_current_insts ++ emitted_insts c sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts c sc) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id = sc.cs_next_id ==>
  run_inst_seq (emitted_insts c sc) (EL 3 states) = OK (s with vs_inst_idx := (EL 3 states).vs_inst_idx)
Proof
  strip_tac >> qpat_x_assum `cuts = _` SUBST_ALL_TAC >>
  qpat_x_assum `LIST_REL _ _ _` (strip_assume_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  `LENGTH states = SUC (3 + LENGTH prep)` by fs[] >>
  `EL (3 + LENGTH prep) states = s /\
   EL (3 + LENGTH prep) (sa::ac::bc::c::prep) = sc` by
    (conj_tac
     >- (`states <> []` by (Cases_on `states` >> fs[]) >> fs[LAST_EL]) >>
     qspec_then `sa::ac::bc::c::prep` mp_tac LAST_EL >>
     simp[LAST_CONS_cond, ADD_CLAUSES] >> fs[LAST_CONS_cond, ADD_CLAUSES]) >>
  `((EL 3 states).vs_current_bb = c.cs_current_bb /\
    (EL 3 states).vs_inst_idx = LENGTH c.cs_current_insts) /\
   s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `!n. n < LENGTH (sa::_) ==> _`
       (fn th => mp_tac (Q.SPEC `3` th) >> mp_tac (Q.SPEC `3 + LENGTH (prep:compile_state list)` th)) >>
     BETA_TAC >>
     qpat_assum `EL _ (sa::_) = (sc:compile_state)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `EL _ states = (s:venom_state)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[EL_CONS, ADD_CLAUSES]) >>
  qabbrev_tac `R = \p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ c.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
    gas_origin_edge F explicit ctx fn p ms (OK q)` >>
  `RTC R (EL 3 states) (EL (3 + LENGTH prep) states)` by
    (irule create_indexed_rtc_join >> rpt strip_tac >>
     `i < LENGTH (ac::bc::c::prep)` by simp[] >>
     qpat_assum `!i. i < LENGTH (ac::_) ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     `EL (i-3) (c::prep) = EL i (sa::ac::bc::c::prep) /\
      EL (i+1-3) (c::prep) = EL i (ac::bc::c::prep)` by
       (`?j. i = SUC (SUC (SUC j))` by (qexists_tac `i-3` >> decide_tac) >>
        `SUC (SUC (SUC j)) - 3 = j /\ SUC (SUC (SUC j)) + 1 - 3 = SUC j` by decide_tac >>
        asm_rewrite_tac[] >> simp[]) >>
     qpat_x_assum `EVERY (\z. _ <= z.cs_next_id /\ _) (c::prep)`
       (assume_tac o SIMP_RULE bool_ss [EVERY_EL, BETA_THM]) >>
     `i-3 < LENGTH (c::prep) /\ i+1-3 < LENGTH (c::prep)` by (simp[] >> decide_tac) >>
     rw[Abbr `R`] >> irule create_prefix_band_rtc >> goal_assum (drule_at Any) >>
     qpat_x_assum `!n. n < LENGTH (c::_) ==> _`
       (fn th => mp_tac (Q.SPEC `i-3` th) >> mp_tac (Q.SPEC `i+1-3` th)) >>
     asm_rewrite_tac[] >> simp[]) >>
  irule create_straight_prefix_run >>
  simp[] >>
  qpat_x_assum `fn_has_code c sc fn` (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  qexistsl_tac [`R`,`bb`,`ctx`,`explicit`,`fn`] >>
  `lookup_block c.cs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  `?rest. bb.bb_instructions = c.cs_current_insts ++ (emitted_insts c sc ++ rest)` by
    (qpat_x_assum `_ ≼ bb'.bb_instructions` mp_tac >> fs[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `!p q. p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = s.vs_inst_idx ==> ~R p q` by
    (simp[Abbr `R`] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >- (simp[Abbr `R`, PULL_EXISTS] >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> fs[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (PURE_REWRITE_TAC[DROP_LENGTH_APPEND, IS_PREFIX_APPEND] >> qexists_tac `rest` >> simp[]) >>
  metis_tac[]
QED

Theorem create_copy_scalar_prefix_rows[local]:
  cuts = a::b::c::prep /\ HD states = s0 /\ LENGTH chunk_rows = LENGTH cuts /\
  LIST_REL (\z u. u.vs_current_bb = z.cs_current_bb /\ u.vs_inst_idx = LENGTH z.cs_current_insts)
    (sa::cuts) states /\
  (!i. i < LENGTH cuts ==> create_expr_prefix (EL i (sa::cuts)) (EL i cuts)
    explicit ctx fn (EL i states) (EL i chunk_rows) (EL (SUC i) states)) /\
  marks = FLAT chunk_rows ==>
  create_expr_prefix sa a explicit ctx fn s0 (EL 0 chunk_rows) (EL 1 states) /\
  create_expr_prefix a b explicit ctx fn (EL 1 states) (EL 1 chunk_rows) (EL 2 states) /\
  create_expr_prefix b c explicit ctx fn (EL 2 states) (EL 2 chunk_rows) (EL 3 states) /\
  (EL 1 states).vs_current_bb = a.cs_current_bb /\ (EL 1 states).vs_inst_idx = LENGTH a.cs_current_insts /\
  (EL 2 states).vs_current_bb = b.cs_current_bb /\ (EL 2 states).vs_inst_idx = LENGTH b.cs_current_insts /\
  (EL 3 states).vs_current_bb = c.cs_current_bb /\ (EL 3 states).vs_inst_idx = LENGTH c.cs_current_insts /\
  marks = EL 0 chunk_rows ++ (EL 1 chunk_rows ++ (EL 2 chunk_rows ++ FLAT (DROP 3 chunk_rows)))
Proof
  strip_tac >> qpat_x_assum `cuts = _` SUBST_ALL_TAC >>
  qpat_x_assum `LIST_REL _ _ _` (strip_assume_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  `EL 0 states = s0` by (Cases_on `states` >> fs[]) >>
  qpat_x_assum `!i. _ ==> create_expr_prefix _ _ _ _ _ _ _ _`
    (fn th => map_every (fn k => qspec_then k mp_tac th) [`0`,`1`,`2`]) >>
  qpat_x_assum `!i. i < LENGTH _ ==> _`
    (fn th => map_every (fn k => qspec_then k mp_tac th) [`1`,`2`,`3`]) >>
  `3 < LENGTH states` by fs[] >>
  simp[EL_CONS] >> rpt strip_tac >> simp[] >>
  `2 < LENGTH chunk_rows` by fs[] >>
  `TAKE 3 chunk_rows = [EL 0 chunk_rows; EL 1 chunk_rows; EL 2 chunk_rows]` by
    (map_every (fn k => qspecl_then [`chunk_rows:bool list list`,k] mp_tac TAKE_EL_SNOC)
       [`2`,`1`] >>
     `chunk_rows <> []` by (Cases_on `chunk_rows` >> fs[]) >>
     simp[TAKE1, SNOC] >> decide_tac) >>
  `FLAT (TAKE 3 (chunk_rows:bool list list) ++ DROP 3 chunk_rows) = FLAT chunk_rows` by
    (PURE_REWRITE_TAC[TAKE_DROP] >> REFL_TAC) >>
  pop_assum mp_tac >> simp[FLAT_APPEND, APPEND_ASSOC] >> metis_tac[]
QED

Theorem create_size_exit_copy:
  !cx ann has_salt rof ks args dflt.
    EVERY (create_operand_completed_ok cx) (create_operand_order CreateCopyOf has_salt args) ==>
    create_expr_size_exit cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
Proof
  rewrite_tac[create_expr_size_exit_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `?result. compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >> strip_tac >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [create_call_itinerary_def, create_kind_case_def, create_copy_itinerary_def]) >>
  rename1 `lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `lower_value compile_expr cenv (expr_type value_e) value_e a = (value_op,b)` >>
  rename1 `create_itinerary_salt _ _ b salt_op c` >>
  rename1 `create_size_dispatch_tail rof dispatch sd created bufop len value_op salt_op result sb` >>
  `well_typed_expr env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> simp[]) >>
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
  drule_all create_copy_scalar_prefix_rows >> strip_tac >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?acc. accounts_agree H cx.txn.target acc (EL 3 states).vs_accounts /\ accounts_well_typed acc` by
    (irule create_copy_replay_accounts_at_cuts >>
     qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
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
     simp[] >> qexistsl_tac [`tail`,`FLAT (DROP 3 chunk_rows)`,`env`,`ee`] >>
     fs[APPEND_ASSOC])
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sa c` by
    (`!ce ty e u. cs_extends u (SND (lower_value compile_expr ce ty e u))` by
       simp[lower_value_labels, compile_expr_labels] >>
     `cs_extends b c` by metis_tac[compile_create_salt_labels, compile_expr_labels, SND] >>
     metis_tac[cs_extends_trans, SND]) >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     Cases_on `salt_op` >>
     qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
     (conj_tac
      >- (qpat_assum `emit_op _ _ sc = _` (fn th =>
            mp_tac (SIMP_RULE bool_ss [ci_mono_def, th, SND] ci_mono_emit_op)) >>
          simp[ci_mono_def] >> metis_tac[SND]) >>
      qspecl_then [`created`,`rof`,`sd`] mp_tac compile_check_create_result_labels >>
      asm_rewrite_tac[SND] >> simp[])) >>
  `fn_has_code c sc func` by metis_tac[fn_has_code_mid] >>
  `inst.inst_id = sc.cs_next_id /\ eval_operand len s = SOME w` by
    (Cases_on `salt_op` >> fs[mk_inst_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c sc) (EL 3 states) =
    OK (s with vs_inst_idx := (EL 3 states).vs_inst_idx)` by
    (irule create_copy_fixed_run >> asm_rewrite_tac[] >>
     qpat_assum `(cuts:compile_state list) = _::_::_::_` (irule_at Any) >>
     qpat_assum `fn_has_code c sc func` (irule_at Any) >>
     `get_instruction bb (LENGTH (c.cs_current_insts ++ emitted_insts c sc)) = SOME inst` by fs[] >>
     pop_assum (irule_at Any) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`sa`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`chunk_rows`] >>
     fs[]) >>
  `eval_operand len (s with vs_inst_idx := (EL 3 states).vs_inst_idx) = SOME w` by
    simp[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  drule_all create_copy_pre_dispatch_length_bound >> simp[GSYM NOT_LESS_EQUAL]
QED
