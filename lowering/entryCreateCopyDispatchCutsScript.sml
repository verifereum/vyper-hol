(* The CopyOf operand rows on the observed itinerary, before source replay. *)
Theory entryCreateCopyDispatchCuts
Ancestors
  createSizePrefixCuts createSizeCopyScalarCode createSizeIndexedRun
  createSizeObservedPrefix createCtorSegmentArrival createSizeCopyLength
  createSizeStraightPrefix createSizeDispatch createSizeItinerary
  exprSimSend exprBodyPreProps exprSimFullBundleProps ghostPcTransportPtr
  createExprSizeExitDefs s1PrefixDefs fragExec gasExplicitSites
  externalEntryShape exprLoweringProps exprLowering compileEnv builtinCreate
  vyperTypeSystem vyperAST loweringStateRelDefs accountsRelProps
  venomInst venomState venomExecSemantics vfmConstants list rich_list pair

Theorem copy_dispatch_cuts:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx ty (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s0 marks s /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE; CREATE2] ==> j.inst_id <= inst.inst_id) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; off; sz; salt_arg])) /\
  eval_operand sz s = SOME w ==>
  ?target_e value_e salt_e target value_op salt a1 a2 a3 b1 b2 b3 u1 u2 u3 m1 m2 m3 mr.
    has_salt = IS_SOME salt_e /\
    args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e]) /\
    lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a1) /\
    lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value_op,a2) /\
    compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target_e) (gas_shadow_expr target_e)
      shadow_sa = (target,b1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type value_e) (gas_shadow_expr value_e)
      b1 = (value_op,b2) /\
    compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt_e)
      b2 = (salt,b3) /\
    gas_shadow_state a1 b1 /\ gas_shadow_state a2 b2 /\ gas_shadow_state a3 b3 /\
    fn_has_code sa a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
    fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\ fn_has_code b2 b3 shadow_func /\
    create_expr_prefix sa a1 (gas_explicit_sites ctx shadow_ctx) ctx func s0 m1 u1 /\
    create_expr_prefix a1 a2 (gas_explicit_sites ctx shadow_ctx) ctx func u1 m2 u2 /\
    create_expr_prefix a2 a3 (gas_explicit_sites ctx shadow_ctx) ctx func u2 m3 u3 /\
    u1.vs_current_bb = a1.cs_current_bb /\ u1.vs_inst_idx = LENGTH a1.cs_current_insts /\
    u2.vs_current_bb = a2.cs_current_bb /\ u2.vs_inst_idx = LENGTH a2.cs_current_insts /\
    u3.vs_current_bb = a3.cs_current_bb /\ u3.vs_inst_idx = LENGTH a3.cs_current_insts /\
    marks = m1 ++ (m2 ++ (m3 ++ mr)) /\
    (!H acc. accounts_agree H cx.txn.target acc u3.vs_accounts /\ accounts_well_typed acc ==>
       w2n w <= 2 * max_code_size)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
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
  suspend "paired_code"
QED

Resume copy_dispatch_cuts[paired_code]:
  `well_typed_expr env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)` by
    (drule expr_body_pre_static_facts >> simp[]) >>
  qabbrev_tac `salt_e = if has_salt then SOME (HD rest) else NONE` >>
  `has_salt = IS_SOME salt_e /\
   args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e])` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     qpat_assum `args = target_e::value_e::rest` (pure_rewrite_tac o single) >>
     Cases_on `has_salt` >> simp[Abbr `salt_e`, well_typed_expr_def, create_arg_types_ok_def] >>
     Cases_on `rest` >> simp[] >> rename1 `MAP expr_type rs = _ ==> _` >> Cases_on `rs` >> simp[]) >>
  `compile_create_salt compile_expr cenv salt_e b = (salt_op,c)` by
    (qpat_x_assum `create_itinerary_salt _ _ b salt_op c` mp_tac >>
     qpat_assum `Abbrev (salt_e = _)` (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     Cases_on `salt_e` >> simp[create_itinerary_salt_def, compile_create_salt_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  rename1 `emit_op ADD [code; Lit 11w] _ = (len,sc)` >>
  rename1 `marks = FLAT chunk_rows` >>
  `dispatch = sc` by
    (qpat_assum `LAST (sa::cuts) = dispatch` mp_tac >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `dispatch = sc` SUBST_ALL_TAC >>
  `compile_create_dispatch bufop len value_op salt_op rof sc = (result,sb)` by
    (Cases_on `salt_op` >>
     qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
     qpat_x_assum `created = Var out` SUBST_ALL_TAC >>
     simp[compile_create_dispatch_def, comp_bind_def]) >>
  drule_all create_copy_preparation_code >> disch_then (strip_assume_tac o Q.SPEC `value_op`) >>
  `compile_create_copy target value_op salt_op rof c = (result,sb)` by
    (first_x_assum irule >> simp[]) >>
  drule_all create_copy_scalar_code >> strip_tac >>
  suspend "index"
QED

Resume copy_dispatch_cuts[index]:
  qabbrev_tac `n = LENGTH (cuts : compile_state list)` >>
  qabbrev_tac `C = \i. EL i (sa::cuts)` >>
  qabbrev_tac `U = \i. EL i (states : venom_state list)` >>
  qabbrev_tac `M = \i. EL i (chunk_rows : bool list list)` >>
  `LENGTH states = SUC n /\ LENGTH (sa::cuts) = SUC n` by fs[LIST_REL_EL_EQN, Abbr `n`] >>
  `U 0 = s0 /\ U n = s` by (Cases_on `states` >> gvs[EL,LAST_EL,Abbr `U`]) >>
  `C n = sc` by
    (qspec_then `sa::cuts` mp_tac LAST_EL >> simp[Abbr `C`]) >>
  `C 0 = sa /\ C 1 = a /\ C 2 = b /\ C 3 = c /\ 3 <= n` by fs[Abbr `C`, Abbr `n`, EL_CONS] >>
  `!i j. i <= j /\ j <= n ==> (C i).cs_next_id <= (C j).cs_next_id` by
    (drule create_itinerary_index_mono >> simp[Abbr `C`,Abbr `n`,ci_mono_def]) >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
    create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shadow_ctx) ctx func
      (U i) (M i) (U (SUC i))` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (first_assum irule >> decide_tac) >>
     qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `i` (drule_then mp_tac)) >>
     simp_tac bool_ss [Abbr `C`, Abbr `U`, Abbr `M`, EL, TL]) >>
  `inst.inst_id = sc.cs_next_id /\ eval_operand len s = SOME w /\ inst.inst_opcode <> PHI` by
    (Cases_on `salt_op` >> fs[mk_inst_def] >> metis_tac[]) >>
  `ctor_segment_fetch func s = SOME inst` by
    (pure_rewrite_tac[ctor_segment_fetch_def] >>
     qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  `~(U 0).vs_halted /\ ctor_segment_fetch func (U n) = SOME inst /\ (C n).cs_next_id <= inst.inst_id` by simp[] >>
  map_every (fn pat => qpat_assum pat (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (C = _)`,`Abbrev (U = _)`,`Abbrev (M = _)`] >>
  drule_all raw_observed_spine >> strip_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac) [`C = (\i. _)`,`U = (\i. _)`,`M = (\i. _)`] >>
  `!i. i <= n ==> (U i).vs_current_bb = (C i).cs_current_bb /\
                    (U i).vs_inst_idx = LENGTH (C i).cs_current_insts` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!i. i <= n ==> ~(U i).vs_halted /\ _`
       (qspec_then `i` (drule_then mp_tac)) >> simp_tac bool_ss [PAIR_EQ]) >>
  suspend "bound"
QED

Resume copy_dispatch_cuts[bound]:
  `cs_extends sa c` by
    (drule create_itinerary_index_mono >>
     disch_then (qspecl_then [`0`,`3`] mp_tac) >> simp[ci_mono_def,EL_CONS]) >>
  `cs_extends sc sb` by metis_tac[compile_create_dispatch_labels, SND] >>
  `fn_has_code c sc func` by metis_tac[fn_has_code_mid] >>
  `run_inst_seq (emitted_insts c sc) (U 3) = OK (s with vs_inst_idx := (U 3).vs_inst_idx)` by
    (qpat_assum `U n = s` (pure_once_rewrite_tac o single o SYM) >>
     irule (Q.INST [`i` |-> `3`] create_indexed_straight_run) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `3 <= n /\ n <= n` by decide_tac >>
     qpat_assum `!i. i <= n ==> (U i).vs_current_bb = _ /\ _`
       (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th) [`3`,`n`]) >>
     simp[] >>
     qexistsl_tac [`C`,`ctx`,`bb`,`gas_explicit_sites ctx shadow_ctx`,`func`,`inst`,`M`] >>
     conj_tac >- simp[] >>
     conj_tac
     >- (qx_gen_tac `j` >> strip_tac >>
         `j < n /\ j <= n /\ SUC j <= n` by decide_tac >>
         qpat_assum `!i. i < n ==> _ /\ create_expr_prefix _ _ _ _ _ _ _ _`
           (qspec_then `j` (drule_then strip_assume_tac)) >>
         qpat_assum `!i j. _ ==> (C i).cs_next_id <= (C j).cs_next_id`
           (fn th => map_every (fn qs => qspecl_then qs mp_tac th >>
             (impl_tac >- decide_tac) >> disch_tac) [[`3`,`j`],[`SUC j`,`n`]]) >>
         `c.cs_next_id <= (C j).cs_next_id /\ (C (SUC j)).cs_next_id <= sc.cs_next_id` by
           (qpat_assum `(C 3).cs_next_id <= _` mp_tac >>
            qpat_assum `(C (SUC j)).cs_next_id <= (C n).cs_next_id` mp_tac >>
            qpat_assum `C 3 = c` (pure_rewrite_tac o single) >>
            qpat_assum `C n = sc` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `U n = s` (pure_rewrite_tac o single) >>
     qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` mp_tac >>
     qpat_assum `get_instruction bb s.vs_inst_idx = SOME inst` mp_tac >>
     map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`s.vs_current_bb = sc.cs_current_bb`,`s.vs_inst_idx = LENGTH sc.cs_current_insts`,
        `sc.cs_current_bb = c.cs_current_bb`,`sc.cs_current_insts = c.cs_current_insts ++ emitted_insts c sc`] >>
     simp_tac bool_ss [LENGTH_APPEND] >> rpt disch_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand len (s with vs_inst_idx := (U 3).vs_inst_idx) = SOME w` by
    simp[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  `!H acc. accounts_agree H cx.txn.target acc (U 3).vs_accounts /\ accounts_well_typed acc ==>
      w2n w <= 2 * max_code_size` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all create_copy_pre_dispatch_length_bound >> simp[]) >>
  suspend "rows"
QED

Resume copy_dispatch_cuts[rows]:
  `0 < n /\ 1 < n /\ 2 < n /\ 1 <= n /\ 2 <= n` by decide_tac >>
  qpat_assum `!i. i <= n ==> (U i).vs_current_bb = _ /\ _`
    (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th) [`1`,`2`,`3`]) >>
  qpat_assum `!i. i < n ==> _ /\ create_expr_prefix _ _ _ _ _ _ _ _`
    (fn th => map_every (fn q => qspec_then q (drule_then
       (strip_assume_tac o SIMP_RULE bool_ss [DECIDE ``SUC 0 = 1``,
         DECIDE ``SUC 1 = 2``, DECIDE ``SUC 2 = 3``])) th) [`0`,`1`,`2`]) >>
  `marks = M 0 ++ (M 1 ++ (M 2 ++ FLAT (DROP 3 chunk_rows)))` by
    (qpat_assum `!i. i < n ==> FLAT (DROP i chunk_rows) = _`
       (fn th => map_every (fn q => qspec_then q (drule_then mp_tac) th) [`0`,`1`,`2`]) >>
     simp_tac bool_ss [DROP_0, DECIDE ``SUC 0 = 1``, DECIDE ``SUC 1 = 2``, DECIDE ``SUC 2 = 3``] >>
     rpt disch_tac >> fs[]) >>
  qexistsl_tac [`target_e`,`value_e`,`salt_e`,`target`,`value_op`,`salt_op`,
    `a`,`b`,`c`,`b1`,`b2`,`b3`,`U 1`,`U 2`,`U 3`,`M 0`,`M 1`,`M 2`,`FLAT (DROP 3 chunk_rows)`] >>
  simp[] >>
  map_every (fn q => qpat_assum q mp_tac)
    [`create_expr_prefix (C 0) (C 1) _ _ _ _ _ _`,
     `create_expr_prefix (C 1) (C 2) _ _ _ _ _ _`,
     `create_expr_prefix (C 2) (C 3) _ _ _ _ _ _`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C 0 = sa`,`C 1 = a`,`C 2 = b`,`C 3 = c`,`U 0 = s0`] >>
  rpt disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise copy_dispatch_cuts
