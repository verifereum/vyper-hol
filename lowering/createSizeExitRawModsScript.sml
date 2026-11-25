Theory createSizeExitRawMods
Ancestors
  createSizeExitRaw createExprSizeExitDefsMods
  bodySingletonCallSupport[qualified,ignore_grammar]
  exprSimFullBundleProps fragExec gasExplicitSites s1PrefixDefs venomExecSemantics venomInst
  venomState vyperCreate vyperState relation list words pair bodyFullIfExpReach
  builtinCreate arithmetic createSizeDispatch exprLowering vfmConstants externalEntryShape
  compileEnv createSizeItinerary exprLoweringProps exprBodyPreProps rich_list
  exprSimHypsDefs vyperTypeSystem bodyPtrDefs loweringPosts context createSizeRawSourceMods
  bodyInvCodeProps vyperAST allocLimits vyperTypeCallGraph exprSimSend integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate loweringStateRelDefs
  dallocaBlueprintArgs createSizeRawPairedCode createSizeRawExtent createOperandSizeReject
  createExprSizeExitDefs createSizePrefixCutsMods createSizeRawReplayMods createSizeRawDataEntryMods
  createSizeRawObserved createSizeRawPayloadReplayMods createSizeOperandPreMods
  createSizeRawPayloadNoCopyMods gasShadowCompileBase
  exprSimIfExpCompat exprSimAbiEncodeArgsPhysicalCapacity exprSimSource
  vyperTypeEvalCaseProofs vyperTypeArgFits exprSimHyps

Theorem raw_payload_snapshot_no_copy_mods[local]:
  compile_expr ce (expr_type e) e ca = (v,cm) /\
    expr_body_pre_mods mods ce cx env e p /\
    ~exprs_can_mutate ce rest /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_snapshot_vv ce (exprs_can_mutate ce rest)
      (ext_call_arg_value (lowered_value_type ce e) v) cm = (saved,cn) ==>
    cm = cn
Proof
  ACCEPT_TAC raw_payload_snapshot_no_copy_static_mods
QED

Theorem create_size_exit_raw_mods:
  !mods exps cx ann hs rof ks args df.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs args) ==>
    create_expr_size_exit_mods mods exps cx (Call ann (CreateTarget RawCreate hs rof ks) args df)
Proof
  rewrite_tac[create_expr_size_exit_mods_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_mods_def]) >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  `?result. compile_create_call compile_expr cenv RawCreate hs rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call,compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv RawCreate hs rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts_mods >> strip_tac >>
  suspend "layout"
QED

Resume create_size_exit_raw_mods[layout]:
  rename1 `eval_operand sz s = SOME w` >>
  rename1 `create_size_dispatch_tail rof sc sd created bufop len amount salt_op result sb` >>
  `len = sz /\ inst.inst_id = sc.cs_next_id /\ inst.inst_opcode <> PHI` by
    (Cases_on `salt_op` >> qpat_assum `inst = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
     fs[mk_inst_def]) >>
  qpat_x_assum `len = sz` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
      [create_call_itinerary_def,vyperASTTheory.create_kind_case_def,create_raw_itinerary_def]) >>
  rename [`compile_expr cenv (expr_type be) be sa = (bcvv,a)`,
          `compile_create_snapshot cenv bcvv _ a = (snap,b)`,
          `emit_op MLOAD [snap] b = (lenop,c)`, `emit_op ADD [snap;Lit 32w] c = (data,cd)`,
          `lower_value compile_expr cenv (expr_type av) av cv = (amount,cq)`,
          `create_itinerary_salt cenv _ cq salt_op cf`] >>
  `sc = cf` by
    (qpat_assum `LAST (sa::cuts) = sc` mp_tac >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
     `sa::([a;b;c;cd] ++ prep ++ [cq;cf]) = ([sa;a;b;c;cd] ++ prep) ++ [cq;cf]` by
       simp[APPEND_ASSOC] >>
     pop_assum (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `sc = cf` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `xs = if hs then FRONT rest else rest` >>
  qabbrev_tac `salte = if hs then SOME (LAST rest) else NONE` >>
  qabbrev_tac `cap = bytelike_type_bound (lowered_value_type cenv be) +
       abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs))` >>
  `rest = xs ++ (if hs then [LAST rest] else [])` by
    (Cases_on `hs` >> simp_tac (srw_ss()) [Abbr `xs`] >> sym_tac >>
     irule APPEND_FRONT_LAST >> fs[]) >>
  suspend "bands"
QED

Resume create_size_exit_raw_mods[bands]:
  qmatch_asmsub_rename_tac `marks = FLAT mark_rows` >>
  qabbrev_tac `C = \i. EL i (sa::cuts)` >>
  qabbrev_tac `Obs = \i. EL i states` >>
  qabbrev_tac `M = \i. EL i mark_rows` >>
  qabbrev_tac `R = \i. FLAT (DROP i mark_rows)` >>
  qabbrev_tac `n = LENGTH cuts` >>
  qabbrev_tac `vp = 4 + LENGTH prep` >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  `cs_extends sc sb` by
    (`?opc ops. emit_op opc ops sc = (created,sd) /\ compile_check_create_result created rof sd = (result,sb)` by
       (Cases_on `salt_op` >> fs[create_size_dispatch_tail_def] >> metis_tac[]) >>
     irule cs_extends_trans >> qexists_tac `sd` >>
     metis_tac[ci_mono_def,ci_mono_emit_op,externalEntryShapeTheory.compile_check_create_result_labels,SND]) >>
  `!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k)` by
    (drule create_itinerary_index_mono >> simp[Abbr `C`,Abbr `n`]) >>
  `C 0 = sa /\ C n = sc` by
    (conj_tac >- simp[Abbr `C`] >>
     qpat_assum `LAST (sa::cuts) = sc` (mp_tac o SYM) >>
     simp_tac bool_ss [Abbr `C`,Abbr `n`,LAST_EL,NOT_CONS_NIL,LENGTH,prim_recTheory.PRE]) >>
  `!i k. i <= k /\ k <= n ==> fn_has_code (C i) (C k) func` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i k. _ ==> ci_mono (C i) (C k)` (fn th =>
       map_every (fn ts => qspecl_then ts mp_tac th >> (impl_tac >- decide_tac) >>
                          disch_then assume_tac)
         [[`0`,`i`],[`i`,`k`],[`k`,`n`]]) >>
     `cs_extends (C k) sb` by metis_tac[ci_mono_def,cs_extends_trans] >>
     irule fn_has_code_mid >> conj_tac
     >- (qpat_assum `ci_mono (C i) (C k)` (mp_tac o REWRITE_RULE[ci_mono_def]) >> asm_simp_tac bool_ss []) >>
     qexistsl_tac [`sb`,`sa`] >>
     qpat_assum `ci_mono (C 0) (C i)` (mp_tac o REWRITE_RULE[ci_mono_def]) >>
     asm_simp_tac bool_ss []) >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
    fn_has_code (C i) (C (SUC i)) func /\
    create_expr_prefix (C i) (C (SUC i)) explicit ctx func (Obs i) (M i) (Obs (SUC i))` by
    (gen_tac >> strip_tac >>
     `i <= SUC i /\ SUC i <= n` by decide_tac >>
     qpat_assum `!i k. _ ==> ci_mono (C i) (C k)` (qspecl_then [`i`,`SUC i`] (drule_all_then assume_tac)) >>
     conj_tac >- fs[ci_mono_def] >>
     conj_tac >- (first_assum irule >> simp[]) >>
     qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _` (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `C`,Abbr `Obs`,Abbr `M`,EL,TL]) >>
  `ctor_segment_fetch func s = SOME inst` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (fn th =>
       simp_tac bool_ss [ctor_segment_fetch_def,th,optionTheory.OPTION_BIND_def]) >>
     first_assum ACCEPT_TAC) >>
  suspend "observed"
QED

Resume create_size_exit_raw_mods[observed]:
  `LENGTH mark_rows = n` by simp[Abbr `n`] >>
  map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (C = _)`,`Abbrev (Obs = _)`,`Abbrev (M = _)`,`Abbrev (R = _)`,
     `Abbrev (n = _)`,`Abbrev (vp = _)`] >>
  drule_all create_raw_observed_bands >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n = SUC (SUC vp)` by
    (qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single) >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `vp = 4 + LENGTH prep` (pure_rewrite_tac o single) >>
     simp_tac arith_ss [LENGTH_APPEND,LENGTH]) >>
  qpat_x_assum `if xs = [] then _ else _`
    (fn th =>
       let val [empty,nonempty] = CONJUNCTS (PURE_REWRITE_RULE [COND_EXPAND_IMP] th)
       in assume_tac empty >>
          strip_assume_tac (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) nonempty)
       end) >>
  suspend "pair"
QED

Resume create_size_exit_raw_mods[pair]:
  rename1 `compile_abi_encode_values_to_buf _ _ _ _ = (_,en)` >>
  `xs = (if hs then FRONT rest else rest)` by simp_tac bool_ss [Abbr `xs`] >>
  `salte = (if hs then SOME (LAST rest) else NONE)` by simp_tac bool_ss [Abbr `salte`] >>
  `cap = bytelike_type_bound (lowered_value_type cenv be) +
    abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs))`
    by simp_tac bool_ss [Abbr `cap`] >>
  `if xs = [] then bufop = data /\ len = lenop /\ cv = cd else
   compile_create_ctor_args compile_expr cenv xs cd = (vals,k) /\
   create_itinerary_ctor_rows cenv xs vals cd k cs mid vs /\
   compile_alloc_buffer cap k = (buf,ca) /\
   compile_copy_memory_dynamic buf.buf_operand data lenop ca = ((),cb) /\
   emit_op ADD [buf.buf_operand;lenop] cb = (dst,cc) /\
   compile_abi_encode_values_to_buf cenv dst (ZIP (vals,MAP (lowered_value_type cenv) xs)) cc = (alen,en) /\
   emit_op ADD [lenop;alen] en = (len,cv) /\ bufop = buf.buf_operand` by
    (IF_CASES_TAC >>
     first_assum (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `args = be::av::rest` SUBST_ALL_TAC >>
  drule_all create_raw_paired_operand_code >>
  disch_then (qx_choosel_then [`ha`,`hp`,`hq`,`hsc`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "header"
QED

Resume create_size_exit_raw_mods[header]:
  `1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ vp <= n /\ SUC vp <= n` by
    (qpat_assum `n = SUC (SUC vp)` (pure_rewrite_tac o single) >>
     qpat_assum `vp = 4 + LENGTH prep` (pure_rewrite_tac o single) >> decide_tac) >>
  map_every (fn (ix,ceq) =>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _` (qspec_then ix mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum ceq (fn th => disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[PAIR_EQ,th])))
    [(`1`,`C 1 = a`),(`2`,`C 2 = b`),(`3`,`C 3 = c`),(`4`,`C 4 = cd`),
     (`vp`,`C vp = cv`),(`SUC vp`,`C (SUC vp) = cq`)] >>
  qpat_assum `Abbrev (explicit = _)`
    (fn h => rule_assum_tac (ONCE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] h])) >>
  `eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (be::av::rest) df)
     (es with gas_obs := gas_explicit (M 0 ++ (M 1 ++ M 2 ++ M 3 ++ FLAT (DROP 4 mark_rows)))
       s0.vs_gas_readings ++ tail) = (res,ee)` by
    (qpat_assum `marks = _ ++ FLAT (DROP 4 mark_rows)` (fn th =>
       qpat_assum `eval_expr cx (Call _ _ _ _) (es with gas_obs := gas_explicit marks _ ++ tail) = _`
         (mp_tac o REWRITE_RULE [th])) >> simp_tac bool_ss [GSYM APPEND_ASSOC]) >>
  let
    fun fix (premise, fact) next th = qpat_assum fact (mp_then (Pat premise) next th)
    val prefix = `create_expr_prefix _ _ _ _ _ _ _ _`
    val entry = `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`
  in
    List.foldr (fn (anchor,next) => fix anchor next) drule_all
      [(entry,entry),
       (`eval_expr _ (Call _ _ _ _) _ = _`,
        `eval_expr cx (Call _ _ _ _) (es with gas_obs := gas_explicit (M 0 ++ _) _ ++ tail) = (res,ee)`),
       (prefix,`create_expr_prefix sa a _ _ _ s0 (M 0) (Obs 1)`),
       (prefix,`create_expr_prefix a b _ _ _ (Obs 1) (M 1) (Obs 2)`),
       (prefix,`create_expr_prefix b c _ _ _ (Obs 2) (M 2) (Obs 3)`),
       (prefix,`create_expr_prefix c cd _ _ _ (Obs 3) (M 3) (Obs 4)`)]
      create_raw_data_entry_at_cuts_mods
  end >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`p0`,`tv`,`code`,`Gr`,`tnr`,`lenvar`,`datavar`] (map_every assume_tac o CONJUNCTS)))
  >- (disj2_tac >> first_assum ACCEPT_TAC) >>
  suspend "payload"
QED

Resume create_size_exit_raw_mods[payload]:
  `!i u vs u'. i < LENGTH xs /\ ~exprs_can_mutate cenv (DROP (SUC i) xs) /\
     eval_exprs cx (DROP (SUC i) xs) u = (INL vs,u') ==>
     u'.immutables = u.immutables /\ !tr. get_storage cx u' tr = get_storage cx u tr` by
    (qpat_assum `!xs. _ ==> !i u vs u'. _ ==> u'.immutables = _ /\ _` (qspec_then `xs` mp_tac) >>
     impl_tac
     >- (disj1_tac >> qexistsl_tac [`ann`,`hs`,`rof`,`ks`,`be`,`av`,`LAST rest`,`df`] >>
         qpat_assum `rest = _` (fn th => simp_tac bool_ss [SimpLHS,Once th])) >>
     disch_then ACCEPT_TAC) >>
  drule_then (fn th => qpat_assum `MEM func ctx.ctx_functions`
    (mp_then (Pos hd) assume_tac th)) body_inv_no_phi_mods >>
  qabbrev_tac `rowC = \i. C (4+2*i)` >>
  qabbrev_tac `rowObs = \i. Obs (4+2*i)` >>
  `rowC 0 = cd /\ rowObs 0 = Obs 4` by
    (qpat_assum `C 4 = cd` (fn th =>
       simp_tac bool_ss [Abbr `rowC`,Abbr `rowObs`,MULT_CLAUSES,ADD_CLAUSES,th])) >>
  rename1 `xs <> [] ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ pidx = 4 + 2 * LENGTH xs /\ _` >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
   ?cvs payload pval Gval tnval.
     LENGTH cvs = LENGTH xs /\
     encode_create_ctor_args (get_tenv cx) (MAP expr_type xs) cvs = SOME payload /\
     bind (eval_exprs cx (av::(if hs then [LAST rest] else [])))
       (\kvs. eval_create_operands cx RawCreate hs rof (MAP expr_type (be::av::rest))
         (blueprint_literal_offset cx hs (be::av::rest)) (BytesV code::(cvs ++ kvs))) pval = (res,ee) /\
     valid_horizon cx st0 H pval.storage_trace /\
     pval.gas_obs = gas_explicit (M vp ++ M (SUC vp)) (Obs vp).vs_gas_readings ++ tail /\
     expr_sim_inv_mods mods cenv cx env pval /\ return_buf_frame d cenv cv (Obs vp) /\
     alloca_history func (Obs vp) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs vp)) /\
     (!f i z. frag_reachable ctx func (Obs vp) f i z ==> dalloca_fmp_headroom i z) /\
     ~(Obs vp).vs_halted /\ (Obs vp).vs_current_bb = cv.cs_current_bb /\
     (Obs vp).vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved cenv cv /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
     (!K. valid_horizon cx st0 K pval.storage_trace ==>
       stmt_state_rel K ctx func cenv cx pval (Obs vp) /\ immutable_frame_mods func cenv cx pval (Obs vp) /\
       storage_well_formed_on cx pval (FST K) /\ ghost_inv_at_mods (DF K) lo d cenv cx pval Gval tnval (Obs vp)) /\
     (if xs = [] then payload = [] /\ len = lenop /\ cv = rowC 0 /\ Obs vp = rowObs 0
      else (!x v. not_fresh_at (rowC 0) x /\ lookup_var x (rowObs 0) = SOME v ==> lookup_var x (Obs (pidx+4)) = SOME v) /\
        eval_operand alen (Obs (pidx+4)) = SOME (n2w (LENGTH payload)) /\
        eval_operand len (Obs vp) = SOME (n2w (LENGTH code + LENGTH payload)) /\
        (!x. len = Var x ==> not_fresh_at cv x) /\ M (pidx+4) = [])`
    suffices_by
      (disch_then (DISJ_CASES_THEN2 assume_tac
        (qx_choosel_then [`cvs`,`payload`,`pval`,`Gval`,`tnval`] (map_every assume_tac o CONJUNCTS)))
       >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "keywords") >>
  irule (Q.INST [`C` |-> `rowC`, `St` |-> `rowObs`] create_raw_payload_at_cuts_mods) >>
  suspend "payload_pre"
QED

Resume create_size_exit_raw_mods[payload_pre]:
  map_every (fn p => qpat_assum p (pure_rewrite_tac o single))
    [`rowC 0 = cd`,`rowObs 0 = Obs 4`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC))) >>
  qpat_x_assum `xs <> [] ==> fn_has_code _ _ _ /\ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [IMP_CONJ_THM]) >>
  qpat_x_assum `xs <> [] ==> ?hd hk hcs hmid. LENGTH hcs = _ /\ _`
    (qx_choosel_then [`hd`,`hk`,`hcs`,`hmid`] assume_tac o
     CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) o
     CONV_RULE (RAND_CONV (REWRITE_CONV [GSYM IMP_CONJ_THM]))) >>
  qexistsl_tac [`\i. M (4+2*i)`, `Gr`, `\i. EL i mid`, `\i. Obs (SUC (4+2*i))`,
    `\i. FLAT (DROP (4+2*i) mark_rows)`, `\i. EL i hmid`, `\i. EL i hcs`,
    `\i. M (SUC (4+2*i))`, `\i. EL i vs`, `ca`, `M pidx`, `ann`, `cb`, `s`, `bb`,
    `M (pidx+1)`, `buf`, `\j. C (pidx+4+j)`, `cap`, `\j. M (pidx+4+j)`,
    `M (pidx+2)`, `df`, `inst`, `dst`, `be`, `en`, `M (pidx+3)`, `es`,
    `gas_explicit_sites ctx shadow_ctx`, `exps`, `ks`, `lenvar`, `3`, `off`,
    `n2w (buffer_allocation_base (Obs 1) a.cs_next_id + 32)`, `p0`,
    `bytelike_type_bound (lowered_value_type cenv be)`, `\j. Obs (pidx+4+j)`,
    `Obs pidx`, `salt`, `k`, `shadow_ctx`, `shadow_func`, `datavar`, `cc`,
    `Obs (pidx+1)`, `Obs (pidx+2)`, `vals`, `len`, `tnr`, `Obs (pidx+3)`, `value`, `w`] >>
  BETA_TAC >>
  simp_tac bool_ss [ADD_CLAUSES,MULT_CLAUSES] >>
  suspend "payload_common"
QED

Resume create_size_exit_raw_mods[payload_common]:
  qpat_assum `rest = xs ++ _` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `xs = (if hs then FRONT rest else rest)` (fn th =>
    qpat_assum `bind (eval_exprs cx ((if hs then FRONT rest else rest) ++ _)) _ p0 = _`
      (assume_tac o PURE_REWRITE_RULE[GSYM th])) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `xs = []`
  >- (qpat_assum `xs = []` (simp_tac bool_ss o single) >>
      qpat_assum `xs = [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
      `vp = 4` by
        (qpat_assum `vp = 4 + LENGTH prep` (pure_rewrite_tac o single) >>
         qpat_assum `prep = []` (simp_tac (srw_ss()) o single)) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `vp = 4` (fn th => simp_tac bool_ss [SimpLHS,GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `xs <> []` (simp_tac bool_ss o single) >>
  suspend "payload_nonempty"
QED

Resume create_size_exit_raw_mods[payload_nonempty]:
  qpat_x_assum `xs <> [] ==> compile_create_ctor_args _ _ _ _ = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt (qpat_x_assum `xs <> [] ==> fn_has_code _ _ _` (drule_then assume_tac)) >>
  qpat_x_assum `xs <> [] ==> LENGTH hcs = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `create_itinerary_ctor_rows`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[create_itinerary_ctor_rows_def]) >>
  `pidx+4+3 = n /\ SUC (pidx+4) = vp /\ pidx+4 <= n` by
    (map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`n = SUC (SUC vp)`,`vp = pidx + 5`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `k = rowC (LENGTH xs) /\ Obs pidx = rowObs (LENGTH xs)` by
    (qpat_assum `pidx = 4 + 2 * LENGTH xs` (fn th =>
       simp_tac bool_ss [Abbr `rowC`,Abbr `rowObs`,GSYM th]) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `C (pidx+4) = en` (fn th =>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
      (qspec_then `pidx+4` (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[th])))) >>
  `create_expr_prefix en cv (gas_explicit_sites ctx shadow_ctx) ctx func
     (Obs (pidx+4)) (M (pidx+4)) (Obs vp)` by
    (qpat_assum `!i. i < n ==> (C i).cs_next_id <= _ /\ _` (qspec_then `pidx+4` mp_tac) >>
     (impl_tac >-
       (qpat_assum `pidx+4+3 = n` (pure_rewrite_tac o single o SYM) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
     map_every (fn p => qpat_assum p (pure_rewrite_tac o single))
       [`SUC (pidx+4) = vp`,`C (pidx+4) = en`,`C vp = cv`] >> simp_tac bool_ss []) >>
  `FLAT (DROP (4+2*LENGTH xs) mark_rows) =
    M pidx ++ M (pidx+1) ++ M (pidx+2) ++ M (pidx+3) ++ M (pidx+4) ++ (M vp ++ M (SUC vp))` by
    suspend "payload_marks" >>
  `EVERY (source_body_call_supported cx) (int_calls_exprs xs)` by suspend "payload_calls" >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv_mods mods cenv cx env p0` mp_tac >>
     simp_tac bool_ss [expr_sim_inv_mods_def]) >>
  `cap < dimword (:256)` by suspend "payload_capacity" >>
  `w2n (n2w (LENGTH code):bytes32) <= LENGTH code` by simp_tac (srw_ss()) [w2n_n2w,MOD_LESS_EQ] >>
  `ptr_covers Gr tnr datavar (Obs 4) (w2n (n2w (LENGTH code):bytes32))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `LENGTH code` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n (n2w (buffer_allocation_base (Obs 1) a.cs_next_id + 32):bytes32) +
      w2n (n2w (LENGTH code):bytes32) <= (Obs 4).vs_alloca_next` by
    (qpat_assum `w2n (n2w _) + LENGTH code <= _` mp_tac >>
     qpat_assum `w2n (n2w (LENGTH code)) <= LENGTH code` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_assum `pidx+4+3 = n` (pure_rewrite_tac o single) >>
  suspend "payload_nonempty_join"
QED

Resume create_size_exit_raw_mods[payload_marks]:
  qpat_assum `pidx = 4 + 2 * LENGTH xs` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `!i. i < n ==> FLAT (DROP i mark_rows) = _`
    (fn th => map_every (fn i => qspec_then i mp_tac th >>
      (impl_tac >-
        (qpat_assum `pidx+4+3 = n` (pure_rewrite_tac o single o SYM) >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
      disch_then (assume_tac o SIMP_RULE bool_ss [DECIDE ``SUC i = i+1``,GSYM ADD_ASSOC,
        DECIDE ``1+1=2 /\ 2+1=3 /\ 3+1=4 /\ 4+1=5``]))
      [`pidx`,`pidx+1`,`pidx+2`,`pidx+3`,`pidx+4`]) >>
  map_every (fn i => qpat_assum i (fn th => simp_tac bool_ss [SimpLHS,Once th]))
    [`FLAT (DROP pidx mark_rows) = _`,`FLAT (DROP (pidx+1) mark_rows) = _`,
     `FLAT (DROP (pidx+2) mark_rows) = _`,`FLAT (DROP (pidx+3) mark_rows) = _`,
     `FLAT (DROP (pidx+4) mark_rows) = _`] >>
  `pidx + 5 = vp` by
    (qpat_assum `SUC (pidx+4) = vp` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_assum `pidx+5 = vp` (pure_rewrite_tac o single) >>
  qpat_assum `FLAT (DROP vp mark_rows) = _` (fn th => simp_tac bool_ss [th,GSYM APPEND_ASSOC])
QED

Resume create_size_exit_raw_mods[payload_calls]:
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_body_pre_mods_def]) >>
  `!ys zs. int_calls_exprs (ys ++ zs) = int_calls_exprs ys ++ int_calls_exprs zs` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[int_calls_expr_def]) >>
  qpat_assum `EVERY (source_body_call_supported cx) (int_calls_expr _)` mp_tac >>
  simp_tac bool_ss [int_calls_expr_def,EVERY_APPEND] >>
  qpat_assum `rest = xs ++ _` (pure_once_rewrite_tac o single) >>
  qpat_assum `!ys zs. int_calls_exprs (ys ++ zs) = _`
    (fn th => simp_tac bool_ss [th,EVERY_APPEND])
QED

Resume create_size_exit_raw_mods[payload_capacity]:
  qpat_assum `expr_body_pre_mods mods cenv cx env (Call _ _ _ _) es`
    (fn th => assume_tac (MATCH_MP expr_body_pre_mods_well_typed th) >>
      assume_tac (MATCH_MP expr_body_pre_mods_inv th) >>
      map_every assume_tac (CONJUNCTS (REWRITE_RULE [expr_body_pre_mods_def] th))) >>
  drule_then (qx_choose_then `kbound` (map_every assume_tac o CONJUNCTS))
    createSizeRawSourceTheory.create_raw_first_type >>
  `!e. MEM e (be::av::rest) ==> arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (gen_tac >> disch_tac >>
     `expr_body_pre_mods mods cenv cx env e es` by
       (irule create_call_operand_body_pre_mods >>
        qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     drule expr_body_pre_mods_well_typed >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env es` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> suspend "payload_fits") >>
  `bytelike_type_bound (lowered_value_type cenv be) <= kbound` by
    (qpat_assum `!e. MEM e (be::av::rest) ==> _` (qspec_then `be` mp_tac) >> simp_tac bool_ss [MEM] >>
     qpat_assum `expr_type be = BaseT _` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `lowered_value_type cenv be` >> simp[arg_type_fits_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[arg_type_fits_def,bytelike_type_bound_def,vyperASTTheory.bound_length_def]) >>
  `abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)) <=
   abi_size_bound cenv.ce_struct_fields (TupleT (MAP expr_type xs))` by
    (irule (cj 2 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_size_bound) >>
     simp_tac (srw_ss()) [vyperTypeArgFitsTheory.arg_types_fit_LIST_REL,LIST_REL_EL_EQN,EL_MAP] >>
     gen_tac >> disch_tac >> qpat_assum `!e. MEM e (be::av::rest) ==> _` irule >>
     qpat_assum `rest = xs ++ _` (pure_once_rewrite_tac o single) >>
     simp_tac bool_ss [MEM,MEM_APPEND] >> disj2_tac >> disj2_tac >> disj1_tac >>
     irule EL_MEM >> first_assum ACCEPT_TAC) >>
  `~(LENGTH rest < if hs then 1 else 0)` by
    (qpat_assum `hs ==> rest <> []` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `hs` >> simp[]) >>
  qpat_assum `alloc_limits_expr cenv (Call _ _ _ _)` mp_tac >>
  simp_tac (srw_ss()) [alloc_limits_expr_def,ext_call_alloc_ok_def] >>
  qpat_assum `xs = (if hs then FRONT rest else rest)` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `expr_type be = BaseT _` (pure_rewrite_tac o single) >>
  suspend "payload_capacity_bound"
QED

Resume create_size_exit_raw_mods[payload_fits]:
  rpt strip_tac >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      cenv.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
      gvs[Once well_typed_expr_def,lowered_value_type_def,expr_type_def] >>
      first_x_assum (drule_then SUBST1_TAC) >>
      fs[type_widens_to_def]) >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates,well_formed_type_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
  drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >> strip_tac >>
  gvs[ifexp_arg_type_fits_refl]
QED

Resume create_size_exit_raw_mods[payload_capacity_bound]:
  qpat_assum `xs <> []` (fn th => simp_tac bool_ss [LET_THM,th]) >>
  qpat_assum `~(LENGTH rest < if hs then 1 else 0)` (simp_tac bool_ss o single) >>
  simp_tac (srw_ss()) [bytelike_type_bound_def,vyperASTTheory.bound_length_def,Abbr `cap`,
    dimword_def,venomMemPropsTheory.dimindex_256] >>
  qpat_assum `bytelike_type_bound (lowered_value_type cenv be) <= kbound` mp_tac >>
  qpat_assum `abi_size_bound _ (TupleT (MAP (lowered_value_type cenv) xs)) <= _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> decide_tac
QED

Resume create_size_exit_raw_mods[payload_nonempty_join]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (map_every (fn p => qpat_assum p (pure_rewrite_tac o single o SYM))
         [`data = Var datavar`,`lenop = Var lenvar`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp_tac bool_ss [DECIDE ``!a b:num. SUC (a+b) = a+SUC b``] >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `k = rowC (LENGTH xs)` (pure_rewrite_tac o single o SYM) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "payload_row"
QED

Resume create_size_exit_raw_mods[payload_row]:
  gen_tac >> disch_tac >>
  `i <= LENGTH xs /\ SUC i <= LENGTH xs /\ 4 <= 4+2*i /\ 4+2*i < n /\ 4+2*i <= n /\
   SUC (4+2*i) < n /\ SUC (4+2*i) <= n /\ 4+2*SUC i <= n` by
    (qpat_assum `i < LENGTH xs` mp_tac >>
     qpat_assum `pidx+4+3 = n` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `pidx = 4+2*LENGTH xs` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[MULT_CLAUSES] >> decide_tac) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  map_every (fn p => qpat_assum p (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))))
    [`!i. i < LENGTH xs ==> C (SUC (4+2*i)) = _ /\ _`,
     `!i. i < LENGTH xs ==> compile_expr cenv _ _ _ = _ /\ _`,
     `!i. i < LENGTH xs ==> compile_expr (gas_shadow_env T cenv) _ (gas_shadow_expr _) _ = _ /\ _`] >>
  qpat_assum `!i. i <= LENGTH xs ==> C (4+2*i) = _`
    (fn th => map_every (fn j => qspec_then j mp_tac th >>
       (impl_tac >- first_assum ACCEPT_TAC) >> disch_then assume_tac) [`i`,`SUC i`]) >>
  qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
    (fn th => map_every (fn j => qspec_then j
      (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[PAIR_EQ])) th)
      [`SUC (4+2*i)`,`4+2*SUC i`]) >>
  qpat_assum `!i. i < n ==> FLAT (DROP i mark_rows) = _`
    (fn th => map_every (fn j => qspec_then j (drule_then assume_tac) th)
      [`4+2*i`,`SUC (4+2*i)`]) >>
  qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
    (qspec_then `SUC (4+2*i)` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i k. _ ==> ci_mono (C i) (C k)`
    (qspecl_then [`4`,`4+2*i`] (drule_all_then
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ci_mono_def]))) >>
  `SUC (SUC (4+2*i)) = 4+2*SUC i /\ 4+(2+2*i) = 4+2*SUC i` by
    (POP_ASSUM_LIST (K ALL_TAC) >> simp[MULT_CLAUSES] >> decide_tac) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [Abbr `rowC`,Abbr `rowObs`] >>
  suspend "payload_row_match"
QED

Resume create_size_exit_raw_mods[payload_row_match]:
  map_every (fn p => qpat_assum p (pure_rewrite_tac o single))
    [`C (4+2*i) = EL i cs`,`C (4+2*SUC i) = EL (SUC i) cs`,
     `4+(2+2*i) = 4+2*SUC i`] >>
  map_every (fn p => qpat_assum p (rule_assum_tac o ONCE_REWRITE_RULE o single))
    [`SUC (SUC (4+2*i)) = 4+2*SUC i`,`C (SUC (4+2*i)) = EL i mid`,
     `C (4+2*SUC i) = EL (SUC i) cs`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `C 4 = cd` (pure_rewrite_tac o single o SYM) >>
       qpat_assum `C (4+2*i) = EL i cs` (pure_rewrite_tac o single o SYM) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rename1 `FLAT (DROP (4+2*i) mark_rows) = _` >>
       map_every (fn p => qpat_assum p (pure_once_rewrite_tac o single))
         [`FLAT (DROP (4+2*i) mark_rows) = _`,`FLAT (DROP (SUC (4+2*i)) mark_rows) = _`] >>
       simp_tac bool_ss [GSYM APPEND_ASSOC] >> NO_TAC) >>
  suspend "payload_row_copy"
QED

Resume create_size_exit_raw_mods[payload_row_copy]:
  Cases_on `exprs_can_mutate cenv (DROP (SUC i) xs)`
  >- (qpat_assum `exprs_can_mutate cenv _` (simp_tac bool_ss o single) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `~exprs_can_mutate cenv _` (simp_tac bool_ss o single) >>
  disch_tac >>
  `expr_body_pre_mods mods cenv cx env (EL i xs) p0` by
    (irule create_call_operand_body_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `rest = xs ++ _` (pure_once_rewrite_tac o single) >>
     simp_tac bool_ss [MEM,MEM_APPEND] >> disj2_tac >> disj2_tac >> disj1_tac >>
     irule EL_MEM >> first_assum ACCEPT_TAC) >>
  `EL i mid = EL (SUC i) cs` by
    (irule raw_payload_snapshot_no_copy_mods >>
     qpat_assum `compile_expr cenv _ (EL i xs) (EL i cs) = _` (irule_at Any) >>
     qpat_assum `expr_body_pre_mods mods cenv cx env (EL i xs) p0` (irule_at Any) >>
     qexistsl_tac [`EL i vals`,`DROP (SUC i) xs`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `EL i mid = EL (SUC i) cs ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Resume create_size_exit_raw_mods[keywords]:
  `?sop. if hs then
     lower_value compile_expr cenv (expr_type (LAST rest)) (LAST rest) cq = (sop,sc) /\
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type (LAST rest))
       (gas_shadow_expr (LAST rest)) hq = (sop,hsc) /\
     expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (cq,sc,hq,hsc) /\
     create_expr_prefix cq sc (gas_explicit_sites ctx shadow_ctx) ctx func
       (Obs (SUC vp)) (M (SUC vp)) s /\
     s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts
     else sc = cq /\ hsc = hq /\ s = Obs (SUC vp) /\ M (SUC vp) = []` by suspend "salt_cut" >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
   ?source_vals source_ops source_state.
     eval_create_operands cx RawCreate hs rof (MAP expr_type (be::av::rest))
       (blueprint_literal_offset cx hs (be::av::rest)) source_vals source_state = (res,ee) /\
     dest_create_args RawCreate hs (create_operand_layout RawCreate hs source_vals) = SOME source_ops /\
     source_ops.co_code_src = BytecodeCodeSource code /\ source_ops.co_ctor_args = cvs /\
     create_arg_ctor_types RawCreate hs (MAP expr_type (be::av::rest)) = SOME (MAP expr_type xs) /\
     (!x w. not_fresh_at cv x /\ lookup_var x (Obs vp) = SOME w ==> lookup_var x (Obs (SUC vp)) = SOME w) /\
     cv.cs_next_var <= cq.cs_next_var /\
     (!x w. not_fresh_at cq x /\ lookup_var x (Obs (SUC vp)) = SOME w ==> lookup_var x s = SOME w)`
    suffices_by
      (disch_then (DISJ_CASES_THEN2 assume_tac
        (qx_choosel_then [`source_vals`,`source_ops`,`source_state`] (map_every assume_tac o CONJUNCTS)))
       >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "extent") >>
  irule create_raw_keywords_at_cuts_mods >> suspend "keywords_pre"
QED

Resume create_size_exit_raw_mods[salt_cut]:
  qpat_assum `case salte of NONE => _ | SOME _ => _` mp_tac >>
  qpat_assum `salte = _` (pure_rewrite_tac o single) >>
  Cases_on `hs` >> simp_tac bool_ss [optionTheory.option_case_def]
  >- (disch_then (qx_choose_then `sop` (map_every assume_tac o CONJUNCTS)) >>
      qexists_tac `sop` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `cq = sc ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC))
QED

Resume create_size_exit_raw_mods[keywords_pre]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`DF`,`Gval`,`H`,`amount`,`ann`,`av`,`cenv`,`sc`,`ctx`,`d`,`df`,`be`,
    `es`,`env`,`exps`,`func`,`ks`,`lo`,`M vp`,`M (SUC vp)`,`pval`,`LAST rest`,`sop`,
    `hp`,`hq`,`hsc`,`shadow_ctx`,`shadow_func`,`src`,`st0`,`tail`,`tnval`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `rest = xs ++ _` (fn th => simp_tac bool_ss [SimpLHS,Once th])
QED

Resume create_size_exit_raw_mods[extent]:
  `eval_operand len (Obs vp) = SOME (n2w (LENGTH code + LENGTH payload)) /\
   (!x. len = Var x ==> not_fresh_at cv x)` by suspend "payload_size" >>
  `eval_operand len s = SOME (n2w (LENGTH code + LENGTH payload))` by suspend "size_frame" >>
  `2 * max_code_size < LENGTH code + LENGTH payload` by
    (`w = n2w (LENGTH code + LENGTH payload)` by
       (qpat_assum `eval_operand len s = SOME w` (fn h =>
          qpat_assum `eval_operand len s = SOME (n2w _)`
            (ACCEPT_TAC o SIMP_RULE bool_ss [h,optionTheory.SOME_11]))) >>
     qpat_assum `2 * max_code_size < w2n w` mp_tac >>
     qpat_assum `w = n2w _` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[w2n_n2w] >> disch_tac >>
     irule LESS_LESS_EQ_TRANS >>
     qexists_tac `(LENGTH code + LENGTH payload) MOD dimword (:256)` >>
     simp[MOD_LESS_EQ]) >>
  disj1_tac >>
  `eval_create_operands cx RawCreate hs rof (MAP expr_type (be::av::rest))
    (blueprint_literal_offset cx hs (be::av::rest)) source_vals source_state =
      (INR (Error (RuntimeError "create initcode too large")),source_state)` by
    (irule raw_operands_size_reject >>
     qexistsl_tac [`code`,`MAP expr_type xs`,`source_ops`,`payload`,
       `create_operand_layout RawCreate hs source_vals`] >>
     rpt conj_tac >> TRY ((REFL_TAC ORELSE first_assum ACCEPT_TAC) >> NO_TAC) >>
     qpat_assum `source_ops.co_ctor_args = cvs` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (res,ee)`
    (fn h => qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (INR _,_)`
      (mp_tac o PURE_REWRITE_RULE [h])) >> simp_tac bool_ss [PAIR_EQ]
QED

Resume create_size_exit_raw_mods[payload_size]:
  Cases_on `xs = []`
  >- (qpat_assum `xs = []` (fn th => qpat_assum `if xs = [] then payload = [] /\ _ else _`
        (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [th])) >>
      map_every (fn p => qpat_assum p (pure_rewrite_tac o single))
        [`payload = []`,`len = lenop`,`cv = rowC 0`,`Obs vp = rowObs 0`,
         `rowC 0 = cd`,`rowObs 0 = Obs 4`,`lenop = Var lenvar`] >>
      simp_tac bool_ss [LENGTH,ADD_CLAUSES,eval_operand_def,operand_11] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `xs <> []` (fn th => qpat_assum `if xs = [] then payload = [] /\ _ else _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [th])) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_size_exit_raw_mods[size_frame]:
  `s.vs_labels = (Obs vp).vs_labels` by
    (map_every (fn p => qpat_assum p
      (mp_then (Pos hd) assume_tac createSizePrefixReplayTheory.create_prefix_labels))
      [`create_expr_prefix cv cq _ _ _ (Obs vp) _ _`,
       `create_expr_prefix cq sc _ _ _ (Obs (SUC vp)) _ s`] >>
     qpat_assum `s.vs_labels = (Obs (SUC vp)).vs_labels` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `eval_operand len (Obs vp) = SOME (n2w _)` mp_tac >>
  Cases_on `len` >> simp_tac bool_ss [eval_operand_def] >>
  TRY (qpat_assum `s.vs_labels = (Obs vp).vs_labels` (pure_rewrite_tac o single) >>
       simp_tac bool_ss [] >> NO_TAC) >>
  suspend "size_var"
QED

Resume create_size_exit_raw_mods[size_var]:
  disch_tac >> rename1 `lookup_var z s = SOME _` >>
  qpat_assum `!x. Var z = Var x ==> not_fresh_at cv x`
    (qspec_then `z` (assume_tac o SIMP_RULE bool_ss [])) >>
  qpat_assum `!x w. not_fresh_at cv x /\ lookup_var x (Obs vp) = SOME w ==> _`
    (drule_all_then assume_tac) >>
  `not_fresh_at cq z` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cv` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x w. not_fresh_at cq x /\ lookup_var x (Obs (SUC vp)) = SOME w ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Finalise create_size_exit_raw_mods
