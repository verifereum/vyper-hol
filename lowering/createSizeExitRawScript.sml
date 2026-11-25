Theory createSizeExitRaw
Ancestors
  bodySingletonCallSupport[qualified,ignore_grammar]
  exprSimFullBundleProps fragExec gasExplicitSites s1PrefixDefs venomExecSemantics venomInst
  venomState vyperCreate vyperState relation list words pair bodyFullIfExpReach
  builtinCreate arithmetic createSizeDispatch exprLowering vfmConstants externalEntryShape
  compileEnv createSizeItinerary exprLoweringProps exprBodyPreProps rich_list
  exprSimHypsDefs vyperTypeSystem bodyPtrDefs loweringPosts context createSizeRawSource
  bodyInvCodeProps vyperAST allocLimits vyperTypeCallGraph exprSimSend integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate loweringStateRelDefs
  dallocaBlueprintArgs createSizeRawPairedCode createSizeRawExtent createOperandSizeReject
  createExprSizeExitDefs createSizePrefixCuts createSizeRawReplay createSizeRawDataEntry
  createSizeRawObserved createSizeRawPayloadReplay createSizeOperandPre

Theorem raw_itinerary_index[local]:
  !cuts sa sc. create_itinerary_code sa cuts sc ==>
    (!i. i <= LENGTH cuts ==> ci_mono sa (EL i (sa::cuts)) /\
                              ci_mono (EL i (sa::cuts)) sc) /\
    (!i. i < LENGTH cuts ==> ci_mono (EL i (sa::cuts)) (EL (SUC i) (sa::cuts)))
Proof
  rpt gen_tac >> strip_tac >>
  drule create_itinerary_index_mono >> strip_tac >>
  drule create_itinerary_code_relations >> strip_tac >>
  `EL (LENGTH cuts) (sa::cuts) = sc` by
    (qspec_then `sa::cuts` mp_tac LAST_EL >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> conj_tac
      >- (qpat_assum `!i j. _ ==> ci_mono _ _`
            (qspecl_then [`0`,`i`] mp_tac) >>
          impl_tac >- simp[] >>
          disch_then (ACCEPT_TAC o REWRITE_RULE [EL,HD])) >>
      qpat_assum `!i j. _ ==> ci_mono _ _`
        (qspecl_then [`i`,`LENGTH cuts`] mp_tac) >>
      impl_tac >- simp[] >>
      qpat_assum `EL (LENGTH cuts) (sa::cuts) = sc`
        (PURE_REWRITE_TAC o single) >>
      disch_then ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!i j. _ ==> ci_mono _ _`
    (qspecl_then [`i`,`SUC i`] mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then ACCEPT_TAC
QED

Theorem raw_payload_snapshot_no_copy[local]:
  compile_expr ce (expr_type e) e ca = (v,cm) /\
    expr_body_pre ce cx env e p /\
    ~exprs_can_mutate ce rest /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_snapshot_vv ce (exprs_can_mutate ce rest)
      (ext_call_arg_value (lowered_value_type ce e) v) cm = (saved,cn) ==>
    cm = cn
Proof
  strip_tac >>
  drule_all bodyFullExtCallPosAggregateTheory.extcall_operand_snapshot_type >>
  strip_tac >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,comp_return_def,pairTheory.PAIR_EQ]
QED

Theorem raw_source_extent_reject[local]:
  w2n (w:bytes32) <= LENGTH (code:word8 list) + LENGTH (payload:word8 list) /\
    2 * max_code_size < w2n w /\
    dest_create_args RawCreate hs (create_operand_layout RawCreate hs vs) = SOME ops /\
    create_arg_ctor_types RawCreate hs tys = SOME ct /\
    ops.co_code_src = BytecodeCodeSource code /\
    encode_create_ctor_args (get_tenv cx) ct ops.co_ctor_args = SOME payload ==>
    eval_create_operands cx RawCreate hs rof tys lit vs st =
      (INR (Error (RuntimeError "create initcode too large")),st)
Proof
  strip_tac >>
    `2 * max_code_size < LENGTH code + LENGTH payload` by decide_tac >>
    irule raw_operands_size_reject >>
    qexistsl_tac [`code`, `ct`, `ops`, `payload`, `create_operand_layout RawCreate hs vs`] >>
    simp[]
QED

Theorem create_size_exit_raw:
  !cx ann hs rof ks args df.
    EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs args) ==>
    create_expr_size_exit cx (Call ann (CreateTarget RawCreate hs rof ks) args df)
Proof
  rewrite_tac[create_expr_size_exit_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  `?result. compile_create_call compile_expr cenv RawCreate hs rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv RawCreate hs rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >> strip_tac >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [create_call_itinerary_def, create_kind_case_def, create_raw_itinerary_def]) >>
  rename1 `compile_expr cenv (expr_type be) be sa = (bcvv,a)` >>
  rename1 `compile_create_snapshot cenv bcvv _ a = (snap,b)` >>
  rename1 `emit_op MLOAD [snap] b = (lenop,c)` >>
  rename1 `emit_op ADD [snap; Lit 32w] c = (data,cd)` >>
  rename1 `lower_value compile_expr cenv (expr_type av) av cv = (amount,cq)` >>
  rename1 `create_itinerary_salt cenv _ cq salt_op cf` >>
  rename1 `create_size_dispatch_tail rof sc sd created bufop sizeop amount salt_op result sb` >>
  `sc = cf` by
    (qpat_assum `LAST (sa::cuts) = sc` mp_tac >>
     qpat_assum `cuts = _` (fn th => PURE_REWRITE_TAC[th]) >>
     `sa::([a;b;c;cd] ++ prep ++ [cq;cf]) = ([sa;a;b;c;cd] ++ prep) ++ [cq;cf]` by
       simp[APPEND_ASSOC] >>
     pop_assum (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `sc = cf` (SUBST_ALL_TAC o SYM) >>
  `inst.inst_id = sc.cs_next_id /\ inst.inst_opcode <> PHI /\ eval_operand sizeop s = SOME w` by
    (Cases_on `salt_op` >> fs[mk_inst_def] >> metis_tac[]) >>
  `ctor_segment_fetch func s = SOME inst` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (pure_rewrite_tac o (fn h => [ctor_segment_fetch_def,h])) >>
     pure_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  suspend "bands"
QED

Resume create_size_exit_raw[bands]:
  qabbrev_tac `xs = if hs then FRONT rest else rest` >>
  qabbrev_tac `salte = if hs then SOME (LAST rest) else NONE` >>
  qabbrev_tac `cap = bytelike_type_bound (lowered_value_type cenv be) +
       abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs))` >>
  qabbrev_tac `rawcomp = \i. EL i (sa::cuts)` >>
  qabbrev_tac `rawobs = \i. EL i states` >>
  qabbrev_tac `Ms = \i. EL i chunks'` >>
  qabbrev_tac `ncut = LENGTH cuts` >>
  qabbrev_tac `vp = 4 + LENGTH prep` >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  `?opc ops. emit_op opc ops sc = (created,sd) /\ compile_check_create_result created rof sd = (result,sb)` by
    (Cases_on `salt_op` >> fs[create_size_dispatch_tail_def] >> metis_tac[]) >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     metis_tac[ci_mono_def,ci_mono_emit_op,externalEntryShapeTheory.compile_check_create_result_labels,pairTheory.SND]) >>
  drule raw_itinerary_index >> strip_tac >>
  `!i. i < ncut ==> (rawcomp i).cs_next_id <= (rawcomp (SUC i)).cs_next_id /\
    fn_has_code (rawcomp i) (rawcomp (SUC i)) func /\
    create_expr_prefix (rawcomp i) (rawcomp (SUC i)) explicit ctx func (rawobs i) (Ms i) (rawobs (SUC i))` by
    (qpat_x_assum `cuts = _` kall_tac >>
     simp[Abbr `rawcomp`,Abbr `rawobs`,Abbr `Ms`,Abbr `ncut`,Abbr `explicit`] >> rpt strip_tac >>
     `SUC i <= LENGTH cuts /\ i <= LENGTH cuts` by decide_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> ci_mono _ _` (qspec_then `i` (drule_then assume_tac)) >>
     TRY (fs[ci_mono_def] >> NO_TAC) >>
     TRY (qpat_assum `!i. i < LENGTH cuts ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `i` mp_tac) >> simp[] >> NO_TAC) >>
     qpat_assum `!i. i <= LENGTH cuts ==> _ /\ _` (fn th =>
       map_every (fn j => qspec_then j mp_tac th) [`i`,`SUC i`]) >>
     simp_tac bool_ss [EL_restricted,DECIDE ``SUC i <= n <=> i < n``] >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     `cs_extends sa (EL i (sa::cuts)) /\ cs_extends (EL i (sa::cuts)) (EL i cuts) /\
      cs_extends (EL i cuts) sc` by fs[ci_mono_def] >>
     `cs_extends (EL i cuts) sb` by metis_tac[cs_extends_trans] >>
     irule fn_has_code_mid >>
     qpat_assum `fn_has_code sa sb func` (irule_at Any) >> simp[]) >>
  mp_tac (Q.INST [`C` |-> `rawcomp`, `Obs` |-> `rawobs`, `M` |-> `Ms`, `n` |-> `ncut`,
    `vpos` |-> `vp`, `chunks0` |-> `chunks'`, `fn` |-> `func`, `bad` |-> `s`,
    `dispatch` |-> `inst`, `d` |-> `cd`, `len` |-> `lenop`, `size_op` |-> `sizeop`,
    `cenv` |-> `cenv`] (SPEC_ALL create_raw_observed_bands)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[markerTheory.Abbrev_def])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "pair"
QED

Resume create_size_exit_raw[pair]:
  qpat_x_assum `args = be::av::rest` SUBST_ALL_TAC >>
  qpat_x_assum `if xs = [] then _ else _`
    (fn th =>
       let val [empty,nonempty] = CONJUNCTS (PURE_REWRITE_RULE [COND_EXPAND_IMP] th)
       in assume_tac empty >>
          strip_assume_tac (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) nonempty)
       end) >>
  rename1 `xs <> [] ==> _ /\ _ /\ _ /\ _ /\ _ /\
    compile_abi_encode_values_to_buf _ _ _ _ = (_,en) /\ _` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `be`, `v` |-> `av`, `dflt` |-> `df`,
    `hsa` |-> `shadow_sa`, `hsb` |-> `shadow_sb`, `parent_vv` |-> `vv`, `sctx` |-> `shadow_ctx`,
    `fn` |-> `func`, `sfn` |-> `shadow_func`, `vv` |-> `bcvv`, `d` |-> `cd`,
    `p` |-> `cv`, `q` |-> `cq`, `value` |-> `amount`, `salt` |-> `salt_op`,
    `vvs` |-> `vs`, `j` |-> `ca`, `m` |-> `cb`, `n` |-> `cc`, `o'` |-> `en`]
      (SPEC_ALL create_raw_paired_operand_code)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    TRY (IF_CASES_TAC >> fs[] >> NO_TAC) >> simp[markerTheory.Abbrev_def])) >>
  disch_then (qx_choose_then `ha` (qx_choose_then `hp` (qx_choose_then `hq` (qx_choose_then `hsc`
    (map_every assume_tac o CONJUNCTS))))) >>
  suspend "header"
QED

Resume create_size_exit_raw[header]:
  `ncut = SUC (SUC vp)` by
    (simp[Abbr `ncut`,Abbr `vp`] >> decide_tac) >>
  `1 <= ncut /\ 2 <= ncut /\ 3 <= ncut /\ 4 <= ncut /\ vp <= ncut /\ SUC vp <= ncut` by
    (simp[Abbr `vp`] >> decide_tac) >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _`
    (fn th => map_every (fn i =>
      qspec_then i mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]))
      [`1`,`2`,`3`,`4`,`vp`,`SUC vp`]) >>
  qpat_assum `Abbrev (explicit = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rename1 `return_buf_frame dep' cenv sa s0` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `be`, `v` |-> `av`, `dep` |-> `dep'`,
    `parent_vv` |-> `vv`, `vv` |-> `bcvv`, `shadow_a` |-> `ha`, `d` |-> `cd`, `len` |-> `lenop`,
    `u` |-> `rawobs 1`, `z` |-> `rawobs 2`, `l` |-> `rawobs 3`, `r` |-> `rawobs 4`,
    `ms` |-> `Ms 0`, `msS` |-> `Ms 1`, `msL` |-> `Ms 2`, `msD` |-> `Ms 3`,
    `later` |-> `FLAT (DROP 4 chunks')`] (SPEC_ALL create_raw_data_entry_at_cuts)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    pure_asm_rewrite_tac [APPEND_ASSOC] >> simp_tac bool_ss [] >>
    qpat_assum `marks = _ ++ FLAT (DROP 4 chunks')` (fn h =>
      qpat_assum `eval_expr _ (Call _ _ _ _) _ = (res,ee)`
        (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_ASSOC] o SUBS [h])))) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `p0` strip_assume_tac))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "payload"
QED

Resume create_size_exit_raw[payload]:
  `xs ++ (if hs then [LAST rest] else []) = rest` by
    (Cases_on `hs` >> simp_tac (srw_ss()) [Abbr `xs`] >>
     irule APPEND_FRONT_LAST >>
     qpat_assum `T ==> rest <> []` (ACCEPT_TAC o SIMP_RULE bool_ss [])) >>
  qpat_assum `Abbrev (xs = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >> drule_all bodyFullIfExpReachTheory.body_inv_no_phi >> simp[]) >>
  rename1 `xs <> [] ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ pidx = 4 + 2 * LENGTH xs /\ _` >>
  qpat_x_assum `xs <> [] ==> fn_has_code cd k func /\ _`
    (fn th =>
       let
         val split = CONV_RULE (REWR_CONV IMP_CONJ_THM)
         fun distribute h =
           case total split h of
             NONE => strip_assume_tac (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) h)
           | SOME pair => assume_tac (CONJUNCT1 pair) >> distribute (CONJUNCT2 pair)
       in distribute th end) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `shctx` |-> `shadow_ctx`, `shfunc` |-> `shadow_func`,
    `e` |-> `be`, `entry` |-> `es`, `args` |-> `xs`, `saltE` |-> `LAST rest`, `out` |-> `ee`,
    `tys` |-> `MAP expr_type (be::av::rest)`, `lit` |-> `blueprint_literal_offset cx hs (be::av::rest)`,
    `d` |-> `dep'`, `G0` |-> `Gr`, `tn0` |-> `tnr`, `lvar` |-> `lenvar`, `src` |-> `datavar`,
    `C` |-> `(\i:num. rawcomp (4+2*i))`, `St` |-> `(\i:num. rawobs (4+2*i))`,
    `R` |-> `(\i:num. FLAT (DROP (4+2*i) chunks'))`, `Chunk` |-> `(\i:num. Ms (4+2*i))`,
    `Snap` |-> `(\i. Ms (SUC (4+2*i)))`, `Mid` |-> `(\i. rawobs (SUC (4+2*i)))`,
    `V` |-> `(\i. EL i vs)`, `M` |-> `(\i. EL i mid)`, `Sh` |-> `(\i. EL i hcs)`, `SM` |-> `(\i. EL i hmid)`,
    `uval` |-> `rawobs (vp:num)`, `size_op` |-> `sizeop`, `kwmarks` |-> `Ms (vp:num) ++ Ms (SUC vp)`,
    `svs` |-> `vals`, `se` |-> `k`, `s` |-> `rawobs (pidx:num)`, `capacity` |-> `cap`,
    `prefix_bound` |-> `bytelike_type_bound (lowered_value_type cenv be)`,
    `p` |-> `n2w (buffer_allocation_base (rawobs 1) a.cs_next_id + 32)`,
    `a` |-> `ca`, `b` |-> `cb`, `st` |-> `cc`, `dst_op` |-> `dst`,
    `su` |-> `rawobs ((pidx:num)+1)`, `sv` |-> `rawobs ((pidx:num)+2)`,
    `u` |-> `rawobs ((pidx:num)+3)`, `t` |-> `rawobs ((pidx:num)+4)`,
    `am` |-> `Ms (pidx:num)`, `bm` |-> `Ms ((pidx:num)+1)`, `cm` |-> `Ms ((pidx:num)+2)`,
    `encmarks` |-> `Ms ((pidx:num)+3)`, `dm` |-> `Ms ((pidx:num)+4)`,
    `c` |-> `(\i:num. rawcomp (pidx+4+i))`, `r` |-> `(\i:num. rawobs (pidx+4+i))`,
    `chunk` |-> `(\i:num. Ms (pidx+4+i))`, `n` |-> `3`, `bad` |-> `s`, `bbad` |-> `bb`, `dispatch` |-> `inst`]
    (SPEC_ALL create_raw_payload_at_cuts)) >>
  BETA_TAC >>
  (impl_tac >- suspend "payload_pre") >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `cvs` (qx_choose_then `payload` (qx_choose_then `pval`
      (qx_choose_then `Gval` (qx_choose_then `tnval` (map_every assume_tac o CONJUNCTS)))))))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "keywords"
QED

Resume create_size_exit_raw[payload_pre]:
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `(if hs then FRONT rest else rest) = xs` (fn h =>
    qpat_assum `bind (eval_exprs cx _) _ p0 = _` (ACCEPT_TAC o SUBS [h])) >> NO_TAC) >>
  Cases_on `xs = []`
  >- (qpat_assum `xs = [] ==> prep = [] /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      `vp = 4` by simp[Abbr `vp`] >>
      pure_asm_rewrite_tac [COND_CLAUSES,ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >>
      qpat_assum `vp = 4` (fn h =>
        qpat_assum `FLAT (DROP vp chunks') = _` (ACCEPT_TAC o SUBS [h]))) >>
  qpat_assum `xs <> []` (simp_tac bool_ss o single) >>
  suspend "payload_nonempty"
QED

Resume create_size_exit_raw[payload_nonempty]:
  qpat_x_assum `xs <> [] ==> compile_create_ctor_args _ _ _ _ = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt (qpat_x_assum `xs <> [] ==> fn_has_code _ _ _` (drule_then assume_tac)) >>
  qpat_x_assum `xs <> [] ==> LENGTH hcs = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `create_itinerary_ctor_rows`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [create_itinerary_ctor_rows_def]) >>
  `pidx+4+3 = ncut /\ SUC (pidx+4) = vp /\ pidx+4 <= ncut` by decide_tac >>
  `!i. i < LENGTH xs ==> SUC (4+2*i) < ncut /\ 4+2*i < ncut /\ 4+2*SUC i <= ncut` by decide_tac >>
  `!j. 4 <= j /\ j <= ncut ==> ci_mono cd (rawcomp j)` by suspend "row_monotonic" >>
  `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs)`
    by suspend "raw_calls" >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv cenv cx env p0` mp_tac >>
     simp_tac (srw_ss()) [expr_sim_inv_split_def,expr_sim_inv_mods_def]) >>
  `cap < dimword (:256)` by suspend "raw_capacity" >>
  `w2n (n2w (LENGTH code):bytes32) <= LENGTH code` by simp[w2n_n2w,MOD_LESS_EQ] >>
  `ptr_covers Gr tnr datavar (rawobs 4) (w2n (n2w (LENGTH code):bytes32))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `LENGTH code` >> simp[]) >>
  `(rawobs (pidx+4)).vs_current_bb = en.cs_current_bb /\
   (rawobs (pidx+4)).vs_inst_idx = LENGTH en.cs_current_insts` by
    (qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _` (qspec_then `pidx+4` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `create_expr_prefix en cv explicit ctx func (rawobs (pidx+4)) (Ms (pidx+4)) (rawobs vp)` by
    (qpat_assum `!i. i < ncut ==> _ /\ fn_has_code _ _ _ /\ _` (qspec_then `pidx+4` mp_tac) >>
     (impl_tac >- decide_tac) >>
     qpat_assum `SUC (pidx+4) = vp` (fn h =>
       qpat_assum `rawcomp (pidx+4) = en` (fn e =>
         qpat_assum `rawcomp vp = cv` (fn v =>
           disch_then (ACCEPT_TAC o SIMP_RULE bool_ss [h,e,v] o CONJUNCT2 o CONJUNCT2))))) >>
  `FLAT (DROP pidx chunks') = Ms pidx ++ Ms (pidx+1) ++ Ms (pidx+2) ++ Ms (pidx+3) ++
     Ms (pidx+4) ++ (Ms vp ++ Ms (SUC vp))` by suspend "raw_payload_marks" >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES,pairTheory.PAIR_EQ] >> simp_tac bool_ss [] >> NO_TAC) >>
  REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES] >>
  TRY (qpat_assum `pidx = (4:num)+2*LENGTH xs` (SUBST1_TAC o SYM) >>
       pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `rawcomp (pidx:num) = k` (SUBST1_TAC) >>
       pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (simp_tac bool_ss [Abbr `cap`] >> NO_TAC) >>
  TRY (qpat_assum `pidx+4+3 = (ncut:num)` SUBST1_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rename1 `_ + _ <= (rawobs 4).vs_alloca_next` >> decide_tac >> NO_TAC) >>
  TRY (qpat_assum `data = Var datavar` (SUBST1_TAC o SYM) >>
       qpat_assum `lenop = Var lenvar` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `lenop = Var lenvar` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "payload_row"
QED

Resume create_size_exit_raw[row_monotonic]:
  Induct >- simp[] >> strip_tac >> Cases_on `j = 3`
  >- (qpat_x_assum `j = 3` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [ci_mono_refl] >>
      qpat_assum `rawcomp 4 = cd` (simp_tac (srw_ss()) o (fn th => [th,ci_mono_refl]))) >>
  `4 <= j /\ j < ncut /\ j <= ncut` by decide_tac >>
  `ci_mono cd (rawcomp j)` by (first_x_assum irule >> first_assum ACCEPT_TAC ORELSE simp[]) >>
  `ci_mono (rawcomp j) (rawcomp (SUC j))` by
    (simp_tac (srw_ss()) [Abbr `rawcomp`] >>
     qpat_assum `!i. i < LENGTH cuts ==> ci_mono _ _` (qspec_then `j` mp_tac) >>
     qpat_assum `Abbrev (ncut = LENGTH cuts)`
       (fn h => simp_tac bool_ss [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] h)]) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp_tac (srw_ss()) []) >>
  irule ci_mono_trans >> qexists_tac `rawcomp j` >> simp[]
QED

Resume create_size_exit_raw[raw_calls]:
  drule_all_then assume_tac bodySingletonCallSupportTheory.body_inv_expr_pre_calls >>
  simp[EVERY_MEM] >> qx_gen_tac `call` >> disch_tac >>
  `MEM call (int_calls_expr (Call ann (CreateTarget RawCreate hs rof ks) (be::av::rest) df))` by
    (`!ys zs. int_calls_exprs (ys ++ zs) = int_calls_exprs ys ++ int_calls_exprs zs` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[int_calls_expr_def]) >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >>
     simp[int_calls_expr_def]) >>
  qpat_assum `EVERY _ (int_calls_expr (Call _ _ _ _))`
    (qspec_then `call` mp_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
  simp[]
QED

Resume create_size_exit_raw[raw_capacity]:
  qpat_assum `expr_body_pre cenv cx env (Call _ _ _ _) es`
    (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
  drule create_raw_first_type >> strip_tac >>
  `!e. MEM e (be::av::rest) ==> expr_body_pre cenv cx env e es` by
    (gen_tac >> disch_tac >> drule_all create_call_operand_body_pre >> simp[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e es) xs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     first_x_assum irule >> simp[] >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >> simp[]) >>
  drule create_ctor_args_abi_bound >> strip_tac >>
  `bytelike_type_bound (lowered_value_type cenv be) <= n` by
    (irule raw_create_bytecode_bound >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cx`,`env`,`es`] >> simp[]) >>
  `~(LENGTH rest < if hs then 1 else 0)` by
    (Cases_on `hs` >> simp[] >> qpat_assum `T ==> rest <> []` (mp_tac) >> simp[]) >>
  qpat_assum `alloc_limits_expr cenv (Call _ _ _ _)` mp_tac >>
  simp_tac (srw_ss()) [alloc_limits_expr_def,ext_call_alloc_ok_def] >>
  qpat_assum `(if hs then FRONT rest else rest) = xs` (pure_rewrite_tac o single) >>
  qpat_assum `xs <> []` (fn h => simp_tac bool_ss [LET_THM,h]) >>
  qpat_assum `expr_type be = _` (pure_rewrite_tac o single) >>
  simp_tac (srw_ss()) [vyperTypeSystemTheory.bytelike_type_bound_def,vyperASTTheory.bound_length_def] >>
  (strip_tac >> simp[Abbr `cap`,dimword_def,venomMemPropsTheory.dimindex_256] >> decide_tac)
QED

Resume create_size_exit_raw[raw_payload_marks]:
  `pidx < ncut /\ pidx+1 < ncut /\ pidx+2 < ncut /\ pidx+3 < ncut /\ pidx+4 < ncut` by decide_tac >>
  qpat_assum `!i. i < ncut ==> FLAT (DROP i chunks') = _`
    (fn th => map_every (fn i => qspec_then i mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`pidx`,`pidx+1`,`pidx+2`,`pidx+3`,`pidx+4`]) >>
  qpat_assum `SUC (pidx+4) = vp` (fn h =>
    qpat_assum `FLAT (DROP (pidx+4) chunks') = _` (assume_tac o SUBS [h])) >>
  `FLAT (DROP ncut chunks') = []` by
    (qpat_assum `LENGTH chunks' = ncut` (SUBST1_TAC o SYM) >> simp[DROP_LENGTH_NIL]) >>
  simp[DECIDE ``SUC n = n+1``,ADD_ASSOC,APPEND_ASSOC] >>
  `2 * LENGTH xs + 11 = ncut` by decide_tac >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Resume create_size_exit_raw[payload_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH xs ==> SUC (4+2*i) < ncut /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `4 <= 4+2*i /\ 4+2*i <= ncut /\ SUC i <= LENGTH xs /\ i <= LENGTH xs /\
   SUC (SUC (4+2*i)) = 4+2*SUC i /\ SUC (4+2*i) <= ncut` by decide_tac >>
  qpat_assum `!i. i <= LENGTH xs ==> rawcomp _ = EL i cs`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`i`,`SUC i`]) >>
  rpt (qpat_x_assum `!i. i < LENGTH xs ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!i. i < LENGTH xs ==> rawcomp _ = EL i mid /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]))
      [`SUC (4+2*i)`,`4+2*SUC i`]) >>
  qpat_assum `!j. 4 <= j /\ j <= ncut ==> ci_mono _ _`
    (qspec_then `4+2*i` mp_tac) >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (assume_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `!i. i < ncut ==> FLAT (DROP i chunks') = _`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`4+2*i`,`SUC (4+2*i)`]) >>
  qpat_assum `!i. i < ncut ==> _ /\ fn_has_code _ _ _ /\ _`
    (qspec_then `SUC (4+2*i)` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `4+(2+2*i) = 4+2*SUC i` by decide_tac >>
  pop_assum SUBST1_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [APPEND_ASSOC] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `rawcomp 4 = cd` SUBST1_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "payload_row_left"
QED

Resume create_size_exit_raw[payload_row_left]:
  Cases_on `exprs_can_mutate cenv (DROP (SUC i) xs)`
  >- (qpat_assum `exprs_can_mutate cenv (DROP (SUC i) xs)` (simp_tac bool_ss o single) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
      qpat_assum `SUC (SUC (4+2*i)) = (4:num)+2*SUC i` (fn index =>
        qpat_assum `rawcomp (SUC (4+2*i)) = EL i mid` (fn from =>
          qpat_assum `fn_has_code (rawcomp (SUC (4+2*i))) _ func`
            (ACCEPT_TAC o PURE_REWRITE_RULE [index,from])))) >>
  qpat_assum `~exprs_can_mutate cenv (DROP (SUC i) xs)` (simp_tac bool_ss o single) >>
  disch_tac >>
  `expr_body_pre cenv cx env (EL i xs) p0` by
    (irule create_call_operand_body_pre >> (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >> simp[EL_MEM]) >>
  `EL i mid = EL (SUC i) cs` by
    (drule_all raw_payload_snapshot_no_copy >> simp_tac bool_ss []) >>
  qpat_assum `EL i mid = EL (SUC i) cs ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Resume create_size_exit_raw[keywords]:
  qabbrev_tac `opt_salt = (salt_op:operand option)` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `shctx` |-> `shadow_ctx`,
    `fnc` |-> `func`, `shfnc` |-> `shadow_func`, `d` |-> `dep'`,
    `e` |-> `be`, `entry` |-> `es`, `args` |-> `be::av::rest`, `salt` |-> `LAST rest`,
    `p` |-> `pval`, `G` |-> `Gval`, `tn` |-> `tnval`,
    `ca` |-> `cv`, `cm` |-> `cq`, `cn` |-> `sc`,
    `sca` |-> `hp`, `scm` |-> `hq`, `scn` |-> `hsc`,
    `amount_op` |-> `amount`, `salt_op` |-> `THE (opt_salt:operand option)`,
    `u` |-> `rawobs (vp:num)`, `m` |-> `rawobs (SUC vp)`, `n` |-> `s`,
    `ma` |-> `Ms (vp:num)`, `ms` |-> `Ms (SUC vp)`, `out` |-> `ee`]
    (SPEC_ALL create_raw_keywords_at_cuts)) >>
  (impl_tac >- suspend "keywords_pre") >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `source_vals` (qx_choose_then `source_ops` (qx_choose_then `source_state`
      (map_every assume_tac o CONJUNCTS)))))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "extent"
QED

Resume create_size_exit_raw[keywords_pre]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  suspend "keywords_left"
QED

Resume create_size_exit_raw[keywords_left]:
  qpat_assum `case salte of NONE => _ | SOME _ => _` mp_tac >>
  Cases_on `hs` >> simp_tac (srw_ss()) [Abbr `salte`,Abbr `opt_salt`] >>
  strip_tac >> TRY (qpat_assum `cq = sc ==> _` (drule_then strip_assume_tac)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (sym_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  pure_asm_rewrite_tac [] >> simp_tac (srw_ss()) []
QED


Resume create_size_exit_raw[extent]:
  `w2n w <= LENGTH (code:word8 list) + LENGTH (payload:word8 list)` by suspend "extent_bound" >>
  disj1_tac >>
  `eval_create_operands cx RawCreate hs rof (MAP expr_type (be::av::rest))
     (blueprint_literal_offset cx hs (be::av::rest)) source_vals source_state =
     (INR (Error (RuntimeError "create initcode too large")),source_state)` by
    (irule raw_source_extent_reject >>
     qexistsl_tac [`code`, `MAP expr_type xs`, `source_ops`, `payload`, `w`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (res,ee)`
    (fn h => qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (INR _,_)`
      (mp_tac o PURE_REWRITE_RULE [h])) >> simp_tac (srw_ss()) []
QED

Resume create_size_exit_raw[extent_bound]:
  irule (INST_TYPE [``:β`` |-> ``:expr``] create_raw_pre_dispatch_extent) >>
  qexistsl_tac [`cd`,`b`,`c`,`cq`,`xs`,`ctx`,`cv`,`data`,`explicit`,`func`,
                `rawobs 3`,`lenop`,`Ms 3`,`rawobs 4`,`s`,`sizeop`,`snap`,
                `rawobs vp`,`rawobs (SUC vp)`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  Cases_on `xs = []`
  >- (qpat_assum `xs = [] ==> prep = [] /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `xs = []` (fn h =>
        qpat_assum `if xs = [] then payload = [] /\ _ else _`
          (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
      pure_asm_rewrite_tac [COND_CLAUSES,ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss []) >>
  suspend "extent_nonempty"
QED

Resume create_size_exit_raw[extent_nonempty]:
  qpat_assum `xs <> [] ==> compile_create_ctor_args _ _ _ _ = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `xs <> [] ==> fn_has_code en cv func` (drule_then assume_tac) >>
  qpat_assum `xs <> []` (fn h =>
    qpat_assum `if xs = [] then payload = [] /\ _ else _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
  qpat_assum `xs <> []` (simp_tac bool_ss o single) >>
  qexistsl_tac [`en`,`rawobs (pidx+4)`,`alen`,`Ms (pidx+4)`] >>
  `pidx+4 <= ncut` by decide_tac >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _` (qspec_then `pidx+4` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[pairTheory.PAIR_EQ]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >> NO_TAC) >>
  qpat_assum `pidx = (4:num)+2*LENGTH xs` (SUBST1_TAC o SYM) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `rawcomp 4 = cd` (fn h =>
    qpat_assum `!x v. not_fresh_at (rawcomp (4+2*0)) x /\ _ ==> lookup_var x (rawobs (pidx+4)) = _`
      (ACCEPT_TAC o SIMP_RULE bool_ss [ADD_CLAUSES,MULT_CLAUSES,h]))
QED

Finalise create_size_exit_raw
