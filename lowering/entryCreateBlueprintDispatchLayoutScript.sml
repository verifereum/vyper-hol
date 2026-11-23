Theory entryCreateBlueprintDispatchLayout
Ancestors
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec gasExplicitSites gasSummary
  s1PrefixDefs venomInst venomState vyperCreate vyperState relation list words pair
  builtinCreate arithmetic exprLowering vfmConstants compileEnv createSizeItinerary
  exprLoweringProps exprBodyPreProps rich_list exprSimHypsDefs vyperTypeSystem bodyPtrDefs
  loweringPosts context vyperAST vyperStorageFootprint vyperValue exprSimSend integer_word
  createCtorSegmentArrival loweringStateRelDefs ptrDiscipline bodySim
  createSizeBlueprintOuterPairedCode createSizeBlueprintRawPayloadCode
  createSizeBlueprintAbiPayloadCode createExprSizeExitDefs createSizePrefixCuts
  createSizeBlueprintObserved

(* The observed cuts are determined by lowering and the target prefix,
   before any source operand is replayed. *)
Theorem blueprint_dispatch_layout:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,hsa,hsb,vv,s0,G0,tn0) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shctx) ctx fnc s0 marks s /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb fnc.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  (!x. MEM x (fn_insts fnc) /\ x.inst_id IN frag_ids sa sb /\
       MEM x.inst_opcode [CREATE;CREATE2] ==> x.inst_id <= inst.inst_id) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;offop;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;offop;sz;saltop])) ==>
  ?target amount salt off ctors later target_op ca cprep cm cn cb cf sc
   sca scprep scm scn scb data len offset_op code prep app salt_op
   C Obs M R n j.
    args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
    later = amount::((if hs then [salt] else []) ++ [off]) /\
    lower_value compile_expr ce (expr_type target) target sa = (target_op,ca) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) hsa = (target_op,sca) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,ca,hsa,sca) /\
    C 0 = sa /\ Obs 0 = s0 /\ marks = M 0 ++ R 1 /\
    create_expr_prefix sa ca (gas_explicit_sites ctx shctx) ctx fnc s0 (M 0) (Obs 1) /\
    (Obs 1).vs_current_bb = ca.cs_current_bb /\
    (Obs 1).vs_inst_idx = LENGTH ca.cs_current_insts /\
    C 1 = ca /\ C j = cprep /\ C (SUC j) = cm /\ C (j+2) = cn /\
    C (j+3) = cb /\ C (j+4) = cf /\ C n = sc /\ j = SUC (LENGTH prep) /\ j+4 <= n /\
    n = j+4+LENGTH app /\ (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
    Obs n = s /\ R n = [] /\
    (!i. i <= n ==> ~(Obs i).vs_halted /\
      (Obs i).vs_current_bb = (C i).cs_current_bb /\
      (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
      ?x. ctor_segment_fetch fnc (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id) /\
    (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fnc) /\
    (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx fnc
        (Obs i) (M i) (Obs (SUC i)) /\ R i = M i ++ R (SUC i) /\
      (C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = [])) /\
    compile_create_blueprint_args compile_expr ce raw later ctors ca = ((data,len),cprep) /\
    compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw (MAP gas_shadow_expr later)
      (MAP gas_shadow_expr ctors) sca = ((data,len),scprep) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cprep,sca,scprep) /\
    lower_value compile_expr ce (expr_type amount) amount cprep = (value,cm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) scprep = (value,scm) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cprep,cm,scprep,scm) /\
    (if hs then ?sop. salt_op = SOME sop /\
      lower_value compile_expr ce (expr_type salt) salt cm = (sop,cn) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) scm = (sop,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn)
     else salt_op = NONE /\ cn = cm /\ scn = scm) /\
    ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
       offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn) \/
     (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb))) /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op cb = (code,cf) /\
    create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz /\
    (if raw then
      ?e v saved raw_op c0 c1 c2 c3 h0 ssaved h1 h2.
        ctors = [e] /\ prep = [c0;c1;c2;c3;cprep] /\
        j = 6 /\ C 2 = c0 /\ C 3 = c1 /\ C 4 = c2 /\ C 5 = c3 /\
        R 1 = M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j))) /\
        compile_expr ce (expr_type e) e ca = (v,c0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce later) v c0 = (saved,c1) /\
        unwrap_value ce saved c1 = (raw_op,c2) /\
        emit_op MLOAD [raw_op] c2 = (len,c3) /\ emit_op ADD [raw_op;Lit 32w] c3 = (data,cprep) /\
        compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (v,h0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) v h0 = (ssaved,h1) /\
        unwrap_value ce ssaved h1 = (raw_op,h2) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c0,sca,h0) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c2,sca,h2) /\
        fn_has_code c0 c1 fnc /\ fn_has_code c2 cprep fnc
     else if ctors = [] then j = 1 /\ cprep = ca /\ data = Lit 0w /\ len = Lit 0w
     else ?vals k cs mid vvs buf a hk ha hcs hmid q.
       q = 1+2*LENGTH ctors /\ j = q+2 /\ C q = k /\ C (SUC q) = a /\
       R q = M q ++ M (SUC q) ++ R j /\
       compile_create_ctor_args compile_expr ce ctors ca = (vals,k) /\
       create_itinerary_ctor_rows ce ctors vals ca k cs mid vvs /\
       compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
         (TupleT (MAP (lowered_value_type ce) ctors))) k = (buf,a) /\
       compile_abi_encode_values_to_buf ce buf.buf_operand
         (ZIP (vals,MAP (lowered_value_type ce) ctors)) a = (len,cprep) /\
       data = buf.buf_operand /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,k,sca,hk) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (k,a,hk,ha) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,cprep,ha,scprep) /\
       (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
       (!i. i < LENGTH ctors ==>
         C (SUC (1+2*i)) = EL i mid /\
         R (1+2*i) = (M (1+2*i) ++ M (SUC (1+2*i))) ++ R (1+2*SUC i) /\
         create_expr_prefix (EL i cs) (EL (SUC i) cs) (gas_explicit_sites ctx shctx) ctx fnc
           (Obs (1+2*i)) (M (1+2*i) ++ M (SUC (1+2*i))) (Obs (1+2*SUC i)) /\
         compile_expr (gas_shadow_env T ce) (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (EL i hcs) =
           (EL i vvs,EL i hmid) /\
         compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
           (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (EL i vvs)) (EL i hmid) =
           (EL i vals,EL (SUC i) hcs) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `?result. compile_create_call compile_expr ce (CreateFromBlueprint raw) hs rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call,compile_call_def] >>
     Cases_on `compile_create_call compile_expr ce (CreateFromBlueprint raw) hs rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >>
  strip_tac >>
  suspend "layout"
QED

Resume blueprint_dispatch_layout[layout]:
  `value' = value /\ bufop = offop /\ len = sz /\ inst.inst_id = sc.cs_next_id /\ inst.inst_opcode <> PHI` by
    (Cases_on `salt` >> qpat_x_assum `inst = _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
     fs[mk_inst_def]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`value' = value`,`bufop = offop`,`len = sz`] >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [create_call_itinerary_def,vyperASTTheory.create_kind_case_def,create_blueprint_itinerary_def]) >>
  qabbrev_tac `later = value_e::TAKE (if hs then 2 else 1) rest` >>
  qabbrev_tac `suffix = if hs then TL rest else rest` >>
  `?se oe ctors. args = target_e::value_e::((if hs then [se] else []) ++ oe::ctors) /\
    TL suffix = ctors /\ HD suffix = oe /\
    later = value_e::((if hs then [se] else []) ++ [oe]) /\
    (if hs then SOME (HD rest) else NONE) = (if hs then SOME se else NONE)` by
    (Cases_on `hs` >> Cases_on `rest` >> fs[Abbr `later`,Abbr `suffix`] >>
     TRY (Cases_on `t` >> fs[])) >>
  map_every (fn q => qpat_x_assum q (fn h => rule_assum_tac (PURE_REWRITE_RULE[h])))
    [`TL suffix = ctors`,`HD suffix = oe`,
     `(if hs then SOME (HD rest) else NONE) = (if hs then SOME se else NONE)`] >>
  `LAST app = sc` by
    (`app <> []` by
       (qpat_assum `create_blueprint_append_itinerary _ _ _ _ _ _ app _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `args_len = Lit 0w` >>
        simp[create_blueprint_append_itinerary_def, PULL_EXISTS] >> metis_tac[NOT_CONS_NIL]) >>
     `sa::cuts = (sa::a::(prep ++ [c;d';e;f])) ++ app` by simp[APPEND_ASSOC] >>
     qpat_assum `LAST (sa::cuts) = sc` (mp_tac o SYM) >>
     qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >> simp[LAST_APPEND_NOT_NIL]) >>
  `expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,sb,hsa,hsb)` by simp[expr_sim_full_code_def] >>
  drule_all create_blueprint_outer_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  suspend "observed"
QED

Resume blueprint_dispatch_layout[observed]:
  qmatch_asmsub_rename_tac `marks = FLAT mark_rows` >>
  qabbrev_tac `C = \i. EL i (sa::cuts)` >>
  qabbrev_tac `Obs = \i. EL i states` >>
  qabbrev_tac `M = \i. EL i mark_rows` >>
  qabbrev_tac `R = \i. FLAT (DROP i mark_rows)` >>
  qabbrev_tac `n = LENGTH cuts` >> qabbrev_tac `j = SUC (LENGTH prep)` >>
  `!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx fnc
    (Obs i) (M i) (Obs (SUC i))` by
    (qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [Abbr `C`,Abbr `Obs`,Abbr `M`,Abbr `n`,EL,HD,TL]) >>
  map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (C = _)`,`Abbrev (Obs = _)`,`Abbrev (M = _)`,`Abbrev (R = _)`,
     `Abbrev (n = _)`,`Abbrev (j = _)`] >>
  `ctor_segment_fetch fnc s = SOME inst` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (fn th =>
       simp_tac bool_ss [ctor_segment_fetch_def,th,optionTheory.OPTION_BIND_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all create_blueprint_observed_bands >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `1 <= n` by decide_tac >>
  qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
    (qspec_then `1` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `C 1 = a` (fn th =>
    map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[th]))
      [`(Obs 1).vs_current_bb = _`,`(Obs 1).vs_inst_idx = _`]) >>
  suspend "pack"
QED

Resume blueprint_dispatch_layout[pack]:
  `n = j+4+LENGTH app` by
    (qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single) >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `j = SUC (LENGTH prep)` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_APPEND] >> decide_tac) >>
  `!i. i < LENGTH app ==> C (j+5+i) = EL i app` by
    (rpt strip_tac >>
     `j+5+i = SUC (i+(j+4))` by
       (POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD1] >> decide_tac) >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >>
     qpat_assum `j+5+i = _` (pure_rewrite_tac o single) >>
     simp_tac bool_ss [EL,TL] >>
     qpat_assum `DROP (j+4) cuts = app` (pure_rewrite_tac o single o SYM) >>
     sym_tac >> irule listTheory.EL_DROP >>
     qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `n = j+4+LENGTH app` (pure_rewrite_tac o single) >>
     qpat_assum `i < LENGTH app` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qexistsl_tac [`target_e`,`value_e`,`se`,`oe`,`ctors`,`later`,`target`,`a`,`b`,`c`,`d'`,`e`,`f`,`sc`,
    `hca`,`hb`,`hc`,`hd`,`he`,`args_buf`,`args_len`,`off`,`code`,`prep`,`app`,`salt`,
    `C`,`Obs`,`M`,`R`,`n`,`j`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "payload"
QED

Resume blueprint_dispatch_layout[payload]:
  Cases_on `raw` >> simp_tac bool_ss [COND_CLAUSES]
  >- suspend "raw" >>
  Cases_on `ctors = []`
  >- (qpat_assum `ctors = []` (simp_tac bool_ss o single) >> suspend "empty") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >> suspend "abi"
QED

Resume blueprint_dispatch_layout[raw]:
  `?ex. ctors = [ex]` by
    (drule expr_body_pre_static_facts >> disch_then (assume_tac o cj 2) >>
     qpat_assum `args = target_e::value_e::_` mp_tac >>
     qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `hs` >>
     simp[well_typed_expr_def,create_arg_types_ok_def,MAP_EQ_CONS] >>
     rpt strip_tac >> gvs[MAP_EQ_CONS] >> metis_tac[]) >>
  qpat_assum `ctors = [ex]` (fn th =>
    qpat_assum `create_blueprint_args_itinerary _ T _ ctors _ _ _ _ _`
      (mp_tac o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,th]) >>
    qpat_assum `compile_create_blueprint_args _ _ T _ ctors _ = _`
      (assume_tac o REWRITE_RULE[th]) >>
    qpat_assum `compile_create_blueprint_args _ _ T _ (MAP gas_shadow_expr ctors) _ = _`
      (assume_tac o REWRITE_RULE[th,MAP])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!cm cs cu cl. prep = [cm;cs;cu;cl;b] ==> _`
    (fn th => drule th >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all create_blueprint_raw_payload_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `compile_expr ce (expr_type ex) ex a = (v0,k0)` >>
  qmatch_asmsub_rename_tac `compile_snapshot_vv ce (exprs_can_mutate ce later) v0 k0 = (snap0,k1)` >>
  qmatch_asmsub_rename_tac `unwrap_value ce snap0 k1 = (ptr0,k2)` >>
  qmatch_asmsub_rename_tac `emit_op MLOAD [ptr0] k2 = (args_len,k3)` >>
  qmatch_asmsub_rename_tac `compile_expr (gas_shadow_env T ce) (expr_type ex) (gas_shadow_expr ex) hca = (v0,sk0)` >>
  qmatch_asmsub_rename_tac `compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) v0 sk0 = (ssnap0,sk1)` >>
  qmatch_asmsub_rename_tac `unwrap_value ce ssnap0 sk1 = (ptr0,sk2)` >>
  qexistsl_tac [`ex`,`v0`,`snap0`,`ptr0`,`sk0`,`ssnap0`,`sk1`,`sk2`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C 2 = _`,`C 3 = _`,`C 4 = _`,`C 5 = _`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_dispatch_layout[empty]:
  qpat_assum `ctors = []` (fn th =>
    qpat_assum `create_blueprint_args_itinerary _ F _ ctors _ _ _ _ _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,th])) >>
  conj_tac >-
    (map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`j = SUC (LENGTH prep)`,`prep = []`] >> EVAL_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_dispatch_layout[abi]:
  qpat_assum `ctors <> []` (fn ne =>
    qpat_assum `create_blueprint_args_itinerary _ F _ ctors _ _ _ _ _`
      (mp_tac o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,ne])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `args_buf = _` (fn th =>
    qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctors) _ = _`
      (assume_tac o REWRITE_RULE[th])) >>
  drule_all create_blueprint_abi_payload_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `1+2*LENGTH ctors = 1+2*LENGTH ctors` by REFL_TAC >>
  qpat_assum `!vals k cs mid vv a' p. create_itinerary_ctor_rows _ _ _ _ _ _ _ _ /\ _ ==> _`
    (fn th => drule_all th >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`vals`,`cs`,`mid`,`vs`,`buf`,`hk`,`hm`,`hcs`,`hmid`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C (1+2*LENGTH ctors) = k`,`C (SUC (1+2*LENGTH ctors)) = m`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise blueprint_dispatch_layout
