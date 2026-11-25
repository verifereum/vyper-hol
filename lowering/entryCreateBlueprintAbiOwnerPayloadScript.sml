Theory entryCreateBlueprintAbiOwnerPayload
Ancestors
  entryCreateEncodedArgExtent createSizeBlueprintAbiKeywords bodyFullPreds
  createCtorPayloadLength createSizeCtorPayload createSizeRawEncoderReplay
  createSizeBlueprintKeywordReplay createSizeObservedPrefix createSizeCtorValueRow
  bodyFullExtCallDirectState bodyFullExtCallPosAggregate bodyInvCodeProps exprBodyPreProps exprSimHypsDefs
  exprSimFullBundleProps exprLoweringProps bodySim bodyPtrDefs loweringPosts
  loweringStateRelDefs ptrDiscipline fragGasOriginPtr fragGasOrigin fragExec
  createExprSizeExitDefs createSizePrefixReplay vyperStorageFootprint
  vyperStorageTrace gasExplicitSites gasSummary vyperCreate vyperInterpreter
  bodyFullIfExpReach createSizeOperandPre freshWrites rich_list stmtLoweringMono
  vyperTypeCallGraph vyperAST vyperTyping vfmConstants createCtorObservedSilence
  createMarkedPath relation bodyFullHashKeccakFixed createSizeRawReplay
  compileEnv exprLowering vyperState venomState venomInst context arithmetic words pair list

(* Compare the observed prefix against the silent pointer replay at the
   same cursor; no determinism claim across different cursors is needed. *)
Theorem abi_payload_readings[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a b explicit ctx func s ms t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') ==>
  ms = [] /\ t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule create_prefix_readings >> disch_tac >>
  `ms = []` suffices_by simp[] >>
  irule ctor_observed_cut_silent >>
  qexistsl [`ctx`,`(b.cs_current_bb,LENGTH b.cs_current_insts)`,`explicit`,`func`,`t`,`s`] >>
  simp[] >> qpat_x_assum `create_expr_prefix a b _ _ _ s ms t`
    (mp_tac o REWRITE_RULE[raw_encoder_prefix_rtc]) >>
  match_mp_tac RTC_MONOTONE >> simp[FORALL_PROD,create_marked_edge_def,PULL_EXISTS]
QED

(* St and C index the row boundaries (1 + 2*i in the enclosing layout).
   Suffix cuts start at the observed encoder exit, not at its inferred result. *)
Theorem blueprint_agreed_abi_payload:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks)
      (target::amount::((if hs then [salt] else []) ++ off::ctors)) df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions /\
  compile_create_blueprint_args compile_expr ce F later ctors (C 0) = ((data,len),en) /\
  eval_operand target_op (St 0) = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv ce cx env p0 /\ body_const_cells_agree [(NONE,tops)] cx env p0 /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (ctors = [] ==> t = St 0 /\ R 0 = rest) /\
  (ctors <> [] ==>
    LENGTH svs = LENGTH ctors /\
    compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,C (LENGTH ctors)) /\
    (!i. i < LENGTH ctors ==>
      compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) = (V i,M i) /\
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
        (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (M i) =
        (EL i svs,C (SUC i)) /\
      ci_mono (C 0) (C i) /\
      create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i) (Mid i) /\
      create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (Mid i) (Snap i) (St (SUC i)) /\
      fn_has_code (M i) (C (SUC i)) func /\
      (Mid i).vs_current_bb = (M i).cs_current_bb /\
      (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
      (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
           (C (SUC i)).cs_next_id <= j.inst_id)) /\
    (!k. bind (eval_exprs cx ctors) k p0 = (res,out) /\
         (!vs. storage_trace_frame (k vs)) ==>
      (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
      ?vs E. E 0 = p0 /\ LENGTH vs = LENGTH ctors /\
        eval_exprs cx ctors p0 = (INL vs,E (LENGTH ctors)) /\
        k vs (E (LENGTH ctors)) = (res,out) /\
        valid_horizon cx st0 H (E (LENGTH ctors)).storage_trace /\
        body_const_cells_agree [(NONE,tops)] cx env (E (LENGTH ctors)) /\
        (!i. i <= LENGTH ctors ==>
          (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
          expr_sim_inv ce cx env (E i) /\
          (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
          ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
          (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
        (!i. i < LENGTH ctors ==>
          bind (eval_expr cx (EL i ctors)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
          (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i ctors)) = SOME tv /\
            evaluate_type (get_tenv cx) (expr_type (EL i ctors)) = SOME ann /\
            arg_type_fits (lowered_value_type ce (EL i ctors)) (expr_type (EL i ctors)) /\
            value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
          (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
             stmt_state_rel K ctx func ce cx (E i) (St i) /\
             storage_well_formed_on cx (E i) (FST K) /\
             ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
            (is_word_type (lowered_value_type ce (EL i ctors)) ==>
              ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
                lower_value compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) =
                  (op,C (SUC i)) ==>
                expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i ctors)
                  (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
                  ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
            (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
              ?g' h' rv. eval_expr cx (EL i ctors) (E i) = (INL rv,E (SUC i)) /\
              !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
                vv_post K ctx func ce cx (EL i ctors) (E i) (C i) (M i) (St i)
                  ((E (SUC i)) with gas_obs := []) rv (V i) (Mid i) /\
                vv_store_bound cx (post_value_type ce (EL i ctors)) (lowered_value_type ce (EL i ctors))
                  ((E (SUC i)) with gas_obs := []) rv (V i) (Mid i) /\
                ptr_vv_ok cx (post_value_type ce (EL i ctors)) rv (V i)
                  ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
                alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
                ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
                ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
                (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i ctors)) ==>
                  ptr_buf_ok ce (EL i ctors) op g' (Mid i)) /\
                (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok ce (EL i ctors) p.ptr_operand g' (Mid i)) /\
                (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
                  ?val. read_result cx rv ((E (SUC i)) with gas_obs := []) =
                    (INL val,(E (SUC i)) with gas_obs := []) /\
                  !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i ctors)) = SOME rt /\
                    eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                      val_in_memory rt val (w2n w) mem)))))) /\
    capacity = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) /\
    compile_alloc_buffer capacity (C (LENGTH ctors)) = (buf,a) /\
    fn_has_code (C (LENGTH ctors)) a func /\
    su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix (C (LENGTH ctors)) a (gas_explicit_sites ctx shctx) ctx func
      (St (LENGTH ctors)) am su /\
    compile_abi_encode_values_to_buf ce buf.buf_operand (ZIP (svs,MAP (lowered_value_type ce) ctors))
      a = (len,en) /\ fn_has_code a en func /\
    create_expr_prefix a en (gas_explicit_sites ctx shctx) ctx func su encmarks t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    R (LENGTH ctors) = am ++ encmarks ++ rest /\
    c 0 = en /\ r 0 = t /\ r n = bad /\
    (!k. k < n ==> (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      create_expr_prefix (c k) (c (SUC k)) (gas_explicit_sites ctx shctx) ctx func
        (r k) (chunk k) (r (SUC k))) /\
    lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
    get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
    ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;offop;sz]) \/
     (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;offop;sz;salto])) /\
    eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint F) hs rof
       (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs p G tn bytes.
    LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p0 = (INL cvs,p) /\
    bind (eval_exprs cx later)
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
    valid_horizon cx st0 H p.storage_trace /\ body_const_cells_agree [(NONE,tops)] cx env p /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bytes /\
    eval_operand len t = SOME (n2w (LENGTH bytes)) /\
    (!x. len = Var x ==> not_fresh_at en x) /\
    (!at_add. (!x w. not_fresh_at en x /\ lookup_var x t = SOME w ==>
        lookup_var x at_add = SOME w) ==>
      ?w. eval_operand len at_add = SOME w /\ w2n w < 2 ** 64) /\
    eval_operand target_op t = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at en x) /\
    expr_sim_inv ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = \vs. bind (eval_exprs cx later)
    (\ws. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(vs ++ ws)))` >>
  `bind (eval_exprs cx ctors) k p0 = (res,out)` by
    fs[Abbr `k`, blueprint_abi_bind_append] >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`, evaluate_storage_trace_frame, storage_trace_frame_bind_all,
      storage_trace_frame_create_operands] >>
  Cases_on `ctors = []` >- suspend "empty" >>
  qpat_x_assum `ctors <> [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `!k. bind (eval_exprs cx ctors) k p0 = _ /\ _ ==> _`
    (qspec_then `k` mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choosel_then [`cvs`,`E`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "nonempty"
QED

Resume blueprint_agreed_abi_payload[empty]:
  gvs[compile_create_blueprint_args_def, comp_return_def, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `k [] p0 = _` (mp_then Any irule valid_horizon_frame) >> simp[]) >>
  disj2_tac >> qexistsl [`p0`,`G0`,`tn0`] >>
  simp[return_def, eval_operand_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_agreed_abi_payload[nonempty]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!i p. i < LENGTH ctors /\ expr_sim_inv ce cx env p ==>
         expr_body_pre ce cx env (EL i ctors) p` by
    (rpt strip_tac >> irule create_call_operand_body_pre >> simp[] >>
     qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) entry` (irule_at Any) >>
     simp[MEM_APPEND,EL_MEM]) >>
  `capacity < dimword (:256)` by
    (drule_all encoded_blueprint_tuple_allocation >>
     simp[dimword_def] >> strip_tac >> gvs[]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_split_def,expr_sim_inv_mods_def] >>
  qabbrev_tac `se = C (LENGTH ctors)` >>
  qabbrev_tac `s = St (LENGTH ctors)` >>
  qabbrev_tac `ee = E (LENGTH ctors)` >>
  `ci_mono (C 0) se` by
    (qspecl_then [`compile_expr`,`ce`,`ctors`,`C 0`] mp_tac
       ci_mono_compile_create_ctor_args >> simp[ci_mono_compile_expr_sa]) >>
  `ci_mono se a` by
    (qspecl_then [`capacity`,`se`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono a en` by
    (qspecl_then [`ce`,`buf.buf_operand`,`ZIP (svs,MAP (lowered_value_type ce) ctors)`,`a`]
       mp_tac ci_mono_compile_abi_encode_values_to_buf >> simp[]) >>
  `ci_mono (C 0) en` by
    (irule ci_mono_trans >> qexists_tac `a` >> simp[] >>
     irule ci_mono_trans >> qexists_tac `se` >> simp[]) >>
  `!i. i <= LENGTH ctors ==> (St i).vs_labels = (St 0).vs_labels` by
    (Induct >> simp[] >> disch_tac >>
     `i < LENGTH ctors /\ i <= LENGTH ctors` by decide_tac >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     qpat_assum `create_expr_prefix (C i) (M i) _ _ _ _ _ _`
       (assume_tac o MATCH_MP create_prefix_labels) >>
     qpat_assum `create_expr_prefix (M i) _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP create_prefix_labels) >> simp[]) >>
  `EVERY (\call. FST call = NONE /\ IS_SOME (supported_function_decl tops call Internal))
    (int_calls_exprs ctors)` by suspend "calls" >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH ctors` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s am (OK su)` by
    (irule raw_observed_prefix_alloc >> qexistsl [`se`,`a`,`buf`,`capacity`] >>
     gs[Abbr `s`,Abbr `se`]) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at se x /\ not_fresh_at en x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce se /\ local_ptrs_reserved ce en` by
    metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `!j. j < LENGTH ctors ==> (St (SUC j)).vs_labels = (St j).vs_labels` by
    (rpt strip_tac >> `j <= LENGTH ctors /\ SUC j <= LENGTH ctors` by decide_tac >>
     qpat_assum `!i. i <= LENGTH ctors ==> (St i).vs_labels = _`
       (fn th => map_every (fn idx => qspec_then idx (drule_then assume_tac) th) [`j`,`SUC j`]) >>
     simp[]) >>
  suspend "payload_length"
QED

Resume blueprint_agreed_abi_payload[calls]:
  drule_all_then assume_tac bodySingletonCallSupportTheory.body_inv_expr_pre_calls >>
  simp[EVERY_MEM] >> qx_gen_tac `call` >> disch_tac >>
  `MEM call (int_calls_expr (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks)
      (target::amount::((if hs then [salt] else []) ++ off::ctors)) df))` by
    (Cases_on `hs` >> gvs[int_calls_expr_def]) >>
  qpat_assum `EVERY _ (int_calls_expr (Call _ _ _ _))`
    (qspec_then `call` mp_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
  simp[]
QED

Resume blueprint_agreed_abi_payload[payload_length]:
  qmatch_asmsub_rename_tac `compile_abi_encode_values_to_buf _ _ _ _ = (alen,en)` >>
  mp_tac (Q.INST [`raw` |-> `F`, `args` |-> `ctors`, `vs` |-> `cvs`,
                  `explicit` |-> `gas_explicit_sites ctx shctx`,
                  `st` |-> `a`, `dst_op` |-> `buf.buf_operand`, `u` |-> `su`,
                  `off` |-> `offop`, `salt` |-> `salto`] create_ctor_payload_length
     |> PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES,
                          ADD_CLAUSES,REFL_CLAUSE]) >>
  (impl_tac >- suspend "producer_pre") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  disch_then (qx_choose_then `bytes` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?G tn Gt tt pbase root dst Gu tu. _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  suspend "finish"
QED

Resume blueprint_agreed_abi_payload[producer_pre]:
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  `LENGTH ctors = LENGTH cvs` by simp[] >>
  `?K. valid_horizon cx st0 K (E (LENGTH ctors)).storage_trace` by
    (qexists_tac `H` >> fs[Abbr `ee`]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by simp[] >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (se = _)`,`Abbrev (s = _)`,`Abbrev (ee = _)`] >>
  `compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,C (LENGTH ctors))` by
    (qpat_assum `se = C (LENGTH ctors)` (pure_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [PAIR_EQ] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `E 0 = p0` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexists_tac `H` >>
       qpat_assum `ee = E (LENGTH ctors)` (pure_rewrite_tac o single o SYM) >>
       first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "producer_row" >>
  suspend "producer_callback"
QED

Resume blueprint_agreed_abi_payload[producer_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  `(C 0).cs_next_var <= (C i).cs_next_var` by
    (qpat_assum `ci_mono (C 0) (C i)` (mp_tac o REWRITE_RULE[ci_mono_def]) >> simp[]) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `C 0` >> simp[]) >>
  `local_ptrs_reserved ce (C i)` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `C 0` >> simp[]) >>
  `i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  `expr_body_pre ce cx env (EL i ctors) (E i)` by simp[] >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `SUC i` (drule_then strip_assume_tac)) >>
  simp[] >> disch_tac >> Cases_on `exprs_can_mutate ce (DROP (SUC i) ctors)` >> simp[]
  >- (conj_tac
      >- (irule raw_observed_prefix_live >>
          qexistsl [`C i`,`M i`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Chunk i`,`St i`] >>
          `i <= LENGTH ctors` by decide_tac >> simp[]) >>
      simp[GSYM PAIR_EQ,GSYM IMP_DISJ_THM] >>
      qpat_assum `create_expr_prefix (M i) _ _ _ _ _ _ _`
        (mp_tac o MATCH_MP blueprint_ctor_segment_rtc) >> simp[PAIR_EQ]) >>
  `vv_type (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) =
     lowered_value_type ce (EL i ctors)` by metis_tac[extcall_operand_snapshot_type] >>
  `C (SUC i) = M i` by
    (qpat_assum `compile_snapshot_vv _ _ _ (M i) = _`
       (mp_tac o PURE_REWRITE_RULE[compile_snapshot_vv_def]) >>
     simp[comp_return_def]) >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _` mp_tac >>
  simp[] >> metis_tac[create_prefix_empty]
QED

Resume blueprint_agreed_abi_payload[producer_callback]:
  map_every qx_gen_tac [`i`,`g`,`h`] >> strip_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  qpat_assum `!g h. (!K. valid_horizon _ _ _ _ ==> _) ==> _`
    (qspecl_then [`g`,`h`] (drule_then ACCEPT_TAC))
QED

Resume blueprint_agreed_abi_payload[finish]:
  qhdtm_assum `abi_encode_saved_state`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_def]) >>
  qmatch_asmsub_rename_tac `ghost_inv_at _ lo d ce cx ee Gout tout t` >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,_,_) [] (OK su,_,_) /\ _`
    (qspec_then `DF H` (map_every assume_tac o CONJUNCTS)) >>

  `!f inst z. frag_reachable ctx func s f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `Abbrev (s = _)`
       (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  `!f inst z. frag_reachable ctx func su f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s,_,_) [] (OK su,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `!f inst z. frag_reachable ctx func t f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (su,_,_) [] (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `H` (drule_then
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `t.vs_labels = (St 0).vs_labels` by
    (qpat_assum `create_expr_prefix se a _ _ _ s am su`
       (assume_tac o MATCH_MP create_prefix_labels) >>
     qpat_assum `create_expr_prefix a en _ _ _ su encmarks t`
       (assume_tac o MATCH_MP create_prefix_labels) >>
     simp[Abbr `s`]) >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >>
     qexistsl [`C 0`,`St 0`] >> simp[] >>
     qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (mp_tac o cj 1 o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `ee.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail` by suspend "exit_gas" >>
  disj2_tac >> qexistsl [`cvs`,`ee`,`Gout`,`tout`,`bytes`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `k cvs ee = _` (ACCEPT_TAC o SIMP_RULE bool_ss [Abbr `k`]) >> NO_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  suspend "at_add"
QED

Resume blueprint_agreed_abi_payload[exit_gas]:
  qpat_assum `create_expr_prefix se a _ _ _ s am su`
    (mp_then Any drule_all abi_payload_readings) >> strip_tac >>
  qpat_assum `create_expr_prefix a en _ _ _ su encmarks t`
    (mp_then Any drule_all abi_payload_readings) >> strip_tac >>
  qpat_assum `(E (LENGTH ctors)).gas_obs = _` mp_tac >>
  simp[Abbr `ee`,Abbr `s`]
QED

Resume blueprint_agreed_abi_payload[at_add]:
  qx_gen_tac `at_add` >> disch_tac >>
  irule (INST_TYPE [alpha |-> ``:vyper_value``] encoded_blueprint_replayed_length_at_add) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl [`bytes`,`svs`,`t`,`cvs`] >> simp[] >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)))
QED

Finalise blueprint_agreed_abi_payload
