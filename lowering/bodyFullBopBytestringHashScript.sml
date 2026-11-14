Theory bodyFullBopBytestringHash
Ancestors
  bodySimFull bodyFullGhostFrame bodyPtrBopTypedSource bodyPtrBopHashRun
  bodyPtrBopHashSemantic bodyPtrBopHashCompile bodyPtrBopHashEndpoint bodyPtrBopHashFootprint
  bodyPtrBopHashSuffix bodyPtrBopHashFrame bodyMemBopHeldHash
  bodyPtrIfExpBytesFrame abiEncodeOwnership venomInst loweringStateRelDefs
  externalEntryShape fragExec fragGasCopyLoop fragGasSeqPtr gasOutcomeFullCompose
  exprSimWordArgs bytestringHashProps exprSimHashBoundary exprSimHash exprSimHyps exprLoweringProps
  exprSimProps bodyFullPreds bodyPtrDefs gasStorage vyperStorageTrace
  loweringPosts exprSimMemDefs allocaHistoryFragment
  gasOutcomeFull exprOperandVar exprLowering compileEnv vyperTyping
  vyperValue vyperInterpreter venomState words list vyperStorageFootprint
Libs pairLib

Theorem bop_bytestring_hash_post_view:
  is_bytestring_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\
  lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
  compile_bytestring_hash m cb = (h,sz) /\
  fn_has_code sa sz func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa cb s ee v m t /\
      expr_store_bound cx (expr_type e) v m t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\
      ptr_val_ok cx (post_value_type cenv e) v m HG un t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e m HG t) /\
      ghost_kept_at lo cenv es sa G tn s HG un) /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (res,ee)) ==>
  ?v tv p w contents b.
    res = INL v /\ m = Var p /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    ~is_word_type (expr_type e) /\
    expr_val_at cenv cx (expr_type e) sa cb ee v (Var p) t /\
    ptr_val_ok cx (expr_type e) v (Var p) HG un t /\
    lookup_var p t = SOME w /\ not_fresh_at cb p /\
    (v = BytesV contents \/
     ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
    w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
    mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
    b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by
    (drule bop_typed_source_witness >>
     disch_then (qspecl_then [`v`, `ee`] mp_tac) >> simp[] >> metis_tac[]) >>
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `expr_val_at cenv cx (expr_type e) sa cb ee v m t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     gvs[expr_post_def, post_value_type_bytestring]) >>
  `?w. eval_operand m t = SOME w` by metis_tac[expr_val_at_def] >>
  `val_footprint tv v <> 0` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
     Cases_on `v` >> gvs[evaluate_type_def, value_has_type_def, val_footprint_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def, val_footprint_def]) >>
  `?p. m = Var p` by
    metis_tac[ptr_val_ok_def, ptr_mem_ok_def, post_value_type_bytestring] >>
  gvs[] >>
  `lookup_var p t = SOME w` by gvs[eval_operand_def] >>
  `not_fresh_at cb p` by metis_tac[compile_lower_value_var] >>
  `?contents b.
     (v = BytesV contents \/ ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
     w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
     mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
     b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >- (gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         drule hash_string_post_view >> simp[evaluate_type_def] >> strip_tac >>
         metis_tac[optionTheory.SOME_11, LENGTH_MAP]) >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule hash_dynamic_post_view >> simp[evaluate_type_def] >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`contents`, `b`] >> simp[]
QED

Theorem bop_bytestring_hash_operational_certificate:
  ~t.vs_halted /\
  is_bytestring_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\
  lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
  compile_bytestring_hash m cb = (h,sz) /\
  fn_has_code sa sz func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa cb s ee v m t /\
      expr_store_bound cx (expr_type e) v m t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\
      ptr_val_ok cx (post_value_type cenv e) v m HG un t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e m HG t) /\
      ghost_kept_at lo cenv es sa G tn s HG un) /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (res,ee)) /\
  (?v tv p w contents b.
    res = INL v /\ m = Var p /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    ~is_word_type (expr_type e) /\
    expr_val_at cenv cx (expr_type e) sa cb ee v (Var p) t /\
    ptr_val_ok cx (expr_type e) v (Var p) HG un t /\
    lookup_var p t = SOME w /\ not_fresh_at cb p /\
    (v = BytesV contents \/
     ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
    w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
    mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
    b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)) ==>
  ?raw u HG' un'.
    u = (raw with vs_inst_idx := LENGTH sz.cs_current_insts) /\
    run_inst_seq (emitted_insts cb sz) t = OK raw /\
    (raw with vs_vars := t.vs_vars) = t /\
    (!x. not_fresh_at cb x ==>
       lookup_var x raw = lookup_var x t /\ FLOOKUP HG' x = FLOOKUP HG x /\
       FLOOKUP un'.t_var x = FLOOKUP un.t_var x) /\
    un'.t_mem = un.t_mem /\ un'.t_stor = un.t_stor /\
    un'.t_trans = un.t_trans /\ un'.t_imm = un.t_imm /\
    op_prov HG' h = NONE /\ op_taint un' h = {} /\
    (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
    (?v contents. res = INL v /\
      (v = BytesV contents \/
       ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
      eval_operand h u = SOME (word_of_bytes_be (Keccak_256_w64 contents))) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,HG,un) []
         (OK u,HG',un'))
Proof
  strip_tac >> qpat_x_assum `m = Var _` SUBST_ALL_TAC >>
  drule compile_bytestring_hash_run_nofresh >>
  disch_then (qspecl_then [`t`, `contents`, `b`] mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qx_choose_then `hash_end` strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by gvs[storage_trace_domain_def] >>
  (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
   (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) >>
  `cs_extends sa cb /\ sa.cs_next_var <= cb.cs_next_var /\
    sa.cs_next_id <= cb.cs_next_id` by
    (drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
  `cs_extends cb sz` by
    (mp_tac (Q.SPECL [`Var p`, `cb`, `\x. T`] compile_bytestring_hash_labels) >>
     simp[]) >>
  `fn_has_code cb sz func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sz`, `sa`] >>
     simp[cs_extends_refl]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
    metis_tac[expr_post_state] >>
  `32 + LENGTH contents <= val_footprint tv v` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def,
         val_footprint_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def,
         val_footprint_def]) >>
  drule_all bop_hash_semantic_ranges >> strip_tac >>
  `ptr_mem_ok cx (expr_type e) v (Var p) HG un t` by
    gvs[ptr_val_ok_def] >>
  `eval_operand (Var p) t = SOME w` by simp[eval_operand_def] >>
  `(!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN un.t_mem) /\
   (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH contents ==>
        i NOTIN un.t_mem)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >-
       (gvs[value_has_type_def] >> drule ptr_mem_ok_string_clean >>
        simp[evaluate_type_def]) >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def] >>
     drule ptr_mem_ok_bytes_clean >> simp[evaluate_type_def]) >>
  `w2n (w + 32w) = w2n w + 32` by
    (qpat_assum `w = n2w b` (fn th => rewrite_tac[th]) >>
     simp[word_add_n2w]) >>
  `!i. w2n (w + 32w) <= i /\
        i < w2n (w + 32w) + LENGTH contents ==> i NOTIN un.t_mem` by simp[] >>
  `mem_word_at (w2n w) t.vs_memory = n2w (LENGTH contents)` by
    (qpat_assum `w = n2w b` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  qpat_assum `emitted_insts _ _ = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all (GEN_ALL (REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]
    (Q.INST [`h` |-> `h'`,
             `iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
             `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
             `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h']`]
      (SPEC_ALL bop_hash_run_checked)))) >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`, `PG`, `DF (storage_trace_horizon ee.storage_trace)`]
      strip_assume_tac th) >>
  rename1 `inst_seq_ptr _ 0 ctx func PG HG un _ t HGf unf` >>
  `!D. inst_seq_ptr D 0 ctx func PG HG un
     [mk_inst aId ADD [Var p; Lit 32w] [q];
      mk_inst lId MLOAD [Var p] [l];
      mk_inst hId SHA3 [Var q; Var l] [h']] t HGf unf` by
    (gen_tac >>
     qpat_assum `!fn PG D. _` (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!fn PG D. _` kall_tac >>
     `G' = HGf /\ tn' = unf` by metis_tac[inst_seq_ptr_ghost_unique] >>
     gvs[]) >>
  `unf.t_imm = un.t_imm` by
    (qpat_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ HGf unf`
       (mp_then Any mp_tac inst_seq_ptr_immutable_frame) >>
     simp[mk_inst_def]) >>
  `allocas_from lo t` by gvs[ghost_inv_at_def] >>
  `!D. inst_seq_ptr D lo ctx func PG HG un
     [mk_inst aId ADD [Var p; Lit 32w] [q];
      mk_inst lId MLOAD [Var p] [l];
      mk_inst hId SHA3 [Var q; Var l] [h']] t HGf unf` by
    (gen_tac >> irule inst_seq_ptr_lower_bound_transport >>
     conj_tac >- simp[mk_inst_def] >>
     simp[] >> qexists_tac `0` >> simp[]) >>
  `b + 32 + LENGTH contents <= t.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >>
     gvs[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts cb sz) t` by
    (irule held_hash_mem_ok >> goal_assum (drule_at Any) >>
     simp[eval_operand_def] >> qexistsl_tac [`h`, `Var p`] >>
     simp[eval_operand_def] >> gvs[] >> decide_tac) >>
  drule_all bop_hash_compile_placement >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  drule compile_bytestring_hash_shape >> strip_tac >>
  qexistsl_tac [`hash_end`, `HGf`, `unf`] >>
  simp[] >>
  rpt strip_tac >>
  qspecl_then [`DF H`, `emitted_insts cb sz`, `t`, `hash_end`] mp_tac
    (Q.GEN `D` run_inst_seq_gas_origin_ptr_path) >>
  simp[] >>
  disch_then (qspecl_then [`HG`, `un`, `HGf`, `unf`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  qexists_tac `bb` >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[] >> metis_tac[]
QED
