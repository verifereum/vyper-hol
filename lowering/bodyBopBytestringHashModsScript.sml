(* Read-only hash suffix after a reached linked bytestring child. *)
Theory bodyBopBytestringHashMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPostsMods
  bodyFullHashKeccakFixed bodyPtrBopHashSuffix bodyMemBopHeldHash
  bytestringHashProps abiEncodeOwnership bodyPtrBopHashSemantic
  bodyPtrBopHashFootprint bodyPtrBopHashCompile bodyPtrBopHashRun
  fragGasSeqPtr fragGasCopySeqLiftProps fragGasOriginPtr
  exprSimWordArgs loweringPosts bodyPtrDefs vyperStorageTrace venomState
  compileEnv venomInst words list finite_map pred_set
  bodyPtrIfExpBytesFrame ptrDiscipline exprSimConvertBytes
  exprSimHashBoundary exprLoweringProps exprLowering exprOperandVar exprSimProps
  bodyFullShadowBodyInv bodyPtrBopHashCoverage exprSimLiteralWord
  gasOutcomeFullPostMods gasOutcomeFullBindMods vyperValueOperation vyperTyping
  valueEncodingDefs loweringStateRelDefs freshWrites fragExec keccak vyperValue
  bodyBopBytestringHashLocationMods bodyBopBytestringHashRangesMods
  bodyBopBytestringHashFrameMods vyperStorageFootprint vyperInterpreter vyperState
Libs monadsyntax

Theorem bytestring_hash_no_dalloca[local]:
  EVERY (\i. i.inst_opcode <> DALLOCA) (pre ++ i::post) ==>
    unitTransformDefs$dalloca_no_wrap i u
Proof
  simp[EVERY_APPEND] >> strip_tac >>
  irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >> simp[]
QED

Theorem bytestring_hash_run_mods[local]:
  compile_bytestring_hash (Var p) cb = (h,sz) /\ not_fresh_at cb p /\
  fn_has_code cb sz func /\ ~t.vs_halted /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\
  lookup_var p t = SOME (n2w b) /\
  mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
  mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
  b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256) /\
  b + 32 + LENGTH contents <= t.vs_alloca_next /\
  ptr_covers G tn p t 32 /\ FLOOKUP G p = SOME (root,len) /\
  (0 < LENGTH contents ==> root <= b + 32 /\
    b + 32 + LENGTH contents <= root + len) /\
  (!i. b <= i /\ i < b + 32 ==> i NOTIN tn.t_mem) /\
  (!i. b + 32 <= i /\ i < b + 32 + LENGTH contents ==> i NOTIN tn.t_mem) ==>
  ?raw G' tn'.
    run_inst_seq (emitted_insts cb sz) t = OK raw /\
    eval_operand h raw = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    (raw with vs_vars := t.vs_vars) = t /\
    (!x. not_fresh_at cb x ==> lookup_var x raw = lookup_var x t /\
         FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    op_prov G' h = NONE /\ op_taint tn' h = {} /\
    (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
       (OK (raw with vs_inst_idx := LENGTH sz.cs_current_insts),G',tn'))
Proof
  strip_tac >>
  `eval_operand (Var p) t = SOME (n2w b)` by simp[eval_operand_def] >>
  drule (Q.INST [`x` |-> `Var p`] compile_bytestring_hash_run_nofresh) >>
  disch_then (qspecl_then [`t`, `contents`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cb sz) t` by
    (irule held_hash_mem_ok >> goal_assum (drule_at Any) >>
     qexistsl [`LENGTH contents`,`h`] >> simp[] >> decide_tac) >>
  drule_all bop_hash_compile_placement >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  drule compile_bytestring_hash_shape >> strip_tac >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  `w2n (n2w b + 32w:bytes32) = b + 32` by simp[word_add_n2w] >>
  `mem_word_at (w2n (n2w b:bytes32)) t.vs_memory = n2w (LENGTH contents)` by simp[] >>
  `(0 < LENGTH contents ==> root <= w2n (n2w b + 32w:bytes32) /\
    w2n (n2w b + 32w:bytes32) + LENGTH contents <= root + len)` by simp[] >>
  `!i. w2n (n2w b:bytes32) <= i /\ i < w2n (n2w b:bytes32) + 32 ==>
       i NOTIN tn.t_mem` by simp[] >>
  `!i. w2n (n2w b + 32w:bytes32) <= i /\
       i < w2n (n2w b + 32w:bytes32) + LENGTH contents ==> i NOTIN tn.t_mem` by simp[] >>
  qpat_assum `emitted_insts cb sz = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all (GEN_ALL (SIMP_RULE bool_ss [REFL_CLAUSE, AND_CLAUSES]
    (Q.INST [`h` |-> `h'`,
             `iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
             `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
             `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h']`]
      (SPEC_ALL bop_hash_run_checked)))) >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`, `PG`, `D0`] strip_assume_tac th) >>
  rename1 `inst_seq_ptr D0 0 ctx func PG G tn _ t Gf tnf` >>
  rename1 `run_inst_seq _ t = OK raw` >>
  `tnf.t_imm = tn.t_imm` by
    (qpat_assum `inst_seq_ptr D0 _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac inst_seq_ptr_immutable_frame) >>
     simp[mk_inst_def]) >>
  qexistsl [`raw`, `Gf`, `tnf`] >> simp[] >>
  conj_tac >- simp[op_taint_def] >>
  gen_tac >>
  qpat_x_assum `!fn PG D. _` (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `G' = Gf /\ tn' = tnf` by metis_tac[inst_seq_ptr_ghost_unique] >>
  qpat_x_assum `G' = Gf` SUBST_ALL_TAC >>
  qpat_x_assum `tn' = tnf` SUBST_ALL_TAC >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts cb sz) t Gf tnf` by
    (irule inst_seq_ptr_lower_bound_transport >>
     conj_tac >- simp[mk_inst_def] >> simp[] >> qexists_tac `0` >> simp[]) >>
  `ctx_has_dalloca ctx ==> !pre i post u. emitted_insts cb sz = pre ++ i::post /\
     run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     rename1 `emitted_insts cb sz = pre ++ i::post` >>
     `EVERY (\j. j.inst_opcode <> DALLOCA) (pre ++ i::post)` by
       (qpat_assum `emitted_insts cb sz = pre ++ i::post`
          (fn th => pure_once_rewrite_tac[GSYM th]) >>
        qpat_assum `emitted_insts cb sz = [_;_;_]` (fn th =>
          pure_once_rewrite_tac[th]) >> simp[mk_inst_def]) >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >> fs[EVERY_APPEND]) >>
  qpat_assum `inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      run_inst_seq_gas_origin_ptr_path) >>
  disch_then (qspecl_then [`explicit`, `raw`] mp_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cb sz)` by simp[mk_inst_def, is_terminator_def] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts cb sz) = []` by simp[mk_inst_def] >>
  `run_inst_seq (emitted_insts cb sz) t = OK raw` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts cb sz) t` by simp[] >>
  `isPREFIX (emitted_insts cb sz) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `emitted_insts cb sz = [_;_;_]` (fn th => pure_once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `t.vs_inst_idx + LENGTH (emitted_insts cb sz) = LENGTH sz.cs_current_insts` by simp[] >>
  disch_then (qspec_then `bb` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* The prefix lands at t. The chosen suffix is independent of H.
   Only the normal post changes; the gas-outcome lift can keep its exit post. *)
Theorem bop_bytestring_hash_mods:
  is_bytestring_type (expr_type e) /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (res,ee)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?v tv bs. res = INL v /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\
    (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    expr_sim_inv_mods mods cenv cx env ee /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (case bytestring_literal_hash e of
       SOME digest => h = Lit digest /\ sz = sa /\ t = s /\ G = G0 /\ tn = tn0 /\
          digest = word_of_bytes_be (Keccak_256_w64 bs)
     | NONE => ?m cb b p. m = Var p /\ not_fresh_at cb p /\
          lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
          compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
          t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
          expr_post_mods H ctx func cenv cx e es sa cb s ee v m t /\
          expr_store_bound cx (post_value_type cenv e) v m t /\
          ptr_val_ok cx (post_value_type cenv e) v m G tn t /\ ptr_buf_ok cenv e m G t /\
          eval_operand m t = SOME (n2w b) /\ mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
          mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
          b + 32 < dimword(:256) /\ LENGTH bs < dimword(:256))) ==>
  ?u G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G',tn') /\
    ?v bs. res = INL v /\
      (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
      eval_operand h u = SOME (word_of_bytes_be (Keccak_256_w64 bs)) /\
      op_prov G' h = NONE /\ op_taint tn' h = {} /\
      (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\
      stmt_state_rel H ctx func cenv cx ee u /\
      immutable_frame_mods func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' u /\
      ghost_kept_at lo cenv es sa G0 tn0 s G' tn' /\
      ~u.vs_halted /\ u.vs_current_bb = sz.cs_current_bb /\
      u.vs_inst_idx = LENGTH sz.cs_current_insts /\ alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
      wb_frame cenv es ee sa s u /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s u)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  Cases_on `bytestring_literal_hash e` >>
  qpat_assum `bytestring_literal_hash e = _` (fn eq =>
    qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
      (assume_tac o BETA_RULE o PURE_REWRITE_RULE [eq, optionTheory.option_case_def]))
  >- suspend "dynamic" >> suspend "literal"
QED

Resume bop_bytestring_hash_mods[dynamic]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then `v` (qx_choose_then `tv` (qx_choose_then `bs`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `?m cb b p. _` strip_assume_tac >>
  qpat_x_assum `m = Var p` SUBST_ALL_TAC >>
  drule_all_then assume_tac bytestring_hash_location_mods >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_bytestring] >>
  qpat_assum `post_value_type cenv e = _` (fn eq =>
    qpat_assum `ptr_val_ok _ (post_value_type _ _) _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  drule_all_then strip_assume_tac bytestring_hash_ranges_mods >>
  `lookup_var p t = SOME (n2w b)` by fs[eval_operand_def] >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `raw` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))))
    bytestring_hash_run_mods >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sz.cs_current_insts`, `G'`, `tn'`] >>
  qx_gen_tac `H` >> strip_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then `v1` (qx_choose_then `tv1` (qx_choose_then `bs1`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `?m cb b p. _`
    (qx_choose_then `m1` (qx_choose_then `cb1` (qx_choose_then `b1`
      (qx_choose_then `p1` strip_assume_tac)))) >>
  qpat_x_assum `m1 = Var p1` SUBST_ALL_TAC >>
  `p1 = p /\ cb1 = cb` by
    (qpat_assum `lower_value compile_expr _ _ _ _ = (Var p1,cb1)` mp_tac >>
     qpat_assum `lower_value compile_expr _ _ _ _ = (Var p,cb)` (fn eq => pure_once_rewrite_tac[eq]) >> simp[]) >>
  qpat_x_assum `p1 = p` SUBST_ALL_TAC >>
  qpat_x_assum `cb1 = cb` SUBST_ALL_TAC >>
  `raw with vs_inst_idx := LENGTH sz.cs_current_insts =
   raw with vs_inst_idx := LENGTH sz.cs_current_insts` by REFL_TAC >>
  drule_all_then strip_assume_tac bytestring_hash_frame_mods >>
  `v1 = v` by
    (qpat_assum `res = INL v1` mp_tac >>
     qpat_assum `res = INL v` (fn eq => pure_once_rewrite_tac[eq]) >> simp[]) >>
  qpat_x_assum `v1 = v` SUBST_ALL_TAC >>
  qexistsl_tac [`v`,`bs`] >> simp[ghostPcTransportPtrTheory.eval_operand_inst_idx]
QED

Resume bop_bytestring_hash_mods[literal]:
  `ee.scopes = es.scopes` by
    (`?ann l. e = Literal ann l` by
       (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac >>
        Cases_on `e` >> fs[bytestring_literal_hash_def]) >>
     qpat_x_assum `e = Literal _ _` SUBST_ALL_TAC >>
     qpat_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     pure_rewrite_tac[literal_read_all_tails, pairTheory.PAIR_EQ] >> strip_tac >>
     qpat_assum `es with gas_obs := _ = ee` (SUBST1_TAC o SYM) >> simp[]) >>
  qexistsl_tac [`t`,`G`,`tn`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then `v` (qx_choose_then `tv` (qx_choose_then `bs`
    (map_every assume_tac o CONJUNCTS)))) >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qexistsl_tac [`v`,`bs`] >>
  qpat_x_assum `h = Lit _` SUBST_ALL_TAC >>
  qpat_x_assum `sz = sa` SUBST_ALL_TAC >>
  qpat_x_assum `t = s` SUBST_ALL_TAC >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[eval_operand_def, op_prov_def, ptrDisciplineTheory.op_taint_def,
         wb_frame_refl, pure_frame_refl])
QED

Finalise bop_bytestring_hash_mods
