Theory exprSimPopStorage
Ancestors
  exprSimDefs exprSimProps loweringPosts
  exprSimPop exprSimLen exprSimLeaves accountsRelProps
  vyperInterpreter vyperState vyperValueOperation finite_map
  vyperTypeAssignContext vyperPlaceResultTyping vyperTypeEnv vyperTypeInvariants
  vyperStorageBackend vyperStorage
  exprLowering compileEnv loweringStateRelDefs vyperAST emitHelper
  exprSimHyps exprSimHypsDefs exprSimAttributeFields exprSimFieldLayout vfmState
  exprLoweringProps venomState vyperLookupStorage list
  emitHelperProps venomExecSemantics venomInst exprSimVVFrame
  gasOutcome gasSummary fragExec fragGasMode fragGasPath fragGasSeq fragGasSeqAbort
  exprSimTopLevelProps

(* Evaluation at a known declared dynamic-array slot, outside a static frame.
   This boundary does not assume that all top-level declarations are storage
   declarations. *)
Theorem eval_pop_storage:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT et (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) /\
  ~cx.txn.is_static ==>
  eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) es =
    let len = w2n (lookup_storage (n2w slot) (get_storage cx es tr)) in
    if len = 0 then
      (INR (Error (RuntimeError "pop empty storage array")), es)
    else
      (INL (PlaceR (StoragePlace tr
        (n2w slot + n2w (1 + (len - 1) * type_slot_size tv)) tv)),
       set_storage cx es tr
         (apply_writes (n2w slot) [(0,n2w (len - 1))] (get_storage cx es tr)))
Proof
  strip_tac >>
  simp[evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, get_place_def, pop_place_def, get_storage_backend_eq,
       ignore_bind_def, check_def, assert_def, raise_def,
       write_storage_slot_eq, encode_value_def, encode_base_to_slot_def,
       integer_wordTheory.i2w_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
QED

Theorem pop_storage_target_facts:
  well_typed_expr env (Pop ann (TopLevelNameTarget (src,id))) /\
  env_consistent env cx es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME d ==>
  ?n tr name slot tv.
    d = (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
    lookup_var_slot_from_layout cx tr src name = SOME slot /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
      SOME (ArrayTV tv (Dynamic n))
Proof
  strip_tac >>
  drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
  drule_all type_place_target_global_lookup >> strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,id)`
  >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      gvs[optionTheory.IS_SOME_EXISTS, vyperValueTheory.evaluate_type_def,
          AllCaseEqs()] >> metis_tac[]) >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]
QED

Theorem compile_expr_pop_storage:
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (ArrayT et bd) ==>
  compile_expr cenv ty (Pop ann (TopLevelNameTarget (src,id))) sa =
    let loc = if tr then LocTransient else LocStorage in
    let result = compile_dynarray_pop (Lit slot) 1
      (elem_size_in_location cenv loc et)
      cenv.ce_is_ctor cenv.ce_imm_alloca loc sa in
    (LocatedValue ann (mk_ptr (FST result) loc), SND result)
Proof
  strip_tac >> Cases_on `tr` >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, compile_get_target_ptr_def, comp_return_def,
       word_scale_def] >>
  pairarg_tac >> simp[]
QED

Theorem pop_storage_compiler_facts:
  expr_sim_inv cenv cx env es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, name) ==>
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME typ
Proof
  strip_tac >> fs[expr_sim_inv_def] >>
  qpat_x_assum `!src id ts tr typ id_str. _` drule >>
  disch_then drule >> simp[]
QED

Theorem pop_storage_element_size:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  elem_size_in_location cenv (if tr then LocTransient else LocStorage) et =
    type_slot_size tv
Proof
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
  Cases_on `tr` >>
  simp[elem_size_in_location_def, is_slot_addressed_def,
       slot_count_of_memory_size]
QED

(* Shortening the header preserves deadness if the element area is unchanged. *)
Theorem dead_bytes_dynarray_shorten:
  !st st' bs n tv.
  w2n (lookup_storage (n2w bs) st') <=
    w2n (lookup_storage (n2w bs) st) /\
  (!i. bs + 1 <= i /\ i < bs + 1 + n * type_slot_size tv ==>
       lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
  !j b. dead_bytes st bs (ArrayTV tv (Dynamic n)) j b ==>
        dead_bytes st' bs (ArrayTV tv (Dynamic n)) j b
Proof
  rpt gen_tac >> strip_tac >> simp[dead_bytes_def] >> rpt strip_tac >>
  qexists_tac `i` >> simp[] >>
  Cases_on `i < w2n (lookup_storage (n2w bs) st')`
  >- (`i < w2n (lookup_storage (n2w bs) st)` by decide_tac >>
      gvs[] >>
      `dead_bytes st' (bs + 1 + i * type_slot_size tv) tv j b <=>
       dead_bytes st (bs + 1 + i * type_slot_size tv) tv j b` suffices_by simp[] >>
      irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
      first_x_assum irule >>
      `i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
        (qpat_x_assum `i < n` (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1) >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.LEFT_ADD_DISTRIB]) >>
      decide_tac) >>
  gvs[] >> Cases_on `i < w2n (lookup_storage (n2w bs) st)` >> gvs[] >>
  drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem dead_bytes_pop_header:
  !st (slot:bytes32) tv n.
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) ==>
  !j b. dead_bytes st (w2n slot) (ArrayTV tv (Dynamic n)) j b ==>
    dead_bytes
      (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
      (w2n slot) (ArrayTV tv (Dynamic n)) j b
Proof
  rpt gen_tac >> strip_tac >> match_mp_tac dead_bytes_dynarray_shorten >>
  conj_tac
  >- (`w2n (lookup_storage slot st) - 1 < dimword (:256)` by
        (qspec_then `lookup_storage slot st` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
      gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
          wordsTheory.w2n_n2w]) >>
  rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n slot` by
    gvs[vyperValueTheory.type_slot_size_def] >>
  `(n2w i:bytes32) <> slot` by
    (strip_tac >>
     `w2n (n2w i:bytes32) = w2n slot` by simp[] >>
     gvs[wordsTheory.w2n_n2w]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem storage_dead_pop_header:
  declared_storage_region cx mid name subs =
    SOME (tr, slot, ArrayTV tv (Dynamic n)) /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) j b
Proof
  strip_tac >> fs[storage_dead_def] >>
  rename1 `dead_bytes st (w2n k) tv' j b` >>
  qexistsl_tac [`mid'`, `n'`, `subs'`, `k`, `tv'`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  Cases_on `(k,tv') = (slot,ArrayTV tv (Dynamic n))`
  >- (gvs[] >> irule dead_bytes_pop_header >> simp[]) >>
  `ranges_disjoint (w2n k) (type_slot_size tv')
                   (w2n slot) (type_slot_size (ArrayTV tv (Dynamic n)))` by
    (first_x_assum irule >> metis_tac[]) >>
  `dead_bytes
     (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
     (w2n k) tv' j b <=> dead_bytes st (w2n k) tv' j b` suffices_by simp[] >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n slot` by
    (fs[vyperStorageFrameTheory.ranges_disjoint_def,
        vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `(n2w i:bytes32) <> slot` by
    (strip_tac >>
     `w2n (n2w i:bytes32) = w2n slot` by simp[] >>
     gvs[wordsTheory.w2n_n2w]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem stmt_state_rel_pop_header:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs =
    SOME (tr, slot, ArrayTV tv (Dynamic n)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (update_storage slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1))
        (get_storage cx es tr)))
    (if tr then
       tstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s
     else
       sstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`]
     >- (irule accounts_rel_tstore >> simp[] >> qexists_tac `es` >>
         simp[set_storage_backend_eq, get_storage_def, vfmStateTheory.lookup_account_def] >>
         rpt strip_tac >> irule storage_dead_pop_header >> metis_tac[]) >>
     irule accounts_rel_sstore >> simp[] >> qexists_tac `es` >>
     simp[set_storage_backend_eq, get_storage_def, vfmStateTheory.lookup_account_def] >>
     rpt strip_tac >> irule storage_dead_pop_header >> metis_tac[]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        set_storage_def, local_ptrs_rel_def, local_backed_def, local_region_def,
        lookup_var_def, immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def] >> Cases_on `tr` >>
     simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  qexistsl [`es`, `s`] >> simp[] >>
  Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

Theorem storage_range_agree_dyn_last:
  storage_range_agree st st' w (ArrayTV tv (Dynamic n)) /\
  len = w2n (lookup_storage w st) /\ 0 < len /\ len <= n ==>
  storage_range_agree st st' (w + n2w (1 + (len - 1) * type_slot_size tv)) tv
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (simp[storage_range_agree_def] >>
      metis_tac[wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ,
                arithmeticTheory.LESS_EQ_LESS_TRANS, prim_recTheory.LESS_REFL]) >>
  `(len - 1) * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (`len - 1 < n` by decide_tac >>
     pop_assum (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1) >>
     qpat_x_assum `n = _` SUBST1_TAC >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES] >>
     decide_tac) >>
  fs[storage_range_agree_def, vyperValueTheory.type_slot_size_def] >>
  `w2n w + (1 + (len - 1) * type_slot_size tv) < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (1 + (len - 1) * type_slot_size tv)) =
   w2n w + (1 + (len - 1) * type_slot_size tv)` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  `w2n (w + n2w (type_slot_size tv * (w2n (lookup_storage w st) - 1) + 1)) =
   w2n w + (1 + (len - 1) * type_slot_size tv)` by
    (qpat_x_assum `len = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_x_assum `w2n (w + _) = _` mp_tac >>
     simp_tac bool_ss [arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  conj_tac >- decide_tac >>
  rpt strip_tac >> qpat_x_assum `!k b. _` irule >>
  reverse conj_tac >- decide_tac >> strip_tac >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.ADD_ASSOC] >>
  irule dyn_array_elem_dead >>
  conj_tac >- simp[] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >> qexists_tac `n` >> simp[]
QED

Theorem storage_range_agree_frame:
  storage_range_agree st st' w tv /\
  (!i. w2n w <= i /\ i < w2n w + type_slot_size tv ==>
       lookup_storage (n2w i) su = lookup_storage (n2w i) st /\
       lookup_storage (n2w i) su' = lookup_storage (n2w i) st') ==>
  storage_range_agree su su' w tv
Proof
  strip_tac >> fs[storage_range_agree_def] >> rpt strip_tac >>
  `dead_bytes su (w2n w) tv (w2n k) b <=>
   dead_bytes st (w2n w) tv (w2n k) b` by
    (irule (cj 1 dead_bytes_frame) >> simp[]) >>
  `lookup_storage k su = lookup_storage k st /\
   lookup_storage k su' = lookup_storage k st'` by
    (first_x_assum (qspec_then `w2n k` mp_tac) >> simp[]) >>
  gvs[]
QED

(* A header write cannot affect a non-wrapping element interval above it. *)
Theorem storage_pop_element_frame:
  storage_range_agree st st' elem tv /\
  (type_slot_size tv = 0 \/ w2n header < w2n elem) ==>
  storage_range_agree
    (apply_writes header [(0,v)] st)
    (apply_writes header [(0,v')] st') elem tv
Proof
  strip_tac >> irule storage_range_agree_frame >>
  qexistsl_tac [`st`, `st'`] >> simp[] >> rpt strip_tac >>
  `n2w i <> header` by
    (strip_tac >>
     `i < dimword(:256)` by
       (fs[storage_range_agree_def] >> decide_tac) >>
     `w2n (n2w i : bytes32) = i` by simp[] >>
     `w2n header = i` by metis_tac[] >> decide_tac) >>
  simp[apply_writes_def, lookup_storage_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem pop_element_slots_frame:
  slots_in_range st (w2n elem) tv /\
  w2n elem + type_slot_size tv <= dimword(:256) /\
  (type_slot_size tv = 0 \/ w2n header < w2n elem) ==>
  slots_in_range (apply_writes header [(0,v)] st) (w2n elem) tv
Proof
  strip_tac >>
  `slots_in_range (apply_writes header [(0,v)] st) (w2n elem) tv =
   slots_in_range st (w2n elem) tv` suffices_by simp[] >>
  irule (cj 1 slots_in_range_read_agree) >> rpt strip_tac >>
  `w2n elem + i < dimword(:256)` by decide_tac >>
  `n2w (w2n elem + i) <> header` by
    (strip_tac >>
     `w2n (n2w (w2n elem + i) : bytes32) = w2n elem + i` by simp[] >>
     `w2n header = w2n elem + i` by metis_tac[] >> decide_tac) >>
  fs[read_slot_def, apply_writes_def, lookup_storage_def,
       update_storage_def, combinTheory.APPLY_UPDATE_THM, arithmeticTheory.ADD_COMM]
QED

Theorem pop_storage_holds:
  evaluate_type (get_tenv cx) ann = SOME tv /\
  well_formed_type_value tv /\
  slots_in_range (get_storage cx es tr) (w2n elem) tv /\
  storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) elem tv ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem es s
Proof
  strip_tac >> drule_all decode_value_from_slots_in_range >> strip_tac >>
  simp[loweringPostsTheory.storage_holds_def, read_storage_slot_eq, read_result_def,
       read_place_def]
QED

Theorem dynarray_pop_storage_shape:
  !slot tr esz is_ctor imm sa r sb.
    compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
      (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
         mk_inst (sa.cs_next_id + 1) ISZERO [Var x0] [x1];
         mk_inst (sa.cs_next_id + 2) ISZERO [Var x1] [x2];
         mk_inst (sa.cs_next_id + 3) ASSERT [Var x2] [];
         mk_inst (sa.cs_next_id + 4) SUB [Var x0; Lit 1w] [x3];
         mk_inst (sa.cs_next_id + 5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
         mk_inst (sa.cs_next_id + 6) ADD [Lit slot; Lit 1w] [x4];
         mk_inst (sa.cs_next_id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
         mk_inst (sa.cs_next_id + 8) ADD [Var x4; Var x5] [x6]]
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`,
                `STRING #"%" (toString (sa.cs_next_var + 3))`,
                `STRING #"%" (toString (sa.cs_next_var + 4))`,
                `STRING #"%" (toString (sa.cs_next_var + 5))`] >>
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC]
QED

Theorem storage_pop_step_load[local]:
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s =
    OK (update_var out (if tr then tload slot s else sload slot s) s)
Proof
  Cases_on `tr` >> simp[step_inst_base_def, exec_read1_def, mk_inst_def, eval_operand_def]
QED

Theorem storage_pop_step_store[local]:
  IS_SOME (lookup_var x s) /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [Lit slot; Var x] []) s =
    OK (if tr then tstore slot (THE (lookup_var x s)) s
        else sstore slot (THE (lookup_var x s)) s)
Proof
  Cases_on `tr` >> Cases_on `lookup_var x s` >>
  simp[step_inst_base_def, exec_write2_def, mk_inst_def, eval_operand_def]
QED

Theorem storage_pop_step_add_literals[local]:
  step_inst_base (mk_inst id ADD [Lit a; Lit b] [out]) s =
    OK (update_var out (a+b) s)
Proof
  irule step_ADD >> simp[eval_operand_def]
QED

Theorem storage_pop_vars[local]:
  (sstore a v s).vs_vars = s.vs_vars /\
  (tstore a v s).vs_vars = s.vs_vars /\
  sstore a v (s with vs_vars := X) = sstore a v s with vs_vars := X /\
  tstore a v (s with vs_vars := X) = tstore a v s with vs_vars := X
Proof
  simp[sstore_def, tstore_def]
QED

val storage_pop_run_simps =
  [run_inst_seq_def, storage_pop_step_load, storage_pop_step_store,
   storage_pop_step_add_literals, pop_step_ISZERO, pop_step_ASSERT,
   pop_step_SUB_lit, pop_step_MUL_lit, pop_step_ADD_var, storage_pop_vars, lookup_var_def, update_var_def,
   FLOOKUP_UPDATE, bool_to_word_def];

Theorem dynarray_pop_storage_run_empty:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
     mk_inst (id+6) ADD [Lit slot; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s = Abort a s'
Proof
  strip_tac >> fs storage_pop_run_simps
QED

Theorem dynarray_pop_storage_run:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\ ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?u. run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
     mk_inst (id+6) ADD [Lit slot; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s = OK u /\
    u = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := u.vs_vars /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz)
Proof
  strip_tac >> fs storage_pop_run_simps >>
  Cases_on `tr` >> fs storage_pop_run_simps >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >>
  simp[sstore_def, tstore_def] >> rw[] >> gvs[]
QED

(* Postcondition packaging stays independent of the header-write proof. *)
Theorem pop_storage_vv_post:
  (!id path. tv <> PlaceR (MemoryPlace id path)) /\
  stmt_state_rel ctx func cenv cx es' u /\
  storage_holds cx tr ann tv slot es' u /\
  lookup_var x u = SOME slot /\
  u.vs_memory = s0.vs_memory /\ u.vs_allocas = s0.vs_allocas /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s0) ==>
  vv_post ctx func cenv cx (Pop ann tgt) es sa sb s0 es' tv
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  Cases_on `tr` >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, contextTheory.mk_ptr_def, eval_operand_def,
       loweringPostsTheory.locals_kept_def, expr_type_def]
QED

Theorem pop_declared_array_agree:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)
    w (ArrayTV tv (Dynamic n))
Proof
  strip_tac >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `storage_read_live cx tr (get_storage cx es tr) w (ArrayTV tv (Dynamic n))` by
    (irule declared_storage_region_read_live >> metis_tac[]) >>
  drule_all vyperStorageLayoutSafetyTheory.storage_layout_safe_region_nonoverflow >> strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]) >>
  irule storage_range_agree_of_live >> metis_tac[]
QED

Theorem pop_declared_array_slots:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  slots_in_range (get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n))
Proof
  strip_tac >>
  `contract_storage_well_formed cx es` by fs[expr_sim_inv_def] >>
  irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >>
  simp[get_storage_backend_eq] >> metis_tac[]
QED

Theorem pop_declared_header_load:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  (if tr then tload w s else sload w s) =
    lookup_storage w (get_storage cx es tr)
Proof
  strip_tac >>
  `storage_read_live cx tr (get_storage cx es tr) w (ArrayTV tv (Dynamic n))` by
    (irule declared_storage_region_read_live >> metis_tac[]) >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >> simp[sload_def, tload_def]
QED

Theorem pop_array_length_bound:
  slots_in_range st (w2n w) (ArrayTV tv (Dynamic n)) ==>
  w2n (lookup_storage w st) <= n
Proof
  simp[Once slots_in_range_def, read_slot_def]
QED

Theorem pop_array_last_slots:
  slots_in_range st (w2n w) (ArrayTV tv (Dynamic n)) /\
  len = w2n (lookup_storage w st) /\ 0 < len ==>
  slots_in_range st
    (w2n (w + n2w (1 + (len - 1) * type_slot_size tv))) tv
Proof
  strip_tac >>
  `len <= n` by metis_tac[pop_array_length_bound] >>
  `MIN len n = len` by simp[arithmeticTheory.MIN_DEF] >>
  `dyn_slots_in_range st (w2n w + 1) tv len` by
    gvs[Once slots_in_range_def, read_slot_def] >>
  `len - 1 < len` by decide_tac >>
  drule_all vyperStorageWritePreservationTheory.dyn_slots_in_range_index >>
  strip_tac >>
  `slots_in_range st
      (w2n (w + n2w (1 + (len - 1) * type_slot_size tv))) tv =
    slots_in_range st (w2n w + 1 + (len - 1) * type_slot_size tv) tv` by
    (irule (cj 1 slots_in_range_offset_cong) >>
     Cases_on `w` >> simp[wordsTheory.word_add_n2w,
                          arithmeticTheory.MOD_PLUS]) >>
  simp[]
QED


Theorem pop_array_last_bounds:
  0 < len /\ len <= n /\
  w2n (w:bytes32) + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) ==>
  w2n (w + n2w (1 + (len - 1) * type_slot_size tv)) + type_slot_size tv <=
    dimword(:256) /\
  (type_slot_size tv = 0 \/
   w2n w < w2n (w + n2w (1 + (len - 1) * type_slot_size tv)))
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (simp[] >> metis_tac[wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `(len - 1) * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (`len - 1 < n` by decide_tac >>
     pop_assum (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1) >>
     qpat_x_assum `n = _` SUBST1_TAC >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES] >>
     decide_tac) >>
  fs[vyperValueTheory.type_slot_size_def] >>
  `w2n w + (1 + (len - 1) * type_slot_size tv) < dimword(:256)` by decide_tac >>
  `w2n (w + n2w (type_slot_size tv * (len - 1) + 1)) =
   w2n w + (type_slot_size tv * (len - 1) + 1)` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  PURE_ASM_REWRITE_TAC [] >> decide_tac
QED

Theorem pop_storage_updated_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s
       else sstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s)
        with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (apply_writes w [(0,n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))]
        (get_storage cx es tr))) u
Proof
  strip_tac >> drule_all stmt_state_rel_pop_header >> strip_tac >>
  simp[apply_writes_def] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  first_x_assum (drule_then mp_tac) >>
  Cases_on `tr` >> gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

Theorem pop_storage_positive_holds:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with vs_vars := u.vs_vars ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (set_storage cx es tr (apply_writes w [(0,n2w (len - 1))] (get_storage cx es tr))) u
Proof
  strip_tac >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) w (ArrayTV tv (Dynamic n))` by
    (irule pop_declared_array_agree >> metis_tac[]) >>
  `slots_in_range (get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n))` by
    (irule pop_declared_array_slots >> metis_tac[]) >>
  `len <= n` by metis_tac[pop_array_length_bound] >>
  `w2n w + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
    fs[storage_range_agree_def] >>
  Q.SUBGOAL_THEN
    `w2n elem + type_slot_size tv <= dimword(:256) /\
      (type_slot_size tv = 0 \/ w2n w < w2n elem)` assume_tac
  >- metis_tac[pop_array_last_bounds] >>
  `slots_in_range (get_storage cx es tr) (w2n elem) tv` by
    metis_tac[pop_array_last_slots] >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) elem tv` by
    metis_tac[storage_range_agree_dyn_last] >>
  irule pop_storage_holds >>
  pure_rewrite_tac[vyperStorageBackendTheory.get_storage_after_set] >>
  conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[pop_element_slots_frame] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  `storage_range_agree
     (apply_writes w [(0,n2w (len - 1))] (get_storage cx es tr))
     (apply_writes w [(0,n2w (len - 1))]
       (if tr then contract_transient s else contract_storage s)) elem tv` by
    metis_tac[storage_pop_element_frame] >>
  Cases_on `tr` >>
  gvs[contract_storage_def, contract_transient_def, sstore_def, tstore_def,
      LET_THM, apply_writes_def, vfmStateTheory.lookup_account_def]
QED

Theorem pop_storage_gas_obs:
  get_storage cx (es with gas_obs := g) tr = get_storage cx es tr /\
  set_storage cx (es with gas_obs := g) tr X =
    set_storage cx es tr X with gas_obs := g
Proof
  Cases_on `tr` >> simp[get_storage_def, set_storage_def]
QED

Theorem pop_storage_holds_gas_obs:
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w es s ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w
    (es with gas_obs := g) s
Proof
  rw[loweringPostsTheory.storage_holds_def, read_result_def, read_place_def] >>
  qexistsl_tac [`tvt`, `v`] >> simp[len_rss_obs, pop_storage_gas_obs]
QED

Theorem pop_ssr_gas_obs:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := g) s
Proof
  strip_tac >> drule msg_gas_state_frame >>
  disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `g`] mp_tac) >>
  simp[NoAsms]
QED

Theorem compile_pop_storage_normalized_sim:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) ==>
  expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  rw[exprSimDefsTheory.expr_vv_sim_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
   ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
    type_slot_size tv` by (irule pop_storage_element_size >> metis_tac[]) >>
  drule_all compile_expr_pop_storage >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sa` >>
  drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,ArrayTV tv (Dynamic n))` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  drule_all pop_declared_header_load >> strip_tac >>
  drule_all eval_pop_storage >> strip_tac >>
  qpat_x_assum `!ty sa' ann'. _` kall_tac >>
  qpat_x_assum `compile_dynarray_pop _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_hashmap_info _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_module_var_type _ = _` kall_tac >>
  qspecl_then [`sa`, `r`, `func`] mp_tac storageCopyGasPathTheory.storage_copy_code_prefix >>
  impl_tac
  >- simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa r)` by
    (simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by simp[] >>
  Cases_on `lookup_storage (n2w slot) (get_storage cx es tr) = 0w`
  >- (`?a s'. run_inst_seq (emitted_insts sa r) s0 = Abort a s'` by
        (simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
         irule dynarray_pop_storage_run_empty >> simp[]) >>
      drule_at (Pat `run_inst_seq _ _ = Abort _ _`)
        run_inst_seq_abort_zero_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`,
                    `es`, `Abort a (s' with vs_inst_idx := j)`] >>
      simp[gas_marked_exec_def, exit_result_def, expr_exit_def, LET_THM,
           pop_storage_gas_obs]) >>
  suspend "positive"
QED

Resume compile_pop_storage_normalized_sim[positive]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by simp[] >>
  `~s0.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa r) s0 = OK u` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`)
    tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  impl_tac
  >- (simp[] >> qpat_x_assum `EVERY _ (emitted_insts _ _)` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[EVERY_MEM]) >>
  strip_tac >>
  `gas_path ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sa.cs_current_insts + 9))` by
    (qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     Cases_on `tr` >> simp[mk_inst_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts _ _) _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s0` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `0 < w2n (lookup_storage (n2w slot) (get_storage cx es tr))` by
    (Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >> gvs[]) >>
  `lookup_storage (n2w slot) (get_storage cx es tr) - 1w =
   n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)` by
    (Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >>
     gvs[GSYM wordsTheory.n2w_sub]) >>
  `u = (if tr then tstore (n2w slot)
      (n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)) s0
    else sstore (n2w slot)
      (n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)) s0)
      with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `u.vs_current_bb = s0.vs_current_bb` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  `vv_post ctx func cenv cx (Pop ann (TopLevelNameTarget (src,id))) es sa r s0
     (set_storage cx es tr
        (apply_writes (n2w slot)
           [(0, n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
           (get_storage cx es tr)) with gas_obs := [])
     (PlaceR (StoragePlace tr
        (n2w slot + n2w (1 + (w2n (lookup_storage (n2w slot)
           (get_storage cx es tr)) - 1) * type_slot_size tv)) tv))
     (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage)))
     u` by
    (irule pop_storage_vv_post >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- (qpat_x_assum `u = _` mp_tac >> Cases_on `tr` >>
                 simp[sstore_def, tstore_def, venom_state_component_equality]) >>
     conj_tac >- (qpat_x_assum `u = _` mp_tac >> Cases_on `tr` >>
                 simp[sstore_def, tstore_def, venom_state_component_equality]) >>
     conj_tac
     >- (irule pop_ssr_gas_obs >> irule pop_storage_updated_state_rel >>
         metis_tac[]) >>
     qexists_tac `n2w slot + n2w (1 +
       (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1) * type_slot_size tv)` >>
     conj_tac >- (PURE_ASM_REWRITE_TAC [] >>
       pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w,
            arithmeticTheory.ADD_ASSOC] >> REFL_TAC) >>
     irule pop_storage_holds_gas_obs >>
     simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM] >>
     irule pop_storage_positive_holds >>
     Cases_on `tr` >> fs[] >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr
        (n2w slot + n2w (1 + (w2n (lookup_storage (n2w slot)
           (get_storage cx es tr)) - 1) * type_slot_size tv)) tv))`,
     `set_storage cx es tr
        (apply_writes (n2w slot)
           [(0, n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
           (get_storage cx es tr))`,
     `OK (u with vs_inst_idx := LENGTH sa.cs_current_insts + 9)`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, exit_result_def, LET_THM,
       pop_storage_gas_obs] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED

Finalise compile_pop_storage_normalized_sim

