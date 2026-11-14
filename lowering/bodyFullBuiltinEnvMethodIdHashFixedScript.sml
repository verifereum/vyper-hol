(* Fixed-byte MethodId hashing with a shared finite-horizon endpoint. *)
Theory bodyFullBuiltinEnvMethodIdHashFixed
Ancestors
  exprSimHash bodyFullGhostFrame bodyFullUnwrapSlotPost fragGasSeqPtr gasOutcomeFullCompose
  allocaHistoryFragment exprSimHashBoundary exprOperandVar allocationPtr wordLoadStorePtr
  bodyPtrHashBuiltinsAllocFrame ptrSafetyTransport ghostPcTransportPtr
  instIdxIndep unitTransformDefs memSafeRun bodyMemoryDefs
  ptrDiscipline venomMemDefs loweringPosts fragExecMem
  ctorDeployMemoryRunPtrPrefixSteps exprPtrUnwrapCopyEdges contextCodegenRel memLocDefs
  bodyPtrDefs exprSimDefs exprSimProps exprSimHypsDefs exprLoweringProps
  builtinHashing compileEnv loweringStateRelDefs vyperStorageTrace
  venomState venomInst venomExecSemantics finite_map list rich_list words vyperStorageFootprint arithmetic fragExec

Theorem method_id_hash_fixed_full_run:
 !DF lo d explicit ctx func PG cenv cx e es sa sm sh s0 st0 mid v x s G tn hash bty.
 expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
 ~is_bytestring_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
 value_has_type (BaseTV bty) v /\
 lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
 compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
 fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
 ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
 local_ptrs_reserved cenv sm /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 return_buf_frame d cenv sm s /\
 MAP FDOM es.scopes = MAP FDOM mid.scopes /\
 storage_trace_domain cx st0 mid.storage_trace /\
 ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
 s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
   expr_store_bound cx (expr_type e) v x s /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
   ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
   (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s))
 ==>
 ?u Gh tnh bs.
 LENGTH bs = 32 /\
 (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] =
   INL (BytesV (TAKE 4 bs))) /\
 eval_operand hash u = SOME
   (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
 op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
 ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
 u.vs_inst_idx = LENGTH sh.cs_current_insts /\ alloca_history func u /\
 s.vs_alloca_next <= u.vs_alloca_next /\ local_ptrs_reserved cenv sh /\
 return_buf_frame d cenv sh u /\
 (!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s /\
   FLOOKUP Gh p = FLOOKUP G p /\ op_taint tnh (Var p) = op_taint tn (Var p)) /\
 (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
   FLOOKUP u.vs_allocas aid = SOME (a,len) /\
   (aid < sm.cs_next_id ==>
     mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory)) /\
 locals_kept cenv mid mid s u /\ pure_frame cenv func mid sm s u /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK u,Gh,tnh) /\
   stmt_state_rel H ctx func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gh tnh u /\
   ghost_kept_at lo cenv mid sm G tn s Gh tnh)
Proof
 rpt gen_tac >> strip_tac >>
 `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
 `expr_post (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx e es sa sm s0 mid v x s` by metis_tac[] >>
 drule_all method_id_hash_typed_post_run >> strip_tac >>
 `?m payload. bty = BytesT (Fixed m) /\ v = BytesV payload /\ m <= 32` by
   (Cases_on `bty` >> gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >>
    gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
 gvs[] >>
 `compile_keccak256_bytesm x m sm = (hash,sh)` by
   gvs[compile_method_id_hash_def, is_bytestring_type_def] >>
 `?w. eval_operand x s = SOME w /\ LENGTH payload = m /\
    TAKE (LENGTH payload) (word_to_bytes_be w) = payload` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    drule_at (Pos hd) hash_fixed_post_view >> simp[]) >>
 `!p. x = Var p ==> not_fresh_at sm p` by
   (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
 `?p out. hash = Var out /\
    emitted_insts sm sh =
      [mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p];
       mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] [];
       mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [out]] /\
    ~not_fresh_at sm p /\ ~not_fresh_at sm out /\ p <> out` by
   (qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
    simp[compile_keccak256_bytesm_def, contextTheory.compile_alloc_buffer_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
    pop_assum (SUBST1_TAC o SYM) >> pop_assum (SUBST1_TAC o SYM) >>
    simp[NoAsms, emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
    qexists `STRING #"%" (toString sm.cs_next_var)` >>
    simp[NoAsms, not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
 `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid s` by metis_tac[loweringPostsTheory.expr_post_def] >>
 Cases_on `compile_alloc_buffer 32 sm` >>
 rename1 `compile_alloc_buffer 32 sm = (buf,si)` >>
 `buf.buf_operand = Var p /\ emitted_insts sm si =
    [mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]] /\
    fn_has_code sm si func` by
   (qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
    qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
    qpat_assum `fn_has_code sm sh func` mp_tac >>
    qpat_assum `emitted_insts sm sh = _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    simp[compile_keccak256_bytesm_def, contextTheory.compile_alloc_buffer_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
    gvs[emitted_insts_def] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
    gvs[mk_inst_def, DROP_LENGTH_APPEND,
      fn_has_code_def, emitted_blocks_def, IS_PREFIX_APPEND] >>
    metis_tac[APPEND_ASSOC]) >>
 `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
   (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
 `32 < dimword (:256)` by simp[dimword_def] >>
 drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
 `step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t'` by
   (qpat_x_assum `run_inst_seq (emitted_insts sm si) s = OK t'` mp_tac >>
    simp[run_inst_seq_def, AllCaseEqs()]) >>
 `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func)` by
   (`p = STRING #"%" (toString sm.cs_next_var)` by
      (qpat_assum `compile_alloc_buffer 32 sm = _` mp_tac >>
       qpat_assum `buf.buf_operand = Var p` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
       rpt strip_tac >> gvs[]) >> simp[]) >>
 `op_taint tn x = {} /\ allocas_from lo s` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    gvs[ptr_val_ok_def, loweringPostsTheory.post_value_type_def, is_word_type_def,
      ghost_inv_at_def]) >>
 qabbrev_tac `Ga = step_prov PG G
   (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) t'` >>
 qabbrev_tac `tna = step_taint
   (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) s t' tn` >>
 `ptr_covers Ga tna p t' 32` by
   (simp[Abbr `Ga`, Abbr `tna`] >>
    drule_all alloca_step_ptr_covers >> simp[]) >>
 `!q. x = Var q ==> q <> p` by metis_tac[] >>
 `eval_operand x t' = SOME w /\ op_taint tna x = {}` by
   (simp[Abbr `tna`] >> drule_all hash_alloca_old_operand >> simp[]) >>
 `lookup_var p t' = SOME w'` by
   (qpat_assum `eval_operand buf.buf_operand t' = _` mp_tac >>
    qpat_assum `buf.buf_operand = Var p` (fn th => rewrite_tac[th]) >>
    simp[eval_operand_def]) >>
 qabbrev_tac `z = mstore (w2n w') w t'` >>
 qabbrev_tac `Gs = step_prov PG Ga
   (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) z` >>
 qabbrev_tac `tns = step_taint
   (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) t' z tna` >>
 `ptr_covers Gs tns p z 32 /\
   (!i. w2n w' <= i /\ i < w2n w'+32 ==> i NOTIN tns.t_mem)` by
   (simp[Abbr `Gs`, Abbr `tns`, Abbr `z`] >>
    drule_all bodyPtrHashBuiltinsKeccakFixedTheory.hash_store_covered_clean >> simp[]) >>
 `lo <= s.vs_alloca_next` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
 `allocas_from lo t' /\ lo <= t'.vs_alloca_next` by
   (irule step_inst_allocas_from >>
    qexistsl [`ctx`, `0`, `mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]`, `s`] >>
    simp[step_inst_non_invoke, mk_inst_def]) >>
 `lo <= w2n w'` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
 `(!q. q <> p ==> lookup_var q t' = lookup_var q s /\
    FLOOKUP Ga q = FLOOKUP G q /\ op_taint tna (Var q) = op_taint tn (Var q)) /\
  (!i. ~(w2n w' <= i /\ i < w2n w'+32) ==> (i IN tna.t_mem <=> i IN tn.t_mem))` by
   (simp[Abbr `Ga`, Abbr `tna`] >>
    drule_all hash_alloca_exterior_effects >>
    disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >> simp[]) >>
 `step_inst_base (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) t' = OK z` by
   simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def, Abbr `z`] >>
 `m < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
 qabbrev_tac `hv = word_of_bytes T (0w:bytes32)
    (Keccak_256_w64 (mem_bytes_at (w2n w') m z.vs_memory))` >>
 qabbrev_tac `u = update_var out hv z` >>
 `step_inst_base (mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [out]) z = OK u` by
   (simp[Abbr `u`, Abbr `hv`] >> irule step_SHA3_bytes >>
    simp[eval_operand_def, Abbr `z`, mstore_def, lookup_var_def]) >>
 qabbrev_tac `Gh = step_prov PG Gs
   (mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [out]) u` >>
 qabbrev_tac `tnh = step_taint
   (mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [out]) z u tns` >>
 `Gs = Ga /\ tns = tna with t_mem := tna.t_mem DIFF {i | w2n w' <= i /\ i < w2n w'+32}` by
   (simp[Abbr `Gs`, Abbr `tns`, Abbr `z`] >>
    drule_all wordLoadStorePtrTheory.mstore_ghost_frame >> strip_tac >>
    simp[ptrDisciplineTheory.taint_component_equality] >>
    simp[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.imm_taint_def,
      mk_inst_def, mstore_def]) >>
 `Gh = DRESTRICT Gs (COMPL {out}) /\ tnh = tns with t_var := tns.t_var |+ (out,{})` by
   simp[Abbr `Gh`, Abbr `tnh`, Abbr `u`, bodyPtrHashBuiltinsKeccakTheory.hash_sha3_ghost] >>
 `!D. ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) s` by
   simp[prefix_alloca_inst_ok] >>
 `!D k. ptr_inst_ok D lo 0 ctx func Ga tna
     (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) (t' with vs_inst_idx := k)` by
   (rpt gen_tac >> irule ptr_inst_ok_mstore_tainted >>
    simp[ptr_covers_def, ptrDisciplineTheory.allocas_from_def,
      lookup_var_def] >>
    fs[ptr_covers_def, lookup_var_def]) >>
 `!D k. ptr_inst_ok D lo 0 ctx func Gs tns
     (mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [out]) (z with vs_inst_idx := k)` by
   suspend "sha3_check" >>
 suspend "finish"
QED

Resume method_id_hash_fixed_full_run[sha3_check]:
 rpt gen_tac >>
 `allocas_from lo (z with vs_inst_idx := k)` by
   (fs[Abbr `z`, mstore_def, allocas_from_def] >> first_assum MATCH_ACCEPT_TAC) >>
 `ptr_covers Gs tns p (z with vs_inst_idx := k) 32` by simp[] >>
 `!a i. lookup_var p (z with vs_inst_idx := k) = SOME a /\
    w2n a <= i /\ i < w2n a+32 ==> i NOTIN tns.t_mem` by
   (rpt strip_tac >>
    `a = w'` by fs[Abbr `z`, mstore_def, lookup_var_def] >> metis_tac[]) >>
 match_mp_tac (Q.INST [`lo0` |-> `0`] ptr_inst_ok_lower_bound_transport) >>
 conj_tac >- simp[] >>
 conj_tac >- first_assum MATCH_ACCEPT_TAC >>
 match_mp_tac (Q.SPECL [`D`, `ctx`, `func`, `Gs`, `tns`,
   `z with vs_inst_idx := k`, `sm.cs_next_id+2`, `p`, `out`, `m`, `0`]
   bodyPtrHashBuiltinsKeccakFixedTheory.hash_fixed_input_sha3_ok) >>
 rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume method_id_hash_fixed_full_run[finish]:
 rename1 `run_inst_seq (emitted_insts sm sh) s = OK typed_end` >>
 `run_inst_seq (emitted_insts sm sh) s = OK u` by
   (qpat_x_assum `run_inst_seq (emitted_insts sm sh) s = OK typed_end`
      (K all_tac) >> simp[run_inst_seq_def]) >>
 `typed_end = u` by
   (qpat_x_assum `run_inst_seq (emitted_insts sm sh) s = OK typed_end` mp_tac >>
    qpat_x_assum `run_inst_seq (emitted_insts sm sh) s = OK u` SUBST1_TAC >>
    simp[]) >>
 qpat_x_assum `typed_end = u` SUBST_ALL_TAC >>
 `same_blocks sm sh /\
  sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sh)` by
   (mp_tac (Q.INST [`sa` |-> `sm`, `sb` |-> `sh`, `x` |-> `x`,
      `m` |-> `m`, `op` |-> `hash`] keccak_suffix_shape) >> simp[]) >>
 `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sh ++ rest` by
   (qpat_assum `fn_has_code sm sh func`
      (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
    rename1 `lookup_block sh.cs_current_bb func.fn_blocks = SOME codebb` >>
    qpat_x_assum `isPREFIX sh.cs_current_insts codebb.bb_instructions`
      (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
    rename1 `codebb.bb_instructions = sh.cs_current_insts ++ code_tail` >>
    qexistsl_tac [`codebb`, `code_tail`] >>
    qpat_x_assum `same_blocks sm sh`
      (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
    simp_tac bool_ss [ASSUME ``s.vs_current_bb = sm.cs_current_bb``,
      GSYM (ASSUME ``sh.cs_current_bb = sm.cs_current_bb``),
      ASSUME ``lookup_block sh.cs_current_bb func.fn_blocks = SOME codebb``,
      ASSUME ``s.vs_inst_idx = LENGTH sm.cs_current_insts``,
      ASSUME ``codebb.bb_instructions = sh.cs_current_insts ++ code_tail``,
      ASSUME ``sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh``,
      GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
 `t'.vs_accounts = s.vs_accounts /\ t'.vs_transient = s.vs_transient /\
  t'.vs_immutables = s.vs_immutables /\ t'.vs_call_ctx = s.vs_call_ctx /\
  t'.vs_current_bb = s.vs_current_bb /\ t'.vs_halted = s.vs_halted /\
  s.vs_alloca_next <= t'.vs_alloca_next` by
   (qpat_x_assum `step_inst_base (mk_inst sm.cs_next_id ALLOCA _ _) s = OK t'`
      mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    simp[step_inst_base_def, mk_inst_def, eval_operand_def,
      exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
    gvs[update_var_def]) >>
 `compile_keccak256_bytesm x (LENGTH payload) sm = (hash,sh) /\
  LENGTH payload <= 32` by simp[] >>
 `(!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid a len. aid < sm.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!n a len. local_region cenv mid.scopes s n a len ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  pure_frame cenv func mid sm s u` by
    (mp_tac (Q.SPECL [`x`, `payload`, `sm`, `sh`, `s`, `hash`, `w`,
      `storage_trace_horizon ((mid:evaluation_state).storage_trace)`, `mid`]
      (Q.GENL [`val_op`, `bs`, `sa`, `sb`, `s`, `op`, `w`, `H`, `es`]
        (INST_TYPE [alpha |-> ``:256``] compile_keccak256_bytesm_frame))) >>
    impl_tac >- (rpt conj_tac >> simp[]) >>
    disch_then (qx_choose_then `frame_end` strip_assume_tac) >>
    `frame_end = u` by
      (qpat_x_assum `run_inst_seq (emitted_insts sm sh) s = OK frame_end` mp_tac >>
       qpat_assum `run_inst_seq (emitted_insts sm sh) s = OK u` SUBST1_TAC >> simp[]) >>
    qpat_x_assum `frame_end = u` SUBST_ALL_TAC >>
    rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
 `(!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q s /\
    FLOOKUP Gh q = FLOOKUP G q /\ op_taint tnh (Var q) = op_taint tn (Var q))` by
   (rpt strip_tac >> `q <> p /\ q <> out` by metis_tac[] >>
    simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
    simp[Abbr `tna`, step_taint_def, set_var_taint_def,
      out_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
 `tnh.t_mem SUBSET tn.t_mem` by
   (simp[pred_setTheory.SUBSET_DEF] >> qx_gen_tac `j` >> strip_tac >>
    Cases_on `w2n w' <= j /\ j < w2n w'+32` >>
    fs[] >> metis_tac[]) >>
 `(!j. j < w2n w' \/ w2n w'+32 <= j ==>
    (j IN tnh.t_mem <=> j IN tn.t_mem))` by
   (rpt strip_tac >>
    `~(w2n w' <= j /\ j < w2n w'+32)` by decide_tac >> fs[]) >>
 `(!a k. a+k <= w2n w' \/ w2n w'+32 <= a ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory)` by
   (rpt strip_tac >>
    simp[Abbr `u`, update_var_def, Abbr `z`] >>
    irule EQ_TRANS >>
    irule_at (Pos hd) valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
    simp[]) >>
 `(!n a len. local_region cenv mid.scopes s n a len ==>
    w2n w'+32 <= a \/ a+len <= w2n w')` by
   (rpt strip_tac >>
    `local_region cenv mid.scopes t' n a len` by
      (irule (Q.SPECL [`cenv`, `mid.scopes`, `sm`, `mid.scopes`,
        `s`, `t'`, `n`, `a`, `len`] local_region_frame_fwd) >>
       simp[] >> metis_tac[]) >>
    qpat_assum `!name b len. local_region cenv mid.scopes t' name b len ==> _`
      (qspecl_then [`n`, `a`, `len`] mp_tac) >>
    simp[regions_disjoint_def] >> decide_tac) >>
 `alloca_inv s /\ alloca_inv t' /\ local_ptrs_rel func cenv mid.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 `w2n w'+32 <= t'.vs_alloca_next` by
   (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
 `run_inst_seq_mem_ok (emitted_insts sm sh) s` by
   (simp[run_inst_seq_mem_ok_def] >>
    simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, memory_range_of_operands_def,
      mk_inst_def, eval_operand_def, Abbr `z`, mstore_def] >> decide_tac) >>
 `!id opc ops outs. (mk_inst id opc ops outs).inst_opcode = opc` by
   simp[mk_inst_def] >>
 `!D. inst_seq_ptr D lo ctx func PG G tn
    (emitted_insts sm sh) s Gh tnh` by
   (gen_tac >>
    qpat_x_assum `Gs = Ga` kall_tac >>
    qpat_x_assum `tns = tna with t_mem := _` kall_tac >>
    qpat_x_assum `Gh = DRESTRICT Gs (COMPL {out})` kall_tac >>
    qpat_x_assum `tnh = tns with t_var := _` kall_tac >>
    fs[inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
      exec_result_map_def, Abbr `Ga`, Abbr `tna`, Abbr `Gs`, Abbr `tns`,
      Abbr `Gh`, Abbr `tnh`]) >>
 `~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  s.vs_inst_idx+3 = LENGTH sh.cs_current_insts` by
   fs[Abbr `u`, Abbr `z`, update_var_def, mstore_def, same_blocks_def] >>
 `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables /\ u.vs_call_ctx = s.vs_call_ctx /\
  allocas_from lo u /\ lo <= u.vs_alloca_next` by
   (fs[Abbr `u`, Abbr `z`, update_var_def, mstore_def, allocas_from_def] >>
    rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
 `tnh.t_stor = tn.t_stor /\ tnh.t_trans = tn.t_trans /\ tnh.t_imm = tn.t_imm` by
   simp[Abbr `tnh`, Abbr `tns`, Abbr `tna`, step_taint_def,
     store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def] >>
 qabbrev_tac `fin = u with vs_inst_idx := s.vs_inst_idx+3` >>
 `!q. not_fresh_at sm q ==> lookup_var q fin = lookup_var q s /\
    FLOOKUP Gh q = FLOOKUP G q /\ op_taint tnh (Var q) = op_taint tn (Var q)` by
   fs[Abbr `fin`, lookup_var_def] >>
 `!a k. a+k <= w2n w' \/ w2n w'+32 <= a ==>
    mem_bytes_at a k fin.vs_memory = mem_bytes_at a k s.vs_memory` by
   (simp[Abbr `fin`] >> first_assum MATCH_ACCEPT_TAC) >>
 `allocas_from lo fin /\ lo <= fin.vs_alloca_next /\
  s.vs_alloca_next <= fin.vs_alloca_next` by simp[Abbr `fin`, allocas_from_def] >>
 `!D. stor_taint_ok_at D tnh fin <=> stor_taint_ok_at D tn s` by
   simp[stor_taint_ok_at_def, Abbr `fin`] >>
 `alloca_history func fin` by
   (mp_tac (Q.SPECL [`func`, `bb`, `s`, `emitted_insts sm sh`, `rest`, `u`]
      alloca_history_run_inst_seq) >>
    impl_tac >- (simp[EVERY_MEM] >> rpt strip_tac >>
      gvs[mk_inst_def, is_terminator_def]) >>
    simp[Abbr `fin`]) >>
 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK fin,Gh,tnh)` by
   (gen_tac >>
    `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn)
      (MAP (\i. (func.fn_name,i.inst_id) IN explicit)
        (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sh)))
      (OK (u with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sh)),Gh,tnh)` by
      (match_mp_tac (Q.SPECL [`emitted_insts sm sh`, `s`, `u`, `G`, `tn`,
         `Gh`, `tnh`, `ctx`, `func`, `bb`] run_inst_seq_gas_origin_ptr_path) >>
       rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
       simp[IS_PREFIX_APPEND] >> qexists_tac `rest` >> first_assum MATCH_ACCEPT_TAC) >>
    qpat_x_assum `gas_origin_ptr_path _ _ (MAP _ _) _` mp_tac >>
    simp[mk_inst_def, Abbr `fin`, ADD_COMM]) >>
 `sm.cs_next_var <= sh.cs_next_var` by metis_tac[method_id_hash_grows] >>
 `local_ptrs_reserved cenv sh` by
   (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
 `return_buf_frame d cenv sh fin` by
   (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sm`] >>
    simp[] >> rpt strip_tac >>
    qpat_assum `!q. not_fresh_at sm q ==> lookup_var q fin = lookup_var q s /\ _`
      (qspec_then `x` mp_tac) >> simp[]) >>
 `locals_kept cenv mid mid s u` by
   (irule locals_kept_regions >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
 `locals_kept cenv mid mid s fin /\ pure_frame cenv func mid sm s fin` by
   (qpat_assum `pure_frame cenv func mid sm s u` mp_tac >>
    fs[Abbr `fin`, pure_frame_def]) >>
 `ghost_kept_at lo cenv mid sm G tn s Gh tnh` by
   (simp[ghost_kept_at_def] >> fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid fin /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gh tnh fin` by
   (gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
    impl_tac >- simp[] >> strip_tac >>
    `stmt_state_rel H ctx func cenv cx mid s /\
     storage_well_formed_on cx mid (FST H)` by
      fs[loweringPostsTheory.expr_post_def] >>
    `stmt_state_rel H ctx func cenv cx mid u` by
      (mp_tac (Q.SPECL [`x`, `payload`, `sm`, `sh`, `s`, `hash`, `w`, `H`, `mid`]
        (Q.GENL [`val_op`, `bs`, `sa`, `sb`, `s`, `op`, `w`, `H`, `es`]
          (INST_TYPE [alpha |-> ``:256``] compile_keccak256_bytesm_frame))) >>
       impl_tac >- (rpt conj_tac >> simp[]) >>
       disch_then (qx_choose_then `allH_end` strip_assume_tac) >>
       `allH_end = u` by
         (qpat_x_assum `run_inst_seq (emitted_insts sm sh) s = OK allH_end` mp_tac >>
          qpat_assum `run_inst_seq (emitted_insts sm sh) s = OK u` SUBST1_TAC >> simp[]) >>
       qpat_x_assum `allH_end = u` SUBST_ALL_TAC >> first_assum MATCH_ACCEPT_TAC) >>
    conj_tac >- simp[Abbr `fin`, stmt_state_rel_inst_idx] >>
    conj_tac >- simp[] >>
    `stor_taint_ok_at (DF H) tnh fin` by fs[ghost_inv_at_def] >>
    match_mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `s`, `start` |-> `w2n (w':256 word)`,
      `nb` |-> `32`, `func` |-> `func`, `G` |-> `G`, `tn` |-> `tn`]
      unwrap_slot_copy_ghost_inv_at) >>
    rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >> simp[] >>
    first_assum MATCH_ACCEPT_TAC) >>
 `op_taint tnh hash = {} /\ op_prov Gh hash = NONE` by
   simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
 qexistsl_tac [`fin`, `Gh`, `tnh`, `bs`] >>
 simp[Abbr `fin`, lookup_var_def] >> metis_tac[]
QED

Finalise method_id_hash_fixed_full_run

(* end *)
