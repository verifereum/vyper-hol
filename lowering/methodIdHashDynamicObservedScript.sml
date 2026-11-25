(* The selected bytestring MethodId hash run, with its counted landing. *)
Theory methodIdHashDynamicObserved
Ancestors
  stateRelProj
  exprSimMemDefs abiBuiltinAllocation bodyFullUnwrapRun exprSimHash bodyFullGhostFrame fragGasSeqPtr gasOutcomeFullCompose exprPtrCtorImmStore
  bodyMemBiMethodIdSuffix bodyPtrSignedConvertSourceFrame bodyMemoryDefs
  allocaHistoryFragment exprSimHashBoundary exprOperandVar bodyPtrHashBuiltinsCases bodyPtrHashBuiltinsKeccakBytesRun
  bodyPtrDefs exprSimDefs exprSimProps exprSimHypsDefs exprLoweringProps ptrDiscipline exprPtrUnwrapScalarEdges bodyPtrHashBuiltinsBoundary
  builtinHashing compileEnv loweringStateRelDefs vyperStorageTrace memLocDefs ptrSafeRun contextCodegenRel codegenRel
  venomState venomInst venomExecSemantics finite_map list rich_list words vyperStorageFootprint arithmetic fragExec

Theorem method_id_hash_dynamic_observed:
 !DF lo d explicit ctx func PG cenv cx e es sa sm sh s0 st0 mid v x s G tn hash bty.
 expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
 is_bytestring_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
 value_has_type (BaseTV bty) v /\
 lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
 compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
 fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ local_ptrs_reserved cenv sa /\
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
 (?raw. run_inst_seq (emitted_insts sm sh) s = OK raw /\
        u = (raw with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
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
   (aid < sm.cs_next_id ==> !i. a <= i /\ i < a+len ==>
     EL i u.vs_memory = EL i s.vs_memory)) /\
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
 `compile_keccak256_bytes x sm = (hash,sh)` by
   metis_tac[method_id_hash_as_keccak] >>
 `?len dst out. hash = Var out /\
    emitted_insts sm sh =
      [mk_inst sm.cs_next_id MLOAD [x] [len];
       mk_inst (sm.cs_next_id+1) ADD [x; Lit 32w] [dst];
       mk_inst (sm.cs_next_id+2) SHA3 [Var dst; Var len] [out]] /\
    ~not_fresh_at sm len /\ ~not_fresh_at sm dst /\ ~not_fresh_at sm out /\
    ALL_DISTINCT [len;dst;out]` by
   (qpat_x_assum `compile_keccak256_bytes _ _ = _` mp_tac >>
    simp[compile_keccak256_bytes_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
    strip_tac >>
    pop_assum (SUBST1_TAC o SYM) >>
    pop_assum (SUBST1_TAC o SYM) >>
    simp[NoAsms, emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
    qexistsl [`STRING #"%" (toString sm.cs_next_var)`,
      `STRING #"%" (toString (sm.cs_next_var+1))`] >>
    simp[NoAsms, not_fresh_at_def]) >>
 `ptr_val_ok cx (expr_type e) v x G tn s` by
   metis_tac[loweringPostsTheory.post_value_type_bytestring] >>
 `?p b payload base cap. x = Var p /\ eval_operand x s = SOME (n2w b) /\
    FLOOKUP G p = SOME (base,cap) /\ base <= b /\
    b+32+LENGTH payload <= base+cap /\ op_taint tn x = {} /\
    (!i. b <= i /\ i < b+32+LENGTH payload ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH payload) /\
    mem_bytes_at (b+32) (LENGTH payload) s.vs_memory = payload /\
    b+32 < dimword (:256) /\ LENGTH payload < dimword (:256) /\
    b+32+LENGTH payload <= s.vs_alloca_next` by suspend "payload" >>
 `not_fresh_at sm p` by
   (drule_at (Pos hd) compile_lower_value_var >> simp[] >> metis_tac[]) >>
 `ALL_DISTINCT [p;len;dst;out]` by
   (fs[ALL_DISTINCT] >> metis_tac[]) >>
 `allocas_from lo s` by
   (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
 `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sh) s
    (DRESTRICT (DRESTRICT G (COMPL {len}) |+ (dst,(base',cap))) (COMPL {out}))
    (tn with t_var := tn.t_var |+ (len,{}) |+ (dst,{}) |+ (out,{}))` by suspend "pointer" >>
 suspend "endpoint"
QED

Resume method_id_hash_dynamic_observed[endpoint]:
 `!q. x = Var q ==> not_fresh_at sm q` by simp[] >>
 drule_all compile_keccak256_bytes_run >> strip_tac >>
 `t' = t` by metis_tac[exec_result_11] >>
 qpat_x_assum `t' = t` SUBST_ALL_TAC >>
 qabbrev_tac `Gh = DRESTRICT (DRESTRICT G (COMPL {len}) |+ (dst,(base',cap))) (COMPL {out})` >>
 qabbrev_tac `tnh = tn with t_var := tn.t_var |+ (len,{}) |+ (dst,{}) |+ (out,{})` >>
 `!q. not_fresh_at sm q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP Gh q = FLOOKUP G q /\ op_taint tnh (Var q) = op_taint tn (Var q)` by
   (rpt strip_tac >>
    `q <> len /\ q <> dst /\ q <> out` by metis_tac[] >>
    simp[Abbr `Gh`, Abbr `tnh`, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]) >>
 `same_blocks sm sh /\ sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh` by
   (qpat_x_assum `compile_keccak256_bytes _ _ = _` mp_tac >>
    simp[NoAsms, compile_keccak256_bytes_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
    strip_tac >> pop_assum (SUBST1_TAC o SYM) >>
    simp[NoAsms, same_blocks_def, emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
 qabbrev_tac `u = t with vs_inst_idx := LENGTH sh.cs_current_insts` >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid Gh tnh u` by
   (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
    qexistsl [`G`, `mid`, `s`, `sm`, `tn`] >>
    simp[Abbr `u`, Abbr `tnh`] >>
    qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
    simp[venom_state_component_equality] >> strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
 `run_inst_seq_mem_ok (emitted_insts sm sh) s` by
   (irule method_id_bytes_hash_mem_ok >>
    qexistsl [`b`, `LENGTH (payload:word8 list)`, `hash`, `x`] >>
    simp[MOD_LESS] >> decide_tac) >>
 `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = s.vs_current_bb` by
   (qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
    simp[venom_state_component_equality]) >>
 `u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by
   (qpat_assum `t with vs_vars := _ = s` mp_tac >>
    simp[Abbr `u`, venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
 `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `u`] >>
 `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q s /\
      FLOOKUP Gh q = FLOOKUP G q /\ op_taint tnh (Var q) = op_taint tn (Var q)` by
   (rpt strip_tac >>
    simp[NoAsms, Abbr `u`, lookup_var_def] >>
    fs[lookup_var_def]) >>
 `sm.cs_next_var <= sh.cs_next_var /\ sm.cs_next_id <= sh.cs_next_id` by
   (qpat_assum `compile_method_id_hash _ _ _ = _`
      (mp_then Any strip_assume_tac method_id_hash_grows) >> simp[]) >>
 `local_ptrs_reserved cenv sh` by
   (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
 `return_buf_frame d cenv sh u` by
   (irule return_buf_frame_frame >> qexistsl [`cenv`, `s`, `sm`] >> simp[]) >>
 `locals_kept cenv mid mid s u /\ pure_frame cenv func mid sm s u` by
   (simp[loweringPostsTheory.pure_frame_mem_eq] >> irule locals_kept_mem >> simp[]) >>
 `ghost_kept_at lo cenv mid sm G tn s Gh tnh` by
   (simp[ghost_kept_at_def, Abbr `tnh`] >> metis_tac[]) >>
 `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
   (qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
    first_assum ACCEPT_TAC) >>
 `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
 `alloca_history func u` by
   (simp[NoAsms, Abbr `u`] >>
    irule emitted_alloca_history >> simp[] >>
    qexistsl [`emitted_insts sm sh`, `s`, `sm`] >>
    fs[same_blocks_def, mk_inst_def, is_terminator_def]) >>
 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,Gh,tnh)` by
   (gen_tac >> simp[NoAsms, Abbr `u`] >>
    irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
    qexistsl [`emitted_insts sm sh`, `sm`] >>
    fs[same_blocks_def, mk_inst_def, is_terminator_def] >>
    rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
    `MEM i (emitted_insts sm sh)` by
      (qpat_assum `emitted_insts sm sh = _` (pure_once_rewrite_tac o single) >>
       qpat_assum `[_;_;_] = _` (pure_once_rewrite_tac o single) >> simp[]) >>
    qpat_x_assum `MEM i (emitted_insts sm sh)` mp_tac >>
    qpat_assum `emitted_insts sm sh = _` (pure_once_rewrite_tac o single) >>
    PURE_REWRITE_TAC[MEM] >> strip_tac >> gvs[]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\
    storage_well_formed_on cx mid (FST H)` by
   (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    `stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H)` by
      (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
    simp[] >> irule stmt_state_rel_readonly_vars_pc >>
    qexistsl_tac [`s`, `sm`] >> simp[] >> metis_tac[]) >>
 `eval_operand hash u = SOME
    (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))` by
   (simp[NoAsms, Abbr `u`, ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
    first_assum ACCEPT_TAC) >>
 `op_taint tnh hash = {} /\ op_prov Gh hash = NONE` by
   (qpat_assum `hash = Var out` SUBST1_TAC >>
    simp[Abbr `tnh`, Abbr `Gh`, op_taint_def, op_prov_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
 `~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
  u.vs_inst_idx = LENGTH sh.cs_current_insts /\ s.vs_alloca_next <= u.vs_alloca_next` by
   fs[Abbr `u`, same_blocks_def] >>
 qexistsl [`u`, `Gh`, `tnh`, `bs`] >> conj_tac
 >- (qexists_tac `t` >> simp[Abbr `u`]) >>
 simp[]
QED

Resume method_id_hash_dynamic_observed[payload]:
 Cases_on `bty` >> gvs[is_bytestring_type_def] >>
 Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
 >~ [`expr_type e = BaseT (BytesT bd)`]
 >- (rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     drule_at (Pos hd) hash_dynamic_post_view >> simp[] >> strip_tac >>
     drule_at (Pos hd) hash_dynamic_bytes_operand >> simp[is_word_type_def] >> strip_tac >>
     qexistsl [`p`, `b`, `l`] >>
     gvs[ptr_covers_def, eval_operand_def] >>
     qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[exprSimMemDefsTheory.expr_store_bound_def] >>
     simp[is_word_type_def, val_store_size_def, eval_operand_def] >>
     qspec_then `LENGTH l` mp_tac abi_builtin_word_size_capacity >> decide_tac) >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 drule_at (Pos hd) hash_string_post_view >> simp[] >> strip_tac >>
 drule_at (Pos hd) hash_string_operand >> simp[is_word_type_def] >> strip_tac >>
 qexistsl [`p`, `b`, `MAP (n2w o ORD) s'`] >>
 gvs[ptr_covers_def, eval_operand_def] >>
 qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
 pure_rewrite_tac[exprSimMemDefsTheory.expr_store_bound_def] >>
 simp[is_word_type_def, val_store_size_def, eval_operand_def] >>
 qspec_then `LENGTH s'` mp_tac abi_builtin_word_size_capacity >> decide_tac
QED

Resume method_id_hash_dynamic_observed[pointer]:
 gen_tac >>
 qpat_x_assum `x = Var p` SUBST_ALL_TAC >>
 qpat_x_assum `s.vs_inst_idx = _` kall_tac >>
 `b < dimword (:256)` by decide_tac >>
 `w2n (n2w b:bytes32) = b` by simp[] >>
 `ptr_covers G tn p s 32` by
   (simp[ptr_covers_def] >> qexists `n2w b` >>
    gvs[eval_operand_def] >> decide_tac) >>
 `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
   (rpt gen_tac >> disch_tac >>
    qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
 `mload b s = n2w (LENGTH payload)` by fs[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
 `step_inst_base (mk_inst sm.cs_next_id MLOAD [Var p] [len]) s =
    OK (update_var len (n2w (LENGTH payload)) s)` by
   (pure_once_rewrite_tac[step_inst_base_def] >>
    gvs[mk_inst_def, exec_read1_def]) >>
 simp[Once inst_seq_ptr_def] >>
 conj_tac >- (irule ptr_inst_ok_mload_lo >> simp[]) >>
 `!i. w2n (n2w b:bytes32) <= i /\ i < w2n (n2w b:bytes32)+32 ==> i NOTIN tn.t_mem` by simp[] >>
 `step_prov PG G (mk_inst sm.cs_next_id MLOAD [Var p] [len])
    (update_var len (n2w (LENGTH payload)) s) = DRESTRICT G (COMPL {len}) /\
  step_taint (mk_inst sm.cs_next_id MLOAD [Var p] [len]) s
    (update_var len (n2w (LENGTH payload)) s) tn = tn with t_var := tn.t_var |+ (len,{})` by
   (irule hash_mload_ghost >> qexists `n2w b` >> simp[]) >>
 simp[] >>
 qabbrev_tac `s1 = update_var len (n2w (LENGTH payload)) s with vs_inst_idx := SUC s.vs_inst_idx` >>
 qabbrev_tac `G1 = DRESTRICT G (COMPL {len})` >>
 qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (len,{})` >>
 `eval_operand (Var p) s1 = SOME (n2w b) /\
  eval_operand (Var len) s1 = SOME (n2w (LENGTH payload)) /\
  FLOOKUP G1 p = SOME (base',cap) /\ op_taint tn1 (Var p) = {}` by
   gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
     eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
     FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
 `step_inst_base (mk_inst (sm.cs_next_id+1) ADD [Var p;Lit 32w] [dst]) s1 =
    OK (update_var dst (n2w b+32w) s1)` by
   (pure_once_rewrite_tac[step_inst_base_def] >>
    simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
 simp[Once inst_seq_ptr_def] >>
 conj_tac >-
   (irule ptr_inst_ok_copy_arith >>
    simp[op_taint_def, Abbr `s1`, allocas_from_def, update_var_def]) >>
 simp[hash_add_ghost] >>
 qabbrev_tac `s2 = update_var dst (n2w b+32w) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
 qabbrev_tac `G2 = G1 |+ (dst,(base',cap))` >>
 `step_prov PG G1 (mk_inst (sm.cs_next_id+1) ADD [Var p;Lit 32w] [dst])
    (update_var dst (n2w b+32w) s1) = G2` by
   simp[Abbr `G2`, step_prov_def, set_prov_def, out_prov_def,
     first_prov_def, op_prov_def, mk_inst_def] >>
 simp[] >>
 qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (dst,{})` >>
 `eval_operand (Var dst) s2 = SOME (n2w (b+32)) /\
  eval_operand (Var len) s2 = SOME (n2w (LENGTH payload)) /\
  FLOOKUP G2 dst = SOME (base',cap) /\
  op_taint tn2 (Var dst) = {} /\ op_taint tn2 (Var len) = {}` by
   gvs[Abbr `s2`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`, ALL_DISTINCT,
     eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
     FLOOKUP_UPDATE, word_add_n2w] >>
 `!i. b+32 <= i /\ i < b+32+LENGTH payload ==> i NOTIN tn2.t_mem` by
   (simp[Abbr `tn2`, Abbr `tn1`] >> rpt gen_tac >> disch_tac >>
    qpat_x_assum `!i. b <= i /\ i < b+32+LENGTH payload ==> _` irule >> decide_tac) >>
 `step_inst_base (mk_inst (sm.cs_next_id+2) SHA3 [Var dst;Var len] [out]) s2 =
    OK (update_var out (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at (b+32) (LENGTH payload) s2.vs_memory))) s2)` by
   (irule step_SHA3_bytes >> simp[]) >>
 simp[Once inst_seq_ptr_def] >>
 conj_tac >-
   (`access_ok lo G2 func (mk_inst (sm.cs_next_id+2) SHA3 [Var dst;Var len] [out]) s2` by
      (simp[access_ok_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, memory_range_of_operands_def,
         mem_read_ops_def, mk_inst_def] >>
       rpt strip_tac >> qexistsl [`dst`, `base'`, `cap`] >> simp[] >> decide_tac) >>
    `taint_ok func tn2 (mk_inst (sm.cs_next_id+2) SHA3 [Var dst;Var len] [out]) s2` by
      (irule hash_sha3_taint >> simp[]) >>
    qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac >>
    simp[ptr_inst_ok_def, step_inst_non_invoke] >>
    simp[Abbr `s2`, Abbr `s1`, update_var_def, allocas_from_def]) >>
 simp[bodyPtrHashBuiltinsKeccakTheory.hash_sha3_ghost, inst_seq_ptr_def, Abbr `G2`, Abbr `G1`,
   Abbr `tn2`, Abbr `tn1`]
QED

Finalise method_id_hash_dynamic_observed
