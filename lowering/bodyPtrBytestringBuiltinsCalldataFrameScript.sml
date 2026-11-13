(* Semantic framing of writes into the allocation obtained by runtime replay. *)
Theory bodyPtrBytestringBuiltinsCalldataFrame
Ancestors
  bodyPtrBytestringBuiltinsCalldataRuntime exprSimCalldataSlice
  exprSimLiteralBuffer exprLoweringProps loweringSlice immutableMemoryFrame
  compileEnv loweringStateRelDefs venomState list finite_map loweringPosts emitHelperProps words
  bodyPtrBytestringBuiltinsExternalSlice venomExecSemantics venomInst
  exprSimProps varsExt exprSimAlloc fragExec loweringHalt
  bodyPtrBytestringBuiltinsCalldataReserved freshWrites emitHelper
  bodyPtrBytestringBuiltinsBounds context

(* Allocation changes only variables and the allocation book-keeping. *)
Theorem alloca_storage_projections:
  step_inst_base (mk_inst id ALLOCA [Lit szw] [out]) s = OK u ==>
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[] >> simp[update_var_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[] >> simp[update_var_def]
QED

Theorem allocated_bytes_write_state_rel:
  stmt_state_rel H ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,N) /\
  LENGTH data = n /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  stmt_state_rel H ctx fn cenv cx es
    (mstore b (n2w n)
      (write_memory_with_expansion (b + 32) data s))
Proof
  strip_tac >> gvs[] >> irule bytes_buffer_write_state_rel >>
  simp[] >> conj_tac
  >- (qexists_tac `N` >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!name p len. _` drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s /\
   immutable_alloca_sep fn cenv cx es s` by fs[stmt_state_rel_def, state_rel_def] >>
  `(mstore b (n2w (LENGTH data))
      (write_memory_with_expansion (b + 32) data s)).vs_data_section = s.vs_data_section` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  simp[immutable_mstore_capacity, immutable_write_memory_capacity] >>
  suspend "immutable"
QED

Resume allocated_bytes_write_state_rel[immutable]:
  rpt strip_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >>
  disch_then (drule_all o CONJUNCT2) >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b N` by
    (qpat_x_assum `!inst b sz. _` drule_all >> simp[]) >>
  irule bytes_buffer_write_frame >>
  fs[regions_disjoint_def] >> decide_tac
QED
Finalise allocated_bytes_write_state_rel

Theorem allocated_bytes_write_local_windows:
  LENGTH data = n /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  !name p len. local_region cenv es.scopes s name p len ==>
    mem_bytes_at p len
      (mstore b (n2w n) (write_memory_with_expansion (b + 32) data s)).vs_memory =
    mem_bytes_at p len s.vs_memory
Proof
  strip_tac >> gvs[] >> rpt strip_tac >> irule bytes_buffer_write_frame >>
  qpat_x_assum `!name p len. _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem allocated_bytes_write_locals_kept:
  LENGTH data = n /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  locals_kept cenv es es s
    (mstore b (n2w n)
      (write_memory_with_expansion (b + 32) data s))
Proof
  strip_tac >> gvs[] >> irule locals_kept_regions >> rpt strip_tac >>
  irule bytes_buffer_write_frame >>
  qpat_x_assum `!name p len. _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem calldata_copy_store_runtime:
  emit_void CALLDATACOPY [dst;src;cnt] sa = ((),sm) /\
  emit_void MSTORE [root;cnt] sm = ((),sb) /\
  eval_operand dst s = SOME wd /\ w2n wd = b + 32 /\
  eval_operand root s = SOME wb /\ w2n wb = b /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w n) /\
  a < dimword (:256) /\ n < dimword (:256) /\
  a + n <= LENGTH s.vs_call_ctx.cc_calldata ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore b (n2w n)
      (write_memory_with_expansion (b + 32)
        (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s))
Proof
  strip_tac >>
  qpat_assum `emit_void CALLDATACOPY _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    simp[emitted_insts_def, DROP_APPEND1] >>
  `TAKE n (DROP a s.vs_call_ctx.cc_calldata ++ REPLICATE n 0w) =
    TAKE n (DROP a s.vs_call_ctx.cc_calldata)` by
    (irule TAKE_APPEND1 >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATACOPY [dst;src;cnt] []) s =
    OK (write_memory_with_expansion (b + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, w2n_n2w] >>
  `!op. eval_operand op (write_memory_with_expansion (b + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def,
      write_memory_with_expansion_def, write_memory_def, expand_memory_def]) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [root;cnt] [])
      (write_memory_with_expansion (b + 32)
        (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s) =
    OK (mstore (w2n wb) (n2w n) (write_memory_with_expansion (b + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s))` by
    (irule step_MSTORE >> simp[]) >>
  qpat_x_assum `step_inst_base (mk_inst _ MSTORE _ _) _ = _` mp_tac >>
  simp[run_inst_seq_def]
QED

Theorem calldata_copy_store_semantic:
  emit_void CALLDATACOPY [dst;src;cnt] sa = ((),sm) /\
  emit_void MSTORE [root;cnt] sm = ((),sb) /\
  eval_operand dst s = SOME wd /\ w2n wd = b + 32 /\
  eval_operand root s = SOME wb /\ w2n wb = b /\
  eval_operand src s = SOME (n2w a) /\ eval_operand cnt s = SOME (n2w n) /\
  a < dimword (:256) /\ n < dimword (:256) /\
  a + n <= LENGTH s.vs_call_ctx.cc_calldata /\
  stmt_state_rel H ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,N) /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = mstore b (n2w n) (write_memory_with_expansion (b + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s) /\
    stmt_state_rel H ctx fn cenv cx es t /\
    val_in_memory (BaseTV (BytesT (Dynamic bound)))
      (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) b t.vs_memory /\
    locals_kept cenv es es s t /\ t.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all calldata_copy_store_runtime >> strip_tac >>
  `LENGTH (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) = n` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  qexists_tac `mstore b (n2w n) (write_memory_with_expansion (b + 32)
    (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s)` >>
  simp[] >> conj_tac
  >- (irule allocated_bytes_write_state_rel >> simp[] >> qexistsl_tac [`N`,`inst`] >> simp[] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qspec_then `b` (qspec_then `TAKE n (DROP a s.vs_call_ctx.cc_calldata)` mp_tac)
        bytes_buffer_write_encoding >> simp[]) >>
  irule allocated_bytes_write_locals_kept >> simp[] >>
  qexists_tac `N` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem calldata_size_bounds_semantic:
  emit_op CALLDATASIZE [] sa = (limit,sm) /\
  compile_assert_slice_bounds start (Lit (n2w n)) limit sm = ((),sb) /\
  stmt_state_rel H ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  eval_operand start s = SOME (n2w a) /\
  a < dimword (:256) /\ n < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata ==>
  ?v q. run_inst_seq (emitted_insts sa sm) s = OK v /\
    run_inst_seq (emitted_insts sm sb) v = OK q /\
    q = s with vs_vars := q.vs_vars /\
    stmt_state_rel H ctx fn cenv cx es q /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `sm.cs_next_var = SUC sa.cs_next_var /\
   limit = Var (STRING #"%" (toString sa.cs_next_var))` by
    (qpat_assum `emit_op _ _ _ = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all calldata_size_reserved_runtime >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `eval_operand start u = SOME (n2w a)` by simp[] >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  `!op z. MEM op [start;Lit (n2w n);limit] /\ op = Var z ==>
    not_fresh_at sm z` by
    (simp[] >> rpt strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     simp[not_fresh_at_def]) >>
  `LENGTH u.vs_call_ctx.cc_calldata = LENGTH s.vs_call_ctx.cc_calldata` by
    simp[update_var_def] >>
  drule_all slice_bounds_reserved_natural_runtime >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) u = OK p` by fs[] >>
  `p = s with vs_vars := p.vs_vars` by
    (qpat_x_assum `p = u with vs_vars := _` mp_tac >> simp[update_var_def]) >>
  suspend "frame"
QED

Resume calldata_size_bounds_semantic[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x p = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `stmt_state_rel H ctx fn cenv cx es p` by
    (irule stmt_state_rel_reserved_vars_update >>
     qexistsl_tac [`s`,`sa`] >> simp[]) >>
  qexistsl_tac [`u`,`p`] >> simp[] >> first_assum ACCEPT_TAC
QED
Finalise calldata_size_bounds_semantic


(* The successful calldata slice in the 0.5.0b1 order (size, bounds, buffer,
   copy, length store), replayed semantically from the entry state.  Every
   witness is fixed by the runtime: the state relation is the only fact that
   depends on H. *)
Theorem compile_slice_calldata_semantic:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel H ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 + n <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) ==>
  ?s1 s2 s3 s4 data limit q r u w root p zf.
    emit_op CALLDATASIZE [] sa = (limit,s1) /\
    compile_assert_slice_bounds start (Lit (n2w n)) limit s1 = ((),s2) /\
    compile_slice_out_buf N s2 = ((out,data),s3) /\
    out = Var root /\ data = Var p /\
    run_inst_seq (emitted_insts s1 s2)
      (update_var (STRING #"%" (toString sa.cs_next_var))
        (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s) = OK q /\
    r = q with vs_inst_idx := LENGTH s2.cs_current_insts /\
    stmt_state_rel H ctx fn cenv cx es r /\
    r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
    r.vs_fmp = s.vs_fmp /\
    step_inst_base (mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)] [root]) r = OK u /\
    lookup_var root u = SOME w /\
    MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts fn) /\
    sa.cs_next_id <= s2.cs_next_id /\ s2.cs_next_id < sb.cs_next_id /\
    local_ptrs_reserved cenv s2 /\ w2n w + N < dimword (:256) /\
    zf = (mstore (w2n w) (n2w n)
      (write_memory_with_expansion (w2n w + 32)
        (TAKE n (DROP a s.vs_call_ctx.cc_calldata))
        ((update_var p (w + 32w) u) with vs_inst_idx := r.vs_inst_idx + 2)))
      with vs_inst_idx := LENGTH sb.cs_current_insts /\
    stmt_state_rel H ctx fn cenv cx es zf /\
    val_in_memory (BaseTV (BytesT (Dynamic bound)))
      (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) (w2n w) zf.vs_memory /\
    eval_operand out zf = SOME w /\
    FLOOKUP zf.vs_allocas s2.cs_next_id = SOME (w2n w,N) /\
    (!x val. not_fresh_at sa x /\ lookup_var x s = SOME val ==>
      lookup_var x zf = SOME val) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP zf.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    locals_kept cenv es es s zf /\
    zf.vs_accounts = s.vs_accounts /\ zf.vs_transient = s.vs_transient /\
    zf.vs_call_ctx = s.vs_call_ctx /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes zf name b len ==>
      regions_disjoint (w2n w) N b len) /\
    pure_frame cenv fn es sa s zf
Proof
  strip_tac >>
  drule compile_slice_calldata_stages >> strip_tac >>
  qpat_assum `compile_slice_out_buf _ _ = _`
    (strip_assume_tac o MATCH_MP compile_slice_out_buf_compiler_parts) >>
  rename1 `compile_alloc_buffer N s2 = (buf,sm)` >>
  rename1 `emit_op ADD [Var root; Lit 32w] sm = (Var p,s3)` >>
  qpat_x_assum `out = Var _` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var _` SUBST_ALL_TAC >>
  drule_all calldata_size_bounds_semantic >> strip_tac >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (qpat_assum `emit_op CALLDATASIZE _ _ = (limit,s1)`
       (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `compile_assert_slice_bounds _ _ _ _ = _`
       (strip_assume_tac o MATCH_MP compile_assert_slice_bounds_layout) >>
     simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `v = update_var (STRING #"%" (toString sa.cs_next_var))
     (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s` by
    (drule_all calldata_size_reserved_runtime >>
     disch_then (qspec_then `s` strip_assume_tac) >> gvs[]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_fmp = s.vs_fmp /\ q.vs_memory = s.vs_memory /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient` by
    (qpat_x_assum `q = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qabbrev_tac `r = q with vs_inst_idx := LENGTH s2.cs_current_insts` >>
  `stmt_state_rel H ctx fn cenv cx es r` by simp[Abbr `r`, stmt_state_rel_inst_idx] >>
  `cs_extends sa s2 /\ cs_extends s2 sb /\ cs_extends sm sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code s2 sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code s2 sm fn /\ fn_has_code sm sb fn` by metis_tac[fn_has_code_split] >>
  drule_all slice_buffer_allocation_runtime >> strip_tac >>
  suspend "alloc"
QED

Resume compile_slice_calldata_semantic[alloc]:
  `root = STRING #"%" (toString s2.cs_next_var)` by gvs[] >>
  qpat_x_assum `root = _` SUBST_ALL_TAC >>
  `MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
     [STRING #"%" (toString s2.cs_next_var)]) (fn_insts fn)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `sm.cs_next_id <= sb.cs_next_id /\ p = STRING #"%" (toString sm.cs_next_var)` by
    (qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  suspend "add"
QED

Resume compile_slice_calldata_semantic[add]:
  qpat_assum `compile_alloc_buffer _ _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> p` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x /\ not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `u.vs_accounts = r.vs_accounts /\ u.vs_transient = r.vs_transient /   u.vs_call_ctx = r.vs_call_ctx` by
    (drule alloca_storage_projections >> simp[]) >>
  `u.vs_labels = r.vs_labels` by
    (qpat_x_assum `step_inst_base _ r = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
     every_case_tac >> rw[] >> simp[update_var_def]) >>
  qabbrev_tac `t0 = (update_var p (w + 32w) u) with vs_inst_idx := r.vs_inst_idx + 2` >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /     lookup_var x t0 = lookup_var x s` by
    (gen_tac >> strip_tac >>
     `lookup_var x u = lookup_var x r` by metis_tac[] >>
     `x <> p` by metis_tac[] >>
     `lookup_var x q = lookup_var x s` by metis_tac[] >>
     fs[Abbr `t0`, Abbr `r`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `stmt_state_rel H ctx fn cenv cx es t0` by
    (simp[Abbr `t0`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_reserved_vars_update >> qexistsl_tac [`u`,`sm`] >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> `x <> p` by metis_tac[] >> simp[]) >>
  `!X. (!x. not_fresh_at sa x ==> lookup_var x X = lookup_var x s) ==>
     !name b len. local_region cenv es.scopes X name b len <=>
       local_region cenv es.scopes s name b len` by
    (rpt strip_tac >> simp[local_region_def] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  suspend "copy"
QED

Resume compile_slice_calldata_semantic[copy]:
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w + 32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `t0.vs_labels = s.vs_labels /\ t0.vs_call_ctx = s.vs_call_ctx /\
   t0.vs_memory = s.vs_memory /\ t0.vs_allocas = u.vs_allocas /\
   t0.vs_accounts = s.vs_accounts /\ t0.vs_transient = s.vs_transient` by
    (simp[Abbr `t0`, Abbr `r`, update_var_def] >> fs[Abbr `r`]) >>
  `eval_operand (Var p) t0 = SOME (w + 32w) /\
   eval_operand (Var (STRING #"%" (toString s2.cs_next_var))) t0 = SOME w /\
   eval_operand (Lit (n2w n)) t0 = SOME (n2w n)` by
    (gvs[Abbr `t0`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]) >>
  `eval_operand start t0 = SOME (n2w a)` by
    (Cases_on `start` >> fs[eval_operand_def] >> metis_tac[]) >>
  `(mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString s2.cs_next_var)]).inst_opcode = ALLOCA /\
   FLOOKUP t0.vs_allocas (mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString s2.cs_next_var)]).inst_id = SOME (w2n w,N)` by
    simp[mk_inst_def] >>
  `a + n <= LENGTH t0.vs_call_ctx.cc_calldata` by simp[] >>
  `!name b len. local_region cenv es.scopes t0 name b len ==>
     regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes u name b len` by metis_tac[] >>
     metis_tac[]) >>
  `w2n w = w2n w` by simp[] >>
  drule_all (Q.INST [`b` |-> `w2n w`, `wd` |-> `w + 32w`, `wb` |-> `w`,
      `s` |-> `t0`, `inst` |-> `mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
        [STRING #"%" (toString s2.cs_next_var)]`]
    calldata_copy_store_semantic) >>
  disch_then (qspec_then `bound` strip_assume_tac) >>
  suspend "finish"
QED

Resume compile_slice_calldata_semantic[finish]:
  `LENGTH (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) = n` by
    simp[LENGTH_TAKE_EQ] >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `t = _` SUBST1_TAC >>
     simp[mstore_def, write_memory_with_expansion_def, LET_THM]) >>
  `!b len. b + len <= w2n w \/ w2n w + N <= b ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> qpat_x_assum `t = _` SUBST1_TAC >>
     qspecl_then [`w2n w`,`TAKE n (DROP a s.vs_call_ctx.cc_calldata)`,`t0`,`b`,`len`]
       mp_tac bytes_buffer_write_frame >>
     simp[] >> impl_tac >- decide_tac >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes u name b len` by metis_tac[] >>
     metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >>
     `regions_disjoint (w2n w) N b len` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[] >>
  `!name b len. local_region cenv es.scopes t name b len <=>
     local_region cenv es.scopes s name b len` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`s1`,`s2`,`s3`,`s4`,`Var p`,`limit`,`q`,`r`,`u`,`w`,
    `STRING #"%" (toString s2.cs_next_var)`,`p`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  goalStack.print_tac "PROBE" >> cheat
QED
Finalise compile_slice_calldata_semantic
