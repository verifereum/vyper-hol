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
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,N) /\
  LENGTH data = n /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  stmt_state_rel ctx fn cenv cx es
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
  disch_then drule_all >> strip_tac >>
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
  locals_kept cenv es s
    (mstore b (n2w n)
      (write_memory_with_expansion (b + 32) data s))
Proof
  strip_tac >> gvs[] >> rw[locals_kept_def] >>
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
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,N) /\ 32 + n <= N /\
  (!name p len. local_region cenv es.scopes s name p len ==>
    regions_disjoint b N p len) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = mstore b (n2w n) (write_memory_with_expansion (b + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s) /\
    stmt_state_rel ctx fn cenv cx es t /\
    val_in_memory (BaseTV (BytesT (Dynamic bound)))
      (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) b t.vs_memory /\
    locals_kept cenv es s t /\ t.vs_allocas = s.vs_allocas /\
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
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  eval_operand start s = SOME (n2w a) /\
  a < dimword (:256) /\ n < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata ==>
  ?v q. run_inst_seq (emitted_insts sa sm) s = OK v /\
    run_inst_seq (emitted_insts sm sb) v = OK q /\
    q = s with vs_vars := q.vs_vars /\
    stmt_state_rel ctx fn cenv cx es q /\
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
  `stmt_state_rel ctx fn cenv cx es p` by
    (irule stmt_state_rel_reserved_vars_update >>
     qexistsl_tac [`s`,`sa`] >> simp[]) >>
  qexistsl_tac [`u`,`p`] >> simp[] >> first_assum ACCEPT_TAC
QED
Finalise calldata_size_bounds_semantic

Theorem compile_slice_calldata_semantic:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 + n <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s1 s2 s3 s4 data limit u t v q z zf w G2 tn2 r p.
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]) s = OK u /\
    lookup_var r u = SOME w /\
    t = (update_var p (w + 32w) u) with vs_inst_idx := s.vs_inst_idx + 2 /\
    v = update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t) /\
    out = Var r /\ data = Var p /\
    ptr_covers G2 tn2 r t N /\ ptr_covers G2 tn2 p t (N - 32) /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t.vs_halted /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt s1 t) /\
    q = t with vs_vars := q.vs_vars /\
    compile_slice_out_buf N sa = ((out,data),s1) /\
    emit_op CALLDATASIZE [] s1 = (limit,s2) /\
    compile_assert_slice_bounds start (Lit (n2w n)) limit s2 = ((),s3) /\
    emit_void CALLDATACOPY [data;start;Lit (n2w n)] s3 = ((),s4) /\
    emit_void MSTORE [out;Lit (n2w n)] s4 = ((),sb) /\
    run_inst_seq (emitted_insts s1 s2) t = OK v /\
    run_inst_seq (emitted_insts s2 s3) v = OK q /\
    run_inst_seq (emitted_insts s3 sb) q = OK z /\
    z = mstore (w2n w) (n2w n) (write_memory_with_expansion (w2n w + 32)
      (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) q) /\
    q.vs_inst_idx = LENGTH s1.cs_current_insts /\
    z.vs_inst_idx = LENGTH s1.cs_current_insts /\
    zf = z with vs_inst_idx := LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es zf /\
    val_in_memory (BaseTV (BytesT (Dynamic bound)))
      (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) (w2n w) zf.vs_memory /\
    eval_operand out zf = SOME w /\
    FLOOKUP zf.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    (!x val. not_fresh_at sa x /\ lookup_var x s = SOME val ==>
      lookup_var x zf = SOME val) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP zf.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    locals_kept cenv es s zf /\
    zf.vs_accounts = s.vs_accounts /\ zf.vs_transient = s.vs_transient /\
    zf.vs_call_ctx = s.vs_call_ctx /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes zf name b len ==>
      regions_disjoint (w2n w) N b len)
Proof
  strip_tac >>
  `32 <= N` by decide_tac >>
  drule_all compile_slice_calldata_runtime >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts s2 s3) v = OK q` by fs[] >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_assum `emit_op CALLDATASIZE [] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at s1 x ==> lookup_var x q = lookup_var x t` by
    (rpt strip_tac >>
     `not_fresh_at s2 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
     qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `q = t with vs_vars := q.vs_vars` by
    (qpat_x_assum `q = v with vs_vars := _` mp_tac >> simp[update_var_def]) >>
  suspend "pure_frame"
QED

Resume compile_slice_calldata_semantic[pure_frame]:
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es q` by
    (irule stmt_state_rel_reserved_vars_update >>
     qexistsl_tac [`t`,`s1`] >> simp[]) >>
  `!x val. not_fresh_at sa x /\ lookup_var x s = SOME val ==>
    lookup_var x q = SOME val` by
    (rpt strip_tac >>
     `eval_operand (Var x) t = SOME val` by
       (qpat_assum `!op. _ ==> eval_operand op t = eval_operand op s /\ _`
          (qspec_then `Var x` mp_tac) >>
        simp[eval_operand_def]) >>
     `not_fresh_at s1 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x q = _`
       (qspec_then `x` mp_tac) >> fs[eval_operand_def]) >>
  suspend "local_frame"
QED

Resume compile_slice_calldata_semantic[local_frame]:
  `!name b len. local_region cenv es.scopes q name b len ==>
    local_region cenv es.scopes s name b len` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac
     >- (qexists_tac `fn` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`,`es.scopes`,`q`] >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
    local_region cenv es.scopes u name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[]) >>
  `!name b len. local_region cenv es.scopes q name b len ==>
    regions_disjoint (w2n w) N b len` by metis_tac[] >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_memory = s.vs_memory /\
   q.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `q = t with vs_vars := _` SUBST1_TAC >> simp[update_var_def]) >>
  `FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,N)` by simp[] >>
  `eval_operand (Var r) q = SOME w /\
   eval_operand (Var p) q = SOME (w + 32w)` by metis_tac[] >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w + 32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  suspend "copy"
QED

Resume compile_slice_calldata_semantic[copy]:
  `eval_operand start q = SOME (n2w a)` by simp[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]) (fn_insts fn)` by
    (drule_all buffer_alloc_code >> strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `eval_operand data q = SOME (w + 32w) /\ eval_operand out q = SOME w /\
   eval_operand (Lit (n2w n)) q = SOME (n2w n)` by simp[eval_operand_def] >>
  `(mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]).inst_opcode = ALLOCA /\
   FLOOKUP q.vs_allocas (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]).inst_id =
     SOME (w2n w,N)` by simp[mk_inst_def] >>
  `a + n <= LENGTH q.vs_call_ctx.cc_calldata` by simp[] >>
  `w2n w = w2n w` by simp[] >>
  drule_all calldata_copy_store_semantic >>
  disch_then (qspec_then `bound` strip_assume_tac) >>
  suspend "old_frame"
QED

Resume compile_slice_calldata_semantic[old_frame]:
  rename1 `run_inst_seq (emitted_insts s3 sb) q = OK z` >>
  `!name b len. local_region cenv es.scopes z name b len ==>
    local_region cenv es.scopes q name b len` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
    local_region cenv es.scopes q name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[]) >>
  `LENGTH (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) = n` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  `locals_kept cenv es s z` by
    (irule locals_kept_regions >>
     map_every qx_gen_tac [`name`,`bb`,`sz`] >> strip_tac >>
     `regions_disjoint (w2n w) N bb sz` by
       (qpat_assum `!name b len. local_region cenv es.scopes u name b len ==> _` irule >>
        qexists_tac `name` >>
        qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `z = _` SUBST1_TAC >>
     qspecl_then [`w2n w`,`TAKE n (DROP a q.vs_call_ctx.cc_calldata)`,`q`]
       mp_tac bytes_buffer_write_frame >>
     simp[] >> disch_then irule >> fs[regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `local_region cenv es.scopes q name b len` by metis_tac[] >>
     qpat_assum `z = _` SUBST1_TAC >>
     qspecl_then [`w2n w`,`TAKE n (DROP a q.vs_call_ctx.cc_calldata)`,`q`]
       mp_tac bytes_buffer_write_frame >>
     simp[] >> disch_then irule >>
     `regions_disjoint (w2n w) N b len` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  suspend "projections"
QED

Resume compile_slice_calldata_semantic[projections]:
  `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx` by
    (drule alloca_storage_projections >> simp[]) >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `z = _` SUBST1_TAC >>
     qpat_assum `q = t with vs_vars := _` SUBST1_TAC >>
     simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, update_var_def, LET_THM] >>
     qpat_assum `t = update_var _ _ u with vs_inst_idx := _` SUBST1_TAC >>
     simp_tac (srw_ss()) [update_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume compile_slice_calldata_semantic[finish]:
  `!aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) N b len` by
       (qpat_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >> simp[]) >>
     qpat_assum `z = _` SUBST1_TAC >>
     qspecl_then [`w2n w`,`TAKE n (DROP a q.vs_call_ctx.cc_calldata)`,`q`]
       mp_tac bytes_buffer_write_frame >>
     simp[] >> disch_then irule >> fs[regions_disjoint_def] >> decide_tac) >>
  `q.vs_inst_idx = LENGTH s1.cs_current_insts` by
    (qpat_assum `q = t with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `z.vs_inst_idx = LENGTH s1.cs_current_insts` by
    (qpat_assum `z = _` SUBST1_TAC >>
     simp[write_state_inst_idx]) >>
  `!x. lookup_var x (z with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x z` by
    simp_tac (srw_ss()) [lookup_var_def] >>
  `!name b len. local_region cenv es.scopes
      (z with vs_inst_idx := LENGTH sb.cs_current_insts) name b len <=>
    local_region cenv es.scopes z name b len` by
    simp_tac (srw_ss()) [local_region_def, lookup_var_def] >>
  qexistsl_tac [`s1`,`s2`,`s3`,`s4`,`data`,`limit`,`u`,`t`,`v`,`q`,`z`,
    `z with vs_inst_idx := LENGTH sb.cs_current_insts`,`w`,`G2`,`tn2`,`r`,`p`] >>
  simp[eval_operand_def, stmt_state_rel_inst_idx, locals_kept_inst_idx] >>
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[eval_operand_def]
QED
Finalise compile_slice_calldata_semantic
