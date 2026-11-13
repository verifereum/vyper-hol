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

