(* Compiler-facing shape of the memory hashing prefix. *)
Theory bodyPtrEnvBuiltinsMemoryHashCompile
Ancestors bodyPtrEnvBuiltinsMemoryHash builtinHashing context emitHelper
  compileEnv exprLoweringProps freshWrites words list rich_list finite_map fragExec
  bodyPtrDefs fragGasSeqPtr fragGasPathPtr

Theorem memory_hash_compile_code:
  compile_keccak256_bytes (Var root) sm = (op,sh) /\ not_fresh_at sm root ==>
  ?len dst out.
    op = Var out /\
    emitted_insts sm sh =
      [mk_inst sm.cs_next_id MLOAD [Var root] [len];
       mk_inst (sm.cs_next_id+1) ADD [Var root; Lit 32w] [dst];
       mk_inst (sm.cs_next_id+2) SHA3 [Var dst; Var len] [out]] /\
    root <> len /\ len <> dst /\
    ~not_fresh_at sm len /\ ~not_fresh_at sm dst /\ ~not_fresh_at sm out /\
    sh.cs_current_bb = sm.cs_current_bb /\
    sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
    sh.cs_next_var = sm.cs_next_var + 3 /\
    LENGTH sh.cs_current_insts = LENGTH sm.cs_current_insts + 3
Proof
  strip_tac >>
  gvs[compile_keccak256_bytes_def, emit_op_def, fresh_var_def, fresh_id_def,
      emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexistsl_tac [`STRING #"%" (toString sm.cs_next_var)`,
    `STRING #"%" (toString (sm.cs_next_var+1))`] >>
  gvs[not_fresh_at_def]
QED

Theorem memory_hash_compile_counted:
  compile_keccak256_bytes (Var root) sm = (op,sh) /\ not_fresh_at sm root /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result op G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sm G tn s G' tn'
Proof
  strip_tac >> drule_all memory_hash_compile_code >> strip_tac >>
  `ghost_kept cenv es sm G tn s G tn` by simp[ghost_kept_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     qexists_tac `l` >> simp[]) >>
  qpat_x_assum `op = _` SUBST1_TAC >>
  `LENGTH sh.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sm sh)` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `_ = [_;_;_]`) memory_hash_counted_path >>
  disch_then irule >> gvs[] >> metis_tac[]
QED
