(* Compiler-facing fixed-byte hash prefix. *)
Theory bodyPtrEnvBuiltinsFixedHashCompile
Ancestors bodyPtrEnvBuiltinsFixedHash builtinHashing context emitHelper
  compileEnv exprLoweringProps freshWrites words list rich_list finite_map fragExec
  bodyPtrDefs fragGasSeqPtr fragGasPathPtr venomInst venomState

Theorem fixed_hash_compile_code:
  compile_keccak256_bytesm value m sm = (op,sh) /\
  (!x. value = Var x ==> not_fresh_at sm x) ==>
  ?p out.
    op = Var out /\
    emitted_insts sm sh =
      [mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p];
       mk_inst (sm.cs_next_id+1) MSTORE [Var p; value] [];
       mk_inst (sm.cs_next_id+2) SHA3 [Var p; Lit (n2w m)] [out]] /\
    ~not_fresh_at sm p /\ ~not_fresh_at sm out /\
    (!x. value = Var x ==> x <> p) /\
    sh.cs_current_bb = sm.cs_current_bb /\
    sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
    sh.cs_next_var = sm.cs_next_var + 2 /\
    LENGTH sh.cs_current_insts = LENGTH sm.cs_current_insts + 3
Proof
  strip_tac >>
  gvs[compile_keccak256_bytesm_def, compile_alloc_buffer_def, emit_op_def,
      emit_void_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `STRING #"%" (toString sm.cs_next_var)` >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem fixed_hash_compile_counted:
  compile_keccak256_bytesm value m sm = (op,sh) /\
  (!x. value = Var x ==> not_fresh_at sm x) /\ m <= 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result op G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sm G tn s G' tn'
Proof
  strip_tac >> drule_all fixed_hash_compile_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     qexists_tac `l` >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts fn)` by
    suspend "membership" >>
  qpat_x_assum `op = _` SUBST1_TAC >>
  `LENGTH sh.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sm sh)` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `_ = [_;_;_]`) fixed_hash_prefix_counted >>
  disch_then irule >> gvs[] >> metis_tac[]
QED

Resume fixed_hash_compile_counted[membership]:
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >>
  strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p])
    (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  metis_tac[MEM_DROP_IMP]
QED

Finalise fixed_hash_compile_counted
