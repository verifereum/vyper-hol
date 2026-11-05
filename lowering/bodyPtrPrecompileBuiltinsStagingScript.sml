Theory bodyPtrPrecompileBuiltinsStaging
Ancestors bodyPtrPrecompileBuiltinsFreshFrame bodyPtrPrecompileBuiltinsSeq
          allocationPtr typedCopyPtr fragExecPtr fragGasSeqPtr
          venomExecSemantics venomInst venomState ptrDiscipline bodyPtrDefs
          compileEnv exprLoweringProps finite_map loweringHalt context
          emitHelper contextCodegenRelProps fragExec list rich_list

Theorem allocated_buffer_checked:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) /\
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) out t n
Proof
  strip_tac >> conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_alloca >> simp[]) >>
  irule alloca_step_ptr_covers >> metis_tac[]
QED

Theorem clean_word_store_checked:
  ptr_covers G tn dst s 32 /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
  eval_operand v s = SOME w /\
  step_inst_base (mk_inst id MSTORE [Var dst; v] []) s = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var dst; v] []] s
    (step_prov PG G (mk_inst id MSTORE [Var dst; v] []) t)
    (step_taint (mk_inst id MSTORE [Var dst; v] []) s t tn) /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==>
    i NOTIN (step_taint (mk_inst id MSTORE [Var dst; v] []) s t tn).t_mem)
Proof
  strip_tac >> conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_mstore >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule mstore_word_clean >>
  simp[eval_operand_def] >> metis_tac[]
QED

(* Unlike compile_with_byte_offset this boundary executes ADD even at zero. *)
Theorem point_offset_covers:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out (update_var out (a + n2w off) s) n
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn) (Var out) = {}` by
    simp[copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword (:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       mk_inst_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def,
       wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem point_offset_checked:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var root; Lit (n2w off)] [out]] s
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def] >> irule ptr_inst_ok_copy_len_binop >>
  gvs[ptr_covers_def, op_taint_def]
QED

Theorem clean_word_load_checked:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MLOAD [Var src] [tmp]] s
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) /\
  op_taint (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {}
Proof
  strip_tac >> conj_tac
  >- (`step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
       OK (update_var tmp (mload (w2n a) s) s)` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
      simp[inst_seq_ptr_def] >> irule ptr_inst_ok_mload >> simp[]) >>
  irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem emitted_allocation_checked:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?out G' tn'. buf.buf_operand = Var out /\ not_fresh_at sb out /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    ptr_covers G' tn' out t n
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
          emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all allocated_buffer_checked >> strip_tac >> metis_tac[]
QED
