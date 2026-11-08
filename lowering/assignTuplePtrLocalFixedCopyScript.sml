(* Fixed-size local copies share their raw run endpoint with the pointer
   sequence check. No disjointness of source and destination is required. *)
Theory assignTuplePtrLocalFixedCopy
Ancestors
  typedCopyPtr fragExecPtr fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  exprLoweringProps exprSimBufferStore context compileEnv emitHelper emitHelperProps fragExec
  venomExecSemantics venomInstProofs venomInst venomState finite_map
  list rich_list arithmetic pred_set words valueEncoding

Theorem mcopy_operand_seq_ptr:
  !D ctx fn PG G tn s id dst src count_op a b n.
    ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MCOPY [Var dst; Var src; count_op] []] s G
      (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn) /\
    run_inst_seq [mk_inst id MCOPY [Var dst; Var src; count_op] []] s =
      OK (mcopy (w2n b) (w2n a) (w2n n) s)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  simp[inst_seq_ptr_def, run_inst_seq_def] >>
  conj_tac >- (irule ptr_inst_ok_mcopy_operand >> simp[]) >>
  simp[mcopy_operand_ghost_frame, eval_operand_def]
QED

Theorem mcopy_operand_taint_frames_ptr:
  !tn s id dst src count_op a b n k tn'.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\ w2n n = k /\
    tn' = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) k s) tn ==>
      tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!i. i < k ==>
        (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + k) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >> simp[mcopy_operand_ghost_frame] >>
  conj_tac >-
    simp[step_taint_def, set_var_taint_def, adopt_reset_def,
         imm_taint_def, mk_inst_def] >>
  rpt strip_tac >>
  `!j. j < w2n n ==> i <> j + w2n b` by decide_tac >> metis_tac[]
QED

Theorem compile_fixed_copy_code_ptr:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  emitted_insts sa sb =
    if type_memory_bytes cenv ty = 0 then []
    else [mk_inst sa.cs_next_id MCOPY
      [dst;src;Lit (n2w (type_memory_bytes cenv ty))] []]
Proof
  strip_tac >> Cases_on `type_memory_bytes cenv ty` >>
  gvs[compile_store_memory_def, compile_copy_memory_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, emit_def, emitted_insts_def, DROP_APPEND1]
QED

Theorem compile_fixed_copy_sequence_ptr:
  compile_store_memory cenv (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  n = type_memory_bytes cenv ty /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n ==>
  ?tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (if n = 0 then s else mcopy (w2n b) (w2n a) n s) /\
    (n = 0 ==> tn' = tn) /\
    (n <> 0 ==> tn' = step_taint
      (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s
      (mcopy (w2n b) (w2n a) n s) tn)
Proof
  strip_tac >> drule_all compile_fixed_copy_code_ptr >> strip_tac >>
  Cases_on `n = 0` >- (gvs[inst_seq_ptr_def, run_inst_seq_def]) >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {}` by simp[eval_operand_def, op_taint_def] >>
  qexists_tac `step_taint
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s
    (mcopy (w2n b) (w2n a) n s) tn` >>
  fs[inst_seq_ptr_def, run_inst_seq_def, step_inst_base_opcode_eqs,
     mk_inst_def, eval_operand_def] >>
  conj_tac >- (simp[GSYM mk_inst_def] >>
    irule ptr_inst_ok_mcopy >> simp[] >> metis_tac[]) >>
  simp[GSYM mk_inst_def, mcopy_operand_ghost_frame, eval_operand_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem compile_fixed_copy_frames_ptr:
  compile_store_memory cenv (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  n = type_memory_bytes cenv ty /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    (!p. lookup_var p u = lookup_var p s /\
         op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!off k. off + k <= n ==> mem_bytes_at (w2n b + off) k u.vs_memory =
      mem_bytes_at (w2n a + off) k s.vs_memory) /\ 
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i < n ==> (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all compile_fixed_copy_sequence_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  Cases_on `n = 0` >- (gvs[] >> qexists_tac `tn` >> simp[mem_bytes_at_def]) >>
  gs[] >> qexists_tac `tn'` >> conj_tac >- metis_tac[] >>
  `eval_operand (Var dst) s = SOME b /\
   eval_operand (Var src) s = SOME a /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  `tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!i. i < n ==> (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
     (i IN tn'.t_mem <=> i IN tn.t_mem))` by
    (irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`Lit (n2w n)`, `Var dst`, `sa.cs_next_id`,
                  `n2w n`, `s`, `Var src`] >> fs[]) >>
  qpat_x_assum `tn' = step_taint _ _ _ _` kall_tac >>
  qpat_x_assum `mcopy _ _ _ s = u` (assume_tac o SYM) >>
  conj_tac >-
    (gen_tac >> conj_tac
     >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
     qpat_x_assum `tn'.t_var = tn.t_var` mp_tac >>
     simp[op_taint_def]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule (buffer_mcopy_window |> ONCE_REWRITE_RULE [ADD_COMM]) >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule buffer_mcopy_exterior >> decide_tac) >>
  metis_tac[ADD_COMM]
QED
