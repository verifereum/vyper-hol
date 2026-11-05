(* Ghost-checked literal chunk execution. *)
Theory exprSimPtrLiteralChunks
Ancestors
  exprSimPtrLiteralOps fragGasSeqPtr exprLowering exprLoweringProps
  exprSimLiteralBuffer fragExecPtr bodyPtrDefs ptrDiscipline venomState
  venomExecSemantics venomInst words finite_map compileEnv fragExec instIdxIndep
  emitHelper context rich_list freshWrites ASCIInumbers vfmConstants integer

Theorem literal_chunk_pair_ptr:
  lookup_var src s = SOME (n2w b) /\ FLOOKUP G src = SOME (base_addr,n) /\
  op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx /\
  base_addr <= b /\ b + off + 32 <= base_addr + n /\
  b + off + 32 < dimword (:256) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var src; Lit (n2w off)] [dst];
     mk_inst (id+1) MSTORE [Var dst; Lit w] []] s
    (G |+ (dst,(base_addr,n)))
    (tn with <| t_var := tn.t_var |+ (dst,{});
                t_mem := tn.t_mem DIFF {i | b+off <= i /\ i < b+off+32} |>)
Proof
  strip_tac >>
  `b < dimword (:256) /\ b+off < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit (n2w off)] [dst]) s =
   OK (update_var dst (n2w (b+off)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  drule literal_add_ghost >> disch_then assume_tac >>
  simp[Once inst_seq_ptr_def, literal_add_ptr_inst_ok] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ _ u` >>
  `lookup_var dst u = SOME (n2w (b+off))` by
    simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers (G |+ (dst,(base_addr,n)))
     (tn with t_var := tn.t_var |+ (dst,{})) dst u 32` by
    (simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, w2n_n2w] >>
     decide_tac) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Lit w] []) u =
   OK (mstore (w2n (n2w (b+off):bytes32)) w u)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule literal_mstore_ghost >> disch_then assume_tac >>
  gvs[w2n_n2w] >>
  simp[inst_seq_ptr_def, literal_mstore_ptr_inst_ok]
QED

Theorem literal_inst_seq_ptr_append:
  !xs s u G tn G1 tn1 G2 tn2 ys.
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = OK u /\
  inst_seq_ptr D 0 ctx fn PG G tn xs s G1 tn1 /\
  inst_seq_ptr D 0 ctx fn PG G1 tn1 ys
    (u with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2 ==>
  inst_seq_ptr D 0 ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  first_x_assum irule >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  qexistsl_tac [`G1`, `tn1`] >> gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem literal_chunk_head_shape:
  emit_op ADD [op; Lit off] sa = (dst,sm) /\
  emit_void MSTORE [dst; Lit value] sm = ((),sb) ==>
  ?x. dst = Var x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ADD [op; Lit off] [x];
       mk_inst (sa.cs_next_id+1) MSTORE [Var x; Lit value] []] /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var+1 /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!v. not_fresh_at sa v ==> v <> x)
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem literal_chunk_span:
  !n. 0 < n ==> 32 + 32 * word_size (n - 32) = 32 * word_size n
Proof
  rpt strip_tac >> Cases_on `32 <= n`
  >- (simp[word_size_def] >>
      qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
      disch_then (fn th => map_every (fn q => qspec_then q strip_assume_tac th)
        [`n + 31`, `n - 1`]) >>
      `(n + 31) MOD 32 < 32 /\ (n - 1) MOD 32 < 32` by simp[] >>
      `n - 32 + 31 = n - 1` by decide_tac >>
      simp[] >> intLib.ARITH_TAC) >>
  `n - 32 = 0` by decide_tac >>
  `word_size n = 1` by
    (simp[word_size_def] >> irule arithmeticTheory.DIV_UNIQUE >>
     qexists_tac `n - 1` >> decide_tac) >>
  simp[word_size_def]
QED
