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
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def, word_add_n2w]) >>
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
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def]) >>
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

Theorem literal_chunk_pair_run:
  lookup_var src s = SOME (n2w b) ==>
  run_inst_seq
    [mk_inst id ADD [Var src; Lit (n2w off)] [dst];
     mk_inst (id+1) MSTORE [Var dst; Lit w] []] s =
  OK (mstore (w2n (n2w (b+off):bytes32)) w
       (update_var dst (n2w (b+off)) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit (n2w off)] [dst]) s =
   OK (update_var dst (n2w (b+off)) s)` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  qmatch_goalsub_abbrev_tac `mstore _ _ u` >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Lit w] []) u =
   OK (mstore (w2n (n2w (b+off):bytes32)) w u)` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def,
          Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def] >> simp[mk_inst_def, is_terminator_def]
QED

Theorem literal_chunks_ptr:
  !ptr bs off sa sb p s b G tn base_addr n.
  compile_store_byte_chunks ptr bs off sa = ((),sb) /\ ptr = Var p /\
  not_fresh_at sa p /\ lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (base_addr,n) /\ op_taint tn (Var p) = {} /\
  ~ctx_has_dalloca ctx /\ base_addr <= b /\
  b + off + 32 * word_size (LENGTH bs) <= base_addr + n /\
  b + off + 32 * word_size (LENGTH bs) < dimword (:256) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    tn'.t_mem = tn.t_mem DIFF
      {i | b+off <= i /\ i < b+off+32*word_size (LENGTH bs)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP G' v = FLOOKUP G v /\
      FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- (gvs[compile_store_byte_chunks_def, comp_return_def,
          emitted_insts_def, same_blocks_def, run_inst_seq_def,
          inst_seq_ptr_def, word_size_def] >>
      qexistsl_tac [`G`, `tn`] >> simp[pred_setTheory.EXTENSION]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  drule_all literal_chunk_head_shape >> strip_tac >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `word_of_bytes T 0w chunk` >>
  qabbrev_tac `w = word_of_bytes T 0w chunk` >>
  `32 + 32 * word_size (LENGTH (DROP 32 (hd::tl))) =
     32 * word_size (LENGTH (hd::tl))` by
    (rewrite_tac[listTheory.LENGTH_DROP] >> irule literal_chunk_span >> simp[]) >>
  qpat_x_assum `32 + _ = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `b + offset + 32 <= base_addr + n /\
   b + offset + 32 < dimword (:256)` by decide_tac >>
  suspend "head"
QED

Resume literal_chunks_ptr[head]:
  drule literal_chunk_pair_run >> disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa post = head_code` >>
  qabbrev_tac `u = mstore (w2n (n2w (b+offset):bytes32))
    (word_of_bytes T 0w chunk) (update_var x (n2w (b+offset)) s)` >>
  `run_inst_seq (emitted_insts sa post) s = OK u` by
    simp[Abbr `head_code`, Abbr `u`] >>
  qabbrev_tac `G1 = G |+ (x,(base_addr,n))` >>
  qabbrev_tac `tn1 = tn with <|t_var := tn.t_var |+ (x,{});
    t_mem := tn.t_mem DIFF {i | b+offset <= i /\ i < b+offset+32}|>` >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa post) s G1 tn1` by
    (simp_tac (srw_ss()) [Abbr `head_code`, Abbr `G1`, Abbr `tn1`] >>
     qpat_x_assum `emitted_insts sa post = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
     irule (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]
       (SRULE [] literal_chunk_pair_ptr)) >> simp[]) >>
  `not_fresh_at post p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `p <> x` by metis_tac[] >>
  `lookup_var p u = SOME (n2w b) /\ FLOOKUP G1 p = SOME (base_addr,n) /\
   op_taint tn1 (Var p) = {}` by
    (simp[Abbr `u`, Abbr `G1`, Abbr `tn1`, op_taint_def,
          mstore_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def, op_taint_def]) >>
  qpat_x_assum `!w off id dst. _` kall_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  qabbrev_tac `v = u with vs_inst_idx :=
    s.vs_inst_idx + LENGTH (emitted_insts sa post)` >>
  qpat_x_assum `lookup_var p u = _` mp_tac >>
  `lookup_var p v = lookup_var p u` by simp[Abbr `v`, lookup_var_def] >>
  disch_tac >>
  `lookup_var p v = SOME (n2w b)` by metis_tac[] >>
  qpat_x_assum `lookup_var p u = _` kall_tac >>
  `b + (offset + (32 * word_size (SUC (LENGTH tl) - 32) + 32)) <= base_addr+n /\
   b + (offset + (32 * word_size (SUC (LENGTH tl) - 32) + 32)) < dimword (:256)` by
    decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  suspend "compose"
QED

Resume literal_chunks_ptr[compose]:
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa post)` by
    simp[Abbr `head_code`, mk_inst_def, is_terminator_def] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- metis_tac[same_blocks_trans] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac >- simp[Abbr `head_code`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`t with vs_inst_idx := u.vs_inst_idx`, `G''`, `tn''`] >>
  conj_tac
  >- (`run_inst_seq (emitted_insts post sb) u =
        OK (t with vs_inst_idx := u.vs_inst_idx)` by
        (`u = v with vs_inst_idx := u.vs_inst_idx` by simp[Abbr `v`] >>
         pop_assum (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
         simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
      qpat_x_assum `run_inst_seq (emitted_insts sa post) s = _`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts post sb` assume_tac) >>
      metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
      irule literal_inst_seq_ptr_append >> conj_tac >- simp[] >>
      qexistsl_tac [`G1`, `tn1`, `u`] >> simp[Abbr `v`]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> simp[Abbr `tn1`, pred_setTheory.EXTENSION] >>
      gen_tac >> qpat_x_assum `32 + _ = _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp_tac bool_ss [pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
      Cases_on `x' IN tn.t_mem` >> simp[] >> intLib.ARITH_TAC) >>
  simp[Abbr `tn1`] >>
  qx_gen_tac `z` >> strip_tac >>
  `not_fresh_at post z` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `z <> x` by metis_tac[] >>
  first_x_assum (qspec_then `z` mp_tac) >> simp[] >> strip_tac >>
  gvs[Abbr `v`, Abbr `u`, Abbr `G1`,
      lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE]
QED

Finalise literal_chunks_ptr
