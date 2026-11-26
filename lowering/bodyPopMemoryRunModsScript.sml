(* Count the five consecutive slices of the successful memory Pop. *)
Theory bodyPopMemoryRunMods
Ancestors
  bodyPopHeaderMemoryMods bodyPopLengthTestMods bodyPopLiveCheckMods
  bodyPopHeaderWriteMemoryMods bodyPopAddressMemoryMods exprSimPopNestedLocalRun
  fragGasOriginPtrLoop fragGasSeqAbort bodyBinopFragMemory decoderGhostFramePtr
  fragExec instIdxIndep exprLoweringProps venomState venomInst venomExecSemantics
  ptrDiscipline allocaHistory words rich_list list arithmetic

Theorem pop_memory_cuts[local]:
  isPREFIX (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6)
    (DROP k bb.bb_instructions) ==>
  isPREFIX [mk_inst id MLOAD [Var p] [x0]] (DROP k bb.bb_instructions) /\
  isPREFIX [mk_inst (id+1) ISZERO [Var x0] [x1];
            mk_inst (id+2) ISZERO [Var x1] [x2]] (DROP (k+1) bb.bb_instructions) /\
  isPREFIX [mk_inst (id+3) ASSERT [Var x2] [];
            mk_inst (id+4) SUB [Var x0;Lit 1w] [x3]] (DROP (k+3) bb.bb_instructions) /\
  get_instruction bb (k+5) = SOME (mk_inst (id+5) MSTORE [Var p;Var x3] []) /\
  isPREFIX (DROP 6 (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6))
    (DROP (k+6) bb.bb_instructions)
Proof
  PURE_REWRITE_TAC[IS_PREFIX_APPEND] >> strip_tac >>
  `!j. DROP (k+j) bb.bb_instructions =
       DROP j (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6 ++ l)` by
    (gen_tac >> once_rewrite_tac[ADD_COMM] >>
     pure_rewrite_tac[GSYM DROP_DROP_T] >> asm_rewrite_tac[]) >>
  `isPREFIX (mk_inst (id+5) MSTORE [Var p;Var x3] [] ::
     (DROP 6 (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6) ++ l))
     (DROP (k+5) bb.bb_instructions)` by simp[memory_pop_insts_def] >>
  drule instruction_prefix_cursor >> strip_tac >>
  simp[memory_pop_insts_def, IS_PREFIX_APPEND]
QED

Theorem pop_memory_path_join[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,tm)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,H,tm) [] out) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] out
Proof
  strip_tac >> gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`H`,`t`,`tm`] >> simp[]
QED

(* Run each remaining slice at the reached PC, then erase that cursor
   advance to recover the raw instruction-sequence result. *)
Theorem pop_memory_raw_prepend[local]:
  run_inst_seq xs s = OK q /\ t = (q with vs_inst_idx := j) /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\ run_inst_seq ys t = OK u ==>
  run_inst_seq (xs ++ ys) s = OK (u with vs_inst_idx := q.vs_inst_idx)
Proof
  strip_tac >>
  qpat_assum `run_inst_seq xs s = OK q`
    (mp_then Any (qspec_then `ys` SUBST1_TAC) run_inst_seq_append) >>
  `q = t with vs_inst_idx := q.vs_inst_idx` by gvs[venom_state_fupdselfid] >>
  qpat_x_assum `t = q with vs_inst_idx := j` kall_tac >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem pop_memory_positive_run_mods:
  let code = memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6;
      addr = w2n w + 32 + (len - 1) * esz
  in
  s.vs_inst_idx = k /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP k bb.bb_instructions) /\
  ALL_DISTINCT [p;x0;x1;x2;x3;x4;x5;x6] /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  FLOOKUP G p = SOME (root_base,span) /\
  mem_word_taint tn.t_mem (w2n w) = {} /\ w2n w + 32 <= s.vs_alloca_next /\
  mload (w2n w) s = n2w len /\ 0 < len /\ len < dimword (:256) /\
  addr < dimword (:256) /\ addr + esz <= root_base + span /\
  alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q z H tm.
    run_inst_seq code s = OK q /\ z = (q with vs_inst_idx := k+9) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,H,tm)) /\
    z.vs_memory = (mstore (w2n w) (n2w (len-1)) s).vs_memory /\
    mem_agree_outside {i | w2n w <= i /\ i < w2n w + 32} z.vs_memory s.vs_memory /\
    z = s with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory; vs_inst_idx := k+9|> /\
    lookup_var x6 z = SOME (n2w addr) /\ w2n (n2w addr : bytes32) = addr /\
    FLOOKUP H x6 = SOME (root_base,span) /\ op_taint tm (Var x6) = {} /\
    ptr_covers H tm x6 z esz /\ alloca_history func z /\ allocas_from lo z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule pop_memory_cuts >> strip_tac >>
  drule_all pop_header_memory_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `run_inst_seq [mk_inst id MLOAD [Var p] [x0]] s = OK q1` >>
  rename1 `u = q1 with vs_inst_idx := k+1` >>
  rename1 `op_prov G1 (Var x0) = NONE` >>
  rename1 `op_taint tn1 (Var x0) = {}` >>
  `u.vs_inst_idx = k+1 /\ ~u.vs_halted /\
   lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  qabbrev_tac `test = [mk_inst (id+1) ISZERO [Var x0] [x1];
                        mk_inst (id+2) ISZERO [Var x1] [x2]]` >>
  mp_tac (Q.INST [`id` |-> `id+1`, `G` |-> `G1`, `tn` |-> `tn1`,
                  `s1` |-> `u`, `n` |-> `n2w len`, `code` |-> `test`]
                pop_length_test_mods) >>
  (impl_tac >-
    (`x0 <> x1 /\ x0 <> x2 /\ x1 <> x2` by
       (qpat_assum `ALL_DISTINCT _` mp_tac >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
     `test = [mk_inst (id+1) ISZERO [Var x0] [x1];
              mk_inst ((id+1)+1) ISZERO [Var x1] [x2]]` by
       simp[Abbr `test`, ADD_ASSOC] >>
     asm_rewrite_tac[])) >>
  disch_then strip_assume_tac >>
  rename1 `run_inst_seq test u = OK q3` >>
  rename1 `s3 = q3 with vs_inst_idx := k+3` >>
  rename1 `op_prov G3 (Var x0) = NONE` >>
  rename1 `op_taint tn3 (Var x2) = {}` >>
  `alloca_history func u` by simp[] >>
  `alloca_history func s3` by
    (qpat_assum `s3 = q3 with vs_inst_idx := _` SUBST1_TAC >>
     `k+3 = u.vs_inst_idx + LENGTH test` by simp[Abbr `test`] >>
     pop_assum SUBST1_TAC >> irule alloca_history_no_alloca_slice >>
     conj_tac >-
       (qpat_assum `s3 with <|vs_vars := _; vs_inst_idx := _|> = u`
          (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
     conj_tac >-
       (qpat_assum `s3 = q3 with vs_inst_idx := _`
          (mp_tac o Q.AP_TERM `\z. z.vs_current_bb`) >>
        simp[NoAsms] >> disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists `bb` >> simp[GSYM IS_PREFIX_APPEND]) >>
     simp[Abbr `test`, mk_inst_def]) >>
  `n2w len <> (0w:bytes32)` by simp[n2w_11, LESS_MOD] >>
  mp_tac (Q.INST [`s` |-> `s3`, `G` |-> `G3`, `tn` |-> `tn3`,
                  `n` |-> `n2w len`] (SIMP_RULE bool_ss [LET_THM] pop_live_check_mods)) >>
  (impl_tac >- fs[]) >>
  disch_then strip_assume_tac >>
  rename1 `run_inst_seq _ s3 = OK q5` >>
  qabbrev_tac `s5 = q5 with vs_inst_idx := k+5` >>
  suspend "store"
QED

Resume pop_memory_positive_run_mods[store]:
  `lookup_var p s5 = SOME w /\ FLOOKUP G5 p = SOME (root_base,span) /\
   op_taint tn5 (Var p) = op_taint tn (Var p)` by
    (`p <> x0 /\ p <> x1 /\ p <> x2 /\ p <> x3` by
       (qpat_assum `ALL_DISTINCT _` mp_tac >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
     qpat_assum `!q. q <> x3 ==> _` (qspec_then `p` mp_tac) >>
     qpat_assum `!x. x <> x1 /\ x <> x2 ==> _` (qspec_then `p` mp_tac) >>
     qpat_assum `!x. x <> x0 ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `ptr_covers G5 tn5 p s5 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `lookup_block s5.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `s5.vs_inst_idx = k+5` by simp[Abbr `s5`] >>
  `s5.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `s3 with <|vs_vars := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  mp_tac (Q.INST [`s5` |-> `s5`, `G` |-> `G5`, `tn` |-> `tn5`,
                  `n` |-> `n2w len`] pop_header_mstore_mods) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `run_inst_seq [mk_inst (id+5) MSTORE [Var p;Var x3] []] s5 = OK q6` >>
  rename1 `s6 = q6 with vs_inst_idx := k+6` >>
  suspend "address"
QED

Resume pop_memory_positive_run_mods[address]:
  `lookup_block s6.vs_current_bb func.fn_blocks = SOME bb /\ ~s6.vs_halted` by
    (qpat_assum `s6 = s5 with <|vs_memory := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[]) >>
  `s6.vs_inst_idx = k+6` by simp[] >>
  `ALL_DISTINCT [p;x3;x4;x5;x6]` by
    (qpat_assum `ALL_DISTINCT _` mp_tac >> simp_tac (srw_ss()) []) >>
  `n2w len - 1w = (n2w (len-1):bytes32)` by
    (`len = (len-1)+1` by decide_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th])))) >>
     simp[GSYM word_add_n2w, WORD_ADD_SUB]) >>
  mp_tac (Q.INST [`s` |-> `s6`, `G` |-> `G5`, `tn` |-> `tn5`]
     (SIMP_RULE bool_ss [LET_THM] pop_address_memory_mods)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `run_inst_seq _ s6 = OK q9` >>
  rename1 `FLOOKUP H x6 = SOME (root_base,span)` >>
  rename1 `op_taint tm (Var x6) = {}` >>
  qabbrev_tac `z = q9 with vs_inst_idx := k+9` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,H,tm)` by
    (irule pop_memory_path_join >> qexistsl_tac [`G1`,`u`,`tn1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule pop_memory_path_join >> qexistsl_tac [`G3`,`s3`,`tn3`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule pop_memory_path_join >> qexistsl_tac [`G5`,`s5`,`tn5`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule pop_memory_path_join >> qexistsl_tac [`G5`,`s6`,`tn5`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "raw"
QED

Resume pop_memory_positive_run_mods[raw]:
  qabbrev_tac `a = [mk_inst id MLOAD [Var p] [x0]]` >>
  qabbrev_tac `c = [mk_inst (id+3) ASSERT [Var x2] [];
                     mk_inst (id+4) SUB [Var x0;Lit 1w] [x3]]` >>
  qabbrev_tac `b = [mk_inst (id+5) MSTORE [Var p;Var x3] []]` >>
  qabbrev_tac `tailcode = DROP 6 (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6)` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) tailcode /\
   EVERY (\i. ~is_terminator i.inst_opcode) b /\
   EVERY (\i. ~is_terminator i.inst_opcode) c /\
   EVERY (\i. ~is_terminator i.inst_opcode) test` by
    simp[Abbr `tailcode`, Abbr `b`, Abbr `c`, Abbr `test`, memory_pop_insts_def,
         mk_inst_def, is_terminator_def] >>
  `run_inst_seq (b ++ tailcode) s5 = OK (q9 with vs_inst_idx := q6.vs_inst_idx)` by
    (irule pop_memory_raw_prepend >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`k+6`,`s6`] >> simp[]) >> first_assum ACCEPT_TAC) >>
  `run_inst_seq (c ++ (b ++ tailcode)) s3 = OK (q9 with vs_inst_idx := q5.vs_inst_idx)` by
    (`q9 with vs_inst_idx := q5.vs_inst_idx =
      (q9 with vs_inst_idx := q6.vs_inst_idx) with vs_inst_idx := q5.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> irule pop_memory_raw_prepend >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`k+5`,`s5`] >> conj_tac >- first_assum ACCEPT_TAC >> simp[Abbr `s5`]) >>
     simp[]) >>
  `run_inst_seq (test ++ (c ++ (b ++ tailcode))) u =
      OK (q9 with vs_inst_idx := q3.vs_inst_idx)` by
    (`q9 with vs_inst_idx := q3.vs_inst_idx =
      (q9 with vs_inst_idx := q5.vs_inst_idx) with vs_inst_idx := q3.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> irule pop_memory_raw_prepend >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`k+3`,`s3`] >> simp[]) >> simp[]) >>
  `run_inst_seq (a ++ (test ++ (c ++ (b ++ tailcode)))) s =
      OK (q9 with vs_inst_idx := q1.vs_inst_idx)` by
    (`q9 with vs_inst_idx := q1.vs_inst_idx =
      (q9 with vs_inst_idx := q3.vs_inst_idx) with vs_inst_idx := q1.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> irule pop_memory_raw_prepend >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`k+1`,`u`] >> simp[]) >> simp[]) >>
  `memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6 =
      a ++ (test ++ (c ++ (b ++ tailcode)))` by
    simp[Abbr `a`,Abbr `test`,Abbr `c`,Abbr `b`,Abbr `tailcode`,memory_pop_insts_def] >>
  `run_inst_seq (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6) s =
     OK (q9 with vs_inst_idx := q1.vs_inst_idx)` by
    (qpat_assum `memory_pop_insts _ _ _ _ _ _ _ _ _ _ = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `q9.vs_memory = (mstore (w2n w) (n2w (len-1)) s).vs_memory /\
   z = s with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory; vs_inst_idx := k+9|>` by
    (mp_tac (Q.INST [`hdr` |-> `Var p`] memory_pop_run) >>
     (impl_tac >-
        (qpat_assum `ALL_DISTINCT [p;x0;x1;x2;x3;x4;x5;x6]` mp_tac >>
         simp_tac (srw_ss()) [eval_operand_def] >> metis_tac[])) >>
     qpat_assum `run_inst_seq (memory_pop_insts _ _ _ _ _ _ _ _ _ _) s = _`
       (fn th => simp_tac (srw_ss()) [th]) >>
     strip_tac >> conj_tac
     >- (qpat_assum `q9.vs_memory = _` mp_tac >> simp[]) >>
     qpat_assum `q9 with vs_inst_idx := _ = _`
       (mp_tac o Q.AP_TERM `\v. v with vs_inst_idx := k+9`) >>
     simp_tac (srw_ss()) [Abbr `z`]) >>
  qexistsl_tac [`q9 with vs_inst_idx := q1.vs_inst_idx`,`H`,`tm`] >>
  simp_tac bool_ss [] >>
  `((q9 with vs_inst_idx := q1.vs_inst_idx) with vs_inst_idx := k+9) = z` by simp[Abbr `z`] >>
  pop_assum SUBST1_TAC >>
  suspend "frame"
QED

Resume pop_memory_positive_run_mods[frame]:
  `z.vs_memory = (mstore (w2n w) (n2w (len-1)) s).vs_memory` by
    (qpat_assum `q9.vs_memory = _` mp_tac >> simp_tac (srw_ss()) [Abbr `z`]) >>
  `mem_agree_outside {i | w2n w <= i /\ i < w2n w + 32} z.vs_memory s.vs_memory` by
    (qpat_assum `z.vs_memory = _` SUBST1_TAC >> simp[wordLoadStorePtrTheory.mstore_memory_frame]) >>
  simp[]
QED

Finalise pop_memory_positive_run_mods
