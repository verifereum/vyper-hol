Theory bodyPtrPrecompileBuiltinsAppendLoad
Ancestors bodyPtrPrecompileBuiltinsLoad fragGasPathPtr ghostPcTransportPtr
          exprLoweringProps venomExecSemantics venomInstProofs venomState
          ptrDiscipline bodyPtrDefs venomInst list rich_list finite_map valueEncoding

Theorem appended_clean_mload_path:
  run_inst_seq xs s = OK q /\ LENGTH xs = k /\
  gas_path_ptr D lo ctx fn PG G tn s n G1 tn1
    (OK (q with vs_inst_idx := s.vs_inst_idx + k)) /\
  q.vs_current_bb = s.vs_current_bb /\ ~q.vs_halted /\
  eval_operand (Var dst) q = SOME wo /\
  ptr_covers G1 tn1 dst q 32 /\ allocas_from lo q /\ ~ctx_has_dalloca ctx /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn1.t_mem) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (xs ++ [mk_inst id MLOAD [Var dst] [y]])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G2 tn2.
    run_inst_seq (xs ++ [mk_inst id MLOAD [Var dst] [y]]) s = OK t /\
    gas_path_ptr D lo ctx fn PG G tn s n G2 tn2
      (OK (t with vs_inst_idx := s.vs_inst_idx + k + 1)) /\
    op_prov G2 (Var y) = NONE /\ op_taint tn2 (Var y) = {} /\
    eval_operand (Var y) t = SOME (mem_word_at (w2n wo) q.vs_memory) /\
    t = update_var y (mload (w2n wo) q) q /\
    G2 = step_prov PG G1 (mk_inst id MLOAD [Var dst] [y])
      (t with vs_inst_idx := s.vs_inst_idx + k) /\
    tn2 = step_taint (mk_inst id MLOAD [Var dst] [y])
      (q with vs_inst_idx := s.vs_inst_idx + k)
      (t with vs_inst_idx := s.vs_inst_idx + k) tn1
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id MLOAD [Var dst] [y]` >>
  qabbrev_tac `t = update_var y (mload (w2n wo) q) q` >>
  `step_inst_base i q = OK t` by
    (gvs[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_read1_def, eval_operand_def]) >>
  `run_inst_seq (xs ++ [i]) s = OK t` by
    (drule run_inst_seq_append >> simp[run_inst_seq_def]) >>
  `isPREFIX [i] (DROP (s.vs_inst_idx+k) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     gvs[GSYM DROP_DROP_T, DROP_APPEND]) >>
  qabbrev_tac `q1 = q with vs_inst_idx := s.vs_inst_idx+k` >>
  `step_inst_base i q1 = OK (t with vs_inst_idx := s.vs_inst_idx+k)` by
    (simp[Abbr `q1`, Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs,
          mk_inst_def, exec_read1_def, eval_operand_def, update_var_def,
          mload_def]) >>
  `ptr_covers G1 tn1 dst q1 32 /\ allocas_from lo q1 /\
   (!w. lookup_var dst q1 = SOME w ==>
      !a. w2n w <= a /\ a < w2n w + 32 ==> a NOTIN tn1.t_mem)` by
    (gvs[Abbr `q1`, allocas_from_def, eval_operand_def, lookup_var_def] >>
     metis_tac[]) >>
  `~q1.vs_halted /\ lookup_block q1.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX [mk_inst id MLOAD [Var dst] [y]]
     (DROP q1.vs_inst_idx bb.bb_instructions)` by gvs[Abbr `q1`, Abbr `i`] >>
  qpat_x_assum `step_inst_base i q1 = _` mp_tac >>
  simp[Abbr `i`] >> strip_tac >>
  drule_all clean_mload_path >> disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  gvs[Abbr `q1`] >>
  `eval_operand (Var y) t = SOME (mem_word_at (w2n wo) q.vs_memory)` by
    simp[Abbr `t`, eval_operand_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE, mload_def, mem_word_at_def] >>
  drule_all gas_path_ptr_then >> simp[] >> metis_tac[]
QED
