(* Checked padded-message copy, independent of reason normalization. *)
Theory revertReasonCopyPtr
Ancestors wordLoadStorePtr normalizerAllocationFrame revertReasonLayout revertReasonPrefixFramePtr abiEncoderRounding
  exprLoweringProps venomMemProps venomInst venomExecSemantics venomState
  fragGasSeqPtr typedCopyPtr fragExecPtr bodyPtrDefs decoderGhostFramePtr ptrDiscipline
  words arithmetic list rich_list finite_map codegenRel venomInstProofs

Theorem revert_reason_copy_allocation_frame:
  run_inst_seq (revert_reason_copy id v q op) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule nonallocating_sequence_allocation_fields >>
  goal_assum (drule_at Any) >>
  simp[revert_reason_copy_def, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem mcopy_byte_clean:
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand count_op s = SOME n /\
  w2n a <= i /\ i < w2n a + w2n n /\
  w2n b + (i - w2n a) NOTIN tn.t_mem ==>
  i NOTIN (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s t tn).t_mem
Proof
  strip_tac >>
  gvs[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
      source_memory_write_ranges_def, fixed_source_write_range_def,
      mk_inst_def, range_bytes_def, eval_operand_def,
      sized_source_write_range_def] >> rpt strip_tac >> gvs[]
QED

Theorem mcopy_prefix_clean:
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand count_op s = SOME n /\ k <= w2n n /\
  (!i. w2n b <= i /\ i < w2n b + k ==> i NOTIN tn.t_mem) ==>
  !i. w2n a <= i /\ i < w2n a + k ==>
    i NOTIN (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s t tn).t_mem
Proof
  strip_tac >> gen_tac >> disch_tac >>
  irule mcopy_byte_clean >> simp[]
QED

Theorem mcopy_ptr_covers_frame:
  ptr_covers G tn x s C ==>
  ptr_covers
    (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy a b n s))
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy a b n s) tn) x (mcopy a b n s) C
Proof
  strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem mcopy_prefix_checked:
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  lookup_var dst s = SOME a /\ lookup_var src s = SOME b /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  k <= w2n n /\
  (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MCOPY [Var dst;Var src;count_op] []] s Gf tnf /\
    (!i. w2n a <= i /\ i < w2n a+k ==> i NOTIN tnf.t_mem) /\
    (!x C. ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x (mcopy (w2n a) (w2n b) (w2n n) s) C)
Proof
  strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n a) (w2n b) (w2n n) s)`,
    `step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n a) (w2n b) (w2n n) s) tn`] >>
  conj_tac >-
    (simp[inst_seq_ptr_def] >> conj_tac >-
       (irule ptr_inst_ok_mcopy_operand >> simp[]) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  conj_tac >-
    (gen_tac >> disch_tac >> irule mcopy_byte_clean >>
     simp[eval_operand_def]) >>
  rpt strip_tac >> irule mcopy_ptr_covers_frame >> simp[]
QED

Theorem revert_reason_copy_checks:
  lookup_var dst s = SOME b /\
  run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  ptr_covers G tn dst s (32+contractABI$ceil32 L) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  (!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    dst <> STRING #"%" (toString (v+k))) /\
  L+63 < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    (revert_reason_copy id v (Var dst) (Var src)) s Gf tnf /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> simp[revert_reason_copy_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k;l;m] _ _ _` >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                   arithmeticTheory.LESS_EQ_ADD]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base i s = OK (update_var (STRING #"%" (toString v)) (n2w L) s)` by
    (simp[Abbr `i`] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `op_taint t1 (Var (STRING #"%" (toString v))) = {}` by
    (simp[Abbr `t1`, Abbr `i`] >>
     qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  `t1.t_mem = tn.t_mem` by
    (simp[Abbr `t1`, Abbr `i`] >>
     qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >>
  `!x C. x <> STRING #"%" (toString v) /\ ptr_covers G tn x s C ==>
     ptr_covers g1 t1 x s1 C` by
    (rpt strip_tac >> simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `i`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g1 t1 src s1 (32+contractABI$ceil32 L) /\
   ptr_covers g1 t1 dst s1 (32+contractABI$ceil32 L)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  suspend "controls"
QED

Resume revert_reason_copy_checks[controls]:
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def] >> fs[op_taint_def]) >>
  `step_inst_base j s1 = OK
     (update_var (STRING #"%" (toString (v+1))) (n2w L+31w) s1)` by
    (simp[Abbr `j`] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `s1`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `op_taint t2 (Var (STRING #"%" (toString (v+1)))) = {}` by
    (simp[Abbr `t2`, Abbr `j`] >>
     irule (cj 1 copy_len_binop_ghost_frame) >> simp[]) >>
  `t2.t_mem = tn.t_mem` by
    (simp[Abbr `t2`, Abbr `j`, cj 2 copy_len_binop_ghost_frame]) >>
  `!x C. x <> STRING #"%" (toString (v+1)) /\ ptr_covers g1 t1 x s1 C ==>
     ptr_covers g2 t2 x s2 C` by
    (rpt strip_tac >> simp[Abbr `g2`, Abbr `t2`, Abbr `s2`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `j`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g2 t2 src s2 (32+contractABI$ceil32 L) /\
   ptr_covers g2 t2 dst s2 (32+contractABI$ceil32 L)` by
    (qpat_x_assum `!k. k < 4 ==> _` (qspec_then `1` mp_tac) >>
     simp[] >> metis_tac[]) >>
  suspend "rounded"
QED

Resume revert_reason_copy_checks[rounded]:
  `ptr_inst_ok D 0 0 ctx fn g2 t2 k s2` by
    (simp[Abbr `k`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def] >> fs[op_taint_def]) >>
  `(n2w L:bytes32)+31w && 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w =
   n2w (contractABI$ceil32 L)` by
    (once_rewrite_tac [WORD_AND_COMM] >>
     rewrite_tac [Once WORD_ADD_COMM] >>
     irule abi_encoder_round_ceil32 >> simp[]) >>
  `step_inst_base k s2 = OK (update_var (STRING #"%" (toString (v+2)))
     (n2w (contractABI$ceil32 L)) s2)` by
    (simp[Abbr `k`] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `s2`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g3 t3 _ s3 _ _` >>
  `op_taint t3 (Var (STRING #"%" (toString (v+2)))) = {}` by
    (simp[Abbr `t3`, Abbr `k`] >>
     irule (cj 1 copy_len_binop_ghost_frame) >> simp[]) >>
  `t3.t_mem = tn.t_mem` by
    (simp[Abbr `t3`, Abbr `k`, cj 2 copy_len_binop_ghost_frame]) >>
  `!x C. x <> STRING #"%" (toString (v+2)) /\ ptr_covers g2 t2 x s2 C ==>
     ptr_covers g3 t3 x s3 C` by
    (rpt strip_tac >> simp[Abbr `g3`, Abbr `t3`, Abbr `s3`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `k`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g3 t3 src s3 (32+contractABI$ceil32 L) /\
   ptr_covers g3 t3 dst s3 (32+contractABI$ceil32 L)` by
    (qpat_x_assum `!k. k < 4 ==> _` (qspec_then `2` mp_tac) >>
     simp[] >> metis_tac[]) >>
  suspend "count"
QED

Resume revert_reason_copy_checks[count]:
  rpt (qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `step_inst_base _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!x C. _ /\ ptr_covers _ _ _ _ _ ==> _` kall_tac) >>
  `ptr_inst_ok D 0 0 ctx fn g3 t3 l s3` by
    (simp[Abbr `l`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def] >> fs[op_taint_def]) >>
  `step_inst_base l s3 = OK (update_var (STRING #"%" (toString (v+3)))
     (n2w (32+contractABI$ceil32 L)) s3)` by
    (simp[Abbr `l`] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `s3`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g4 t4 _ s4 _ _` >>
  `op_taint t4 (Var (STRING #"%" (toString (v+3)))) = {}` by
    (simp[Abbr `t4`, Abbr `l`] >>
     irule (cj 1 copy_len_binop_ghost_frame) >> simp[]) >>
  `t4.t_mem = tn.t_mem` by
    (simp[Abbr `t4`, Abbr `l`, cj 2 copy_len_binop_ghost_frame]) >>
  `!x C. x <> STRING #"%" (toString (v+3)) /\ ptr_covers g3 t3 x s3 C ==>
     ptr_covers g4 t4 x s4 C` by
    (rpt strip_tac >> simp[Abbr `g4`, Abbr `t4`, Abbr `s4`] >>
     irule ptr_covers_step_frame >>
     simp[Abbr `l`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g4 t4 src s4 (32+contractABI$ceil32 L) /\
   ptr_covers g4 t4 dst s4 (32+contractABI$ceil32 L)` by
    (qpat_x_assum `!k. k < 4 ==> _` (qspec_then `3` mp_tac) >>
     simp[] >> metis_tac[]) >>
  suspend "copy"
QED

Resume revert_reason_copy_checks[copy]:
  `contractABI$ceil32 L+32 < dimword(:256)` by
    (mp_tac (Q.INST [`cnt` |-> `L`] abi_encoder_ceil32_bounds) >> decide_tac) >>
  `ptr_inst_ok D 0 0 ctx fn g4 t4 m s4` by
    (simp[Abbr `m`] >> irule ptr_inst_ok_mcopy_operand >>
     simp[eval_operand_def, Abbr `s4`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, w2n_n2w, ADD_COMM] >>
     fs[update_var_def, ADD_COMM]) >>
  `!u i. w2n b <= i /\ i < w2n b+32 ==>
     i NOTIN (step_taint m s4 u t4).t_mem` by
    (gen_tac >> gen_tac >> disch_tac >>
     simp[Abbr `m`] >> irule mcopy_byte_clean >>
     qexistsl_tac [`b`, `a`, `n2w (32+contractABI$ceil32 L)`] >>
     qpat_assum `!k. k < 4 ==> _` (fn th =>
       map_every (fn k => qspec_then k assume_tac th) [`0`, `1`, `2`, `3`]) >>
     fs[lookup_var_def] >>
     simp[eval_operand_def, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w, ADD_COMM] >>
     fs[update_var_def, ADD_COMM]) >>
  `?u. step_inst_base m s4 = OK u` by
    (simp[Abbr `m`] >> asm_simp_tac bool_ss [venomInstTheory.mk_inst_def, step_inst_base_opcode_eqs, venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds, combinTheory.K_THM] >>
     qpat_assum `!k. k < 4 ==> _` (fn th =>
       map_every (fn k => qspec_then k assume_tac th) [`0`, `1`, `2`, `3`]) >>
     fs[lookup_var_def] >>
     simp[mk_inst_def, eval_operand_def, Abbr `s4`, Abbr `s3`,
          Abbr `s2`, Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[inst_seq_ptr_def]
QED

Finalise revert_reason_copy_checks

Theorem revert_reason_copy_path_ptr:
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  ptr_covers G tn dst s (32+contractABI$ceil32 L) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  (!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    dst <> STRING #"%" (toString (v+k))) /\
  L+63 < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_copy id v (Var dst) (Var src))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t ==>
  ?Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx+5)) /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all revert_reason_copy_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`] >> reverse conj_tac >- simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (revert_reason_copy id v (Var dst) (Var src))` by
    simp[revert_reason_copy_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[revert_reason_copy_def, mk_inst_def]
QED

Theorem run_inst_seq_non_output_lookup:
  run_inst_seq code s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~MEM x i.inst_outputs) code ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. lookup_var x s` run_inst_seq_preserves_field) >>
  simp[] >> disch_then (qspec_then `x` irule) >> rpt strip_tac >>
  fs[EVERY_MEM] >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule step_preserves_non_output_vars >> simp[]
QED

Theorem inst_seq_ptr_live_pointer_frame:
  run_inst_seq code s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn code s Gf tnf /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~MEM x i.inst_outputs) code /\ ptr_covers G tn x s C ==>
  lookup_var x t = lookup_var x s /\ ptr_covers Gf tnf x t C
Proof
  strip_tac >>
  `lookup_var x t = lookup_var x s` by
    (irule run_inst_seq_non_output_lookup >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (\i. ~MEM x i.inst_outputs) code` by fs[EVERY_MEM] >>
  drule_all inst_seq_ptr_other_output_frame >>
  fs[ptr_covers_def, eval_operand_def]
QED

Theorem revert_reason_copy_live_pointer_frame:
  run_inst_seq (revert_reason_copy id v q op) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (revert_reason_copy id v q op) s Gf tnf /\
  (!k. k < 4 ==> x <> STRING #"%" (toString (v+k))) /\
  ptr_covers G tn x s C ==>
  lookup_var x t = lookup_var x s /\ ptr_covers Gf tnf x t C
Proof
  strip_tac >> irule inst_seq_ptr_live_pointer_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  simp[revert_reason_copy_def, mk_inst_def, is_terminator_def] >>
  qpat_x_assum `!k. k < 4 ==> _` mp_tac >>
  disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
    [`0`, `1`, `2`, `3`]) >> gvs[]
QED

Theorem take_padded_prefix[local]:
  k <= n ==>
  TAKE k (xs ++ REPLICATE n x) = TAKE k (xs ++ REPLICATE k x)
Proof
  strip_tac >> pure_rewrite_tac[TAKE_APPEND, REPLICATE_GENLIST, TAKE_GENLIST] >>
  AP_TERM_TAC >> AP_TERM_TAC >> simp[MIN_DEF] >> decide_tac
QED

Theorem mcopy_mload_prefix:
  32 <= n ==> mload dst (mcopy dst src n s) = mload src s
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `n`, `s`] mcopy_padded_read) >>
  disch_then (mp_tac o AP_TERM ``TAKE 32 : byte list -> byte list``) >>
  simp[TAKE_TAKE_MIN, take_padded_prefix, MIN_DEF, GSYM read_memory_def] >>
  Cases_on `32 < n` >> simp[read_memory_def, mload_def] >>
  `n = 32` by decide_tac >> gvs[]
QED

Theorem revert_reason_copy_mload:
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w L /\ L+63 < dimword(:256) /\
  (!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    dst <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t ==>
  mload (w2n b) t = n2w L
Proof
  strip_tac >>
  `(n2w L:bytes32)+31w && 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w =
   n2w (contractABI$ceil32 L)` by
    (once_rewrite_tac [WORD_AND_COMM] >> rewrite_tac [Once WORD_ADD_COMM] >>
     irule abi_encoder_round_ceil32 >> simp[]) >>
  `contractABI$ceil32 L+32 < dimword(:256)` by
    (mp_tac (Q.INST [`cnt` |-> `L`] abi_encoder_ceil32_bounds) >> decide_tac) >>
  qpat_x_assum `!k. k < 4 ==> _` (fn th =>
    map_every (fn k => qspec_then k assume_tac th) [`0`, `1`, `2`, `3`]) >>
  fs[word_add_n2w] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[revert_reason_copy_def] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, word_add_n2w, w2n_n2w, ADD_COMM] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, word_add_n2w, w2n_n2w, ADD_COMM] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, word_add_n2w, w2n_n2w, ADD_COMM] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w, ADD_COMM] >>
  fs[lookup_var_def] >> simp[run_inst_seq_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[mcopy_mload_prefix] >>
  fs[mload_def]
QED

Theorem revert_reason_copy_boundary_ptr:
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w L /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  ptr_covers G tn dst s (32+contractABI$ceil32 L) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  (!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    dst <> STRING #"%" (toString (v+k))) /\
  L+63 < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_copy id v (Var dst) (Var src))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t ==>
  ?Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+5)) /\
    mload (w2n b) (t with vs_inst_idx := s.vs_inst_idx+5) = n2w L /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x C. (!k. k < 4 ==> x <> STRING #"%" (toString (v+k))) /\
           ptr_covers G tn x s C ==>
      lookup_var x (t with vs_inst_idx := s.vs_inst_idx+5) = lookup_var x s /\
      ptr_covers Gf tnf x (t with vs_inst_idx := s.vs_inst_idx+5) C)
Proof
  strip_tac >> drule_all revert_reason_copy_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  conj_tac >-
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (revert_reason_copy id v (Var dst) (Var src))` by
       simp[revert_reason_copy_def, mk_inst_def, is_terminator_def] >>
     drule_all run_inst_seq_gas_path_ptr >>
     simp[revert_reason_copy_def, mk_inst_def]) >>
  `mload (w2n b) t = n2w L` by
    (drule_all revert_reason_copy_mload >> simp[]) >>
  drule revert_reason_copy_allocation_frame >> strip_tac >>
  conj_tac >- fs[mload_def] >> simp[] >> rpt strip_tac >>
  fs[ADD_COMM] >> drule_all (SRULE [ADD_COMM] revert_reason_copy_live_pointer_frame) >>
  simp[lookup_var_def, ptr_covers_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
