Theory bodyPtrPrecompileBuiltinsRecoveryInput
Ancestors bodyPtrPrecompileBuiltinsPrefixes bodyPtrPrecompileBuiltinsStaging
          bodyPtrPrecompileBuiltinsSeq bodyPtrPrecompileBuiltinsAllocationTransport
          bodyPtrPrecompileBuiltinsObservations
          compileEnv context emitHelper exprLoweringProps fragExec
          venomExecSemantics venomState ptrDiscipline bodyPtrDefs
          finite_map list rich_list venomInst freshWrites

Theorem emitted_direct_word_store_checked:
  emit_void MSTORE [Var bufroot; v] sa = ((),sb) /\
  ptr_covers G tn bufroot s 32 /\ lookup_var bufroot s = SOME a /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx ==>
  ?t tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G tn') /\
    t = mstore (w2n a) w s /\ tn'.t_var = tn.t_var /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MSTORE [Var bufroot; v] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  drule_all clean_word_store_trace_cursors >>
  disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `tnf` strip_assume_tac)) >>
  qexistsl [`t`, `tnf`] >>
  simp[op_taint_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def, write_memory_def]
QED

Theorem word_store_progress:
  (do dst <- emit_op ADD [Var bufroot; Lit (n2w off)];
      emit_void MSTORE [dst; v] od) sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sa sb)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

(* Append one clean word to a certified contiguous input prefix.  The
   old-variable frame makes this independent of the remaining operands. *)
Theorem clean_input_prefix_extend:
  (do dst <- emit_op ADD [Var bufroot; Lit (n2w off)];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK u /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn code
    (s with vs_inst_idx := k) Gu tnu) /\
  ptr_covers Gu tnu bufroot u capacity /\ lookup_var bufroot u = SOME b /\
  off + 32 <= capacity /\ w2n b + capacity < dimword(:256) /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  (!l. v <> Label l) /\ (!p. v = Var p ==> not_fresh_at sa p) /\
  not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx /\
  (!i. ~(w2n b <= i /\ i < w2n b + off) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  tnu.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + off} /\
  tnu.t_stor = tn.t_stor /\ tnu.t_trans = tn.t_trans /\
  (!p. not_fresh_at sa p ==>
    lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
    op_taint tnu (Var p) = op_taint tn (Var p)) ==>
  ?t Gt tnt.
    run_inst_seq (code ++ emitted_insts sb sc) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (code ++ emitted_insts sb sc)
      (s with vs_inst_idx := k) Gt tnt) /\
    ptr_covers Gt tnt bufroot t capacity /\ lookup_var bufroot t = SOME b /\
    (!i. ~(w2n b <= i /\ i < w2n b + (off+32)) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnt.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + (off+32)} /\
    tnt.t_stor = tn.t_stor /\ tnt.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gt p = FLOOKUP G p /\
      op_taint tnt (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand v u = SOME w /\ op_taint tnu v = {} /\
   (!p. v = Var p ==> not_fresh_at sb p)` by
    (Cases_on `v` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `w2n b + off < dimword(:256)` by decide_tac >>
  drule_all emitted_offset_word_store_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >> suspend "compose"
QED

Resume clean_input_prefix_extend[compose]:
  qpat_x_assum `_ sb = ((),sc)` kall_tac >>
  `w2n (b + n2w off) = w2n b + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `!i. ~(w2n b <= i /\ i < w2n b + (off+32)) ==>
    mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (first_x_assum irule >> decide_tac) >>
     `mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 u.vs_memory` by
       (irule memory_observation_mstore >> goal_assum (drule_at Any) >>
        simp[] >> decide_tac) >> simp[]) >>
  qpat_x_assum `s2.vs_memory = _` kall_tac >>
  conj_tac >- (rev_drule run_inst_seq_append >> simp[]) >>
  conj_tac
  >- (irule inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[] >> qexistsl [`Gu`, `u`, `tnu`] >> simp[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (`w2n (b + n2w off) = w2n b + off` by
        (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
      simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
           pred_setTheory.IN_GSPEC] >> gen_tac >>
      Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Finalise clean_input_prefix_extend

Theorem direct_word_store_progress:
  emit_void MSTORE [Var bufroot; v] sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sa sb)
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

Theorem recovery_input_staging_checked:
  emit_void MSTORE [Var bufroot; h] sa = ((),sb) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 96w];
      emit_void MSTORE [dst; q] od) sd = ((),se) /\
  ptr_covers G tn bufroot s 128 /\ lookup_var bufroot s = SOME b /\
  w2n b + 128 < dimword(:256) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand q s = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sa p)) [h;v;r;q] /\
  not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd se) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sd ++ emitted_insts sd se)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' bufroot t 128 /\ lookup_var bufroot t = SOME b /\
    (!i. ~(w2n b <= i /\ i < w2n b + 128) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 128} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  `ptr_covers G tn bufroot s 32` by
    (gvs[ptr_covers_def] >> irule_at Any EQ_REFL >> simp[] >> decide_tac) >>
  drule_all emitted_direct_word_store_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `tn1` strip_assume_tac)) >>
  `ptr_covers G tn1 bufroot s1 128 /\ lookup_var bufroot s1 = SOME b` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    metis_tac[direct_word_store_progress] >>
  suspend "v"
QED

Resume recovery_input_staging_checked[v]:
  `!i. ~(w2n b <= i /\ i < w2n b + 32) ==>
    mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> irule memory_observation_mstore >> simp[] >>
     qexistsl [`w2n b`, `wh`] >> simp[]) >>
  qpat_x_assum `s1 = _` kall_tac >>
  `!p. not_fresh_at sa p ==>
    lookup_var p s1 = lookup_var p s /\ FLOOKUP G p = FLOOKUP G p /\
    op_taint tn1 (Var p) = op_taint tn (Var p)` by simp[] >>
  `32 + 32 <= 128` by simp[] >>
  drule_all (Q.INST [`off` |-> `32`, `capacity` |-> `128`]
    clean_input_prefix_extend) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  suspend "r"
QED

Resume recovery_input_staging_checked[r]:
  `sb.cs_next_var <= sc.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    (qpat_assum `_ sb = ((),sc)`
      (mp_then Any strip_assume_tac (Q.INST [`off` |-> `32`] word_store_progress |> SRULE [])) >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc)` by (simp[] >> decide_tac) >>
  rule_assum_tac (PURE_REWRITE_RULE [EVAL ``32 + 32:num``]) >>
  `64 + 32 <= 128` by simp[] >>
  drule_all (Q.INST [`off` |-> `64`, `capacity` |-> `128`]
    clean_input_prefix_extend) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s3` (qx_choose_then `G3`
    (qx_choose_then `tn3` strip_assume_tac))) >>
  suspend "q"
QED

Resume recovery_input_staging_checked[q]:
  `sc.cs_next_var <= sd.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sd)` by
    (qpat_assum `_ sc = ((),sd)`
      (mp_then Any strip_assume_tac (Q.INST [`off` |-> `64`] word_store_progress |> SRULE [])) >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     ((emitted_insts sa sb ++ emitted_insts sb sc) ++ emitted_insts sc sd)` by
    (simp[] >> decide_tac) >>
  rule_assum_tac (PURE_REWRITE_RULE [EVAL ``64 + 32:num``]) >>
  `96 + 32 <= 128` by simp[] >>
  drule_all (Q.INST [`off` |-> `96`, `capacity` |-> `128`]
    clean_input_prefix_extend) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s4` (qx_choose_then `G4`
    (qx_choose_then `tn4` strip_assume_tac))) >>
  qexistsl [`s4`, `G4`, `tn4`] >>
  simp[GSYM APPEND_ASSOC, pred_setTheory.IN_DIFF, pred_setTheory.IN_GSPEC]
QED

Finalise recovery_input_staging_checked
