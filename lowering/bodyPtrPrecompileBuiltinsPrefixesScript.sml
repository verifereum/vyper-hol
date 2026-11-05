Theory bodyPtrPrecompileBuiltinsPrefixes
Ancestors bodyPtrPrecompileBuiltinsTransfer bodyPtrPrecompileBuiltinsFreshFrame
          bodyPtrPrecompileBuiltinsObservations
          freshWrites builtinMisc context emitHelper exprLoweringProps
          fragExec venomExecSemantics venomState venomInst ptrDiscipline bodyPtrDefs
          finite_map list rich_list compileEnv

(* Scalar staging uses the same offset/store trace as point staging. *)
Theorem offset_store_code[local]:
  (do dst <- emit_op ADD [Var bufroot; Lit (n2w off)];
      emit_void MSTORE [dst; v] od) sa = ((),sb) ==>
  ?dst. emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [Var bufroot; Lit (n2w off)] [dst];
     mk_inst (sa.cs_next_id+1) MSTORE [Var dst; v] []] /\
    (!p. not_fresh_at sa p ==> p <> dst) /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  qexists `STRING #"%" (toString sa.cs_next_var)` >>
  simp[emitted_insts_def, DROP_APPEND1] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem emitted_offset_word_store_checked:
  (do dst <- emit_op ADD [Var bufroot; Lit (n2w off)];
      emit_void MSTORE [dst; v] od) sa = ((),sb) /\
  ptr_covers G tn bufroot s capacity /\ lookup_var bufroot s = SOME a /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  (!p. v = Var p ==> not_fresh_at sa p) /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    t.vs_memory = (mstore (w2n (a + n2w off)) w s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF
      {i | w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule offset_store_code >>
  disch_then (qx_choose_then `dst` strip_assume_tac) >>
  `!p. v = Var p ==> p <> dst` by metis_tac[] >>
  drule_all offset_word_store_trace >>
  disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >> metis_tac[]
QED

Theorem emitted_point_pair_checked:
  (do src <- emit_op ADD [Var root; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w off)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [Var root; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w (off+32))];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  ptr_covers G tn root s 64 /\ lookup_var root s = SOME a /\
  ptr_covers G tn bufroot s capacity /\ lookup_var bufroot s = SOME b /\
  off + 64 <= capacity /\ w2n a + 64 < dimword (:256) /\
  w2n b + off + 64 < dimword (:256) /\
  (!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN tn.t_mem) /\
  not_fresh_at sa root /\ not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' root t 64 /\ ptr_covers G' tn' bufroot t capacity /\
    (!i. ~(w2n b + off <= i /\ i < w2n b + off + 64) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n b + off <= i /\ i < w2n b + off + 64} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `w2n (a + n2w 32) = w2n a + 32 /\
   w2n (b + n2w off) = w2n b + off /\
   w2n (b + n2w (off+32)) = w2n b + off + 32` by
    (conj_tac
     >- (qspecl_then [`a`, `32`] mp_tac abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
         simp[]) >>
     conj_tac
     >- (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
     qspecl_then [`b`, `off+32`] mp_tac
       abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
  `0 + 32 <= 64 /\ w2n a + 0 < dimword (:256) /\
   off + 32 <= capacity /\ w2n b + off < dimword (:256) /\
   (!i. w2n (a + n2w 0) <= i /\ i < w2n (a + n2w 0) + 32 ==>
      i NOTIN tn.t_mem)` by
    (simp[wordsTheory.WORD_ADD_0] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all emitted_point_word_transfer_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  suspend "second"
QED

Resume emitted_point_pair_checked[second]:
  `sa.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var root s1 = SOME a /\ lookup_var bufroot s1 = SOME b /\
   ptr_covers G1 tn1 root s1 64 /\ ptr_covers G1 tn1 bufroot s1 capacity` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sb root /\ not_fresh_at sb bufroot /\
   32 + 32 <= 64 /\ w2n a + 32 < dimword (:256) /\
   off + 32 + 32 <= capacity /\ w2n b + (off+32) < dimword (:256) /\
   (!i. w2n (a + n2w 32) <= i /\ i < w2n (a + n2w 32) + 32 ==>
     i NOTIN tn1.t_mem)` by
    (simp[] >> rpt gen_tac >> strip_tac >>
     gvs[pred_setTheory.IN_DIFF, pred_setTheory.IN_GSPEC] >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  qpat_x_assum `ptr_covers G tn root s 64` kall_tac >>
  qpat_x_assum `ptr_covers G tn bufroot s capacity` kall_tac >>
  drule_all emitted_point_word_transfer_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >> suspend "compose"
QED

Resume emitted_point_pair_checked[compose]:
  qpat_x_assum `_ sb = ((),sc)` kall_tac >>
  `!i. ~(w2n b + off <= i /\ i < w2n b + off + 64) ==>
    mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (irule memory_observation_mstore >> goal_assum (drule_at Any) >>
        simp[] >> decide_tac) >>
     `mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s1.vs_memory` by
       (irule memory_observation_mstore >> goal_assum (drule_at Any) >>
        simp[] >> decide_tac) >> simp[]) >>
  qpat_x_assum `s1.vs_memory = _` kall_tac >>
  qpat_x_assum `s2.vs_memory = _` kall_tac >>
  rpt (qpat_x_assum `!i. _ ==> i NOTIN _` kall_tac) >>
  conj_tac
  >- (rev_drule run_inst_seq_append >> simp[]) >>
  conj_tac
  >- (irule bodyPtrPrecompileBuiltinsSeqTheory.inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[] >> qexistsl [`G1`, `s1`, `tn1`] >> simp[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
           pred_setTheory.IN_GSPEC] >> gen_tac >>
      Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Finalise emitted_point_pair_checked

(* The three fragments are the actual ECMul input-staging cuts, after
   allocation and before allocation of the result. *)
Theorem ecmul_input_staging_checked:
  (do src <- emit_op ADD [Var root; Lit 0w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 0w];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [Var root; Lit 32w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; scalar] od) sc = ((),sd) /\
  ptr_covers G tn root s 64 /\ lookup_var root s = SOME a /\
  ptr_covers G tn bufroot s 96 /\ lookup_var bufroot s = SOME b /\
  w2n a + 64 < dimword (:256) /\ w2n b + 96 < dimword (:256) /\
  (!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN tn.t_mem) /\
  eval_operand scalar s = SOME w /\ op_taint tn scalar = {} /\
  (!l. scalar <> Label l) /\ (!p. scalar = Var p ==> not_fresh_at sa p) /\
  not_fresh_at sa root /\ not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sd)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' root t 64 /\ ptr_covers G' tn' bufroot t 96 /\
    lookup_var bufroot t = SOME b /\
    (!i. ~(w2n b <= i /\ i < w2n b + 96) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 96} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `0 + 64 <= 96 /\ w2n b + 0 + 64 < dimword (:256)` by simp[] >>
  mp_tac (Q.INST [`off` |-> `0`, `capacity` |-> `96`]
    emitted_point_pair_checked |> SRULE []) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  suspend "scalar"
QED

Resume ecmul_input_staging_checked[scalar]:
  `sa.cs_next_var <= sc.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sb = ((),sc)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     simp[] >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var bufroot s1 = SOME b /\ eval_operand scalar s1 = SOME w /\
   op_taint tn1 scalar = {} /\
   (!p. scalar = Var p ==> not_fresh_at sc p)` by
    (Cases_on `scalar` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  qpat_x_assum `_ sb = ((),sc)` kall_tac >>
  qpat_x_assum `ptr_covers G tn root s 64` kall_tac >>
  qpat_x_assum `ptr_covers G tn bufroot s 96` kall_tac >>
  `96 <= 96 /\ w2n b + 64 < dimword (:256)` by simp[] >>
  drule_all (Q.INST [`off` |-> `64`] emitted_offset_word_store_checked |> SRULE []) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >> suspend "compose"
QED

Resume ecmul_input_staging_checked[compose]:
  qpat_x_assum `_ sc = ((),sd)` kall_tac >>
  qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` kall_tac >>
  `w2n (b + n2w 64) = w2n b + 64` by
    (qspecl_then [`b`, `64`] mp_tac
      abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
  `!i. ~(w2n b <= i /\ i < w2n b + 96) ==>
    mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (first_x_assum irule >> decide_tac) >>
     `mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s1.vs_memory` by
       (irule memory_observation_mstore >> goal_assum (drule_at Any) >>
        simp[] >> decide_tac) >> simp[]) >>
  qpat_x_assum `s2.vs_memory = _` kall_tac >>
  `tn2.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 96}` by
    (simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
          pred_setTheory.IN_GSPEC] >> gen_tac >>
     Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >>
      rev_drule run_inst_seq_append >> simp[]) >>
  conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >>
      irule bodyPtrPrecompileBuiltinsSeqTheory.inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[] >> qexistsl [`G1`, `s1`, `tn1`] >> simp[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[pred_setTheory.IN_DIFF, pred_setTheory.IN_GSPEC] >> metis_tac[]
QED

Finalise ecmul_input_staging_checked

Theorem ecadd_input_staging_checked:
  (do src <- emit_op ADD [Var root1; Lit 0w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 0w];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [Var root1; Lit 32w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  (do src <- emit_op ADD [Var root2; Lit 0w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; value] od) sc = ((),sd) /\
  (do src <- emit_op ADD [Var root2; Lit 32w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 96w];
      emit_void MSTORE [dst; value] od) sd = ((),se) /\
  ptr_covers G tn root1 s 64 /\ lookup_var root1 s = SOME a1 /\
  ptr_covers G tn root2 s 64 /\ lookup_var root2 s = SOME a2 /\
  ptr_covers G tn bufroot s 128 /\ lookup_var bufroot s = SOME b /\
  w2n a1 + 64 < dimword (:256) /\ w2n a2 + 64 < dimword (:256) /\
  w2n b + 128 < dimword (:256) /\
  (!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN tn.t_mem) /\
  not_fresh_at sa root1 /\ not_fresh_at sa root2 /\
  not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd se) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sd ++ emitted_insts sd se)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' root1 t 64 /\ ptr_covers G' tn' root2 t 64 /\
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
  strip_tac >>
  mp_tac (Q.INST [`off` |-> `0`, `capacity` |-> `128`,
    `root` |-> `root1`, `a` |-> `a1`] emitted_point_pair_checked |> SRULE []) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  suspend "second"
QED

Resume ecadd_input_staging_checked[second]:
  `sa.cs_next_var <= sc.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sb = ((),sc)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     simp[] >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var root2 s1 = SOME a2 /\ lookup_var bufroot s1 = SOME b /\
   ptr_covers G1 tn1 root2 s1 64` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sc root2 /\ not_fresh_at sc bufroot /\ 128 <= 128 /\
   (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN tn1.t_mem)` by
    (simp[pred_setTheory.IN_DIFF, pred_setTheory.IN_GSPEC]) >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  qpat_x_assum `_ sb = ((),sc)` kall_tac >>
  rpt (qpat_x_assum `ptr_covers G tn _ s _` kall_tac) >>
  `w2n b + 64 + 64 < dimword (:256)` by simp[] >>
  drule_all (Q.INST [`off` |-> `64`] emitted_point_pair_checked |> SRULE []) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >> suspend "compose"
QED

Resume ecadd_input_staging_checked[compose]:
  qpat_x_assum `_ sc = ((),sd)` kall_tac >>
  qpat_x_assum `_ sd = ((),se)` kall_tac >>
  rpt (qpat_x_assum `!i. _ ==> i NOTIN _` kall_tac) >>
  `!i. ~(w2n b <= i /\ i < w2n b + 128) ==>
    mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (first_x_assum irule >> decide_tac) >>
     `mem_bytes_at i 1 s2.vs_memory = mem_bytes_at i 1 s1.vs_memory` by
       (first_x_assum irule >> decide_tac) >> simp[]) >>
  `tn2.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 128}` by
    (simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
          pred_setTheory.IN_GSPEC] >> gen_tac >>
     Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq ys s1 = OK s2` >>
  rewrite_tac[APPEND_ASSOC] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq xs s = OK s1` >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  conj_tac >- (rev_drule run_inst_seq_append >> simp[Abbr `ys`]) >>
  conj_tac
  >- (irule bodyPtrPrecompileBuiltinsSeqTheory.inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[] >> qexistsl [`G1`, `s1`, `tn1`] >>
      simp[Abbr `ys`]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[pred_setTheory.IN_DIFF, pred_setTheory.IN_GSPEC] >> metis_tac[]
QED

Finalise ecadd_input_staging_checked
