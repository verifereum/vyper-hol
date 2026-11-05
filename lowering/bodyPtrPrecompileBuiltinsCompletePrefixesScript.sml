Theory bodyPtrPrecompileBuiltinsCompletePrefixes
Ancestors bodyPtrPrecompileBuiltinsAllocationTransport
          bodyPtrPrecompileBuiltinsRecoveryInput bodyPtrPrecompileBuiltinsPrefixes
          bodyPtrPrecompileBuiltinsSeq bodyPtrPrecompileBuiltinsTransfer
          bodyPtrPrecompileBuiltinsAllocationFrame exprSimLiteralBuffer
          compileEnv context emitHelper exprLoweringProps freshWrites
          fragExec venomInst venomState ptrDiscipline bodyPtrDefs finite_map list

Theorem allocation_progress:
  compile_alloc_buffer n sa = (buf,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sa sb)
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
           emit_def] >> strip_tac >> gvs[]) >>
  drule emitted_allocation_singleton >> simp[mk_inst_def, is_terminator_def]
QED

Theorem ecmul_complete_prefix_checked:
  compile_alloc_buffer 96 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
  (do src <- emit_op ADD [Var root; Lit 0w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 0w];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [Var root; Lit 32w];
      value <- emit_op MLOAD [src]; dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; scalar] od) sc = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sp) s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn root s0 64 /\ lookup_var root s0 = SOME a /\
  w2n a + 64 < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN new_site_bytes s0 s1) /\
  eval_operand scalar s0 = SOME w /\ op_taint tn scalar = {} /\
  (!l. scalar <> Label l) /\ (!p. scalar = Var p ==> not_fresh_at sf p) /\
  not_fresh_at sf root /\ eval_operand ib.buf_operand s1 = SOME b /\
  w2n b + 96 < dimword(:256) /\
  (!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN new_site_bytes s2 s3) ==>
  ?out Gf tnf.
    ob.buf_operand = Var out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++
       (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp) ++
       emitted_insts sp sm) (s0 with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
      (emitted_insts sf sa ++ emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sp ++ emitted_insts sp sm) /\
    ptr_covers Gf tnf bufroot s3 96 /\ ptr_covers Gf tnf out s3 64 /\
    lookup_var bufroot s3 = SOME b /\
    (!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = ((tn.t_mem UNION new_site_bytes s0 s1) DIFF
      {i | w2n b <= i /\ i < w2n b + 96}) UNION new_site_bytes s2 s3 /\
    (!i. ~(w2n b <= i /\ i < w2n b + 96) ==>
      mem_bytes_at i 1 s3.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sf p ==>
      lookup_var p s3 = lookup_var p s0 /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `96 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `96`] emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `inroot` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `inroot = bufroot` by gvs[] >> gvs[] >>
  `sf.cs_next_var <= sa.cs_next_var` by metis_tac[allocation_progress] >>
  `!p. not_fresh_at sf p ==> not_fresh_at sa p` by
    metis_tac[not_fresh_at_mono] >>
  `ptr_covers G1 tn1 root s1 64 /\ lookup_var root s1 = SOME a /\
   eval_operand scalar s1 = SOME w /\ op_taint tn1 scalar = {} /\
   (!p. scalar = Var p ==> not_fresh_at sa p) /\ not_fresh_at sa root` by
    (conj_tac >- metis_tac[] >>
     Cases_on `scalar` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lookup_var bufroot s1 = SOME b` by gvs[eval_operand_def] >>
  `!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN tn1.t_mem` by
    (simp[pred_setTheory.IN_UNION] >> metis_tac[]) >>
  suspend "stage"
QED

Resume ecmul_complete_prefix_checked[stage]:
  qpat_x_assum `ptr_covers G tn root s0 64` kall_tac >>
  drule_all ecmul_input_staging_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  gvs[] >>
  `sa.cs_next_var <= sp.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
     (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sb = ((),sc)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sc = ((),sp)`
       (mp_then Any strip_assume_tac (Q.INST [`off` |-> `64`] word_store_progress |> SRULE [])) >>
     simp[] >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sp p` by
    metis_tac[not_fresh_at_mono] >>
  `64 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `64`, `G` |-> `G2`, `tn` |-> `tn2`]
    emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `out` (qx_choose_then `G3`
    (qx_choose_then `tn3` strip_assume_tac))) >>
  qexistsl [`out`, `G3`, `tn3`] >> suspend "compose"
QED

Resume ecmul_complete_prefix_checked[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sf sa)` by
    metis_tac[allocation_progress] >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sa) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sp sm)` by
    metis_tac[allocation_progress] >>
  rpt (qpat_x_assum `_ _ = ((),_)` kall_tac) >>
  qpat_x_assum `compile_alloc_buffer 96 _ = _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer 64 _ = _` kall_tac >>
  fs[EVERY_APPEND] >> reverse conj_tac >- (rpt strip_tac >> first_assum irule >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G1 tn1
    ((emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp) ++
      emitted_insts sp sm) (s1 with vs_inst_idx := k) G3 tn3` by
    (irule inst_seq_ptr_append_cursors >>
     reverse conj_tac >- simp[] >> qexistsl [`G2`, `s2`, `tn2`] >> simp[]) >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule (Q.INST [`xs` |-> `emitted_insts sf sa`] inst_seq_ptr_append_cursors) >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`, `s1`, `tn1`] >> simp[]
QED

Finalise ecmul_complete_prefix_checked

Theorem ecadd_complete_prefix_checked:
  compile_alloc_buffer 128 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
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
      emit_void MSTORE [dst; value] od) sd = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp) s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn root1 s0 64 /\ lookup_var root1 s0 = SOME a1 /\
  ptr_covers G tn root2 s0 64 /\ lookup_var root2 s0 = SOME a2 /\
  w2n a1 + 64 < dimword(:256) /\ w2n a2 + 64 < dimword(:256) /\
  (!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN new_site_bytes s0 s1) /\
  (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN new_site_bytes s0 s1) /\
  not_fresh_at sf root1 /\ not_fresh_at sf root2 /\
  eval_operand ib.buf_operand s1 = SOME b /\ w2n b + 128 < dimword(:256) /\
  (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN new_site_bytes s2 s3) ==>
  ?out Gf tnf.
    ob.buf_operand = Var out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++
       (emitted_insts sa sb ++ emitted_insts sb sc ++
        emitted_insts sc sd ++ emitted_insts sd sp) ++ emitted_insts sp sm)
      (s0 with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
      (emitted_insts sf sa ++ emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sd ++ emitted_insts sd sp ++ emitted_insts sp sm) /\
    ptr_covers Gf tnf bufroot s3 128 /\ ptr_covers Gf tnf out s3 64 /\
    lookup_var bufroot s3 = SOME b /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = ((tn.t_mem UNION new_site_bytes s0 s1) DIFF
      {i | w2n b <= i /\ i < w2n b + 128}) UNION new_site_bytes s2 s3 /\
    (!i. ~(w2n b <= i /\ i < w2n b + 128) ==>
      mem_bytes_at i 1 s3.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sf p ==>
      lookup_var p s3 = lookup_var p s0 /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `128 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `128`] emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `inroot` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `inroot = bufroot` by gvs[] >> gvs[] >>
  `sf.cs_next_var <= sa.cs_next_var` by metis_tac[allocation_progress] >>
  `!p. not_fresh_at sf p ==> not_fresh_at sa p` by
    metis_tac[not_fresh_at_mono] >>
  `ptr_covers G1 tn1 root1 s1 64 /\ lookup_var root1 s1 = SOME a1 /\
   ptr_covers G1 tn1 root2 s1 64 /\ lookup_var root2 s1 = SOME a2 /\
   not_fresh_at sa root1 /\ not_fresh_at sa root2` by metis_tac[] >>
  `lookup_var bufroot s1 = SOME b` by gvs[eval_operand_def] >>
  `(!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN tn1.t_mem) /\
   (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN tn1.t_mem)` by
    (simp[pred_setTheory.IN_UNION] >> metis_tac[]) >>
  suspend "stage"
QED

Resume ecadd_complete_prefix_checked[stage]:
  rpt (qpat_x_assum `ptr_covers G tn _ s0 64` kall_tac) >>
  drule_all ecadd_input_staging_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >> gvs[] >>
  `sa.cs_next_var <= sp.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
     (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sb = ((),sc)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sc = ((),sd)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     qpat_assum `_ sd = ((),sp)`
       (mp_then Any strip_assume_tac point_word_transfer_progress) >>
     simp[] >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sp p` by
    metis_tac[not_fresh_at_mono] >>
  `64 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `64`, `G` |-> `G2`, `tn` |-> `tn2`]
    emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `out` (qx_choose_then `G3`
    (qx_choose_then `tn3` strip_assume_tac))) >>
  qexistsl [`out`, `G3`, `tn3`] >> suspend "compose"
QED

Resume ecadd_complete_prefix_checked[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sf sa)` by
    metis_tac[allocation_progress] >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sa) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sp sm)` by
    metis_tac[allocation_progress] >>
  rpt (qpat_x_assum `_ _ = ((),_)` kall_tac) >>
  qpat_x_assum `compile_alloc_buffer 128 _ = _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer 64 _ = _` kall_tac >>
  fs[EVERY_APPEND] >> reverse conj_tac >- (rpt strip_tac >> first_assum irule >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G1 tn1
    ((emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp) ++ emitted_insts sp sm)
    (s1 with vs_inst_idx := k) G3 tn3` by
    (irule inst_seq_ptr_append_cursors >>
     reverse conj_tac >- simp[] >> qexistsl [`G2`, `s2`, `tn2`] >> simp[]) >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule (Q.INST [`xs` |-> `emitted_insts sf sa`] inst_seq_ptr_append_cursors) >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`, `s1`, `tn1`] >> simp[]
QED

Finalise ecadd_complete_prefix_checked

Theorem recovery_complete_prefix_checked:
  compile_alloc_buffer 128 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
  emit_void MSTORE [Var bufroot; h] sa = ((),sb) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 96w];
      emit_void MSTORE [dst; q] od) sd = ((),sp) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\ ob.buf_operand = Var out /\
  emit_void MSTORE [Var out; Lit 0w] sm = ((),sz) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp) s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  run_inst_seq (emitted_insts sm sz) s3 = OK s4 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\
  eval_operand h s0 = SOME wh /\ eval_operand v s0 = SOME wv /\
  eval_operand r s0 = SOME wr /\ eval_operand q s0 = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;r;q] /\
  eval_operand ib.buf_operand s1 = SOME b /\ w2n b + 128 < dimword(:256) /\
  (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN new_site_bytes s2 s3) /\
  eval_operand ob.buf_operand s3 = SOME c /\ w2n c + 32 < dimword(:256) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++
       (emitted_insts sa sb ++ emitted_insts sb sc ++
        emitted_insts sc sd ++ emitted_insts sd sp) ++
       emitted_insts sp sm ++ emitted_insts sm sz)
      (s0 with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
      (emitted_insts sf sa ++ emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sd ++ emitted_insts sd sp ++ emitted_insts sp sm ++
       emitted_insts sm sz) /\
    ptr_covers Gf tnf bufroot s4 128 /\ ptr_covers Gf tnf out s4 32 /\
    lookup_var bufroot s4 = SOME b /\ lookup_var out s4 = SOME c /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n c <= i /\ i < w2n c + 32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = (((tn.t_mem UNION new_site_bytes s0 s1) DIFF
      {i | w2n b <= i /\ i < w2n b + 128}) UNION new_site_bytes s2 s3) DIFF
      {i | w2n c <= i /\ i < w2n c + 32} /\
    (!i. ~(w2n b <= i /\ i < w2n b + 128) /\
         ~(w2n c <= i /\ i < w2n c + 32) ==>
      mem_bytes_at i 1 s4.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sf p ==>
      lookup_var p s4 = lookup_var p s0 /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  `128 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `128`] emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `inroot` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `inroot = bufroot` by gvs[] >> gvs[] >>
  `sf.cs_next_var <= sa.cs_next_var` by metis_tac[allocation_progress] >>
  `!p. not_fresh_at sf p ==> not_fresh_at sa p` by
    metis_tac[not_fresh_at_mono] >>
  `!x w. MEM x [h;v;r;q] /\ eval_operand x s0 = SOME w ==>
    eval_operand x s1 = SOME w /\ op_taint tn1 x = {} /\
    (!p. x = Var p ==> not_fresh_at sa p)` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `x` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lookup_var bufroot s1 = SOME b` by gvs[eval_operand_def] >>
  suspend "stage"
QED

Resume recovery_complete_prefix_checked[stage]:
  `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
   eval_operand r s1 = SOME wr /\ eval_operand q s1 = SOME wq /\
   EVERY (\x. op_taint tn1 x = {} /\ (!l. x <> Label l) /\
     (!p. x = Var p ==> not_fresh_at sa p)) [h;v;r;q]` by
    (simp[EVERY_DEF] >> metis_tac[listTheory.MEM]) >>
  drule_all recovery_input_staging_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >> gvs[] >>
  `sa.cs_next_var <= sp.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
     (emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp)` by
    (qpat_assum `_ sa = ((),sb)`
       (mp_then Any strip_assume_tac direct_word_store_progress) >>
     qpat_assum `_ sb = ((),sc)`
       (mp_then Any strip_assume_tac (Q.INST [`off` |-> `32`] word_store_progress |> SRULE [])) >>
     qpat_assum `_ sc = ((),sd)`
       (mp_then Any strip_assume_tac (Q.INST [`off` |-> `64`] word_store_progress |> SRULE [])) >>
     qpat_assum `_ sd = ((),sp)`
       (mp_then Any strip_assume_tac (Q.INST [`off` |-> `96`] word_store_progress |> SRULE [])) >>
     simp[] >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sp p` by
    metis_tac[not_fresh_at_mono] >>
  `32 < dimword(:256)` by simp[] >>
  drule_all (Q.INST [`n` |-> `32`, `G` |-> `G2`, `tn` |-> `tn2`]
    emitted_allocation_transport) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `outroot` (qx_choose_then `G3`
    (qx_choose_then `tn3` strip_assume_tac))) >>
  `outroot = out` by gvs[] >> gvs[] >>
  suspend "zero"
QED

Resume recovery_complete_prefix_checked[zero]:
  `lookup_var out s3 = SOME c` by gvs[eval_operand_def] >>
  `eval_operand (Lit 0w) s3 = SOME 0w /\ op_taint tn3 (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (Q.INST [`v` |-> `Lit 0w`, `G` |-> `G3`, `tn` |-> `tn3`]
    emitted_direct_word_store_checked) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `u` (qx_choose_then `tn4` strip_assume_tac)) >>
  `!i. ~(w2n c <= i /\ i < w2n c + 32) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s3.vs_memory` by
    (rpt strip_tac >> irule bodyPtrPrecompileBuiltinsObservationsTheory.memory_observation_mstore >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `u = mstore _ _ _` kall_tac >> gvs[] >>
  `ptr_covers G3 tn3 bufroot s3 128 /\ lookup_var bufroot s3 = SOME b` by
    metis_tac[] >>
  `ptr_covers G3 tn4 bufroot s4 128 /\ ptr_covers G3 tn4 out s4 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl [`G3`, `tn4`] >> suspend "compose"
QED

Resume recovery_complete_prefix_checked[compose]:
  qpat_assum `emit_void MSTORE _ sm = _`
    (mp_then Any strip_assume_tac direct_word_store_progress) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sf sa) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sp sm)` by
    metis_tac[allocation_progress] >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sa) /\
   EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
     i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sp sm)` by
    metis_tac[allocation_progress] >>
  rpt (qpat_x_assum `_ _ = ((),_)` kall_tac) >>
  qpat_x_assum `compile_alloc_buffer 128 _ = _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer 32 _ = _` kall_tac >>
  fs[EVERY_APPEND] >> reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G2 tn2
    (emitted_insts sp sm ++ emitted_insts sm sz)
    (s2 with vs_inst_idx := k) G3 tn4` by
    (irule inst_seq_ptr_append_cursors >>
     reverse conj_tac >- simp[] >> qexistsl [`G3`, `s3`, `tn3`] >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G1 tn1
    ((emitted_insts sa sb ++ emitted_insts sb sc ++
      emitted_insts sc sd ++ emitted_insts sd sp) ++
      (emitted_insts sp sm ++ emitted_insts sm sz))
    (s1 with vs_inst_idx := k) G3 tn4` by
    (irule inst_seq_ptr_append_cursors >>
     reverse conj_tac >- simp[] >> qexistsl [`G2`, `s2`, `tn2`] >> simp[]) >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule (Q.INST [`xs` |-> `emitted_insts sf sa`] inst_seq_ptr_append_cursors) >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`, `s1`, `tn1`] >> fs[APPEND_ASSOC]
QED

Finalise recovery_complete_prefix_checked
