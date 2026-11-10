(* Compiler-facing checked suffix for the shared reason encoder. *)
Theory reasonFinishPtr
Ancestors reasonFinishCode reasonEncoderTailPtr reasonRevertPtr fragExec
  emitHelper emitHelperProps compileEnv loweringStateRelDefs venomInst compilerChainCode exprLoweringProps bodyPtrDefs
Libs intLib wordsLib

(* Erasing only the fresh-name counter lets emit_op's allocated names feed
   the emit_inst block interfaces without changing any emitted instruction. *)
Theorem reason_emit_op_counter_projection[local]:
  emit_op opc ops sa = (out,sb) ==>
  ?v. out = Var v /\
    v = "%" ++ toString sa.cs_next_var /\
    emit_inst opc ops [v] (sa with cs_next_var := 0) =
      ((),sb with cs_next_var := 0) /\
    sb.cs_next_var = sa.cs_next_var + 1
Proof
  simp[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem reason_emit_inst_counter_projection[local]:
  emit_inst opc ops outs sa = ((),sb) ==>
  emit_inst opc ops outs (sa with cs_next_var := 0) =
    ((),sb with cs_next_var := 0) /\
  sb.cs_next_var = sa.cs_next_var
Proof
  simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem reason_fn_has_code_counter_projection[local]:
  fn_has_code sa sb func ==>
  fn_has_code (sa with cs_next_var := 0) (sb with cs_next_var := 0) func
Proof
  simp[fn_has_code_def, emitted_blocks_def]
QED

Theorem reason_encode_finish_parts[local]:
  reason_encode_finish outer payload tuple slot sa = ((),sb) ==>
  ?src head off tail len tmp0 rounded0 last cnt tmp1 rounded1 item size_out encoded
    start rlen p1 p2 p3 p4 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15.
    emit_op ADD [tuple;Lit 0w] sa = (src,p1) /\
    emit_op ADD [payload;Lit 0w] p1 = (head,p2) /\
    emit_op MLOAD [slot] p2 = (off,p3) /\
    emit_op ADD [payload;off] p3 = (tail,p4) /\
    emit_op MLOAD [src] p4 = (len,c1) /\
    emit_op ADD [len;Lit 31w] c1 = (tmp0,c2) /\
    emit_op AND [tmp0;Lit (i2w (-32))] c2 = (rounded0,c3) /\
    emit_op ADD [tail;rounded0] c3 = (last,c4) /\
    emit_void MSTORE [last;Lit 0w] c4 = ((),c5) /\
    emit_op ADD [Lit 32w;len] c5 = (cnt,c6) /\
    emit_void MCOPY [tail;src;cnt] c6 = ((),c7) /\
    emit_op ADD [len;Lit 31w] c7 = (tmp1,c8) /\
    emit_op AND [tmp1;Lit (i2w (-32))] c8 = (rounded1,c9) /\
    emit_op ADD [Lit 32w;rounded1] c9 = (item,c10) /\
    emit_void MSTORE [head;off] c10 = ((),c11) /\
    emit_op ADD [off;item] c11 = (size_out,c12) /\
    emit_void MSTORE [slot;size_out] c12 = ((),c13) /\
    emit_op MLOAD [slot] c13 = (encoded,c14) /\
    emit_op ADD [outer;Lit 28w] c14 = (start,c15) /\
    (?c16. emit_op ADD [Lit 4w;encoded] c15 = (rlen,c16) /\
      emit_inst REVERT [start;rlen] [] c16 = ((),sb))
Proof
  `i2w (-32) =
    (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w : bytes32)`
    by EVAL_TAC >>
  simp[reason_encode_finish_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def]) >> metis_tac[]
QED

Theorem reason_emit_void_counter_projection[local]:
  emit_void opc ops sa = ((),sb) ==>
  emit_void opc ops (sa with cs_next_var := 0) =
    ((),sb with cs_next_var := 0) /\
  sb.cs_next_var = sa.cs_next_var
Proof
  simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem reason_encode_finish_inst_parts[local]:
  reason_encode_finish (Var outer) (Var payload) (Var tuple) (Var slot) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?src head off tail len tmp0 rounded0 last cnt tmp1 rounded1 item size_out encoded
    start rlen p1 p2 p3 p4 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16.
    emit_inst ADD [Var tuple;Lit 0w] [src] (sa with cs_next_var := 0) = ((),p1) /\
    emit_inst ADD [Var payload;Lit 0w] [head] p1 = ((),p2) /\
    emit_inst MLOAD [Var slot] [off] p2 = ((),p3) /\
    emit_inst ADD [Var payload;Var off] [tail] p3 = ((),p4) /\
    emit_inst MLOAD [Var src] [len] p4 = ((),c1) /\
    emit_inst ADD [Var len;Lit 31w] [tmp0] c1 = ((),c2) /\
    emit_inst AND [Var tmp0;Lit (i2w (-32))] [rounded0] c2 = ((),c3) /\
    emit_inst ADD [Var tail;Var rounded0] [last] c3 = ((),c4) /\
    emit_void MSTORE [Var last;Lit 0w] c4 = ((),c5) /\
    emit_inst ADD [Lit 32w;Var len] [cnt] c5 = ((),c6) /\
    emit_void MCOPY [Var tail;Var src;Var cnt] c6 = ((),c7) /\
    emit_inst ADD [Var len;Lit 31w] [tmp1] c7 = ((),c8) /\
    emit_inst AND [Var tmp1;Lit (i2w (-32))] [rounded1] c8 = ((),c9) /\
    emit_inst ADD [Lit 32w;Var rounded1] [item] c9 = ((),c10) /\
    emit_void MSTORE [Var head;Var off] c10 = ((),c11) /\
    emit_inst ADD [Var off;Var item] [size_out] c11 = ((),c12) /\
    emit_void MSTORE [Var slot;Var size_out] c12 = ((),c13) /\
    emit_inst MLOAD [Var slot] [encoded] c13 = ((),c14) /\
    emit_inst ADD [Var outer;Lit 28w] [start] c14 = ((),c15) /\
    emit_inst ADD [Lit 4w;Var encoded] [rlen] c15 = ((),c16) /\
    emit_inst REVERT [Var start;Var rlen] [] c16 = ((),sb with cs_next_var := 0) /\
    EVERY (\(a,b). fn_has_code a b func)
      (ZIP (FRONT ((sa with cs_next_var := 0)::
        [p1;p2;p3;p4;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16;
         sb with cs_next_var := 0]),
        [p1;p2;p3;p4;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16;
         sb with cs_next_var := 0])) /\
    ALL_DISTINCT [src;head;off;tail;len;tmp0;rounded0;last;cnt;tmp1;rounded1;item;
      size_out;encoded;start;rlen] /\
    (!p. not_fresh_at sa p ==>
      ~MEM p [src;head;off;tail;len;tmp0;rounded0;last;cnt;tmp1;rounded1;item;
        size_out;encoded;start;rlen])
Proof
  strip_tac >> drule reason_encode_finish_parts >> strip_tac >>
  imp_res_tac reason_emit_op_counter_projection >>
  imp_res_tac reason_emit_void_counter_projection >>
  imp_res_tac reason_emit_inst_counter_projection >>
  qpat_x_assum `reason_encode_finish _ _ _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ sa = _` kall_tac) >>
  gvs[] >>
  qexistsl_tac [`"%" ++ toString sa.cs_next_var`,
    `"%" ++ toString (sa.cs_next_var + 1)`,
    `"%" ++ toString (sa.cs_next_var + 2)`,
    `"%" ++ toString (sa.cs_next_var + 3)`,
    `"%" ++ toString (sa.cs_next_var + 4)`,
    `"%" ++ toString (sa.cs_next_var + 5)`,
    `"%" ++ toString (sa.cs_next_var + 6)`,
    `"%" ++ toString (sa.cs_next_var + 7)`,
    `"%" ++ toString (sa.cs_next_var + 8)`,
    `"%" ++ toString (sa.cs_next_var + 9)`,
    `"%" ++ toString (sa.cs_next_var + 10)`,
    `"%" ++ toString (sa.cs_next_var + 11)`,
    `"%" ++ toString (sa.cs_next_var + 12)`,
    `"%" ++ toString (sa.cs_next_var + 13)`,
    `"%" ++ toString (sa.cs_next_var + 14)`,
    `"%" ++ toString (sa.cs_next_var + 15)`] >>
  simp[listTheory.ALL_DISTINCT, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  suspend "slices"
QED

Resume reason_encode_finish_inst_parts[slices]:
  irule (SRULE [] (Q.SPEC
    `[p1 with cs_next_var := 0;p2 with cs_next_var := 0;
      p3 with cs_next_var := 0;p4 with cs_next_var := 0;
      c1 with cs_next_var := 0;c2 with cs_next_var := 0;
      c3 with cs_next_var := 0;c4 with cs_next_var := 0;
      c5 with cs_next_var := 0;c6 with cs_next_var := 0;
      c7 with cs_next_var := 0;c8 with cs_next_var := 0;
      c9 with cs_next_var := 0;c10 with cs_next_var := 0;
      c11 with cs_next_var := 0;c12 with cs_next_var := 0;
      c13 with cs_next_var := 0;c14 with cs_next_var := 0;
      c15 with cs_next_var := 0;c16 with cs_next_var := 0;
      sb with cs_next_var := 0]` compiler_chain_has_code)) >>
  rpt conj_tac >>~-
    ([`cs_extends _ _`],
     metis_tac[SRULE [ci_mono_def] ci_mono_emit_inst,
               SRULE [ci_mono_def] ci_mono_emit_void, pairTheory.SND]) >>
  irule reason_fn_has_code_counter_projection >> simp[]
QED

Finalise reason_encode_finish_inst_parts


Theorem reason_encode_finish_path_ptr:
  reason_encode_finish (Var outer) (Var payload) (Var tuple) (Var slot) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  (!p. MEM p [outer;payload;tuple;slot] ==> not_fresh_at sa p) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var tuple s = SOME a /\ ptr_covers G tn tuple s m /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n /\
  lookup_var payload s = SOME b /\ ptr_covers G tn payload s (32 + m) /\
  lookup_var slot s = SOME addr /\ ptr_covers G tn slot s 32 /\
  (!i. w2n addr <= i /\ i < w2n addr + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n addr) s = 32w /\
  lookup_var outer s = SOME outer_addr /\ ptr_covers G tn outer s (64 + m) /\
  32 <= m /\ w2n (32w + n) <= m /\
  w2n ((n + 31w) && i2w (-32)) + 32 <= m /\
  w2n b + 32 < dimword (:256) /\
  w2n (b + 32w) + w2n ((n + 31w) && i2w (-32)) < dimword (:256) /\
  w2n outer_addr + 28 < dimword (:256) /\
  28 + w2n (4w + (32w + (32w + ((n + 31w) && i2w (-32))))) <= 64 + m ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >> drule_all reason_encode_finish_inst_parts >> strip_tac >>
  fs[Excl "ALL_DISTINCT"] >>
  `?G2 tn2 s2.
    gas_path_ptr D 0 ctx func PG G tn s 0 G2 tn2 (OK s2) /\
    s2.vs_current_bb = c14.cs_current_bb /\
    s2.vs_inst_idx = LENGTH c14.cs_current_insts /\ ~s2.vs_halted /\
    lookup_var encoded s2 = SOME (32w + (32w + ((n + 31w) && i2w (-32)))) /\
    op_taint tn2 (Var encoded) = {} /\
    (!p. ~MEM p [src;head;off;tail;len;tmp0;rounded0;last;cnt;
                tmp1;rounded1;item;size_out;encoded] ==>
      lookup_var p s2 = lookup_var p s /\
      FLOOKUP G2 p = FLOOKUP G p /\
      op_taint tn2 (Var p) = op_taint tn (Var p))` by suspend "payload" >>
  suspend "terminal"
QED

Resume reason_encode_finish_path_ptr[payload]:
  irule (Q.INST [`tuple_capacity` |-> `m`, `capacity` |-> `32 + m`,
    `sa` |-> `sa with cs_next_var := 0`] reason_encoder_payload_ptr) >>
  rpt conj_tac
  >- (simp[])
  >- (simp[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >- (gvs[])
  >>
  qexistsl [`a`, `addr`, `b`, `c1`, `c10`, `c11`, `c12`, `c13`,
    `c2`, `c3`, `c4`, `c5`, `c6`, `c7`, `c8`, `c9`, `m`,
    `p1`, `p2`, `p3`, `payload`, `sa`, `slot`, `p4`, `tuple`] >>
  simp[Excl "ALL_DISTINCT"] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` mp_tac >>
  qpat_x_assum `!p. _ ==> not_fresh_at sa p` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]
QED

Resume reason_encode_finish_path_ptr[terminal]:
  `~MEM outer [src;head;off;tail;len;tmp0;rounded0;last;cnt;
               tmp1;rounded1;item;size_out;encoded]` by
    (qpat_x_assum `!p. not_fresh_at sa p ==> _` mp_tac >>
     qpat_x_assum `!p. _ ==> not_fresh_at sa p` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `lookup_var outer s2 = lookup_var outer s /\
   FLOOKUP G2 outer = FLOOKUP G outer /\
   op_taint tn2 (Var outer) = op_taint tn (Var outer)` by
    (first_x_assum irule >> simp[]) >>
  `ptr_covers G2 tn2 outer s2 (64 + m)` by
    (qpat_x_assum `ptr_covers G tn outer s _` mp_tac >>
     simp[ptr_covers_def]) >>
  `?Gf tnf sf. gas_path_ptr D 0 ctx func PG G2 tn2 s2 0 Gf tnf
      (Abort Revert_abort sf)` by suspend "revert" >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume reason_encode_finish_path_ptr[revert]:
  irule (Q.INST [`capacity` |-> `64 + m`] reason_encoder_revert_path_ptr) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl [`outer_addr`, `c15`, `c16`, `encoded`, `rlen`, `m`,
    `32w + (32w + ((n + 31w) && i2w (-32)))`, `outer`, `c14`,
    `sb with cs_next_var := 0`, `start`] >>
  simp[Excl "ALL_DISTINCT"] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[]
QED

Finalise reason_encode_finish_path_ptr
