(* Linked, gas-silent comparison of two bytestring digests. *)
Theory bodyBopBytestringDigestMods
Ancestors
  bodyFullBopBytestringDigest exprBopDigestProps gasOutcomeFullPostMods

(* The post records the actual instruction run and the readonly frame on
   the same endpoint, for the subsequent parent expression post. *)
Theorem bop_bytestring_digest_suffix_mods:
  (if bop = vyperAST$Eq then emit_op EQ [h1;h2] sa
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] sa)]
                       (SND (emit_op EQ [h1;h2] sa))) = (op,sb) /\
  (bop = Eq \/ bop = NotEq) /\
  eval_operand h1 s = SOME w1 /\ eval_operand h2 s = SOME w2 /\
  op_prov G h1 = NONE /\ op_prov G h2 = NONE /\
  op_taint tn h1 = {} /\ op_taint tn h2 = {} /\
  (!x. h1 = Var x ==> not_fresh_at sa x) /\
  (!x. h2 = Var x ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?cap. bty = BaseT (BytesT (Dynamic cap)) \/ bty = BaseT (StringT cap)) /\
  evaluate_type (get_tenv cx) bty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  ((?bs. v1 = BytesV bs /\ w1 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v1 = StringV str /\ w1 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) /\
  ((?bs. v2 = BytesV bs /\ w2 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v2 = StringV str /\ w2 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (\ss. (bop_result cx ann bop [bty;bty] v1 v2 ss,ss)) (es,s,G,tn)
    (\H res ee Gf tnf t.
      res = INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2)) /\
      ee = (es with gas_obs := []) /\
      eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?raw. t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
        run_inst_seq (emitted_insts sa sb) s = OK raw /\
        (raw with vs_vars := s.vs_vars) = s) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x) /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      op_prov Gf op = NONE /\ op_taint tnf op = {} /\
      (!x. op = Var x ==> not_fresh_at sb x)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!ss. bop_result cx ann bop [bty;bty] v1 v2 ss =
     INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2))` by
    (irule comparison_source_result >> simp[] >>
     qexistsl_tac [`get_tenv cx`, `tv`] >> simp[]) >>
  drule_all bop_bytestring_digest_operational >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >>
  (reverse conj_tac >- simp[]) >>
  qexistsl_tac [`Gf`, `es`,
    `INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2))`, `t`, `tnf`] >>
  gvs[]
QED
