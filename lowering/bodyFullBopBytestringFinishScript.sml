Theory bodyFullBopBytestringFinish
Ancestors
  exprBopDigestProps gasOutcomeFullCompose bodySimFull exprBopSimProps
  loweringStateRelDefs

Theorem bop_bytestring_digest_suffix_full:
  (?raw t Gf tnf.
    t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    run_inst_seq (emitted_insts sa sb) s = OK raw /\
    (raw with vs_vars := s.vs_vars) = s /\
    eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    op_prov Gf op = NONE /\ op_taint tnf op = {} /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf))) /\
  ~s.vs_halted /\ (bop = Eq \/ bop = NotEq) /\
  (?cap. bty = BaseT (BytesT (Dynamic cap)) \/ bty = BaseT (StringT cap)) /\
  evaluate_type (get_tenv cx) bty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  ((?bs. v1 = BytesV bs /\ w1 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v1 = StringV str /\ w1 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) /\
  ((?bs. v2 = BytesV bs /\ w2 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v2 = StringV str /\ w2 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
   (\ss. (bop_result cx ann bop [bty;bty] v1 v2 ss,ss))
   (es,s,G,tn)
   (\H res ee Gf tnf t.
     res = INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2)) /\
     ee = (es with gas_obs := []) /\
     eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (?raw. t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       (raw with vs_vars := s.vs_vars) = s) /\
     (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x) /\
     tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
     tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
     op_prov Gf op = NONE /\ op_taint tnf op = {} /\
     (!x. op = Var x ==> not_fresh_at sb x))
   (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `!ss. bop_result cx ann bop [bty;bty] v1 v2 ss =
     INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2))` by
    (irule comparison_source_result >> metis_tac[]) >>
  (irule gas_outcome_full_pure >>
  (reverse conj_tac >- simp[]) >>
  qexistsl_tac [`Gf`, `es`,
    `INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2))`, `t`, `tnf`] >>
  gvs[] >> metis_tac[])
QED
