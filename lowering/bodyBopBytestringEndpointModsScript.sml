Theory bodyBopBytestringEndpointMods
Ancestors
  bodyBopBytestringDigestMods bodyBopBytestringFinalMods gasOutcomeFullPostMods

Theorem bop_bytestring_compare_digest_endpoint_mods:
  (if bop = vyperAST$Eq then emit_op EQ [h1;h2] sh2
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] sh2)]
                       (SND (emit_op EQ [h1;h2] sh2))) = (op,sb) /\
  (bop = Eq \/ bop = NotEq) /\
  eval_operand h1 u = SOME w1 /\ eval_operand h2 u = SOME w2 /\
  op_prov G2 h1 = NONE /\ op_prov G2 h2 = NONE /\
  op_taint tn2 h1 = {} /\ op_taint tn2 h2 = {} /\
  (!x. h1 = Var x ==> not_fresh_at sh2 x) /\
  (!x. h2 = Var x ==> not_fresh_at sh2 x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  allocas_from lo u /\ ~u.vs_halted /\
  fn_has_code sh2 sb func /\ u.vs_current_bb = sh2.cs_current_bb /\
  u.vs_inst_idx = LENGTH sh2.cs_current_insts /\
  (?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
         expr_type e1 = BaseT (StringT cap)) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  ((?bs. v1 = BytesV bs /\ w1 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 bs)) \/
   (?str. v1 = StringV str /\ w1 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) /\
  ((?bs. v2 = BytesV bs /\ w2 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 bs)) \/
   (?str. v2 = StringV str /\ w2 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (\ss. (bop_result cx (BaseT BoolT) bop
      [expr_type e1;expr_type e1] v1 v2 ss,ss)) (ee,u,G2,tn2)
    (\H res ee' Gf tnf t.
      res = INL (BoolV (if bop = Eq then w1 = w2 else w1 <> w2)) /\
      ee' = (ee with gas_obs := []) /\
      eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?raw. t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       run_inst_seq (emitted_insts sh2 sb) u = OK raw /\
       (raw with vs_vars := u.vs_vars) = u) /\
      (!x. not_fresh_at sh2 x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP Gf x = FLOOKUP G2 x /\ FLOOKUP tnf.t_var x = FLOOKUP tn2.t_var x) /\
      tnf.t_mem = tn2.t_mem /\ tnf.t_stor = tn2.t_stor /\
      tnf.t_trans = tn2.t_trans /\ tnf.t_imm = tn2.t_imm /\
      op_prov Gf op = NONE /\ op_taint tnf op = {} /\
      (!x. op = Var x ==> not_fresh_at sb x)) R
Proof
  strip_tac >>
  irule (Q.INST [`mods` |-> `cenv.ce_modules`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                 `ann` |-> `BaseT BoolT`, `bty` |-> `expr_type e1`,
                 `es` |-> `ee`, `s` |-> `u`, `G` |-> `G2`, `tn` |-> `tn2`,
                 `sa` |-> `sh2`] bop_bytestring_digest_suffix_mods) >>
  rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (qexistsl_tac [`h1`,`h2`] >> simp[]) ORELSE
     (metis_tac[]) ORELSE simp[])
QED

Theorem bop_bytestring_compare_final_post_endpoint_mods:
  wb_frame cenv es es1 sa s0 t /\
  (~expr_has_effect e1 ==> pure_frame cenv func es sa s0 t) /\
  wb_frame cenv es1 ee s1 t u /\
  (~expr_has_effect e2 ==> pure_frame cenv func es1 s1 t u) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee u /\
  immutable_frame_mods func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at s2 x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at s2 x) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq) /\
  ghost_inv_at_mods D lo d cenv cx ee G2 tn2 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 s1 G1 tn1 t G2 tn2 /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  alloca_history func u /\ fn_inst_ids_distinct func /\
  fn_has_code s2 sb func /\
  (if bop = Eq then emit_op EQ [h1;h2] s2
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] s2)]
     (SND (emit_op EQ [h1;h2] s2))) = (op,sb) /\
  u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
  run_inst_seq (emitted_insts s2 sb) u = OK raw0 /\
  (raw0 with vs_vars := u.vs_vars) = u /\
  ss = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (raw with vs_vars := u.vs_vars) = u /\
  ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand op ss = SOME (bool_to_word b) /\
  (!z. not_fresh_at s2 z ==> lookup_var z ss = lookup_var z u /\
    FLOOKUP Gf z = FLOOKUP G2 z /\ FLOOKUP tnf.t_var z = FLOOKUP tn2.t_var z) /\
  tnf.t_mem = tn2.t_mem /\ tnf.t_stor = tn2.t_stor /\
  tnf.t_trans = tn2.t_trans /\ tnf.t_imm = tn2.t_imm /\
  op_prov Gf op = NONE /\ op_taint tnf op = {} ==>
  expr_post_mods H ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee (BoolV b) op ss /\
  expr_store_bound cx (expr_type (Builtin (BaseT BoolT) (Bop bop) [e1;e2]))
    (BoolV b) op ss /\
  ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func ss /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp ss) /\
  s0.vs_alloca_next <= ss.vs_alloca_next /\
  ghost_inv_at_mods D lo d cenv cx ee Gf tnf ss /\
  ptr_val_ok cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2]))
    (BoolV b) op Gf tnf ss /\
  (~is_word_type (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) ==>
    ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) op Gf ss) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> irule bop_bytestring_final_post_mods >>
  rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (qexistsl_tac [`G1`,`G2`,`es1`,`h1`,`h2`,`raw`,`raw0`,`s1`,`s2`,`t`,`tn1`,`tn2`,`u`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) ORELSE simp[])
QED

Theorem bop_bytestring_compare_exit_endpoint_mods:
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)
Proof
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
