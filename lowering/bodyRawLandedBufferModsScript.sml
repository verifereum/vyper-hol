(* The positive-capacity buffered descriptor at the selected CALL landing. *)
Theory bodyRawLandedBufferMods
Ancestors
  bodyRawBufferedResultMods exprSimRawCall bodyFullRawCall
  bodyFullShadowBodyInv bodyFullPreds bodyFullPostsMods
  exprSafeOperand exprOperandVar venomState venomMemDefs
  loweringPosts words arithmetic list

Theorem raw_call_landed_buffer_packet_mods:
  0 < cap /\ (~rev \/ success) /\
  compile_raw_call_outbuf cap s6 = ((ov,op),sout) /\
  fn_has_code s6 sout func /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\
  ci_mono s7 sc /\ cs_extends sc sb /\
  emit_op opc ops s7 = (ok,sc) /\
  compile_raw_call_finish addr dp len gas val_op call_ty cap rev ov op s7 =
    (result,sb) /\
  cap < dimword (:256) /\ ob < dimword (:256) /\ ob + 32 < dimword (:256) /\
  32 + (32 * ((cap + 31) DIV 32) + 32) < dimword (:256) /\
  ov = Var x /\
  eval_operand ov t7 = SOME (n2w ob) /\
  eval_operand op t7 = SOME (n2w (ob + 32)) /\
  safe_operand s7 ov /\ safe_operand s7 op /\
  safe_operand sc ok /\
  eval_operand ok q = SOME (if success then 1w else 0w) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id =
    SOME (ob,32 * ((cap + 31) DIV 32) + 32) /\
  op_prov G7 ov = SOME (ob,32 * ((cap + 31) DIV 32) + 32) /\
  op_prov G7 op = SOME (ob,32 * ((cap + 31) DIV 32) + 32) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  q.vs_allocas = t7.vs_allocas /\
  lookup_var x q = SOME (n2w ob) /\
  FLOOKUP q.vs_allocas s6.cs_next_id =
    SOME (w2n (n2w ob : bytes32),32 * ((cap + 31) DIV 32) + 32) /\
  w2n (n2w (ob + 32) : bytes32) = w2n (n2w ob : bytes32) + 32 /\
  q.vs_returndata = outcome.co_returnData /\
  q.vs_memory = (write_memory_with_expansion (w2n (n2w (ob + 32) : bytes32))
    (TAKE cap q.vs_returndata) t7).vs_memory /\
  tnq.t_mem = tn7.t_mem DIFF
    {i | w2n (n2w (ob + 32) : bytes32) <= i /\
         i < w2n (n2w (ob + 32) : bytes32) + LENGTH (TAKE cap q.vs_returndata)} /\
  q.vs_memory = (write_memory_with_expansion (ob + 32)
    (TAKE cap q.vs_returndata) t7).vs_memory /\
  tnq.t_mem = tn7.t_mem DIFF
    {i | ob + 32 <= i /\ i < ob + 32 + LENGTH (TAKE cap q.vs_returndata)} /\
  ghost_kept_at lo cenv esK s7 G7 tn7 t7 Gq tnq /\
  ptr_covers Gq tnq x q (32 * ((cap + 31) DIV 32) + 32) /\
  MAP FDOM es.scopes = MAP FDOM es2.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id /\
  s6.cs_next_id < s7.cs_next_id /\ s7.cs_next_id < sc.cs_next_id /\
  not_local_ptr cenv es2.scopes var0 /\
  (~rev ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])) /\
  expr_type e = (if rev then BaseT (BytesT (Dynamic cap))
                 else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic cap))]) /\
  es2.scopes = esK.scopes ==>
  ?x w alloc var pre (offset:bytes32) old_tn.
    ov = Var x /\ cap < dimword (:256) /\
    32 + (32 * ((cap + 31) DIV 32) + 32) < dimword (:256) /\
    MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
    alloc.inst_outputs = [var] /\ not_local_ptr cenv es2.scopes var /\
    FLOOKUP q.vs_allocas alloc.inst_id =
      SOME (w2n w,32 * ((cap + 31) DIV 32) + 32) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
    sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= alloc.inst_id /\
    alloc.inst_id < sc.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es2.scopes /\
    not_fresh_at sc x /\ lookup_var x q = SOME w /\
    ptr_covers Gq tnq x q (32 * ((cap + 31) DIV 32) + 32) /\
    w2n offset = w2n w + 32 /\
    q.vs_memory = (write_memory_with_expansion (w2n offset)
      (TAKE cap q.vs_returndata) pre).vs_memory /\
    tnq.t_mem = old_tn.t_mem DIFF
      {i | w2n offset <= i /\
           i < w2n offset + LENGTH (TAKE cap q.vs_returndata)} /\
    (~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
      SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))]))
Proof
    disch_then (map_every assume_tac o CONJUNCTS) >> all_tac >> all_tac >>
  `ci_mono sa s7` by
    (qpat_assum `ci_mono sa s6` (fn th1 =>
       qpat_assum `ci_mono s6 s7` (fn th2 =>
         ACCEPT_TAC (MATCH_MP exprLoweringPropsTheory.ci_mono_trans
           (CONJ th1 th2))))) >>
  `ci_mono sa sc` by
    (qpat_assum `ci_mono sa s7` (fn th1 =>
       qpat_assum `ci_mono s7 sc` (fn th2 =>
         ACCEPT_TAC (MATCH_MP exprLoweringPropsTheory.ci_mono_trans
           (CONJ th1 th2))))) >>
  `local_ptrs_reserved cenv s6 /\ local_ptrs_reserved cenv sc` by
    (conj_tac
     >- (irule exprOperandVarTheory.compiler_ci_mono_reserved >>
         qexists `sa` >> conj_tac >> first_assum ACCEPT_TAC)
     >- (irule exprOperandVarTheory.compiler_ci_mono_reserved >>
         qexists `sa` >> conj_tac >> first_assum ACCEPT_TAC)) >>
  `?alloc var. MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
     alloc.inst_outputs = [var] /\ alloc.inst_id = s6.cs_next_id /\
     not_local_ptr cenv es2.scopes var /\ s6.cs_next_id < sout.cs_next_id` by
    (mp_tac (Q.INST [`sa` |-> `s6`,`sm` |-> `sout`,`scopes` |-> `es2.scopes`,
      `cap` |-> `cap`,`ov` |-> `ov`,`op` |-> `op`]
       exprSimRawCallTheory.raw_call_outbuf_allocation_site) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then strip_assume_tac >>
     qexistsl_tac [`alloc`,`q'`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s6.cs_next_id < sc.cs_next_id` by
    (qpat_assum `s6.cs_next_id < s7.cs_next_id` mp_tac >>
     qpat_assum `s7.cs_next_id < sc.cs_next_id` mp_tac >> decide_tac) >>
  `alloc.inst_id = s6.cs_next_id` by
    (qpat_assum `alloc.inst_id = s6.cs_next_id` ACCEPT_TAC) >>
  `not_fresh_at s7 x` by
    (qpat_assum `safe_operand s7 ov` mp_tac >>
     qpat_assum `ov = Var x` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,exprSafeOperandTheory.safe_operand_def]) >>
  `not_fresh_at sc x` by
    (qpat_assum `ci_mono s7 sc` mp_tac >>
     qpat_assum `not_fresh_at s7 x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  qexistsl_tac [`x`,`n2w ob`,`alloc`,`var`,`t7`,`n2w (ob + 32):bytes32`,`tn7`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `alloc.inst_id = s6.cs_next_id`
         (fn th => rewrite_tac[th])) >>
  TRY (first_assum ACCEPT_TAC) >>
  strip_tac >>
  (conj_tac
   >- first_assum ACCEPT_TAC
   >- metis_tac[])
QED
