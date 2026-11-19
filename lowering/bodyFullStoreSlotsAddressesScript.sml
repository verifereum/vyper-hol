Theory bodyFullStoreSlotsAddresses
Ancestors
  placeStoreSlots typedCopyOriginPtrBase typedMemoryCopy fragGasCopyLoop
  emitHelperProps emitHelper compileEnv ptrDiscipline venomState
  venomExecSemantics venomInst fragGasSeqPtr fragGasOriginPtr
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  assignTuplePtrCopyLen fragGasOriginPtrLoop

Theorem store_address_binop_uniform:
  emit_op opc [left;right] a = (op,b) /\ fn_has_code a b func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at b out /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst a.cs_next_id opc [left;right] [out])
      (update_var out w s) /\
    tf = step_taint (mk_inst a.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    allocas_from lo t /\ op_taint tf op = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    (!p. not_fresh_at a p ==> p <> out /\
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_binop_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> drule_all typed_copy_origin_ptr_binop_path >>
     disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
     gvs[]) >>
  `!p. not_fresh_at a p ==> p <> out` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  qexistsl [`out`,`t`,`G'`,`tn'`] >>
  gvs[] >>
  (simp[typed_copy_origin_ptr_binop_ghost_frame] >>
   conj_tac >- (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
   rpt strip_tac >> `p <> out` by metis_tac[] >>
   simp[typed_copy_origin_ptr_binop_ghost_frame] >>
   simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE])
QED

Theorem store_scaled_address_uniform[local]:
  emit_op MUL [Var counter; Lit (n2w stride)] a = (off,b) /\
  emit_op ADD [bop;off] b = (addr,c) /\ fn_has_code a c func /\
  not_fresh_at a counter /\ (!x. bop = Var x ==> not_fresh_at a x) /\
  lookup_var counter s = SOME (n2w i) /\ eval_operand bop s = SOME w /\
  op_taint tn (Var counter) = {} /\ op_taint tn bop = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    addr = Var out /\ not_fresh_at c out /\ cs_extends a c /\
    eval_operand addr t = SOME (w+n2w(i*stride)) /\ op_taint tf addr = {} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t = s /\
    allocas_from lo t /\ t.vs_current_bb = c.cs_current_bb /\
    t.vs_inst_idx = LENGTH c.cs_current_insts /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!root total n. bop = Var root /\ ptr_covers G tn root s total /\
      i*stride+n <= total /\ w2n w+i*stride < dimword(:256) ==>
      ptr_covers Gf tf out t n)
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `eval_operand (Var counter) s = SOME (n2w i) /\
   eval_operand (Lit (n2w stride)) s = SOME (n2w stride) /\
   op_taint tn (Lit (n2w stride)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `w` |-> `x*y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q1,G1,tn1)` >>
  `q1.vs_labels = s.vs_labels` by simp[Abbr `q1`,update_var_def] >>
  `eval_operand bop q1 = SOME w /\ op_taint tn1 bop = {}` by
    (Cases_on `bop` >> fs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `eval_operand off q1 = SOME (n2w i * n2w stride) /\ ~q1.vs_halted /\
   q1.vs_current_bb = b.cs_current_bb /\
   q1.vs_inst_idx = LENGTH b.cs_current_insts` by
    simp[Abbr `q1`,eval_operand_def,lookup_var_def,update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  `allocas_from lo q1` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     simp[Abbr `q1`, allocas_from_def, update_var_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q1)` by
    (simp[Abbr `q1`,allocas_below_fmp_def,update_var_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (q1,_,_) [] (OK q2,G2,tn2)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK q2,G2,tn2)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `!p. not_fresh_at a p ==> not_fresh_at b p` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_def,
      freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand addr q2 = SOME (w+n2w(i*stride)) /\
   q2.vs_current_bb = c.cs_current_bb /\
   q2.vs_inst_idx = LENGTH c.cs_current_insts /\ ~q2.vs_halted /\
   q2.vs_memory = s.vs_memory /\ q2.vs_allocas = s.vs_allocas /\
   q2.vs_alloca_next = s.vs_alloca_next /\ q2.vs_labels = s.vs_labels /\
   q2.vs_call_ctx = s.vs_call_ctx /\ store_copy_normalize s q2 = s` by
    simp[Abbr `q2`,Abbr `q1`,update_var_def,eval_operand_def,
      lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,wordsTheory.word_mul_n2w,
      stmtSimStoreCopyTheory.store_copy_normalize_def,venom_state_component_equality] >>
  `allocas_from lo q2` by
    (PURE_REWRITE_TAC[allocas_from_def] >>
     qpat_assum `q2.vs_allocas = s.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qexistsl [`out'`,`q2`,`G2`,`tn2`] >> simp[] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qx_genl_tac [`root`,`capacity`,`n`] >> strip_tac >>
  `ptr_covers G1 tn1 root q1 capacity` by
    (irule ptr_covers_lookup_frame >> metis_tac[]) >>
  `root <> out'` by metis_tac[] >>
  `lookup_var root q1 = SOME w` by gvs[eval_operand_def] >>
  `eval_operand off q1 = SOME (n2w (i*stride))` by simp[wordsTheory.word_mul_n2w] >>
  simp[Abbr `G2`,Abbr `tn2`,Abbr `q2`,wordsTheory.word_mul_n2w] >>
  irule typed_copy_origin_ptr_offset_covers >>
  gvs[] >> qexists `capacity` >> simp[]
QED

Theorem store_slots_addresses_origin_ptr_path:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  op_taint tn (Var counter) = {} /\ op_taint tn src = {} /\
  op_taint tn dst = {} /\ i < N /\
  w2n sw + N*ss < dimword(:256) /\
  w2n dw + N*ds <= dimword(:256) /\
  (ss <> 0 ==> ?x. src = Var x /\ ptr_covers G tn x s (N*ss)) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?vsp vdp t Gf tf.
    sp = Var vsp /\ dp = Var vdp /\
    not_fresh_at sb vsp /\ not_fresh_at sb vdp /\
    eval_operand sp t = SOME (sw+n2w (i*ss)) /\
    eval_operand dp t = SOME (dw+n2w (i*ds)) /\
    op_taint tf sp = {} /\ op_taint tf dp = {} /\
    (ss <> 0 ==> ptr_covers Gf tf vsp t ss) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [Var counter; Lit (n2w ss)] sa = (so,s1)` >>
  rename1 `emit_op ADD [src;so] s1 = (sp,s2)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w ds)] s2 = (doff,s3)` >>
  rename1 `emit_op ADD [dst;doff] s3 = (dp,s4)` >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa s2 func /\ fn_has_code s2 s4 func` by
    metis_tac[fragExecTheory.fn_has_code_split,cs_extends_trans] >>
  drule_all store_scaled_address_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `sp = Var vsp` >>
  `eval_operand dst t = SOME dw /\ op_taint tf dst = {} /\
   lookup_var counter t = SOME (n2w i) /\ op_taint tf (Var counter) = {}` by
    (Cases_on `dst` >> fs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `not_fresh_at s2 counter /\ (!x. dst = Var x ==> not_fresh_at s2 x)` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_def,
      freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_x_assum `store_copy_normalize s t = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       venom_state_component_equality,allocas_below_fmp_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  drule_all store_scaled_address_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gf`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    metis_tac[typed_copy_emit_op_mono,exprLoweringPropsTheory.ci_mono_def,
      freshWritesTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `not_fresh_at s4 vsp` by
    metis_tac[typed_copy_emit_op_mono,exprLoweringPropsTheory.ci_mono_def,
      freshWritesTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `eval_operand sp t' = SOME (sw+n2w(i*ss)) /\ op_taint tf' sp = {}` by
    gvs[eval_operand_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t',Gf',tf')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `store_copy_normalize s t' = s` by
    metis_tac[placeStoreSlotsTheory.store_slots_normalize_compose] >>
  qexistsl [`vsp`,`out`,`t'`,`Gf'`,`tf'`] >> simp[] >>
  strip_tac >>
  `i*ss+ss <= N*ss /\ w2n sw+i*ss < dimword(:256)` by
    (conj_tac >- (`i*ss+ss = SUC i*ss` by simp[arithmeticTheory.MULT_CLAUSES] >>
       asm_rewrite_tac[] >> simp[]) >>
     `i*ss <= N*ss` by simp[] >> decide_tac) >>
  `ptr_covers Gf tf vsp t ss` by metis_tac[] >>
  irule ptr_covers_lookup_frame >> metis_tac[]
QED
