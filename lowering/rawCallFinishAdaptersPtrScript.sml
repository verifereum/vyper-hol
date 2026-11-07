Theory rawCallFinishAdaptersPtr
Ancestors
  rawCallResultLayoutPtr rawCallAllocationProofPtr wordArgsPtr
  stmtFragPtr vyperTypeExtCallSoundness

Theorem raw_call_outbuf_finish_metadata:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  local_ptrs_reserved cenv sa ==>
  ci_mono sa sb /\ local_ptrs_reserved cenv sb /\
  (?x. ov = Var x /\ not_fresh_at sb x) /\
  (?y. op = Var y /\ not_fresh_at sb y)
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (qspecl_then [`cap`,`sa`] mp_tac exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                       exprLoweringPropsTheory.ci_mono_def] >>
  Cases_on `cap = 0`
  >- (gvs[] >> drule raw_call_outbuf_zero_steps >> strip_tac >>
      drule raw_call_alloc_buffer_metadata >> metis_tac[]) >>
  `0 < cap` by decide_tac >> drule_all raw_call_outbuf_steps >> strip_tac >>
  drule raw_call_alloc_buffer_metadata >> strip_tac >>
  `ci_mono sm sb` by
    (qspecl_then [`ADD`,`[ov;Lit 32w]`,`sm`] mp_tac
      exprLoweringPropsTheory.ci_mono_emit_op >> simp[]) >>
  conj_tac >- metis_tac[stmtFragPtrTheory.not_fresh_at_mono,
                        exprLoweringPropsTheory.ci_mono_def] >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def] >>
  strip_tac >> gvs[] >> simp[compileEnvTheory.not_fresh_at_def] >>
  qexists_tac `sm.cs_next_var` >> simp[]
QED

Theorem raw_call_finish_local_separation:
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  wb_frame cenv es sa s u /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst capacity a len) ==>
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint dst capacity a len)
Proof
  strip_tac >> drule wb_frame_local_regions >>
  disch_then (qspecl_then [`sa`,`u`,`es`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem raw_call_finish_alloca_separation:
  (!id. id < sa.cs_next_id ==> FLOOKUP u.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!id a len. id < sa.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint dst capacity a len) ==>
  (!id a len. id < sa.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (a,len) ==>
    regions_disjoint dst capacity a len)
Proof
  metis_tac[]
QED


Theorem raw_call_finish_return_metadata:
  ci_mono sa sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x)
Proof
  gvs[exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
QED

Theorem raw_call_zero_finish_shape:
  flags.rcf_max_outsize = 0 ==>
  raw_call_return_type flags =
    (if flags.rcf_revert_on_failure then NoneT else BaseT BoolT) /\
  type_memory_bytes cenv (lowered_value_type cenv
    (Call (raw_call_return_type flags) (RawCallTarget flags) args ann)) =
      (if flags.rcf_revert_on_failure then 0 else 32)
Proof
  Cases_on `flags.rcf_revert_on_failure` >>
  simp[vyperTypeSystemTheory.raw_call_return_type_def,
    exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
    compileEnvTheory.type_memory_bytes_def]
QED

Theorem raw_call_positive_bytes_finish_shape:
  0 < n /\ n < dimword(:256) ==>
  ~is_word_type (BaseT (BytesT (Dynamic n))) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n rd)) <=
    32+((n+31) DIV 32)*32 /\
  type_memory_bytes cenv (lowered_value_type cenv
    (Call (BaseT (BytesT (Dynamic n))) (RawCallTarget flags) args ann)) =
    32+((n+31) DIV 32)*32
Proof
  strip_tac >> drule raw_call_bytes_slot_size_bound >> strip_tac >>
  simp[compileEnvTheory.is_word_type_def,
    vyperValueTheory.evaluate_type_def, raw_call_bytes_type_capacity] >>
  `LENGTH (TAKE n rd) <= n` by simp[listTheory.LENGTH_TAKE_EQ] >>
  drule raw_call_bytes_store_capacity >> simp[]
QED

Theorem raw_call_positive_tuple_finish_shape:
  0 < n /\ n < dimword(:256) ==>
  ~is_word_type (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) /\
  evaluate_type (get_tenv cx) (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV flag;BytesV (TAKE n rd)])) <=
    64+((n+31) DIV 32)*32 /\
  type_memory_bytes cenv (lowered_value_type cenv
    (Call (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))])
      (RawCallTarget flags) args ann)) = 64+((n+31) DIV 32)*32
Proof
  strip_tac >> drule raw_call_bytes_slot_size_bound >> strip_tac >>
  simp[compileEnvTheory.is_word_type_def,
    vyperValueTheory.evaluate_type_def, raw_call_tuple_type_capacity] >>
  `LENGTH (TAKE n rd) <= n` by simp[listTheory.LENGTH_TAKE_EQ] >>
  drule raw_call_tuple_store_capacity >> simp[]
QED

Theorem ext_call_kwarg_nonLabel:
  EVERY (\op. !l. op <> Label l) xs /\
  ext_call_kwarg kw ks xs = SOME op ==>
  !l. op <> Label l
Proof
  strip_tac >> drule rawCallPrefixPtrTheory.ext_call_kwarg_member >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem raw_call_finish_operand_transport:
  wb_frame cenv es sa s u /\ ghost_kept cenv es sa G tn s H un /\
  (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) /\
  eval_operand arg s = SOME w ==>
  eval_operand arg u = SOME w /\
  op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg
Proof
  strip_tac >> Cases_on `arg` >>
  gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
      ptrDisciplineTheory.op_taint_def, bodyPtrDefsTheory.ghost_kept_def] >>
  metis_tac[exprSimWordArgsTheory.wb_frame_vars]
QED
