(* Scalar underflow checks for relative dynamic-member positions. *)
Theory abiDecodePtrHead
Ancestors
  abiDecodePtrRead abiDecodePtrPrims abiDecoderGuard bodyPtrBopScalarCompile
  emitHelper emitHelperProps exprLoweringProps compileEnv list pred_set
  bodyPtrBopScalarSeq

Theorem abi_decode_ge_guard_scalar:
  abi_decode_ge_guard a b sa = ((),sb) /\ a IN A /\ b IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op LT [a;b] sa = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  `bop_scalar_seq R A (emitted_insts sa c2)
     (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_iszero >> simp[] >>
     qexistsl_tac [`c1`, `LT`, `[a;b]`] >> simp[]) >>
  `bop_scalar_seq R (ok INSERT underflow INSERT A)
     (emitted_insts c2 sb) (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> simp[] >> metis_tac[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  asm_rewrite_tac[] >> metis_tac[bop_scalar_seq_append]
QED

(* Success is conditional on the unsigned guard, not on ABI validity. *)
Theorem abi_decode_ge_guard_success_ptr:
  abi_decode_ge_guard a b sa = ((),sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb <= w2n va /\ fresh_vars_wrt sa s /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  `?B. bop_scalar_seq R {a;b} (emitted_insts sa sb) B` by
    (irule abi_decode_ge_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {a;b} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED
