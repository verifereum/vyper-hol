(* Uniform dynamic-argument lower-bound guard, without runtime freshness. *)
Theory defaultBytesGuardPrelude
Ancestors moduleLowering abiDecoderGuard abiDecodeGuardScalar emitHelperProps emitHelper compileEnv
  exprLoweringProps bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  fragGasSeqPtr fragGasOriginPtrLoop fragGasCopyLoop fragExecMem
  bodyPtrDefs ptrDiscipline ptrSafeRun venomState venomExecSemantics venomInst
  finite_map pred_set words list arithmetic

Theorem default_bytes_guard_shape:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) ==>
  abi_decode_ge_guard src (Lit 4w) sa = ((),sb) /\
  inst_extends sa sb /\ same_blocks sa sb /\
  sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_next_id = sa.cs_next_id + 3 /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id LT [src;Lit 4w] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) ISZERO [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) ASSERT [Var ("%" ++ toString (sa.cs_next_var+1))] []]
Proof
  simp[compile_abi_arg_ptr_guard_def, abi_decode_ge_guard_def] >> strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, inst_extends_def, same_blocks_def,
    APPEND_ASSOC, DROP_PREFIX]
QED

Theorem default_bytes_guard_exec:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var ("%" ++ toString (sa.cs_next_var + 1)) 1w
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >> drule default_bytes_guard_shape >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  `step_inst_base (mk_inst sa.cs_next_id LT [src;Lit 4w] [v0]) s =
    OK (update_var v0 0w s)` by
    (qspecl_then [`src`,`Lit 4w`,`w`,`4w`] mp_tac step_LT >>
     simp[eval_operand_def, bool_to_word_def, dimword_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) ISZERO [Var v0] [v1])
    (update_var v0 0w s) = OK (update_var v1 1w (update_var v0 0w s))` by
    (qspecl_then [`Var v0`,`0w`] mp_tac step_ISZERO >>
     simp[eval_operand_def, lookup_var_update_var, bool_to_word_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) ASSERT [Var v1] [])
    (update_var v1 1w (update_var v0 0w s)) =
    OK (update_var v1 1w (update_var v0 0w s))` by
    (irule step_ASSERT_ok >> qexists `1w` >>
     simp[eval_operand_def, lookup_var_update_var]) >>
  gvs[Abbr `v0`, Abbr `v1`] >> simp[run_inst_seq_def]
QED

Theorem default_bytes_guard_uniform_sequence:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w /\
  op_prov G src = NONE /\ op_taint tn src = {} /\ ~ctx_has_dalloca ctx ==>
  ?H u.
    (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H u) /\
    op_prov H src = NONE /\ op_taint u src = {} /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;Lit 4w}
      (emitted_insts sa sb) B` by
    (irule (Q.INST [`a` |-> `src`, `b` |-> `Lit (4w:bytes32)`]
       abi_decode_ge_guard_scalar) >>
     fs[compile_abi_arg_ptr_guard_def, abi_decode_ge_guard_def] >> metis_tac[]) >>
  `!op. op IN {src;Lit 4w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all default_bytes_guard_exec >> strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >> simp[] >>
  reverse conj_tac
  >- (drule bop_scalar_seq_available >> simp[SUBSET_DEF] >> metis_tac[]) >>
  gen_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  metis_tac[inst_seq_ptr_ghost_unique]
QED
