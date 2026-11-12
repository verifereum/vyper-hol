Theory extRetStaticLoopEffectPtr
Ancestors
  extRetEvaluatedStaticLoopResourcePtr extRetEvaluatedStaticLoopPtr
  abiEncoderWindowArray abiDecoderIndexInit abiAllocationHistory abiBuiltinAllocation
  extRetRecursiveResourcePtr compileEnv emitHelper fragExec fragGasPathPtr
  bodyPtrDefs ptrDiscipline venomState venomInst words finite_map list pred_set

Theorem abi_builtin_allocate_registration_effects:
  s.vs_alloca_next <= (abi_builtin_allocate_state site n s).vs_alloca_next /\
  (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
    FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas aid = SOME (p,sz))
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `site = aid` >> gvs[]
QED

Theorem compile_evaluated_dyn_static_loop_effect_counted_ptr:
  compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei k k (Var cv) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  encoder_resource ctx fn sites (w2n a) scap protected s /\
  sa.cs_next_id IN sites /\ MEM (did,w2n b,dcap) protected /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  lookup_var cv s = SOME (n2w (LENGTH vs)) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  k = type_memory_size tv /\ ((ei = AbiPrimWord /\ k = 32) \/ ei = AbiCopy k) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  32 <= scap /\ LENGTH vs < dimword(:256) /\ 32+LENGTH vs*k <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) ==>
  ?addr ip Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\
    eval_operand out sf = SOME (n2w (32+LENGTH vs*k)) /\ op_taint tnf out = {} /\
    encoder_static_loop_inv ctx fn sites (w2n a) scap protected
      ip src dst cv (n2w addr) a b scap dcap tv maxn vs k (LENGTH vs) Gf tnf sf /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\ addr+32 < dimword(:256) /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
      {i | addr <= i /\ i < addr+32}) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_evaluated_dyn_static_loop_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`addr`,`ip`,`Gf`,`tnf`,`sf`] >> simp[] >>
  conj_tac >- simp[abi_builtin_allocate_registration_effects] >>
  conj_tac >- simp[abi_builtin_allocate_registration_effects] >>
  rpt strip_tac >> irule abi_alloca_history_allocate_outside >>
  metis_tac[]
QED
