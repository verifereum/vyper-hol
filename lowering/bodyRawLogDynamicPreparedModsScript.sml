(* The dynamic RawLog preparation is independent of the gas horizon. *)
Theory bodyRawLogDynamicPreparedMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv
  bodyFullRawLogDynamicPrepare bodyFullRawLogDynamicData
  bodyFullRawLogDynamicSequenceFrame revertReasonPrefixFramePtr
  bodyFullHashKeccakFixed exprSimHashBoundary fragGasSeqPtr
  loweringPosts ptrDiscipline bodyPtrDefs venomInst venomState
  exprLoweringProps compileEnv emitHelper rich_list words list arithmetic finite_map

(* The preparation uses the ordinary ghost predicate only at zero. *)
Theorem raw_log_prepare_zero_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s ==>
  ghost_inv_at D 0 d cenv cx ee G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem raw_log_prepare_opcodes[local]:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> DELEGATECALL /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
             i.inst_opcode <> SSTORE /\ i.inst_opcode <> TSTORE /\
             i.inst_opcode <> ISTORE) (emitted_insts sm s2)
Proof
  strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem raw_log_prepare_at_horizon[local]:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops) /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_post_mods H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
  expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
  ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx ee G tn s /\
  ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  ?p Gp tp off.
    run_inst_seq (emitted_insts sm s2) s = OK p /\
    run_inst_seq_mem_ok (emitted_insts sm s2) s /\
    (p with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x p = lookup_var x s) /\
    ghost_kept_at lo cenv ee sm G tn s Gp tp /\
    eval_operand ptr_op p = SOME off /\
    eval_operand len_op p = SOME (n2w (LENGTH bs)) /\
    LENGTH bs < dimword (:256) /\
    eval_operands ops p = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tp op = {}) (ptr_op::len_op::ops) /\
    mem_bytes_at (w2n off) (LENGTH bs) p.vs_memory = bs /\
    (!i. w2n off <= i /\ i < w2n off + LENGTH bs ==> i NOTIN tp.t_mem) /\
    w2n off + LENGTH bs <= p.vs_alloca_next /\
    (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers Gp tp x p (LENGTH bs)) /\
    inst_seq_ptr (DF H) 0 ctx func PG G tn (emitted_insts sm s2) s Gp tp /\
    ghost_inv_at (DF H) 0 d cenv cx ee Gp tp p
Proof
  strip_tac >>
  fs[expr_post_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (fs[expr_post_def] >> drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_then assume_tac raw_log_prepare_zero_ghost >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
      SOME (BaseTV (BytesT (Dynamic cap)))` by gvs[] >>
  `ptr_val_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data_op G tn s /\
   expr_store_bound cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data_op s` by metis_tac[] >>
  `b < dimword (:256)` by decide_tac >>
  drule_all raw_log_dynamic_data_window >> simp[LESS_MOD] >> strip_tac >>
  mp_tac (Q.INST [`D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`,
    `lo` |-> `0`, `topics` |-> `MAP event_value_to_word vals`]
    (INST_TYPE [alpha |-> ``:word8``] raw_log_dynamic_prepare_joint)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  qexistsl [`t`,`G1`,`tn1`,`n2w (b+32)`] >>
  `ghost_kept_at lo cenv ee sm G tn s G1 tn1` by
    (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> simp[]) >>
  fs[LESS_MOD]
QED

Theorem raw_log_dynamic_prepared_mods:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops) /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
    ptr_buf_ok cenv data data_op G s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    eval_operands ops s = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn op = {}) ops /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  ?p Gp tp off.
    run_inst_seq (emitted_insts sm s2) s = OK p /\
    run_inst_seq_mem_ok (emitted_insts sm s2) s /\
    (p with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x p = lookup_var x s) /\
    (!x. not_fresh_at sm x ==>
       FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)) /\
    tp.t_mem = tn.t_mem /\ tp.t_stor = tn.t_stor /\
    tp.t_trans = tn.t_trans /\ tp.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv ee sm G tn s Gp tp /\
    eval_operand ptr_op p = SOME off /\
    eval_operand len_op p = SOME (n2w (LENGTH bs)) /\
    LENGTH bs < dimword (:256) /\
    eval_operands ops p = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tp op = {}) (ptr_op::len_op::ops) /\
    mem_bytes_at (w2n off) (LENGTH bs) p.vs_memory = bs /\
    (!i. w2n off <= i /\ i < w2n off + LENGTH bs ==> i NOTIN tp.t_mem) /\
    w2n off + LENGTH bs <= p.vs_alloca_next /\
    (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers Gp tp x p (LENGTH bs)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      inst_seq_ptr (DF H) 0 ctx func PG G tn (emitted_insts sm s2) s Gp tp /\
      ghost_inv_at (DF H) 0 d cenv cx ee Gp tp p)
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (qspec_then `H0` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all raw_log_prepare_at_horizon >> disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >>
  drule_all raw_log_dynamic_prepare_memory_taint >> strip_tac >>
  drule_all raw_log_prepare_opcodes >> strip_tac >>
  drule_all inst_seq_ptr_nonmemory_taint_frame >> strip_tac >>
  qexistsl [`p`,`Gp`,`tp`,`off`] >>
  simp[] >>
  conj_tac >- fs[ghost_kept_at_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all raw_log_prepare_at_horizon >> disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >>
  `p' = p` by gvs[] >>
  `Gp' = Gp /\ tp' = tp` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[]
QED
