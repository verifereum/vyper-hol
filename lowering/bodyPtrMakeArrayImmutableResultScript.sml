(* A clean completed immutable buffer is robust under ambient dirty. *)
Theory bodyPtrMakeArrayImmutableResult
Ancestors
  bodyPtrMakeArrayImmutableCopy exprSimCopy valueEncodingProps
  bodyPtrDefs typedCopyPtr venomState arithmetic list venomMemProofs valueEncodingProofs

Theorem clean_memory_value_robust:
  val_in_memory tv v at mem /\ val_wf tv v /\
  (!k. k < type_memory_size tv ==> at+k NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==> val_in_memory tv v at mem'
Proof
  rpt strip_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < type_memory_size tv` >>
  `mem_bytes_at (at+j) 1 mem = mem_bytes_at (at+j) 1 mem'` by
    (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem immutable_runtime_result_robust:
  stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n b + type_memory_size tv < dimword(:256) /\
  z.vs_memory = (immutable_transfers F F a b (type_slot_size tv) 0 u).vs_memory /\
  (!k. k < type_memory_size tv ==> w2n b+k NOTIN tnf.t_mem) ==>
  val_wf tv v /\ val_footprint tv v <= type_memory_size tv /\
  (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
    val_in_memory tv v (w2n b) mem)
Proof
  strip_tac >> drule_all copy_runtime_contents >> strip_tac >>
  metis_tac[clean_memory_value_robust]
QED

Theorem immutable_runtime_buffer_ptr_path:
  compile_imm_copy_to_memory F imm src (Var root) (type_slot_size tv) 0 sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var root) /\
  eval_operand src u = SOME a /\ lookup_var root u = SOME b /\
  op_taint tn src = {} /\ allocas_from 0 u /\
  ptr_covers G tn root u (type_memory_size tv) /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP u.vs_inst_idx bb.bb_instructions) /\
  stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n b + type_memory_size tv < dimword(:256) ==>
  ?z Gf tnf.
    copy_runtime_frame sa u sb z /\
    z.vs_memory = (immutable_transfers F F a b (type_slot_size tv) 0 u).vs_memory /\
    gas_path_ptr D 0 ctx func PG G tn u 0 Gf tnf
      (OK (z with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    val_wf tv v /\ val_footprint tv v <= type_memory_size tv /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory tv v (w2n b) mem) /\
    ptr_covers Gf tnf root z (type_memory_size tv) /\
    z.vs_data_section = u.vs_data_section /\ z.vs_immutables = u.vs_immutables /\
    z.vs_allocas = u.vs_allocas /\ z.vs_fmp = u.vs_fmp /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ z.vs_call_ctx = u.vs_call_ctx /\
    z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
    (!i. i < w2n b \/ w2n b+type_memory_size tv <= i ==>
      mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p z = lookup_var p u /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `0 + 32 * type_slot_size tv <= type_memory_size tv` by
    simp[type_memory_size_slots] >>
  drule_all immutable_runtime_copy_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa u sb z` >>
  `!k. k < type_memory_size tv ==> w2n b+k NOTIN tnf.t_mem` by
    fs[type_memory_size_slots] >>
  drule_all immutable_runtime_result_robust >> strip_tac >>
  qexistsl_tac [`z`, `Gf`, `tnf`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!p k. _` irule >> fs[copy_old_operand_def]) >>
  qpat_x_assum `!i. _ \/ _ ==> _ /\ _` mp_tac >>
  simp[type_memory_size_slots]
QED
