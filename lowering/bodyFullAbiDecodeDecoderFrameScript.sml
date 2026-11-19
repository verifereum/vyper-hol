Theory bodyFullAbiDecodeDecoderFrame
Ancestors
  bodyFullAbiDecodeDecoderBase bodyFullUnwrapSlotPost
  bodyFullAllocGeneric bodyPtrIfExpAllocSource bodyPtrIfExpAllocKept
  bodyPtrHashBuiltinsAllocFrame allocationPtr
  abiDecodePtrMemberFrame revertReasonPrefixPtr
  wordLoadStorePtr decoderGhostFramePtr bodyPtrDefs ptrDiscipline
  venomInst venomState venomExecSemantics loweringStateRelDefs
  compileEnv finite_map pred_set words valueEncodingProps

(* A decoder output allocation is not a live local.  This fact, rather than
   a final semantic post, preserves the state relation at the next allocation. *)
Theorem abi_decode_output_write_state_rel[local]:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  not_local_ptr ce es.scopes out /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a+32 <= b+sz /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s) ==>
  !H. V H ==> stmt_state_rel H ctx fn ce cx es (mstore a w s)
Proof
  rpt strip_tac >> irule stmt_state_rel_mstore_alloca >>
  metis_tac[]
QED

Theorem abi_decode_output_write_kept_at[local]:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ghost_kept_at lo ce es sa G0 tn0 s0
    (step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  gvs[ghost_kept_at_def, op_taint_def] >> metis_tac[]
QED

Theorem abi_decode_output_write_inv_at[local]:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ghost_inv_at D lo d ce cx es G tn s /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
     w2n a+32 <= b \/ b+sz <= w2n a) /\ lo <= w2n a ==>
  ghost_inv_at D lo d ce cx es
    (step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
    (mstore (w2n a) w s)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  irule unwrap_slot_copy_ghost_inv_at >>
  conj_tac >- gvs[ghost_inv_at_def, mstore_def] >>
  conj_tac >- (gvs[ghost_inv_at_def, allocas_from_def, mstore_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[ghost_inv_at_def, stor_taint_ok_at_def, mstore_def,
         step_taint_nonmemory_frame, mk_inst_def] >>
  qexistsl_tac [`G`, `fn`, `32`, `s`, `sa`, `w2n a`, `tn`] >>
  simp[op_taint_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem abi_decode_output_write_frame_joint:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  not_local_ptr ce es.scopes out /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= w2n a /\ w2n a+32 <= b+sz /\
  lookup_var dst s = SOME a /\ ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  abi_decode_ptr_window G tn s src input n /\
  (w2n input+n <= w2n a \/ w2n a+32 <= w2n input) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     w2n a+32 <= lb \/ lb+len <= w2n a) /\ lo <= w2n a /\
  ghost_inv_at D lo d ce cx es G tn s /\
  ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s) ==>
  ?t G' tn'.
    t = mstore (w2n a) w s /\
    G' = step_prov PG G (mk_inst id MSTORE [Var dst;value] []) t /\
    tn' = step_taint (mk_inst id MSTORE [Var dst;value] []) s t tn /\
    abi_decode_ptr_write_frame tn s tn' t (w2n a) 32 /\
    abi_decode_ptr_window G' tn' t src input n /\
    ghost_inv_at D lo d ce cx es G' tn' t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn' /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es t)
Proof
  strip_tac >> (
  qexistsl_tac [`mstore (w2n a) w s`,
    `step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s)`,
    `step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn`] >>
  pure_rewrite_tac [REFL_CLAUSE, AND_CLAUSES] >> conj_tac
  >- (drule_all abi_decode_ptr_mstore_frame >>
      disch_then (qspecl_then [`s.vs_inst_idx`, `id`] mp_tac) >>
      simp[mstore_def]) >>
  conj_tac
  >- (drule_all mstore_ghost_frame >>
      disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
      irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
      simp[lookup_var_def, mstore_def, op_taint_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule abi_decode_output_write_inv_at >> metis_tac[]) >>
  conj_tac >- (irule abi_decode_output_write_kept_at >> metis_tac[]) >>
  metis_tac[abi_decode_output_write_state_rel])
QED

(* Only caller-observable bytes must be below the frontier; the scratch
   site's presence in vs_allocas is deliberately unrestricted. *)
Theorem abi_decode_scratch_alloc_kept_at[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx fn ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (~not_fresh_at origin out) /\ lo <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
     b+sz <= s.vs_alloca_next) /\
  ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn ==>
  ghost_kept_at lo ce es0 origin G0 tn0 s0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  strip_tac >> drule_all alloca_step_site >> strip_tac >>
  drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `!i. i < s.vs_alloca_next ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem <=>
     i IN tn.t_mem)` by
    metis_tac[bodyPtrIfExpAllocKeptTheory.alloca_step_taint_below_frontier] >>
  irule unwrap_slot_copy_ghost_kept_at >>
  qexistsl_tac [`G`, `tn`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem abi_decode_scratch_alloc_frame_joint:
  V (H0:(bool # 256 word # type_value) list # num list) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s) /\
  fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sb /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
  buf.buf_operand = Var out /\ n < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (~not_fresh_at origin out) /\ src <> out /\
  abi_decode_ptr_window G tn s src input len /\
  w2n input+len <= s.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
     b+sz <= s.vs_alloca_next) /\
  ghost_inv_at D lo d ce cx es G tn s /\
  ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn ==>
  ?G' tn'.
    G' = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u /\
    tn' = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn /\
    u.vs_memory = s.vs_memory /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    ptr_covers G' tn' out u n /\
    abi_decode_ptr_window G' tn' u src input len /\
    ghost_inv_at D lo d ce cx es G' tn' u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn' /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es u)
Proof
  strip_tac >>
  `stmt_state_rel H0 ctx fn ce cx es s` by metis_tac[] >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  drule_all alloca_step_site >> strip_tac >>
  drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u`,
    `step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn`] >>
  pure_rewrite_tac [REFL_CLAUSE, AND_CLAUSES] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
      simp[] >> rpt strip_tac >>
      `i < s.vs_alloca_next` by decide_tac >>
      metis_tac[bodyPtrIfExpAllocKeptTheory.alloca_step_taint_below_frontier]) >>
  conj_tac
  >- (irule compile_alloc_buffer_ghost_frame_at >> simp[] >>
      conj_tac >- (qexists_tac `sa` >> simp[]) >>
      qexistsl_tac [`H0`, `ctx`, `fn`] >> simp[]) >>
  conj_tac
  >- (irule abi_decode_scratch_alloc_kept_at >> simp[] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      qexistsl_tac [`H0`, `ctx`, `cx`, `es`, `fn`] >> simp[]) >>
  rpt strip_tac >>
  `stmt_state_rel H ctx fn ce cx es s` by metis_tac[] >>
  drule_all compile_alloc_buffer_raw_resources >> simp[]
QED
