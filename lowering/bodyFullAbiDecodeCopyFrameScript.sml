Theory bodyFullAbiDecodeCopyFrame
Ancestors
  bodyFullUnwrapSlotPost bodyFullAbiDecodeDecoderBase typedCopyPtr
  exprSimConcatStore abiDecodePtrMemberFrame allocaHistory decoderGhostFramePtr
  venomState venomInst venomExecSemantics ptrDiscipline bodyPtrDefs
  finite_map pred_set words list pair valueEncodingProps

Theorem abi_decode_mcopy_effects[local]:
  eval_operand dst s = SOME (n2w b) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand count_op s = SOME (n2w n) /\
  a < dimword (:256) /\ b < dimword (:256) /\ n < dimword (:256) /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) ==>
  step_prov PG G (mk_inst id MCOPY [dst;src;count_op] []) (mcopy b a n s) = G /\
  (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s (mcopy b a n s) tn).t_var = tn.t_var /\
  (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s (mcopy b a n s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s (mcopy b a n s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s (mcopy b a n s) tn).t_mem =
    tn.t_mem DIFF {i | b <= i /\ i < b+n}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `eval_operand dst s = _`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`] mp_tac) >>
  disch_then (qspecl_then [`src`, `count_op`, `n2w a`, `n2w n`] mp_tac) >> simp[] >>
  ` {b+i | i < n /\ a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION, GSPECIFICATION] >> gen_tac >>
     Cases_on `i < n` >> simp[] >>
     `a <= a+i /\ a+i < a+n` by decide_tac >> metis_tac[]) >> simp[]
QED

Theorem abi_decode_mcopy_inv_at[local]:
  ghost_inv_at D lo delta ce cx es G tn s /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    b+n <= lb \/ lb+len <= b) /\ lo <= b /\
  tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+n} ==>
  ghost_inv_at D lo delta ce cx es G tf (mcopy b a n s)
Proof
  strip_tac >> irule unwrap_slot_copy_ghost_inv_at >>
  conj_tac >- gvs[ghost_inv_at_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- (gvs[ghost_inv_at_def, allocas_from_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  conj_tac >- gvs[ghost_inv_at_def, stor_taint_ok_at_def, mcopy_def, write_memory_with_expansion_def] >>
  qexistsl_tac [`G`, `fn`, `n`, `s`, `sa`, `b`, `tn`] >>
  simp[op_taint_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> simp[]
QED

Theorem abi_decode_mcopy_snapshots[local]:
  tf.t_var = tn.t_var /\
  EVERY (\(aid,p,base,k,bytes).
    FLOOKUP s.vs_allocas aid = SOME (base,k) /\
    lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at base k s.vs_memory = bytes /\ base+k <= s.vs_alloca_next /\
    (base+k <= b \/ b+n <= base)) live ==>
  EVERY (\(aid,p,base,k,bytes).
    FLOOKUP s.vs_allocas aid = SOME (base,k) /\
    lookup_var p (mcopy b a n s) = SOME (n2w base) /\
    ptr_covers G tf p (mcopy b a n s) k /\
    op_taint tf (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at base k (mcopy b a n s).vs_memory = bytes /\
    base+k <= s.vs_alloca_next) live
Proof
  simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
  rename1 `MEM item live` >> PairCases_on `item` >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `mem_bytes_at item2 item3 (mcopy b a n s).vs_memory =
   mem_bytes_at item2 item3 s.vs_memory` by
    (irule mcopy_mem_bytes_at_disjoint >> simp[]) >>
  gvs[lookup_var_def, mcopy_def, write_memory_with_expansion_def,
      ptr_covers_def, op_taint_def]
QED

(* All side conditions are operation-local: the runtime decoder join must
   supply output ownership and separation for its actual copy interval.
   Clean source bytes imply that MCOPY only removes memory taint; in
   particular no extra kept-region disjointness premise is necessary. *)
Theorem abi_decode_mcopy_frame_joint:
  eval_operand dst s = SOME (n2w b) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand count_op s = SOME (n2w n) /\
  a < dimword (:256) /\ b < dimword (:256) /\ n < dimword (:256) /\
  op_taint tn count_op = {} /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (ob,cap) /\
  ob <= b /\ b+n <= ob+cap /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    ob+cap <= lb \/ lb+len <= ob) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lo <= b /\ alloca_history fn s /\
  abi_decode_ptr_window G tn s input iw (LENGTH input_bytes) /\
  mem_bytes_at (w2n iw) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  (w2n iw+LENGTH input_bytes <= b \/ b+n <= w2n iw) /\
  EVERY (\(aid,p,base,k,bytes).
    FLOOKUP s.vs_allocas aid = SOME (base,k) /\
    lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at base k s.vs_memory = bytes /\ base+k <= s.vs_alloca_next /\
    (base+k <= b \/ b+n <= base)) live /\
  EVERY (\(base,bytes). mem_bytes_at base (LENGTH bytes) s.vs_memory = bytes /\
    (base+LENGTH bytes <= b \/ b+n <= base)) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) ==>
  ?t G' tf.
    t = mcopy b a n s /\
    G' = step_prov PG G (mk_inst id MCOPY [dst;src;count_op] []) t /\
    tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s t tn /\
    G' = G /\ tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+n} /\
    (!x. lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x) /\
      !k. ptr_covers G' tf x t k <=> ptr_covers G tn x s k) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history fn t /\
    abi_decode_ptr_window G' tf t input iw (LENGTH input_bytes) /\
    mem_bytes_at (w2n iw) (LENGTH input_bytes) t.vs_memory = input_bytes /\
    EVERY (\(aid,p,base,k,bytes).
      FLOOKUP t.vs_allocas aid = SOME (base,k) /\
      lookup_var p t = SOME (n2w base) /\ ptr_covers G' tf p t k /\
      op_taint tf (Var p) = {} /\ k = LENGTH bytes /\
      mem_bytes_at base k t.vs_memory = bytes /\ base+k <= t.vs_alloca_next) live /\
    EVERY (\(base,bytes). mem_bytes_at base (LENGTH bytes) t.vs_memory = bytes) protected /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
      ghost_inv_at (DF H) lo delta ce cx es G' tf t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `eval_operand dst s = _`
    (mp_then Any mp_tac abi_decode_mcopy_effects) >>
  disch_then (qspecl_then [`tn`, `src`, `n`, `id`] mp_tac) >>
  disch_then (qspecl_then [`count_op`, `a`, `PG`, `G`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  `tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`, step_taint_nonmemory_frame, mk_inst_def] >>
  simp[] >>
  conj_tac >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def,
                  ptr_covers_def, op_taint_def] >>
  conj_tac >- (gvs[alloca_history_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  conj_tac >- (irule abi_decode_ptr_window_frame >>
    qexistsl_tac [`G`, `s`, `tn`] >>
    simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, op_taint_def] >>
    rpt strip_tac >> decide_tac) >>
  conj_tac >- metis_tac[mcopy_mem_bytes_at_disjoint] >>
  conj_tac >- (irule abi_decode_mcopy_snapshots >> qexists_tac `tn` >> simp[]) >>
  conj_tac >- (gvs[EVERY_MEM] >> rpt strip_tac >>
    rename1 `MEM item protected` >> PairCases_on `item` >>
    first_x_assum drule >> simp[] >> metis_tac[mcopy_mem_bytes_at_disjoint]) >>
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx fn ce cx es s /\
   ghost_inv_at (DF H) lo delta ce cx es G tn s /\
   ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn` by metis_tac[] >>
  conj_tac >- (irule alloca_mcopy_state_rel >> metis_tac[]) >>
  conj_tac >- (irule abi_decode_mcopy_inv_at >> simp[] >>
    conj_tac >- (rpt strip_tac >>
      `ob+cap <= lb \/ lb+len <= ob` by metis_tac[] >> decide_tac) >>
    conj_tac >- (qexists_tac `sa` >> simp[]) >>
    conj_tac >- (qexists_tac `fn` >> simp[]) >>
    qexists_tac `tn` >> simp[]) >>
  gvs[ghost_kept_at_def, op_taint_def] >> metis_tac[]
QED
