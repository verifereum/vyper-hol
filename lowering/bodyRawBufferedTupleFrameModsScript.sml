Theory bodyRawBufferedTupleFrameMods
Ancestors
  bodyFullRawCallTupleLength bodyFullRawCallTupleCopy
  bodyFullRawCallTupleAllocFrame bodyFullRawCallTupleWriteFrame
  exprSimRawCall exprSimRawCallCalldata
  placeMemoryTypedPrimitive venomMemProps venomState venomInst
  venomExecSemantics finite_map words stateRelProj loweringStateRelDefs
  allocaFootprint exprSafeOperand ptrDiscipline fragGasSeqPtr exprLowering
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource bodyFullHashKeccakFixed
  exprSimProps loweringHalt exprLoweringProps allocationPtr venomMemDefs

(* The allocation between the header and copy does not write memory. *)
Theorem tuple_write_window[local]:
  u.vs_memory = (mstore a len s).vs_memory /\
  t.vs_memory = (mcopy (b+32) a k (mstore b flag u)).vs_memory ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!p m. (p+m <= a \/ a+32 <= p) /\ (p+m <= b \/ b+32+k <= p) ==>
     mem_bytes_at p m t.vs_memory = mem_bytes_at p m s.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `LENGTH u.vs_memory` >>
      conj_tac >- simp[venomMemPropsTheory.mstore_memory_nondecreasing] >>
      irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `LENGTH (mstore b flag u).vs_memory` >>
      simp[placeMemoryTypedPrimitiveTheory.mcopy_memory_length,
           venomMemPropsTheory.mstore_memory_nondecreasing]) >>
  rpt gen_tac >> strip_tac >>
  `p+m <= b+32 \/ b+32+k <= p` by decide_tac >>
  `p+m <= b \/ b+32 <= p` by decide_tac >>
  simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint,
       valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]
QED

Theorem tuple_copy_taint_window[local]:
  tn1.t_mem = tn.t_mem DIFF {i | a <= i /\ i < a+32} /\
  (!i. ~(b <= i /\ i < b+32+k) /\ i IN tn2.t_mem ==> i IN tn1.t_mem) /\
  tnf.t_mem =
    ((tn2.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF {i | b+32 <= i /\ i < b+32+k}) UNION
    {b+32+i | i | i < k /\ a+i IN (tn2.t_mem DIFF {i | b <= i /\ i < b+32})} ==>
  !i. ~(a <= i /\ i < a+32) /\ ~(b <= i /\ i < b+32+k) /\
      i IN tnf.t_mem ==> i IN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i IN tnf.t_mem /\ ~(b <= i /\ i < b+32+k) ==> i IN tn2.t_mem` by
    (gen_tac >> simp[pred_setTheory.IN_UNION,pred_setTheory.IN_DIFF] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  rpt strip_tac >>
  `i IN tn2.t_mem` by (first_x_assum irule >> simp[] >> decide_tac) >>
  `i IN tn1.t_mem` by
    (qpat_assum `!i. _ ==> i IN tn1.t_mem` irule >> simp[] >> decide_tac) >>
  qpat_assum `tn1.t_mem = _` (fn th =>
    qpat_x_assum `i IN tn1.t_mem`
      (mp_tac o PURE_REWRITE_RULE [th,pred_setTheory.IN_DIFF])) >>
  tautLib.TAUT_TAC
QED

Theorem tuple_alloca_rows[local]:
  k < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w k)] [p]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,k) ==>
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next |> = s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!aid off m. FLOOKUP t.vs_allocas aid = SOME (off,m) ==>
     FLOOKUP s.vs_allocas aid = SOME (off,m) \/ s.vs_alloca_next <= off)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> gvs[LET_THM]
  >- (gvs[update_var_def,FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `aid = id` >> gvs[FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[]
QED

(* Execute the header once, retaining the ordinary state and the exact write
   of the ghost-checked length-store fragment. *)
Theorem tuple_header_cut[local]:
  emit_op RETURNDATASIZE [] sa = (z,s1) /\
  emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
  compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
  emit_void MSTORE [Var x;cap] s3 = ((),s4) /\
  0 < n /\ n < dimword (:256) /\
  64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  safe_operand sa (Var x) /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  allocas_from lo s ==>
  ?u G1 tn1.
    run_inst_seq (emitted_insts sa s4) s = OK u /\
    stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa s4) s G1 tn1) /\
    ptr_covers G1 tn1 x u (32 + ((n+31) DIV 32)*32) /\
    (!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem) /\
    tn1.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v u = lookup_var v s /\ FLOOKUP G1 v = FLOOKUP G v /\
      op_taint tn1 (Var v) = op_taint tn (Var v)) /\
    (u with vs_vars := s.vs_vars) =
      mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s
Proof
  strip_tac >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  `w2n w <= w2n w /\ w2n w + 32 <= w2n w + (32 + ((n+31) DIV 32)*32)` by decide_tac >>
  drule_all raw_call_output_prefix_ready >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by fs[] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
     simp[alloca_room_def] >> decide_tac) >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by decide_tac >>
  `lookup_var x s = SOME (n2w (w2n w))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    qpat_assum `stmt_state_rel H ctx func cenv cx es s`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
  drule_all raw_call_tuple_length_checked >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  rename1 `ptr_covers G1 tn1 x u _` >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> simp[]
QED
