(* Finite post-allocation tuple head and inline bytes copy. *)
Theory bodyFullRawCallTupleCopy
Ancestors
  rawCallBufferPtr exprSimPtrLiteralOps exprSafeOperand loweringStateRelDefs
  decoderGhostFramePtr ghostPcTransportPtr ptrSafetyTransport
  exprLoweringProps emitHelperProps allocaFootprint
  fragGasSeqPtr fragExecPtr wordLoadStorePtr storageCopyBodyPtr
  stmtReasonMemory exprSimPtrTopLevelImmutableCopy
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  valueEncodingProps valueEncodingProofs loweringPosts ssaOperandFrame
  finite_map words list pred_set

Theorem raw_call_tuple_copy_checked:
 emit_void MSTORE [Var p;ok] sa = ((),s1) /\
 emit_op ADD [Var p;Lit 32w] s1 = (dst,s2) /\
 emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n+31) DIV 32)*32))]
   s2 = ((),sb) /\
 safe_operand sa (Var p) /\ safe_operand sa (Var x) /\ safe_operand sa ok /\
 0 < n /\ LENGTH bs <= n /\
 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
 a + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
 b + (64 + ((n+31) DIV 32)*32) < dimword (:256) /\
 lookup_var x s = SOME (n2w a) /\ lookup_var p s = SOME (n2w b) /\
 ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
 ptr_covers G tn p s (64 + ((n+31) DIV 32)*32) /\
 eval_operand ok s = SOME (if success then 1w else 0w) /\ op_taint tn ok = {} /\
 (a+32+LENGTH bs <= b \/ b+32 <= a) /\
 (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
 allocas_from lo s /\ ~ctx_has_dalloca ctx /\
 run_inst_seq (emitted_insts sa sb) s = OK t ==>
 let cnt = 32 + ((n+31) DIV 32)*32;
     dirty = tn.t_mem DIFF {i | b <= i /\ i < b+32}
 in ?Gf tnf.
   (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
   ptr_covers Gf tnf p t (64 + ((n+31) DIV 32)*32) /\
   (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
        (ArrayV (TupleV [BoolV success;BytesV bs])) b mem) /\
   tnf.t_mem =
     ((dirty DIFF {i | b+32 <= i /\ i < b+32+cnt}) UNION
      {b+32+i | i < cnt /\ a+i IN dirty}) /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
   (t with vs_vars := s.vs_vars) =
      mcopy (b+32) a cnt (mstore b (val_to_w256 (BoolV success)) s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `dst = Var q /\ ~not_fresh_at sa q /\ p <> q /\ x <> q` by
    gvs[safe_operand_def, not_fresh_at_def, Abbr `q`] >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MSTORE [Var p;ok] [];
     mk_inst (sa.cs_next_id+1) ADD [Var p;Lit 32w] [q];
     mk_inst (sa.cs_next_id+2) MCOPY [Var q;Var x;Lit (n2w (32+((n+31) DIV 32)*32))] []]` by
    (irule emitted_insts_three >> qexistsl [`s1`,`s2`] >> gvs[]) >>
  qabbrev_tac `cnt = 32+((n+31) DIV 32)*32` >>
  qabbrev_tac `u = mstore b (val_to_w256 (BoolV success)) s` >>
  qabbrev_tac `v = update_var q (n2w (b+32)) u` >>
  qabbrev_tac `w = mcopy (b+32) a cnt v` >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id MSTORE [Var p;ok] []` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) ADD [Var p;Lit 32w] [q]` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id+2) MCOPY [Var q;Var x;Lit (n2w cnt)] []` >>
  `a < dimword (:256) /\ b < dimword (:256) /\
   b+32 < dimword (:256) /\ cnt < dimword (:256)` by
    (simp[Abbr `cnt`] >> decide_tac) >>
  `val_to_w256 (BoolV success) = (if success then 1w else 0w)` by
    (Cases_on `success` >> EVAL_TAC) >>
  `eval_operand (Var p) s = SOME (n2w b) /\
   eval_operand (Var p) u = SOME (n2w b) /\
   eval_operand (Var q) v = SOME (n2w (b+32)) /\
   eval_operand (Var x) v = SOME (n2w a)` by
    gvs[Abbr `u`, Abbr `v`, mstore_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i1 s = OK u /\ step_inst_base i2 u = OK v /\
   step_inst_base i3 v = OK w` by
    (fs[lookup_var_def] >>
     simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `u`, Abbr `v`, Abbr `w`,
       step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, mstore_def,
       FLOOKUP_UPDATE, word_add_n2w]) >>
  `t = w` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def]) >>
  qabbrev_tac `G1 = step_prov PG G i1 u` >>
  qabbrev_tac `tn1 = step_taint i1 s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 v` >>
  qabbrev_tac `tn2 = step_taint i2 u v tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i3 w` >>
  qabbrev_tac `tn3 = step_taint i3 v w tn2` >>
  `G1 = G /\ tn1 = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (qpat_assum `eval_operand (Var p) s = _`
       (mp_then Any mp_tac storage_copy_store_ghost) >>
     disch_then (fn th => qpat_assum `eval_operand ok s = _`
       (mp_then Any mp_tac th)) >>
     disch_then (qspecl_then [`tn`,`sa.cs_next_id`,`PG`,`G`] mp_tac) >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `i1`, Abbr `u`]) >>
  `?site. FLOOKUP G p = SOME site` by metis_tac[bodyPtrDefsTheory.ptr_covers_def] >>
  `G2 = G |+ (q,site) /\ tn2 = tn1 with t_var := tn1.t_var |+ (q,{})` by
    (drule literal_add_ghost >> disch_then strip_assume_tac >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `v`]) >>
  `G3 = G2 /\ tn3.t_var = tn2.t_var /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
   tn3.t_mem = (tn2.t_mem DIFF {i | b+32 <= i /\ i < b+32+cnt}) UNION
      {b+32+i | i < cnt /\ a+i IN tn2.t_mem}` by
    ((`eval_operand (Lit (n2w cnt)) v = SOME (n2w cnt)` by simp[eval_operand_def] >>
     qpat_assum `eval_operand (Var q) v = _`
       (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
     disch_then (fn th => qpat_assum `eval_operand (Var x) v = _`
       (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `eval_operand (Lit _) v = _`
       (mp_then Any mp_tac th)) >>
     disch_then strip_assume_tac >>
     `tn3.t_imm = tn2.t_imm` by
       simp[Abbr `tn3`, Abbr `i3`, step_taint_nonmemory_frame, mk_inst_def] >>
     fs[arithmeticTheory.LESS_MOD] >>
     simp[Abbr `G3`, Abbr `tn3`, Abbr `i3`, Abbr `w`] >> (gvs[]))) >>
  qexistsl [`G3`,`tn3`] >>
  conj_tac >- suspend "checked" >>
  conj_tac >- suspend "cover" >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "mask" >>
  conj_tac >- suspend "stor" >>
  conj_tac >- suspend "trans" >>
  conj_tac >- suspend "imm" >>
  conj_tac >- suspend "old" >>
  suspend "state"
QED

Resume raw_call_tuple_copy_checked[checked]:
  cheat
QED
Resume raw_call_tuple_copy_checked[cover]:
  `FLOOKUP s.vs_vars p = SOME (n2w b)` by fs[lookup_var_def] >>
  qpat_x_assum `ptr_covers G tn p s _` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, Abbr `w`, Abbr `v`,
       Abbr `u`, lookup_var_def, update_var_def, mcopy_vars, mstore_vars,
       FLOOKUP_UPDATE]
QED
Resume raw_call_tuple_copy_checked[robust]:
  simp[Abbr `w`, Abbr `v`, mcopy_update_var, update_var_def] >>
  irule bool_pair_mstore_mcopy_robust >>
  simp[val_footprint_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def, Abbr `u`, Abbr `cnt`] >>
  decide_tac
QED
Resume raw_call_tuple_copy_checked[mask]:
  simp[]
QED
Resume raw_call_tuple_copy_checked[stor]:
  simp[]
QED
Resume raw_call_tuple_copy_checked[trans]:
  simp[]
QED
Resume raw_call_tuple_copy_checked[imm]:
  simp[]
QED
Resume raw_call_tuple_copy_checked[old]:
  qx_gen_tac `name` >> strip_tac >>
  `name <> q` by metis_tac[] >>
  simp[Abbr `w`, Abbr `v`, Abbr `u`, lookup_var_def, update_var_def,
       mcopy_vars, mstore_vars, FLOOKUP_UPDATE, op_taint_def]
QED
Resume raw_call_tuple_copy_checked[state]:
  simp[Abbr `w`, Abbr `v`, mcopy_update_var, update_var_reset_vars,
       GSYM mcopy_reset_vars, Abbr `u`, GSYM mstore_reset_vars]
QED
Finalise raw_call_tuple_copy_checked
