(* Select only the live bytestring window, retaining whole-buffer capacity
   separately in callers. No additional definitions are needed. *)
Theory annAssignPtrMemoryWindow
Ancestors annAssignPtrMemorySource exprSimProps valueTypingMemoryProps
 bodyPtrDefs arithmetic

Theorem annassign_memory_copy_window_ptr:
 !tenv cenv sty dty stv dtv v a s tn G src dst cap.
 (sty = dty \/ is_bytestring_type sty /\ is_bytestring_type dty) /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\
 type_memory_size stv = type_memory_bytes cenv sty /\
 type_memory_size dtv = type_memory_bytes cenv dty /\
 type_memory_bytes cenv sty < dimword (:256) /\
 type_memory_bytes cenv dty <= cap /\
 ptr_covers G tn src s (type_memory_bytes cenv sty) /\
 ptr_covers G tn dst s cap /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory dtv v a m) ==>
 ?k len. k < dimword (:256) /\ k <= cap /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
 val_footprint dtv v <= k /\
 (if is_bytestring_type dty then
    k = 32 + 32 * ((len+31) DIV 32) /\ mload a s = n2w len /\
    (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem)
  else k = type_memory_bytes cenv dty)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 Cases_on `is_bytestring_type dty`
 >- (`is_bytestring_type sty` by metis_tac[] >>
     drule_all annassign_bytestring_window_ptr >> strip_tac >>
     qexistsl [`32 + 32 * ((len+31) DIV 32)`,`len`] >>
     gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]) >>
 `sty = dty` by metis_tac[] >> gvs[] >>
 `val_footprint dtv v <= type_memory_size dtv` by
   metis_tac[val_footprint_le, value_has_type_memory_wf] >>
 gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]
QED
