(* Value-facing facts for a fresh nonword memory snapshot. *)
Theory bodyMemSnapshotResult
Ancestors
  valueCopyBytes exprSimProps exprSimMemDefs loweringPosts context compileEnv
  valueEncodingProps valueTypingMemoryProps

Theorem snapshot_located_result_facts:
  (lt = ty \/ is_bytestring_type ty /\ is_bytestring_type lt /\
    arg_type_fits lt ty) /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\
  value_has_type tv v /\ value_has_type ltv v /\
  read_result cx raw ee = (INL v,ee) /\
  val_in_memory ltv v (w2n d) z.vs_memory /\
  eval_operand dst z = SOME d /\
  FLOOKUP z.vs_allocas aid = SOME (w2n d,type_memory_size ltv) /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n b sz. local_region ce ee.scopes z n b sz ==>
    w2n d + type_memory_size ltv <= b \/ b + sz <= w2n d) /\
  w2n d + type_memory_size ltv <= z.vs_alloca_next ==>
  vv_holds ce cx ty raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) ee z /\
  vv_at ce cx ty sa sb ee raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
  vv_own ce cx ty sm sb ee raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
  vv_store_bound cx ty lt ee raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z
Proof
  strip_tac >>
  `val_wf tv v /\ val_wf ltv v` by
    metis_tac[value_has_type_memory_wf] >>
  `val_in_memory tv v (w2n d) z.vs_memory /\
   val_footprint tv v <= type_memory_size ltv /\
   val_store_size tv v <= type_memory_size ltv` by
    (Cases_on `lt = ty` >- gvs[val_footprint_le, val_store_size_le] >>
     gvs[] >>
     metis_tac[bytestring_val_in_memory_transfer, bytestring_val_footprint_le,
               bytestring_val_store_size_eq, val_store_size_le]) >>
  (conj_tac
  >- (simp[vv_holds_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[vv_at_def] >> rpt strip_tac >> gvs[] >>
      disj1_tac >>
      qexistsl_tac [`aid`, `w2n d`, `type_memory_size ltv`] >>
      simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac
  >- (simp[vv_own_def] >> rpt strip_tac >> gvs[] >>
      disj1_tac >>
      qexistsl_tac [`aid`, `w2n d`, `type_memory_size ltv`] >> simp[] >>
      metis_tac[]) >>
  simp[vv_store_bound_def] >> rpt strip_tac >> gvs[] >> decide_tac)
QED
