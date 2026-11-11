Theory placeMemoryDeadSuffix
Ancestors
  placeMemoryFieldRebuild exprSimProps vyperPlaceStatePreservation
  exprSimAggregateEncoding exprSimPop valueEncodingProps valueEncoding valueEncodingDefs
  vyperTyping loweringPosts arithmetic list

(* Only the length header and live prefix constrain a dynamic representation. *)
Theorem dynamic_array_dead_suffix_frame:
  LENGTH vs <= cap /\ elems_val_wf vs tv /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
  off + 32 + LENGTH vs * type_memory_size tv <= dst /\
  (!a n. off <= a /\ a + n <= off + 32 + cap * type_memory_size tv /\
    a + n <= dst ==> mem_bytes_at a n mem' = mem_bytes_at a n mem) ==>
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem'
Proof
  simp[Once val_in_memory_def] >> strip_tac >>
  simp[Once val_in_memory_def] >> conj_tac
  >- (`mem_bytes_at off 32 mem' = mem_bytes_at off 32 mem` by
        (first_x_assum irule >> simp[] >> decide_tac) >>
      gvs[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  irule elems_in_memory_intro >> rpt strip_tac >>
  irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[elems_val_wf_EL] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  reverse conj_tac
  >- (drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  sym_tac >> first_x_assum irule >>
  `i + 1 <= LENGTH vs` by decide_tac >>
  `(i + 1) * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  `LENGTH vs * type_memory_size tv <= cap * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  rule_assum_tac (PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
  decide_tac
QED
