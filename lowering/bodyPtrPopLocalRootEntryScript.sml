(* Robust local-array facts at entry to the bare-local pop. *)
Theory bodyPtrPopLocalRootEntry
Ancestors
  bodyPtrPopMemoryHeader exprSimPop exprSimAggregateEncoding
  bodyPtrDefs valueEncoding valueEncodingProps rich_list

Theorem pop_local_robust_layout:
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  ghost_inv d cenv cx es G tn s ==>
  ptr_covers G tn p s sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n w) mem) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n w) mem` by
    (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  simp[] >> metis_tac[pop_robust_dynarray_header_clean]
QED

Theorem pop_robust_elements_split:
  vs <> [] /\
  (!mem. mem_agree_outside tainted original mem ==>
    elems_in_memory vs off tv mem) ==>
  (!mem. mem_agree_outside tainted original mem ==>
    elems_in_memory (FRONT vs) off tv mem) /\
  (!mem. mem_agree_outside tainted original mem ==>
    val_in_memory tv (LAST vs)
      (off + (LENGTH vs - 1) * type_memory_size tv) mem)
Proof
  strip_tac >> conj_tac
  >- metis_tac[elems_in_memory_FRONT] >>
  rpt strip_tac >>
  `LENGTH vs - 1 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `LAST vs = EL (LENGTH vs - 1) vs` by simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
  metis_tac[elems_in_memory_EL]
QED
