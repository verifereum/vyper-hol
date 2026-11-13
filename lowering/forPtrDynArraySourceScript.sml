(* Live-local resources for the dynamic Name iterator. *)
Theory forPtrDynArraySource
Ancestors forPtrElement typedCopyLayoutPtr bodyPtrBopInMemoryContents
  representationCleanPtr valueEncodingProofs arithmetic

Theorem for_dynarray_local_resources_ptr:
  stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) sz) /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap ==>
  ?base.
    lookup_var bp s = SOME base /\ ptr_covers G tn bp s sz /\
    32 + LENGTH vs * type_memory_size tv <= sz /\
    w2n base + sz < dimword (:256) /\
    mem_word_taint tn.t_mem (w2n base) = {} /\
    (!i. w2n base <= i /\ i < w2n base + 32 ==> i NOTIN tn.t_mem) /\
    mload (w2n base) s = n2w (LENGTH vs) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap))
        (ArrayV (DynArrayV vs)) (w2n base) mem) /\
    (!k. k < LENGTH vs ==>
      32 + k * type_memory_size tv + type_memory_size tv <= sz /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv (EL k vs)
          (w2n base + 32 + k * type_memory_size tv) mem)
Proof
  strip_tac >> drule_all stmt_state_rel_local_extent >> strip_tac >>
  drule_all ghost_inv_local_ptr >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap))
        (ArrayV (DynArrayV vs)) (w2n w) mem` by metis_tac[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n w) mem = n2w (LENGTH vs)` by
    metis_tac[dynarray_in_memory_robust_length] >>
  qexists_tac `w` >> rpt conj_tac
  >- simp[]
  >- simp[]
  >- (gvs[valueEncodingTheory.type_memory_size_def] >>
      irule LESS_EQ_TRANS >> qexists_tac `32 + cap * type_memory_size tv` >>
      simp[])
  >- decide_tac
  >- metis_tac[dynarray_memory_header_clean]
  >- metis_tac[robust_mem_word_at_clean]
  >- (rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def])
  >- simp[]
  >> rpt strip_tac
  >- (gvs[valueEncodingTheory.type_memory_size_def] >>
      `SUC k <= cap` by decide_tac >>
      `SUC k * type_memory_size tv <= cap * type_memory_size tv` by
        (irule LESS_MONO_MULT >> simp[]) >>
      qpat_x_assum `SUC k * _ <= _` mp_tac >>
      pure_rewrite_tac[MULT_CLAUSES] >> decide_tac)
  >> metis_tac[dynarray_in_memory_robust_element]
QED
