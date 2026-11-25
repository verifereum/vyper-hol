(* Robust dynamic-array representation after the length and element writes. *)
Theory bodyAppendMemoryEncodingMods
Ancestors
  normalizationPrefixPtr robustCopyTransportPtr exprSimAggregateEncoding
  exprSimProps valueEncodingDefs bodyPtrDefs venomState list arithmetic

Theorem append_memory_robust_array_mods:
  (!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) /\
  (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\
  mem_word_at off new_memory = n2w (LENGTH vs + 1) /\
  DISJOINT {i | off <= i /\ i < off + 32} new_taint /\
  (!mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory tv v (off + 32 + LENGTH vs * type_memory_size tv) mem) /\
  (!i. ~(off <= i /\ i < off + 32) /\
       ~(off + 32 + LENGTH vs * type_memory_size tv <= i /\
         i < off + 32 + (LENGTH vs + 1) * type_memory_size tv) ==>
    mem_bytes_at i 1 new_memory = mem_bytes_at i 1 old_memory /\
    (i IN new_taint <=> i IN old_taint)) ==>
  !mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) off mem
Proof
  strip_tac >> match_mp_tac robust_dynarray_clean_count_assemble >>
  simp[LENGTH_APPEND] >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [EL_APPEND_EQN] >>
      qpat_assum `!mem. mem_agree_outside new_taint new_memory mem ==> _` mp_tac >>
      simp_tac (srw_ss()) [ADD_ASSOC, ADD_COMM]) >>
  `j < LENGTH vs` by decide_tac >>
  `val_wf tv (EL j vs)` by simp[] >>
  `val_footprint tv (EL j vs) <= type_memory_size tv` by
    (irule val_footprint_le >> simp[]) >>
  `(j+1) * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    (simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory tv (EL j vs) (off+32+j*type_memory_size tv) mem` by
    (rpt strip_tac >>
     `elems_in_memory vs (off+32) tv mem` by
       (qpat_assum `!m. mem_agree_outside old_taint old_memory m ==> _`
          (qspec_then `mem` (mp_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def])) >>
        simp[]) >>
     drule_all elems_in_memory_EL >> simp[]) >>
  simp[EL_APPEND_EQN] >>
  match_mp_tac robust_val_in_memory_exterior_frame >>
  qexistsl_tac [`old_taint`, `old_memory`,
    `{i | off <= i /\ i < off+32} UNION
     {i | off+32+LENGTH vs*type_memory_size tv <= i /\
          i < off+32+(LENGTH vs+1)*type_memory_size tv}`] >>
  simp[]
  >- (qpat_assum `!mem. mem_agree_outside old_taint old_memory mem ==>
         val_in_memory tv (EL j vs) _ mem` mp_tac >>
      simp_tac (srw_ss()) [DECIDE ``off+32+n:num = off+(n+32)``]) >>
  rpt strip_tac >> first_assum irule >>
  qpat_assum `(j+1) * type_memory_size tv <= _` mp_tac >>
  simp[RIGHT_ADD_DISTRIB] >> decide_tac
QED
