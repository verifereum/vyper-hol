(* Robustness depends on the count and live element strides, not unused capacity. *)
Theory dynarrayLiveRobustPtr
Ancestors normalizationPrefixPtr calldataTypedRobustPtr exprSimAggregateEncoding
  exprSimProps valueEncoding valueEncodingTyping vyperValue vyperTyping bodyPtrDefs
  list arithmetic pred_set

Theorem clean_live_prefix_dynarray_robust:
  val_in_memory (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) d mem /\
  EVERY (value_has_type tv) vs /\
  (!i. d <= i /\ i < d+32+LENGTH vs*type_memory_size tv ==> i NOTIN tainted) ==>
  !mem'. mem_agree_outside tainted mem mem' ==>
    val_in_memory (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) d mem'
Proof
  strip_tac >> match_mp_tac robust_dynarray_clean_count_assemble >>
  conj_tac >- fs[val_in_memory_def] >>
  conj_tac >-
    (simp[DISJOINT_DEF, EXTENSION] >> gen_tac >>
     Cases_on `d <= x /\ x < d+32` >> simp[] >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  qx_gen_tac `j` >> strip_tac >>
  `value_has_type tv (EL j vs)` by fs[EVERY_EL] >>
  match_mp_tac clean_footprint_val_in_memory_robust >>
  conj_tac >- metis_tac[value_has_type_val_wf] >>
  conj_tac >-
    (irule elems_in_memory_EL >> fs[val_in_memory_def] >> metis_tac[]) >>
  `val_footprint tv (EL j vs) <= type_memory_size tv` by
    metis_tac[val_footprint_le, value_has_type_val_wf] >>
  `j*type_memory_size tv + type_memory_size tv <= LENGTH vs*type_memory_size tv` by
    (`j+1 <= LENGTH vs` by decide_tac >>
     ` (j+1)*type_memory_size tv <= LENGTH vs*type_memory_size tv` by simp[] >>
     qpat_x_assum `(j+1)*_ <= _` mp_tac >>
     pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  rpt strip_tac >> gvs[]
QED
