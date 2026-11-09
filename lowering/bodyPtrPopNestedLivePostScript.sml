Theory bodyPtrPopNestedLivePost
Ancestors
  bodyPtrPopNestedLiveHandoff exprSimPopNestedLocalPost
  augAssignPtrFieldStore valueEncodingProps venomState pred_set
  exprSimPopNestedLocalMemory valueEncoding exprSimPop

(* Restore the overwritten header before applying the ordinary path-update
   lemma. This keeps robustness independent of the particular tainted bytes. *)
Theorem pop_path_update_robust:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\ val_wf tv updated /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
         val_in_memory tv a locbase mem) ==>
  !mem. mem_agree_outside (dirty DIFF {i | locbase+k <= i /\ i < locbase+k+32})
    (mstore (locbase+k) (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory tv updated locbase mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv a locbase mix` by metis_tac[] >>
  `val_in_memory tv updated locbase
    (mstore (locbase+k) (n2w (LENGTH vs-1)) (s with vs_memory := mix)).vs_memory` by
    (irule val_in_memory_pop_path >> simp[] >>
     qexistsl_tac [`a`, `etv`, `n`, `path`] >> simp[]) >>
  irule val_in_memory_mem_agree >> simp[] >>
  goal_assum (drule_at Any) >>
  qexists_tac `type_memory_size tv` >> simp[] >>
  irule memory_byte_agree_window >> gvs[]
QED

Theorem pop_path_result_robust:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
         val_in_memory tv a locbase mem) ==>
  !mem. mem_agree_outside (dirty DIFF {i | locbase+k <= i /\ i < locbase+k+32})
    (mstore (locbase+k) (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory etv (LAST vs)
      (locbase+k+32+(LENGTH vs-1)*type_memory_size etv) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv a locbase mix` by metis_tac[] >>
  `val_in_memory etv (LAST vs)
    (locbase+k+32+(LENGTH vs-1)*type_memory_size etv)
    (mstore (locbase+k) (n2w (LENGTH vs-1)) (s with vs_memory := mix)).vs_memory` by
    (irule pop_path_elem_in_memory >> simp[] >>
     qexistsl_tac [`a`, `n`, `path`, `tv`] >> simp[]) >>
  `val_in_memory tv a locbase (s with vs_memory := mix).vs_memory` by simp[] >>
  `val_wf etv (LAST vs)` by
    (drule_all val_in_memory_mutable_path >>
     simp[val_wf_def] >> strip_tac >>
     drule elems_val_wf_EL >>
     disch_then (qspec_then `LENGTH vs-1` mp_tac) >>
     `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
  qexistsl_tac [`type_memory_size etv`,
    `(mstore (locbase+k) (n2w (LENGTH vs-1)) (s with vs_memory := mix)).vs_memory`] >>
  simp[] >> irule memory_byte_agree_window >> gvs[]
QED
