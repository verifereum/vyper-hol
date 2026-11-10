(* Selected-path transitions only; other owners still need a frame proof. *)
Theory bodyPtrSubscriptHistoryPathStore
Ancestors
  bodyPtrSubscriptHistoryHeader bodyPtrSubscriptHistoryBoundary
  bodyPtrSubscriptCurrentMemory
  valueTypingMemoryProps valueEncoding valueEncodingDefs vyperPlaceStatePreservation
  exprSimProps arithmetic

Theorem current_path_pop_header:
  !tv a base s path vs k etv cap.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a base s.vs_memory /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
    vs <> [] ==>
    val_in_memory (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV (FRONT vs))) (base + k)
      (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
    val_in_memory etv (LAST vs)
      (base + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
      (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `subscripts_type tv path = SOME (ArrayTV etv (Dynamic cap))` by
    metis_tac[mem_path_offset_sound] >>
  `value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule value_has_type_memory_wf >> simp[val_wf_def] >> strip_tac >>
  drule_all mem_path_offset_current_value >> strip_tac >>
  conj_tac
  >- (irule pop_header_shortened_array >> simp[]) >>
  drule_all pop_header_last_element >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM]
QED

Theorem trusted_path_pop_header:
  !tv path trusted vs k etv cap base s.
    read_popped tv path trusted = SOME (ArrayV (DynArrayV vs)) /\
    (!prefix owner d ptv.
      MEM (prefix,owner) trusted /\
      mem_path_offset tv prefix = SOME (d,ptv) ==>
      value_has_type ptv owner /\ well_formed_type_value ptv /\
      val_in_memory ptv owner (base + d) s.vs_memory) /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
    vs <> [] ==>
    val_in_memory (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV (FRONT vs))) (base + k)
      (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
    val_in_memory etv (LAST vs)
      (base + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
      (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule read_popped_owner >> strip_tac >> gvs[] >>
  drule mem_path_offset_append_decompose >> strip_tac >>
  qpat_assum `mem_path_offset tv prefix = SOME _`
    (mp_then Any strip_assume_tac mem_path_offset_sound) >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all current_path_pop_header >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM]
QED
