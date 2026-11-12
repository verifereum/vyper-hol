Theory bodyPtrSubscriptOwnerPop
Ancestors
  bodyPtrSubscriptPathRebuild bodyPtrSubscriptHistoryPathStore
  bodyPtrSubscriptMemoryRebuild valueEncodingProps valueEncodingProofs
  valueEncoding vyperTyping vyperPlaceStatePreservation exprSimProps
  vyperState venomState list arithmetic

Theorem mstore_padded_byte_outside:
  !s b w addr.
    addr < b \/ b+32 <= addr ==>
    (if addr < LENGTH (mstore b w s).vs_memory
     then EL addr (mstore b w s).vs_memory else 0w) =
    (if addr < LENGTH s.vs_memory then EL addr s.vs_memory else 0w)
Proof
  rpt strip_tac >>
  `mem_bytes_at addr 1 (mstore b w s).vs_memory =
   mem_bytes_at addr 1 s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem owner_path_pop_header:
  !tv a base s path vs k etv cap a'.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a base s.vs_memory /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
    vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL a' ==>
    val_in_memory tv a' base
      (mstore (base+k) (n2w (LENGTH vs-1)) s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule_all current_path_pop_header >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    (irule evaluate_subscripts_type >>
     goal_assum (drule_at Any) >> simp[] >>
     drule mem_path_offset_sound >> simp[]) >>
  `value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV (FRONT vs)))` by
    (gvs[value_has_type_def] >>
     `vs = FRONT vs ++ [LAST vs]` by simp[APPEND_FRONT_LAST] >>
     simp[all_have_type_EVERY, LENGTH_FRONT] >>
     qpat_x_assum `all_have_type etv vs` mp_tac >>
     qpat_x_assum `vs = _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[all_have_type_EVERY, EVERY_APPEND]) >>
  drule_at (Pat `assign_subscripts _ _ _ _ = _`) mem_path_replace_in_memory_typed >>
  simp[] >> disch_then (irule o cj 2) >>
  reverse conj_tac >- metis_tac[ADD_COMM] >>
  qexists_tac `s.vs_memory` >> simp[] >> rpt strip_tac >>
  irule mstore_padded_byte_outside >>
  gvs[type_memory_size_def] >> decide_tac
QED
