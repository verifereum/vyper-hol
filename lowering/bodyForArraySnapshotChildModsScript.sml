(* Indexed byte projection from the saved Array-iterator snapshot. *)
Theory bodyForArraySnapshotChildMods
Ancestors
  stmtSimForArray bodyDynArraySource exprSimAggregateEncoding loweringPosts
  valueEncodingProps valueEncoding vyperValueOperation vyperTyping vyperValue
  vyperState arithmetic list

Theorem snapshot_child_stride[local]:
  k < len ==> k * stride + stride <= len * stride
Proof
  strip_tac >>
  `SUC k * stride <= len * stride` by (irule LESS_MONO_MULT >> decide_tac) >>
  pop_assum (mp_tac o REWRITE_RULE [MULT_CLAUSES]) >> decide_tac
QED

Theorem for_array_snapshot_child_mods:
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\ k < LENGTH vs /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV tv bd) ==>
  let v = EL k (array_elements (ArrayTV tv bd) av);
      header = (case bd of Fixed _ => 0 | Dynamic _ => 32);
      delta = header + k * type_memory_size tv
  in
    EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\
    delta + type_memory_size tv <= header + LENGTH vs * type_memory_size tv /\
    delta + type_memory_size tv <= type_memory_size (ArrayTV tv bd) /\
    delta + type_memory_size tv <= val_footprint (ArrayTV tv bd) (ArrayV av) /\
    !base m. val_in_memory (ArrayTV tv bd) (ArrayV av) base m ==>
             val_in_memory tv v (base + delta) m
Proof
  strip_tac >> qpat_x_assum `vs = MAP Value _` SUBST_ALL_TAC >>
  fs[LET_THM, val_footprint_def, LENGTH_MAP, EL_MAP] >>
  `k * type_memory_size tv + type_memory_size tv <=
     LENGTH (array_elements (ArrayTV tv bd) av) * type_memory_size tv` by
    (irule snapshot_child_stride >> first_assum ACCEPT_TAC) >>
  namedCases_on `bd` ["cap", "cap"]
  >- (`?al. av = SArrayV al` by
        (Cases_on `av` >> fs[value_has_type_inv]) >> gvs[] >>
      `LENGTH (array_elements (ArrayTV tv (Fixed cap)) (SArrayV al)) = cap` by
        simp[array_elements_def] >>
      `k < cap` by fs[] >>
      drule_all_then strip_assume_tac fixed_array_elements_typed >>
      fs[type_memory_size_def] >>
      rpt gen_tac >> strip_tac >>
      drule_all_then ACCEPT_TAC fixed_array_element_in_memory) >>
  `?xs. av = DynArrayV xs /\ LENGTH xs <= cap` by
    (Cases_on `av` >> fs[value_has_type_inv]) >> gvs[array_elements_def] >>
  drule_all_then strip_assume_tac dynarray_elements_typed >>
  `LENGTH xs * type_memory_size tv <= cap * type_memory_size tv` by
    simp[LESS_MONO_MULT] >>
  `k * type_memory_size tv + type_memory_size tv <= cap * type_memory_size tv` by
    (irule LESS_EQ_TRANS >> qexists_tac `LENGTH xs * type_memory_size tv` >> simp[]) >>
  simp[type_memory_size_def, GSYM ADD_ASSOC] >>
  qx_genl_tac [`b`,`m`] >> strip_tac >>
  `elems_in_memory xs (b + 32) tv m` by fs[val_in_memory_dynarray] >>
  drule_all_then mp_tac elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]
QED
