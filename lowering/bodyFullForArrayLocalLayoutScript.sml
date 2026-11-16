(* Local array layout at the full, arbitrary-lower-bound invariant. *)
Theory bodyFullForArrayLocalLayout
Ancestors bodyPtrDefs forPtrElement stmtSimForArray exprSimAggregateEncoding
  valueEncodingProps vyperTyping vyperValueOperation arithmetic words

Theorem for_array_local_element_layout_full:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
  value_has_type ent.type ent.value /\
  vs = array_elements ent.type av /\ lookup_var ap s = SOME bword /\
  bytes = type_memory_size tv /\ k < LENGTH vs /\
  header = (case bd of Fixed n => 0 | Dynamic n => 32) ==>
  ptr_covers G tn ap s az /\ w2n bword + az < dimword (:256) /\
  header + LENGTH vs * bytes <= az /\
  header + k * bytes + bytes <= az /\
  w2n (bword + n2w (header + k * bytes)) =
    w2n bword + header + k * bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL k vs) (w2n bword + header + k * bytes) mem)
Proof
  strip_tac >>
  drule_all stmt_state_rel_local_extent >> strip_tac >>
  `ptr_covers G tn ap s az /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory ent.type ent.value (w2n bword) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `w2n bword + az < dimword (:256)` by (gvs[] >> decide_tac) >>
  `header + LENGTH vs * bytes <= az` by
    (Cases_on `bd` >> Cases_on `av` >>
     gvs[value_has_type_def, array_elements_def,
         valueEncodingTheory.type_memory_size_def] >>
     qpat_x_assum `LENGTH _ <= _` (mp_tac o MATCH_MP LESS_MONO_MULT) >>
     disch_then (qspec_then `type_memory_size tv` mp_tac) >> decide_tac) >>
  `header + k * bytes + bytes <= az` by
    (irule fixed_array_element_extent >> qexists_tac `LENGTH vs` >> simp[]) >>
  `w2n bword + (header + k * bytes) < dimword (:256)` by decide_tac >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `w2n bword + (_ + _) < _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     `header + k * bytes < dimword (:256)` by decide_tac >>
     asm_simp_tac bool_ss [word_add_def, w2n_n2w, LESS_MOD] >>
     pure_rewrite_tac[ADD_ASSOC] >> REFL_TAC) >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `bd`
  >- (Cases_on `av` >> gvs[value_has_type_def, fixed_array_elements_length] >>
      strip_tac >> irule fixed_array_element_in_memory >> simp[]) >>
  Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, val_in_memory_dynarray] >>
  strip_tac >> drule_all elems_in_memory_EL >>
  simp[AC ADD_ASSOC ADD_COMM]
QED
