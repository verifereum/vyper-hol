(* Frames for tuple assignment from a distinct physical source layout. *)
Theory tupleWidenedStoreFrame
Ancestors
  typedCopyRankPathMem bodyMemAssignLocalMem tupleMemoryFrame
  bodyMemAssignTopCopySem placeMemoryCopyEffect valueEncodingProofs
  compileEnv venomState bodyMemBopRestWordPath bodyMemoryDefs

Theorem typed_copy_owned_tuple_frame:
  typed_copy_effect ctx func sa sb s t dst written /\
  regions_disjoint b sz dst dsz /\ written <= dsz /\
  b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
  tuple_in_memory vs tvs addr s.vs_memory /\ tuple_val_wf vs tvs ==>
  tuple_in_memory vs tvs addr t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at addr (type_memory_size_list tvs) t.vs_memory =
   mem_bytes_at addr (type_memory_size_list tvs) s.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule (cj 5 val_in_memory_mem_agree_proof) >>
  metis_tac[]
QED

(* Reconstruct source-level locals once, independently of the copy algorithm. *)
Theorem typed_copy_local_write_frame:
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ local_ptrs_reserved cenv sa /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size entry.type) /\
  val_wf entry.type v /\ val_in_memory entry.type v (w2n w) t.vs_memory ==>
  stmt_state_rel ctx func cenv cx
    (es with scopes :=
      pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t
Proof
  strip_tac >>
  drule_then assume_tac typed_copy_effect_record >>
  qabbrev_tac `u = t with <|vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>` >>
  `stmt_state_rel ctx func cenv cx
    (es with scopes :=
      pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) u` by
    (irule local_memory_write_frame >>
     simp[] >> qexistsl_tac [`s`, `sa`, `w`] >>
     simp[Abbr `u`, lookup_var_def] >>
     fs[typed_copy_effect_def, lookup_var_def] >> metis_tac[]) >>
  irule topcopy_normalized_state >>
  qexistsl_tac [`u`, `sa`] >> simp[Abbr `u`, lookup_var_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ _ u2` >>
  `u2 = t with <|vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>` by
    simp[Abbr `u2`, venom_state_component_equality] >>
  gvs[]
QED

Theorem typed_copy_body_frames:
  typed_copy_effect ctx func sa sb s t dst written /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  return_buf_frame d cenv sa s /\ sa.cs_next_var <= sb.cs_next_var ==>
  alloca_history func t /\ return_buf_frame d cenv sb t /\
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func t` by
    (irule (cj 1 rest_word_marked_alloca) >>
     goal_assum (drule_at Any) >>
     metis_tac[typed_copy_effect_path]) >>
  simp[] >> irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s`, `sa`] >> simp[] >>
  metis_tac[typed_copy_effect_lookup]
QED
