Theory bodyPtrBopInLiveStorage
Ancestors
  bodyPtrDefs bodyPtrBopInStorageContents ptrDiscipline compileEnv
  venomState vyperValue pred_set

(* A projection of the located-value post, for either key-addressed backend.
   Natural slot bounds are explicit: callers must discharge word no-wrap. *)
Theorem located_live_key_clean:
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  eval_operand p.ptr_operand s = SOME basew /\
  evaluate_type (get_tenv cx) ty = SOME aty /\
  w2n basew <= w2n key /\
  w2n key < w2n basew + type_slot_size aty /\
  (!b. b < 32 ==> ~dead_bytes
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (w2n basew) aty (w2n key) b) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) key = {}
Proof
  Cases_on `tr` >>
  simp[ptr_vv_ok_def, key_taint_def, EXTENSION] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem located_dynamic_header_clean:
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  eval_operand p.ptr_operand s = SOME basew /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV et (Dynamic cap)) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) basew = {}
Proof
  strip_tac >> irule located_live_key_clean >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[type_slot_size_def, dynamic_array_header_not_dead]
QED

Theorem located_fixed_deadless_clean:
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  eval_operand p.ptr_operand s = SOME basew /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV et (Fixed cap)) /\
  (!st bs j b. ~dead_bytes st bs et j b) /\
  w2n basew <= w2n key /\
  w2n key < w2n basew + type_slot_size (ArrayTV et (Fixed cap)) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) key = {}
Proof
  strip_tac >> irule located_live_key_clean >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[fixed_array_deadless_children]
QED

Theorem located_dynamic_element_clean:
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  eval_operand p.ptr_operand s = SOME basew /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV et (Dynamic cap)) /\
  (!st bs j b. ~dead_bytes st bs et j b) /\
  i < cap /\
  i < w2n (lookup_storage basew
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)) /\
  w2n basew <= w2n key /\
  w2n key < w2n basew + type_slot_size (ArrayTV et (Dynamic cap)) /\
  w2n basew + 1 + i * type_slot_size et <= w2n key /\
  w2n key < w2n basew + 1 + i * type_slot_size et + type_slot_size et /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) key = {}
Proof
  strip_tac >> irule located_live_key_clean >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  gen_tac >> disch_tac >> irule dynamic_array_live_deadless_child >>
  conj_tac >- simp[] >> qexists_tac `i` >> simp[]
QED

Theorem evaluated_word_deadless:
  is_word_type ty /\ evaluate_type tenv ty = SOME et ==>
  ~dead_bytes st bs et j b
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >~ [`evaluate_type tenv (FlagT flags)`]
  >- (simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[dead_bytes_def]) >>
  Cases_on `b'` >> simp[is_word_type_def]
  >~ [`is_word_type (BaseT (BytesT bd))`]
  >- (Cases_on `bd` >> simp[is_word_type_def, evaluate_type_def] >>
      rpt strip_tac >> gvs[AllCaseEqs(), dead_bytes_def]) >>
  simp[evaluate_type_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), dead_bytes_def]
QED
