(* Place-local storage cleanliness, independent of global liveness. *)
Theory bodyPtrSubscriptWordStorage
Ancestors
  bodyPtrDefs exprSimUnwrap compileEnv vyperValue ptrDiscipline
  exprLoweringProps pred_set venomState

(* appendStorageRel has a local slot-size lemma, not an exported interface. *)
Theorem word_type_dead_bytes:
  is_word_type t /\ evaluate_type tenv t = SOME ty ==>
  ~dead_bytes st bs ty j b
Proof
  strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), dead_bytes_def]
QED

Theorem located_word_key_taint_empty:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME ty /\
  ptr_vv_ok cx t tv (LocatedValue t' p) ee G tn s /\
  eval_operand p.ptr_operand s = SOME w /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  key_taint (if p.ptr_location = LocTransient then tn.t_trans else tn.t_stor) w = {}
Proof
  strip_tac >>
  `type_slot_size ty = 1` by metis_tac[word_type_slot_size] >>
  `w2n w < w2n w + 1` by simp[] >>
  gvs[ptr_vv_ok_def, key_taint_def, EXTENSION] >>
  gen_tac >> Cases_on `x < 32` >> simp[] >>
  first_x_assum (qspecl_then [`w`, `x`] mp_tac) >> simp[] >>
  metis_tac[word_type_dead_bytes]
QED
