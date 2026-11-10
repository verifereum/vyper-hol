(* Typed normalized buffers supply the dynamic storage dispatcher's windows. *)
Theory placeStorageBufferBounds
Ancestors
  placeMemoryTypedBase exprSimHyps valueEncodingProps vyperTyping abiDecodeStaticProps
  vyperTypeValues vyperValue valueEncoding venomState words arithmetic

Theorem dynamic_storage_buffer_bounds:
  evaluate_type tenv (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  type_memory_bytes ce et = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n (p:bytes32)) s.vs_memory /\
  w2n p + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  (type_memory_bytes ce et + 31) DIV 32 = type_slot_size tv /\
  type_memory_bytes ce et = 32 * type_slot_size tv /\
  (0 < LENGTH vs ==> type_slot_size tv < dimword (:256)) /\
  LENGTH vs < dimword (:256) /\
  mload (w2n p) s = n2w (LENGTH vs) /\
  w2n p + 32 <= s.vs_alloca_next /\
  (!j. j < LENGTH vs ==>
    w2n (p + n2w (32 + j *
      (if type_slot_size tv = 1 then 32 else type_memory_bytes ce et))) +
      32 * type_slot_size tv <= s.vs_alloca_next)
Proof
  strip_tac >>
  drule vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv >> strip_tac >>
  qpat_assum `evaluate_type _ (ArrayT _ _) = _`
    (mp_then Any strip_assume_tac evaluate_type_well_formed_type_value) >>
  `cap < dimword (:256) /\ LENGTH vs <= cap` by
    fs[well_formed_type_value_def, value_has_type_def] >>
  `type_memory_size tv = 32 * type_slot_size tv` by
    simp[type_memory_size_slots] >>
  `mload (w2n p) s = n2w (LENGTH vs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload] >>
  fs[type_memory_size_def, type_slot_size_def] >>
  conj_tac
  >- (strip_tac >>
      `1 <= cap` by decide_tac >>
      `1 * type_slot_size tv <= cap * type_slot_size tv` by
        simp[LESS_MONO_MULT] >>
      decide_tac) >>
  rpt strip_tac >>
  `SUC j <= cap` by decide_tac >>
  `j * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` by
    (qspecl_then [`SUC j`, `cap`, `type_slot_size tv`] mp_tac LESS_MONO_MULT >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `32 * type_slot_size tv + w2n p +
    (j * (if type_slot_size tv = 1 then 32 else 32 * type_slot_size tv) + 32)
    <= s.vs_alloca_next` by
    (Cases_on `type_slot_size tv = 1`
     >- (gvs[] >> decide_tac) >>
     simp[] >> decide_tac) >>
  `w2n p + (j * (if type_slot_size tv = 1 then 32 else
      32 * type_slot_size tv) + 32) < dimword (:256)` by decide_tac >>
  simp[abiDecodeStaticPropsTheory.w2n_add_n2w_lt]
QED
