(* The bytestring slot loop reads the live source encoding, irrespective of capacity. *)
Theory bodySlotCopyBytesMods
Ancestors
  arithmetic words placeStoreSlots valueCopyBytes bodyPtrDefs
  vyperTyping vyperValue

Theorem slot_copy_bytes_layout_mods:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  w2n k + type_slot_size dtv <= dimword (:256) /\
  (!mem. mem_agree_outside mask memory mem ==> val_in_memory stv v off mem) ==>
  compile_store_slots cenv src dst sty tr sa = ((),sb) /\
  0 < type_slot_size stv /\ 0 < type_slot_size dtv /\
  type_slot_size stv <= type_slot_size dtv /\
  w2n k + type_slot_size stv <= dimword (:256) /\
  (!mem. mem_agree_outside mask memory mem ==> val_in_memory dtv v off mem) /\
  (?writes. encode_value stv v = SOME writes /\ encode_value dtv v = SOME writes)
Proof
  strip_tac >>
  conj_tac
  >- (`compile_store_slots cenv src dst dty tr =
        compile_store_slots cenv src dst sty tr` by
        (irule store_slots_bytes_compile_eq >> simp[]) >> fs[]) >>
  `type_slot_size stv <= type_slot_size dtv /\
   encode_value stv v = encode_value dtv v` by
    (irule store_slots_bytes_encoding >> metis_tac[]) >>
  `0 < type_slot_size stv` by
    (qspecl_then [`tenv`,`sty`,`stv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >> simp[type_slot_size_def]) >>
  `0 < type_slot_size dtv /\ w2n k + type_slot_size stv <= dimword (:256)` by
    decide_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  metis_tac[CONJUNCT1 value_has_type_equiv, optionTheory.IS_SOME_EXISTS]
QED
