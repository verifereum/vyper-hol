(* Robust representation, rather than pointer coverage, ensures clean contents. *)
Theory bodyPtrBopInMemoryContents
Ancestors representationCleanPtr typedCopyLayoutPtr ptrDiscipline pred_set

Theorem robust_scalar_memory_word_clean:
  !v tv a mem tn.
    ((?b. v = BoolV b) \/ (?n. v = IntV n) \/ (?k. v = FlagV k) \/
     (?n. v = DecimalV n) \/ (?bs. v = BytesV bs)) /\
    (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v a m) ==>
    mem_word_taint tn.t_mem a = {}
Proof
  rpt gen_tac >> strip_tac >>
  `!i. a <= i /\ i < a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_prim_clean, robust_val_in_memory_bytes_clean] >>
  simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
  first_x_assum (qspec_then `a + x` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem dynarray_memory_element_clean:
  !tv cap vs addr mem tn i.
    i < LENGTH vs /\
    ((?b. EL i vs = BoolV b) \/ (?n. EL i vs = IntV n) \/
     (?k. EL i vs = FlagV k) \/ (?n. EL i vs = DecimalV n) \/
     (?bs. EL i vs = BytesV bs)) /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Dynamic cap))
           (ArrayV (DynArrayV vs)) addr m) ==>
    mem_word_taint tn.t_mem (addr + 32 + i * type_memory_size tv) = {}
Proof
  metis_tac[robust_scalar_memory_word_clean, dynarray_in_memory_robust_element]
QED

Theorem sarray_memory_element_clean:
  !tv cap kvs addr mem tn i v.
    i < cap /\
    v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
    ((?b. v = BoolV b) \/ (?n. v = IntV n) \/ (?k. v = FlagV k) \/
     (?n. v = DecimalV n) \/ (?bs. v = BytesV bs)) /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Fixed cap))
           (ArrayV (SArrayV kvs)) addr m) ==>
    mem_word_taint tn.t_mem (addr + i * type_memory_size tv) = {}
Proof
  metis_tac[robust_scalar_memory_word_clean, sarray_in_memory_robust_element]
QED

Theorem dynarray_memory_header_clean:
  !tv cap vs addr mem tn.
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Dynamic cap))
           (ArrayV (DynArrayV vs)) addr m) ==>
    mem_word_taint tn.t_mem addr = {}
Proof
  rpt strip_tac >> drule dynarray_in_memory_robust_length >>
  disch_then assume_tac >>
  drule_then assume_tac robust_mem_word_at_clean >>
  simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
  first_x_assum (qspec_then `addr + x` mp_tac) >> simp[] >> metis_tac[]
QED
