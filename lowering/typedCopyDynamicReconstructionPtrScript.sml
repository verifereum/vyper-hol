(* A payload-local update preserves the robust dynamic-array header. *)
Theory typedCopyDynamicReconstructionPtr
Ancestors normalizationPrefixPtr robustCopyTransportPtr valueEncodingDefs
  venomMemProofs valueEncodingProofs arithmetic list

Theorem typed_copy_dynarray_payload_reconstruct_ptr:
  !tv vs dc b m0 mf T0 Tf.
    LENGTH vs <= dc /\ LENGTH vs < dimword (:256) /\
    (!m. mem_agree_outside T0 m0 m ==>
      mem_word_at b m = n2w (LENGTH vs)) /\
    (!i. ~(b+32 <= i /\ i < b+32+dc*type_memory_size tv) ==>
      mem_bytes_at i 1 mf = mem_bytes_at i 1 m0 /\
      (i IN Tf <=> i IN T0)) /\
    (!j. j < LENGTH vs ==> !m.
      mem_agree_outside Tf mf m ==>
      val_in_memory tv (EL j vs) (b+32+j*type_memory_size tv) m) ==>
    !m. mem_agree_outside Tf mf m ==>
      val_in_memory (ArrayTV tv (Dynamic dc))
        (ArrayV (DynArrayV vs)) b m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside Tf mf m ==>
     mem_word_at b m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
      `mem_bytes_at b 32 mf = mem_bytes_at b 32 m0` by
        (irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
         `~(b+32 <= b+x /\ b+x < b+32+dc*type_memory_size tv)` by decide_tac >>
         first_x_assum drule >> simp[EL_mem_bytes_at, LIST_EQ_REWRITE]) >>
      `!i. i < 32 ==> (b+i IN Tf <=> b+i IN T0)` by
        (rpt strip_tac >>
         `~(b+32 <= b+i /\ b+i < b+32+dc*type_memory_size tv)` by decide_tac >>
         metis_tac[]) >>
      drule_all copied_window_agree_witness >>
      disch_then (qx_choose_then `mix` strip_assume_tac) >>
      `mem_word_at b mix = n2w (LENGTH vs)` by metis_tac[] >>
      fs[mem_word_at_def, mem_bytes_at_def] >> metis_tac[]) >>
  metis_tac[robust_dynarray_assemble]
QED
