(* Shape of the constructor-argument decoder, which reads the data section
   with DLOAD: an instance of the generic decoder shape lemma. *)
Theory ctorDecoderShape
Ancestors
  list loweringShapeDefs loweringShapeRules loweringShapeProps
  abiEncoder unitShapeDefs venomInst

Theorem compile_abi_decode_dload_shape:
  (!dst src base hi info.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; base; hi])
      (compile_abi_decode_to_buf dst src DLOAD base hi info) (\x st. T)) /\
  (!dst src base hi elems ao vo.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; base; hi])
      (compile_abi_decode_complex_elems dst src DLOAD base hi elems ao vo) (\x st. T)) /\
  (!dst src base hi ei asz msz ip cnt.
    shape_step F compiler_label
      (\st. EVERY (plain_operand st) [dst; src; base; hi; ip; cnt])
      (compile_abi_decode_dyn_loop dst src DLOAD base hi ei asz msz ip cnt) (\x st. T))
Proof
  rpt conj_tac >> rpt gen_tac >> irule shape_step_conseq >>
  map_every (fn i => TRY (irule_at Any (cj i compile_abi_decode_shape_supported))) [1, 2, 3] >>
  qexists_tac `\st. T` >> simp[shape_stable_def]
QED
