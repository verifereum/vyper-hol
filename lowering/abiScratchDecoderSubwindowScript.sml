(* Actual source slices and output cells inherit physical decoder ownership. *)
Theory abiScratchDecoderSubwindow
Ancestors
  abiScratchDecoderContract abiScratchFootprint abiEncoderArrayFrame
  abiDecoderFootprint abiDecoderFrame abiDecoderContract abiDecoderAllocation
  compileEnv venomState words list arithmetic

Theorem abi_scratch_disjoint_output_subwindow:
  abi_footprint_disjoint sb len ((d,outsz)::fp) /\
  d <= childd /\ childd + childsz <= d + outsz ==>
  abi_footprint_disjoint sb len ((childd,childsz)::fp)
Proof
  simp_tac bool_ss [abi_scratch_disjoint_cons] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_disjoint_windows:
  abi_footprint_disjoint sb len ((d,outsz)::fp) /\
  sb <= childsb /\ childsb + childlen <= sb + len /\
  d <= childd /\ childd + childsz <= d + outsz ==>
  abi_footprint_disjoint childsb childlen ((childd,childsz)::fp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint childsb childlen ((d,outsz)::fp)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`, `len`] >>
     asm_simp_tac bool_ss []) >>
  irule abi_scratch_disjoint_output_subwindow >>
  qexistsl_tac [`d`, `outsz`] >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_subwindow_ranges:
  abi_scratch_decoder_ranges opc hi src dst sb len d outsz first last b cap s /\
  sb <= childsb /\ childsb + childlen <= sb + len /\
  d <= childd /\ childd + childsz <= d + outsz /\
  eval_operand childsrc s = SOME (n2w childsb) /\
  eval_operand childdst s = SOME (n2w childd) ==>
  abi_scratch_decoder_ranges opc hi childsrc childdst childsb childlen childd childsz
    first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint childd childsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`, `outsz`] >>
     asm_simp_tac bool_ss []) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    childsb + childlen <= h /\ h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >>
      disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qexists_tac `h` >> asm_simp_tac bool_ss [] >> decide_tac) >>
  SUBGOAL_THEN ``opc = MLOAD ==> abi_footprint_disjoint childsb childlen
    ((childd,childsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)`` assume_tac
  >- (strip_tac >> qpat_x_assum `opc = MLOAD ==> _` (fn th => drule_all th) >>
      disch_then assume_tac >>
      mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap s`]
        abi_scratch_disjoint_windows) >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED
