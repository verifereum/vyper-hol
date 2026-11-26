(* Runtime-code membership reads the existing immutable data section. *)
Theory bodyMembershipCodeReadInputsMods
Ancestors
  builtinProps compileEnv context words list arithmetic

Theorem membership_code_read_inputs_mods:
  ~cenv.ce_is_ctor /\ loc = LocCode /\
  elem_size_in_location cenv loc ety = 32 /\
  (!i. i < LENGTH ws ==>
    let a = w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) in
    a + 32 <= LENGTH u.vs_data_section /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP a u.vs_data_section ++ REPLICATE 32 0w)) = EL i ws) /\
  (!cap. bd = Dynamic cap ==>
    w2n w + 32 <= LENGTH u.vs_data_section /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws)) ==>
  (!i. i < LENGTH ws ==>
    let addr = w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => word_scale loc) +
                         elem_size_in_location cenv loc ety * i) in
    ptr_load_val cenv.ce_is_ctor loc addr u = EL i ws /\
    w2n addr <= LENGTH u.vs_data_section) /\
  (!cap. bd = Dynamic cap ==>
    w2n w <= LENGTH u.vs_data_section /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws))
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!j. j < LENGTH ws ==> _` (drule_then mp_tac) >>
      Cases_on `bd` >>
      ASM_SIMP_TAC bool_ss [word_scale_def, ptr_load_val_def, LET_THM,
                            vyperASTTheory.bound_case_def] >>
      PURE_ONCE_REWRITE_TAC [Q.SPEC `32` MULT_COMM] >>
      disch_then strip_assume_tac >>
      ASM_SIMP_TAC bool_ss [] >> decide_tac) >>
  gen_tac >> disch_tac >>
  qpat_assum `!cap. bd = Dynamic cap ==> _` (drule_then strip_assume_tac) >>
  simp[] >> decide_tac
QED
