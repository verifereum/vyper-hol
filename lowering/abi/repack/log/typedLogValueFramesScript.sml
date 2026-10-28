(* TOP-LEVEL: a field's typed memory and operand frames preserve any
   saved argument outside the destination footprint, including words. *)
Theory typedLogValueFrames
Ancestors
  typedLogArgs typedStoreFrames typedSArrayDynInvariant
  valueLoadProps memoryValueDefs valueEncoding
  compileEnv venomState venomInst list words arithmetic

Theorem lowered_value_rel_copy_frame:
  !ty tv v src before after ftv copy_count dst_off.
    lowered_value_rel ty tv v src before /\
    log_arg_safe src ty tv before dst_off (copy_count * type_memory_size ftv) /\
    eval_operand src after = eval_operand src before /\
    array_copy_frame ftv copy_count dst_off before.vs_memory after.vs_memory ==>
    lowered_value_rel ty tv v src after
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty`
  >- (qpat_x_assum `lowered_value_rel _ _ _ _ before` mp_tac >> simp[lowered_value_rel_def]) >>
  qpat_x_assum `lowered_value_rel _ _ _ _ before` mp_tac >>
  asm_simp_tac bool_ss [lowered_value_rel_def] >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `src_addr` strip_assume_tac)) >>
  qpat_x_assum `log_arg_safe _ _ _ _ _ _` (mp_tac o REWRITE_RULE [log_arg_safe_def]) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspec_then `src_addr` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `memory_value_rel tv v (w2n src_addr) after.vs_memory` by
    (mp_tac (Q.SPECL [`ftv`, `tv`, `v`, `copy_count`, `dst_off`, `w2n (src_addr:bytes32)`,
       `before.vs_memory`, `after.vs_memory`] array_copy_frame_source) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  simp[lowered_value_rel_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed saved Log value memory frame: " ^ name)
  end) (DB.thms "typedLogValueFrames")
