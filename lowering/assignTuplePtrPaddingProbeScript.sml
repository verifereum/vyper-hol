(* Interface audit only: this is NOT a counterexample to tuple assignment.
   typedCopyPtr's audit_string_padding_unconstrained already checks that byte
   33 is irrelevant to String[1] "a".  Here we check the actual MCOPY taint
   equation at that byte. stmt_frag_ptr does not require ghost_kept after
   assignment; only the RHS expression judgments require that memory frame. *)
Theory assignTuplePtrPaddingProbe
Ancestors
  bodyPtrDefs ptrDiscipline venomState venomInst valueEncoding exprSimProps

Theorem tuple_padding_copy_extent_probe:
  val_store_size (BaseTV (StringT 1)) (StringV "a") = 64
Proof
  EVAL_TAC
QED

Theorem tuple_padding_written_taint_probe:
  !tn s. tn.t_mem = {33} ==>
    161 IN written_taint tn
      (mk_inst 0 MCOPY [Lit 128w; Lit 0w; Lit 64w] []) s /\
    161 NOTIN tn.t_mem
Proof
  rpt strip_tac >>
  gvs[written_taint_def, mk_inst_def, eval_operand_def,
      wordsTheory.dimword_def]
QED
