(* Header interface diagnostic: cleanliness is not scalar provenance. *)
Theory extRetAbiArrayHeaderPtr
Ancestors
  abiEncoderArrayHeader typedCopyLoopHeaderPtr ptrDiscipline
  venomInst venomState finite_map pred_set

Theorem abi_encode_header_count_provenance_obstruction:
  FLOOKUP G iv = NONE /\ FLOOKUP G cv = SOME site ==>
  ~access_ok 0 G fn (mk_inst id LT [Var iv; Var cv] [cmp]) s
Proof
  strip_tac >> simp[access_ok_def, mk_inst_def] >>
  disj2_tac >> gvs[FLOOKUP_DEF]
QED
