Theory bodyPtrBopHashSequence
Ancestors
  bodyPtrBopHashStep bodyPtrBopScalarProbe typedCopyPtr fragGasSeqPtr
  ptrDiscipline venomInst finite_map

Theorem bop_hash_add_provenance:
  FLOOKUP G p = SOME site ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var p; Lit 32w] [q]) u) q =
    SOME site
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE]
QED
