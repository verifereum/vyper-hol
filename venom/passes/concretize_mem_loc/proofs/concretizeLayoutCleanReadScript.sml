Theory concretizeLayoutCleanRead
Ancestors venomExecSemantics venomState contextCodegenRel rich_list list

(* Padded reads depend only on byte agreement in the requested slice. *)
Theorem concretize_read_memory_bytes:
  (!i. i < n ==>
    codegenRel$read_byte (a+i) s.vs_memory =
    codegenRel$read_byte (b+i) t.vs_memory) ==>
  read_memory a n s = read_memory b n t
Proof
  strip_tac >> simp[read_memory_def] >> irule listTheory.LIST_EQ >>
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
  qx_gen_tac `j` >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[codegenRelTheory.read_byte_def, EL_TAKE] >>
  Cases_on `a+j < LENGTH s.vs_memory` >>
  Cases_on `b+j < LENGTH t.vs_memory` >>
  gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
      LENGTH_DROP, rich_listTheory.EL_DROP, rich_listTheory.EL_REPLICATE]
QED
