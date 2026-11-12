(* Source layout boundary for tuple-like internal stack returns. *)
Theory internalReturnTupleBoundaryMem
Ancestors
  internalReturnTupleMem internalReturnBufferBoundaryMem stmtSimReturnWiden
  compileEnv list arithmetic

Theorem internal_return_tuple_count[local]:
  !sft ty. ~is_word_type ty /\ 0 < returns_stack_count sft ty ==>
  ?tys. (case ty of TupleT ts => ts | StructT nm => sft (nsid_to_string nm)
         | _ => []) = tys /\
    tys <> [] /\ EVERY is_word_type tys /\
    returns_stack_count sft ty = LENGTH tys
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def,
       SF boolSimps.COND_elim_ss] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
