(* Static indexed eligibility for heterogeneous typed-copy children. *)
Theory typedCopyReturnFieldSemantics
Ancestors typedMemoryCopy list rich_list arithmetic

Theorem typed_copy_return_fields_semantics:
  !dts sts dtvs stvs vs.
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) sts dts /\
    OPT_MMAP (evaluate_type tenv) dts = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) sts = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dts /\ type_widens_to tenv cs cd /\
      evaluate_type tenv cs = SOME cst /\ evaluate_type tenv cd = SOME cdt /\
      value_has_type cst cv /\ value_has_type cdt cv /\
      val_wf cst cv /\ val_wf cdt cv ==> R cd cs cdt cst cv) ==>
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vs = LENGTH dts /\
    (!i. i < LENGTH dts ==>
      type_memory_bytes ce (EL i dts) = type_memory_size (EL i dtvs) /\
      type_memory_bytes ce (EL i sts) = type_memory_size (EL i stvs) /\
      val_wf (EL i dtvs) (EL i vs) /\ val_wf (EL i stvs) (EL i vs) /\
      R (EL i dts) (EL i sts) (EL i dtvs) (EL i stvs) (EL i vs))
Proof
  Induct >> Cases_on `sts` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[AllCaseEqs(), vyperTypingTheory.value_has_type_def,
       valueEncodingTheory.val_wf_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!sts stvs vs. _ ==> LENGTH sts = _ /\ _` drule_all >>
  strip_tac >> simp[] >> gen_tac >> Cases_on `i` >> simp[] >>
  metis_tac[typed_copy_memory_size]
QED
