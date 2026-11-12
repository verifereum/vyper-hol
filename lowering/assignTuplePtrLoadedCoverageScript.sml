(* Prefix-to-store adapter: loaded aggregate addresses retain capacity for the
   entire member type, including rounded bytestring copy padding. *)
Theory assignTuplePtrLoadedCoverage
Ancestors
  assignTuplePtrStageLoads tupleMemoryLayout valueEncodingProofs
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState list arithmetic

Theorem tuple_loaded_member_coverage_ptr:
  !tys tvs i sitebase addr cap cx vs ops G tn s w p.
  LENGTH tys = LENGTH tvs /\ i < LENGTH tys /\
  sitebase <= (addr:num) /\ addr + type_memory_size_list tvs <= sitebase + cap /\
  ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
  ~is_word_type (EL i tys) /\
  eval_operand (EL i ops) s = SOME w /\
  w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)) /\
  EL i ops = Var p /\ FLOOKUP G p = SOME (sitebase,cap) ==>
  ptr_covers G tn p s (type_memory_size (EL i tvs))
Proof
  rpt gen_tac >> strip_tac >>
  `i < LENGTH tvs` by fs[] >>
  drule tuple_element_interval >> strip_tac >>
  `op_taint tn (Var p) = {} /\ lookup_var p s = SOME w` by
    gvs[ptr_val_ok_def, eval_operand_def] >>
  simp[ptr_covers_def] >>
  qpat_x_assum `addr + type_memory_size_list tvs <= sitebase + cap` mp_tac >>
  qpat_x_assum `SUM (MAP type_memory_size (TAKE i tvs)) + _ <= _` mp_tac >>
  simp[type_memory_size_list_sum] >> decide_tac
QED

Theorem tuple_loaded_operands_coverage_ptr:
  LENGTH tys = LENGTH tvs /\ sitebase <= addr /\
  addr + type_memory_size_list tvs <= sitebase + cap /\
  (!i. i < LENGTH tys ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
    (?w. eval_operand (EL i ops) s = SOME w /\
      (if is_word_type (EL i tys) then w = typed_val_to_w256 (EL i tvs) (EL i vs)
       else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (~is_word_type (EL i tys) ==>
      ?p. EL i ops = Var p /\ FLOOKUP G p = SOME (sitebase,cap))) ==>
  !i. i < LENGTH tys ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
    ?w. eval_operand (EL i ops) s = SOME w /\
      (if is_word_type (EL i tys) then w = typed_val_to_w256 (EL i tvs) (EL i vs)
       else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!p. ~is_word_type (EL i tys) /\ EL i ops = Var p ==>
        ptr_covers G tn p s (type_memory_size (EL i tvs)))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qexists `w` >> simp[] >>
  rpt strip_tac >>
  `?q. EL i ops = Var q /\ FLOOKUP G q = SOME (sitebase,cap)` by metis_tac[] >>
  `w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))` by gvs[] >>
  drule_all tuple_loaded_member_coverage_ptr >> gvs[]
QED
