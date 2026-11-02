(* TOP-LEVEL: compatible element types supply both footprint invariants,
   and the generic loop preserves the prefix names holding its saved length
   and data pointers. These facts do not restrict the element constructors. *)
Theory typedDynLoopValues
Ancestors
  typedDynLoopInvariant typedDynLoopNames vyperEventCompatibility memoryValueTyping
  memoryValueDefs valueEncoding compileEnv vyperTypeSystem vyperValue vyperTyping
  venomState venomInst list words arithmetic

Theorem array_copy_compatible_values_wf:
  !tenv fty aty ftv atv at_index copy_count.
    event_arg_compatible fty aty /\ evaluate_type tenv fty = SOME ftv /\
    evaluate_type tenv aty = SOME atv /\
    (!j. j < copy_count ==> value_has_type atv (at_index j)) ==>
    (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (!j. j < copy_count ==> val_wf ftv (at_index j))
Proof
  rpt gen_tac >> strip_tac >>
  `!v. value_has_type atv v ==> value_has_type ftv v` by
    (drule (CONJUNCT1 event_arg_compatible_value_has_type) >>
     disch_then (qspecl_then [`tenv`, `ftv`, `atv`] mp_tac) >> simp[]) >>
  conj_tac >> rpt gen_tac >> DISCH_TAC >> irule value_has_type_val_wf >>
  `value_has_type atv (at_index j)` by
    (qpat_x_assum `!j. j < copy_count ==> _` (qspec_then `j` mp_tac) >> simp[]) >>
  FIRST [first_assum MATCH_ACCEPT_TAC,
    qpat_x_assum `!v. value_has_type atv v ==> _` (qspec_then `at_index j` mp_tac) >> simp[]]
QED

Theorem array_copy_loop_inv_saved_prefix:
  !var_base num_names cond_label ftv atv at_index copy_count src_data dst_data initial i current.
    array_copy_loop_inv (compiler_var_name var_base 5) cond_label
      (compiler_var_names (var_base + 5) num_names) ftv atv at_index copy_count src_data dst_data initial i current ==>
    !j. j < 5 ==> eval_operand (Var (compiler_var_name var_base j)) current =
      eval_operand (Var (compiler_var_name var_base j)) initial
Proof
  rpt gen_tac >> simp_tac bool_ss [array_copy_loop_inv_def] >> strip_tac >>
  qx_gen_tac `j` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`var_base`, `5`, `num_names`, `initial`, `current`, `j`]
    compiler_operands_frame_before) >> simp[]
QED
