(* TOP-LEVEL: complete sparse fixed-array values expose every typed source
   slot and their physical prefix, including omitted default elements. *)
Theory typedArrayLoopValues
Ancestors
  typedArrayCopyMemory typedSArrayDynSafety memoryValueAbiArray memoryValueDefs valueEncoding
  vyperTypeValues vyperValue vyperTyping list alist arithmetic

Theorem memory_fixed_array_elements:
  !tenv elem_ty elem_tv sparse copy_count offset mem.
    evaluate_type tenv elem_ty = SOME elem_tv /\
    value_has_type (ArrayTV elem_tv (Fixed copy_count)) (ArrayV (SArrayV sparse)) /\
    memory_value_rel (ArrayTV elem_tv (Fixed copy_count)) (ArrayV (SArrayV sparse)) offset mem ==>
    (!j. j < copy_count ==> value_has_type elem_tv
      (case ALOOKUP sparse j of NONE => default_value elem_tv | SOME v => v)) /\
    array_copy_prefix elem_tv (\j. case ALOOKUP sparse j of NONE => default_value elem_tv | SOME v => v)
      copy_count offset mem
Proof
  rpt gen_tac >> strip_tac >>
  `sparse_has_type elem_tv copy_count sparse` by fs[value_has_type_def] >> conj_tac
  >- (rpt gen_tac >> DISCH_TAC >>
      mp_tac (Q.SPECL [`tenv`, `elem_ty`, `elem_tv`, `sparse`, `copy_count`, `j`] sparse_slot_has_type) >> simp[]) >>
  fs[array_copy_fixed_layout]
QED

Theorem value_has_type_sarray_cases:
  !elem_tv copy_count v.
    value_has_type (ArrayTV elem_tv (Fixed copy_count)) v ==>
    ?sparse. v = ArrayV (SArrayV sparse)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[value_has_type_inv] >>
  qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >> simp[value_has_type_inv]
QED

Theorem evaluate_type_dynarray_count_bound:
  !tenv ty tv capacity.
    evaluate_type tenv (ArrayT ty (Dynamic capacity)) = SOME (ArrayTV tv (Dynamic capacity)) ==>
    evaluate_type tenv ty = SOME tv /\ capacity < dimword(:256)
Proof
  rpt gen_tac >> DISCH_TAC >>
  drule evaluate_type_ArrayT_cases >> disch_then (qx_choose_then `candidate_tv` strip_assume_tac) >>
  `candidate_tv = tv` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  asm_simp_tac (srw_ss()) [LET_THM, type_slot_size_def] >> strip_tac >>
  mp_tac (Q.SPECL [`capacity`, `type_slot_size tv`, `1`] array_copy_count_bound) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed sparse array source elements: " ^ name)
  end) (DB.thms "typedArrayLoopValues")
