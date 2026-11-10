(* Struct field layout and memory projection properties. *)
Theory exprSimFieldLayout
Ancestors
  valueEncodingProps
  exprSimHypsDefs compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeExprSoundness
  list rich_list finite_map pair
Libs
  pairLib



Theorem slot_count_of_memory_size:
  !tv. (type_memory_size tv + 31) DIV 32 = type_slot_size tv
Proof
  rw[type_memory_size_slots] >>
  once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
  irule arithmeticTheory.DIV_MULT >> simp[]
QED

Definition fields_layout_def:
  fields_layout (fields : (string # type # num) list)
                (fs : (string # type_value) list) <=>
    LIST_REL (\(n,fty,sz) (n',tv). n = n' /\ sz = type_memory_size tv)
      fields fs
End

Theorem fields_layout_zip[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(name, ty, sz). !tv. evaluate_type tenv ty = SOME tv ==>
                                 sz = type_memory_size tv) fields ==>
    fields_layout fields (ZIP (MAP FST fields, tvs))
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> rpt strip_tac >> gvs[]
QED

Theorem struct_fields_layout:
  !cenv cx env es sid stv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv ==>
    ?fs. stv = StructTV fs /\
         fields_layout
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
            sz = type_memory_size tv) fields` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  simp[get_struct_fields_def] >>
  qpat_x_assum `MAP FST fields = _` (SUBST1_TAC o SYM) >>
  irule fields_layout_zip >> simp[] >>
  drule (cj 2 evaluate_type_mono) >> strip_tac >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  qexists_tac `get_tenv cx` >> simp[]
QED

Theorem fields_in_memory_field:
  !fields fs vals off mem id fv ftv.
    fields_layout fields fs /\ struct_has_type fs vals /\
    fields_in_memory vals fs off mem /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv ==>
    val_in_memory ftv fv (off + struct_field_offset fields id) mem
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> Cases >> simp[] >>
  PairCases_on `h` >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_in_memory_def, struct_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem fields_val_wf_field:
  !vals fs id fv ftv.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv ==>
    val_wf ftv fv
Proof
  Induct >> simp[] >> PairCases >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >> simp[value_has_type_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >> metis_tac[]
QED

Theorem struct_field_offset_le:
  !fields fs id ftv.
    fields_layout fields fs /\ ALOOKUP fs id = SOME ftv ==>
    struct_field_offset fields id + type_memory_size ftv <=
      type_memory_size_fields fs
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> Cases >> simp[] >>
  PairCases_on `h` >>
  simp[struct_field_offset_def, type_memory_size_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem struct_field_offset_slots_eq:
  !fields fs id off ftv.
    fields_layout fields fs /\ struct_field_slot fs id = SOME (off, ftv) ==>
    struct_field_offset_slots fields id = off
Proof
  simp[fields_layout_def] >>
  Induct >> simp[struct_field_slot_def] >> PairCases >> Cases >>
  simp[struct_field_slot_def] >>
  PairCases_on `h` >>
  simp[struct_field_offset_slots_def, struct_field_slot_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[slot_count_of_memory_size] >>
  rename1 `struct_field_slot t id = SOME z` >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED
