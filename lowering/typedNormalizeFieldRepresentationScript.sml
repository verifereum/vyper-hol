(* Ordered heterogeneous reconstruction; no compiler execution. *)
Theory typedNormalizeFieldRepresentation
Ancestors
  typedNormalizeLayout valueEncodingProofs tupleTypedLoad list rich_list arithmetic pair

Theorem normalize_tuple_memory_intro:
  !vs tvs b m.
    LENGTH vs = LENGTH tvs /\
    (!j. j < LENGTH vs ==>
      val_in_memory (EL j tvs) (EL j vs)
        (b + SUM (MAP type_memory_size (TAKE j tvs))) m) ==>
    tuple_in_memory vs tvs b m
Proof
  Induct_on `vs` >- simp[valueEncodingDefsTheory.val_in_memory_def] >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >> strip_tac >>
  simp[valueEncodingDefsTheory.val_in_memory_def] >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> reverse conj_tac >- gvs[] >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[] >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> gvs[]
QED

Theorem normalize_tuple_memory_index:
  LENGTH vs = LENGTH tvs ==>
  (tuple_in_memory vs tvs b m <=>
    !j. j < LENGTH vs ==>
      val_in_memory (EL j tvs) (EL j vs)
        (b + SUM (MAP type_memory_size (TAKE j tvs))) m)
Proof
  metis_tac[normalize_tuple_memory_intro, tuple_in_memory_EL]
QED

Theorem normalize_fields_memory_index:
  LENGTH fields = LENGTH fts ==>
  (fields_in_memory fields fts b m <=>
    !j. j < LENGTH fields ==>
      val_in_memory (SND (EL j fts)) (SND (EL j fields))
        (b + SUM (MAP type_memory_size (TAKE j (MAP SND fts)))) m)
Proof
  strip_tac >> rewrite_tac[fields_in_memory_tuple] >>
  `LENGTH (MAP SND fields) = LENGTH (MAP SND fts)` by simp[] >>
  drule normalize_tuple_memory_index >> simp[EL_MAP]
QED

(* tuple_prefix_sizes supplies compiler/semantic cumulative equality.
   State the consumer at compiler offsets, retaining ordered LIST_REL. *)
Theorem normalize_tuple_compiler_offsets:
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs /\
  LENGTH vs = LENGTH tvs /\
  (!j. j < LENGTH vs ==>
    val_in_memory (EL j tvs) (EL j vs)
      (b + SUM (MAP (type_memory_bytes ce) (TAKE j tys))) m) ==>
  tuple_in_memory vs tvs b m
Proof
  strip_tac >> drule tuple_prefix_sizes >> strip_tac >>
  irule normalize_tuple_memory_intro >> simp[] >> metis_tac[]
QED

Theorem normalize_fields_compiler_offsets:
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv)
    tys (MAP SND fts) /\
  LENGTH fields = LENGTH fts /\
  (!j. j < LENGTH fields ==>
    val_in_memory (SND (EL j fts)) (SND (EL j fields))
      (b + SUM (MAP (type_memory_bytes ce) (TAKE j tys))) m) ==>
  fields_in_memory fields fts b m
Proof
  strip_tac >> rewrite_tac[fields_in_memory_tuple] >>
  irule normalize_tuple_compiler_offsets >>
  conj_tac >- simp[] >> qexistsl_tac [`ce`, `tys`] >> simp[EL_MAP]
QED

(* Ordered nominal alignment already has a checked producer interface:
   structFieldsProps.make_struct_fields_map_consistent supplies
   sfields_tenv_consistent, whose names and types equations relate the
   compiler fields to the semantic StructArgs list in order.
   typedCopyMetadata.built_struct_fields_types/names (names in
   structFieldsProps) expose the MAP equations; evaluated StructTV fields
   are ZIP of those names with evaluate_types results, not an arbitrary
   ALOOKUP-equivalent permutation. Size correspondence is supplied by
   typedNormalizeProducer.checked_return_frame_metadata and
   same_frame_return_metadata; tuple_prefix_sizes converts its LIST_REL
   instance into cumulative compiler/semantic offset equality.
   Actual compiler nominal traversal and stored-size offsets are handled
   by typedNormalizeFields.normalize_nominal_struct_fields_memory_run.
   These reconstruction lemmas require the aligned ordered lists; they do
   not replace metadata coherence by lookup equality. *)
