(*
 * The residual augmented assignment targets of bodySimStmtCases'
 * body_augassign_other: what supported_stmt admits for AugAssign beyond a
 * local, a full-word storage or transient variable, a field of a local, and
 * a supported field of a storage or transient struct.
 *
 * TOP-LEVEL:
 *   supported_aug_toplevel_decl — a supported augmented top-level target
 *                       is a word variable of tops in storage or transient
 *                       storage (any word width, not only full words)
 *   supported_aug_attr_toplevel_field — a supported augmented field of a
 *                       top-level variable is a supported storage field
 *)
Theory bodyAugAssignOther
Ancestors
  supportedStmts supportedTargets supportedExprForms supportedDecls
  supportedTypes bodyStorageMetadata compileEnv vyperAST list alist

Theorem supported_word_type_is_word:
  !ty. supported_word_type ty ==> is_word_type ty
Proof
  Cases >> simp[supported_word_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, is_word_type_def]
QED

Theorem supported_aug_toplevel_decl:
  !tops bindings src id.
    supported_aug_target tops bindings (TopLevelNameTarget (src, id)) ==>
    src = NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      (mut = Storage \/ mut = Transient) /\ is_word_type ty
Proof
  rpt gen_tac >>
  simp[supported_aug_target_def, supported_target_info_def,
       supported_place_root_def] >>
  Cases_on `supported_hashmap_decl tops (src, id)`
  >- (Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
      rename1 `SOME x` >> PairCases_on `x` >>
      drule supported_variable_decl_mem >> strip_tac >>
      Cases_on `x3` >> Cases_on `x0` >> Cases_on `x1` >> simp[] >>
      rw[] >> gvs[] >> first_assum (irule_at Any) >>
      simp[supported_word_type_is_word]) >>
  rename1 `SOME y` >> PairCases_on `y` >> rw[]
QED

Theorem supported_aug_attr_toplevel_field:
  !tops bindings nsid fld.
    supported_aug_target tops bindings
      (AttributeTarget (TopLevelNameTarget nsid) fld) ==>
    supported_storage_field_write tops nsid fld
Proof
  rpt gen_tac >>
  simp[supported_aug_target_def, supported_target_info_def,
       supported_place_root_def, supported_storage_field_write_def,
       supported_storage_fields_def] >>
  Cases_on `supported_hashmap_decl tops nsid`
  >- (Cases_on `supported_variable_decl tops nsid` >> simp[] >>
      rename1 `SOME x` >> PairCases_on `x` >>
      Cases_on `x3` >> Cases_on `x0` >> Cases_on `x1` >> simp[] >>
      rw[] >> Cases_on `x2` >> gvs[] >>
      Cases_on `supported_struct_fields tops p` >> gvs[] >>
      Cases_on `ALOOKUP x' fld` >> gvs[MEM_MAP, PULL_EXISTS] >>
      drule ALOOKUP_MEM >> strip_tac >> first_assum (irule_at Any) >> simp[]) >>
  rename1 `SOME y` >> PairCases_on `y` >> rw[]
QED
