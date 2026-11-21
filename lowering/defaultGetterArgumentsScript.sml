Theory defaultGetterArguments
Ancestors
  compileVyper compileEnv supportedProgram supportedDecls supportedTypes
  vyperAST vyperGetter list pair

val _ = Parse.hide "body";

Theorem supported_getter_key_decoder[local]:
  !ty. supported_hashmap_key_type ty ==>
    is_word_type ty \/ is_bytestring_type ty
Proof
  Cases >> simp[supported_hashmap_key_type_def, supported_scalar_type_def,
                supported_word_type_def, supported_string_type_def,
                is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
       is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, supported_string_type_def,
       is_word_type_def, is_bytestring_type_def]
QED

Theorem supported_build_getter_argument_types[local]:
  !e kt vt n.
    !args ret exp tops.
    supported_hashmap_key_type kt /\
    ((?ty. vt = Type ty) \/ supported_hashmap_value tops vt) /\
    build_getter e kt vt n = (args,ret,exp) ==>
    EVERY (\arg. is_word_type (SND arg) \/
                 is_bytestring_type (SND arg)) args
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[supported_hashmap_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  all_tac >>~- ([`~is_ArrayT vt`], metis_tac[supported_getter_key_decoder]) >>
  all_tac >>~- ([`is_ArrayT vt`],
    pairarg_tac >> gvs[] >>
    `supported_hashmap_key_type (BaseT (UintT 256))` by
      simp[supported_hashmap_key_type_def, supported_scalar_type_def, supported_word_type_def,
           supported_int_width_def] >>
    metis_tac[supported_getter_key_decoder]) >>
  pairarg_tac >> gvs[supported_hashmap_value_def] >>
  metis_tac[supported_getter_key_decoder]
QED

Theorem supported_public_getter_argument_types[local]:
  supported_declaration_header tops decl /\
  public_getter decl = SOME (mut,nr,rr,name,args,ds,ret,body) ==>
  EVERY (\arg. is_word_type (SND arg) \/
               is_bytestring_type (SND arg)) args
Proof
  Cases_on `decl` >> simp[public_getter_def] >>
  Cases_on `v` >> simp[public_getter_def] >>
  rpt strip_tac >>
  gvs[supported_declaration_header_def, AllCaseEqs(), getter_def]
  >- (pairarg_tac >> gvs[] >> Cases_on `t` >>
      gvs[is_ArrayT_def, ArrayT_type_def] >>
      pairarg_tac >> gvs[] >>
      irule supported_build_getter_argument_types >>
      goal_assum (drule_at Any) >>
      simp[supported_hashmap_key_type_def, supported_scalar_type_def, supported_word_type_def,
           supported_int_width_def]) >>
  Cases_on `o'` >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[supported_build_getter_argument_types]
QED

Theorem default_getter_argument_types:
  supported_program tops /\
  MEM (mut,nr,rr,name,args,ds,ret,body) (public_getters tops) ==>
  EVERY (\arg. is_word_type (SND arg) \/
               is_bytestring_type (SND arg)) args
Proof
  simp[MEM_public_getters] >> rpt strip_tac >>
  drule_all supported_program_declaration >> strip_tac >>
  metis_tac[supported_public_getter_argument_types]
QED
