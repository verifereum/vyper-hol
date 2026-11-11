Theory typedCopyWidenBounds
Ancestors
  typedMemoryCopy exprSimHyps vyperTypeSystem vyperValue valueEncoding
  valueEncodingProps arithmetic

Theorem arg_type_fits_memory_size:
  (!sty dty. arg_type_fits sty dty ==>
    !tenv stv dtv.
      evaluate_type tenv sty = SOME stv /\
      evaluate_type tenv dty = SOME dtv ==>
      type_memory_size stv <= type_memory_size dtv) /\
  (!stys dtys. arg_types_fit stys dtys ==>
    !tenv stvs dtvs.
      OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
      OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
      type_memory_size_list stvs <= type_memory_size_list dtvs)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[arg_type_fits_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs(),
      type_memory_size_def] >>
  metis_tac[word_size_monotone, LESS_EQ_LESS_EQ_MONO,
            LESS_MONO_MULT2]
QED

Theorem type_widens_to_memory_size:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  type_memory_size stv <= type_memory_size dtv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[arg_type_fits_memory_size]
QED

Theorem type_widens_to_memory_bytes:
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  type_memory_bytes cenv sty <= type_memory_bytes cenv dty
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv sty = type_memory_size stv` by
    (irule typed_copy_memory_size >> metis_tac[]) >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> metis_tac[]) >>
  gvs[] >> irule type_widens_to_memory_size >> metis_tac[]
QED
