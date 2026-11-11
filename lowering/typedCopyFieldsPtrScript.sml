(* Invariant-threaded composition for recursive typed field copies. *)
Theory typedCopyFieldsPtr
Ancestors
  typedCopyPtr context compileEnv emitHelper contextCodegenRelProps
  bodyPtrDefs fragExecPtr list arithmetic

Theorem compile_typed_copy_fields_frag_ptr:
  !cx ctx PG cenv dst src R I.
    (!dt ds st ss doff soff a b c d dp sp.
       compile_with_byte_offset dst doff a = (dp,b) /\
       compile_with_byte_offset src soff b = (sp,c) /\
       compile_store_memory_typed cenv dp dt sp st c = ((),d) ==>
       cs_extends a d /\
       frag_exec_ptr cx ctx PG a d
         (I (dt::ds) (st::ss) doff soff a)
         (I ds ss (doff + type_memory_bytes cenv dt)
                  (soff + type_memory_bytes cenv st) d) R) ==>
    !dts sts doff soff a z.
      LENGTH dts = LENGTH sts /\
      compile_typed_copy_fields cenv dst src dts sts doff soff a = ((),z) ==>
      cs_extends a z /\
      frag_exec_ptr cx ctx PG a z (I dts sts doff soff a)
        (I [] [] (doff + SUM (MAP (type_memory_bytes cenv) dts))
                 (soff + SUM (MAP (type_memory_bytes cenv) sts)) z) R
Proof
  rpt gen_tac >> disch_tac >> Induct_on `dts`
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      conj_tac >- simp[cs_extends_def] >>
      simp[frag_exec_ptr_def] >> rpt strip_tac >> disj1_tac >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[] >>
      rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  rpt gen_tac >> Cases_on `sts` >> simp[] >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed cenv dp h sp h' sc = (u,sd)` >>
  Cases_on `u` >>
  qpat_x_assum `!sts doff soff a z. _` drule_all >> strip_tac >>
  qpat_x_assum `!dt ds st ss doff soff a b c d dp sp. _` drule_all >>
  disch_then (qspecl_then [`dts`, `t`] strip_assume_tac) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qpat_x_assum `frag_exec_ptr _ _ _ sd z _ _ _` mp_tac >>
  asm_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  strip_tac >>
  metis_tac[frag_exec_ptr_seq]
QED
