(* Counted composition of recursive field stores. *)
Theory bodyPtrIntCallStoreFields
Ancestors
  typedCopyFieldsPtr fragGasPathPtr fragGasSeqPtr context compileEnv
  emitHelper bodyPtrDefs list arithmetic

Theorem intcall_typed_fields_counted_traversal:
  !D ctx fn PG ce dst src I.
    (!dt ds st ss doff soff a b c d dp sp.
      compile_with_byte_offset dst doff a = (dp,b) /\
      compile_with_byte_offset src soff b = (sp,c) /\
      compile_store_memory_typed ce dp dt sp st c = ((),d) ==>
      cs_extends a d /\
      !G tn s. ~s.vs_halted /\ I (dt::ds) (st::ss) doff soff a G tn s ==>
        ?H tf z. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
          I ds ss (doff + type_memory_bytes ce dt)
            (soff + type_memory_bytes ce st) d H tf z) ==>
    !dts sts doff soff a z.
      LENGTH dts = LENGTH sts /\
      compile_typed_copy_fields ce dst src dts sts doff soff a = ((),z) ==>
      cs_extends a z /\
      !G tn s. ~s.vs_halted /\ I dts sts doff soff a G tn s ==>
        ?H tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
          I [] [] (doff + SUM (MAP (type_memory_bytes ce) dts))
            (soff + SUM (MAP (type_memory_bytes ce) sts)) z H tf u
Proof
  rpt gen_tac >> disch_tac >> Induct_on `dts`
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >> conj_tac >- simp[cs_extends_def] >>
      rpt strip_tac >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> Cases_on `sts` >> simp[] >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed ce dp h sp h' sc = (u,sd)` >>
  Cases_on `u` >>
  qpat_x_assum `!sts doff soff a z. _` drule_all >> strip_tac >>
  qpat_x_assum `!dt ds st ss doff soff a b c d dp sp. _` drule_all >>
  disch_then (qspecl_then [`dts`, `t`] strip_assume_tac) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `~z'.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `!G tn s. _` drule_all >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H'`, `tf'`, `u`] >>
  metis_tac[ADD_ASSOC, ADD_COMM]
QED

(* The actual struct path has identical annotations.  Keeping the full lookup
   table fixed while traversing a suffix exposes exactly the required child. *)
Theorem intcall_struct_fields_counted_traversal:
  !D ctx fn PG ce dst src fields I.
    (!nm ty sz rest doff soff a b c d dp sp.
      ALOOKUP fields nm = SOME (ty,sz) /\
      compile_with_byte_offset dst doff a = (dp,b) /\
      compile_with_byte_offset src soff b = (sp,c) /\
      compile_store_memory_typed ce dp ty sp ty c = ((),d) ==>
      cs_extends a d /\
      !G tn s. ~s.vs_halted /\ I ((nm,ty,sz)::rest) doff soff a G tn s ==>
        ?H tf z. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
          I rest (doff + sz) (soff + sz) d H tf z) ==>
    !fs doff soff a z.
      (!nm ty sz. MEM (nm,ty,sz) fs ==> ALOOKUP fields nm = SOME (ty,sz)) /\
      compile_struct_typed_copy ce dst src fs fields doff soff a = ((),z) ==>
      cs_extends a z /\
      !G tn s. ~s.vs_halted /\ I fs doff soff a G tn s ==>
        ?H tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
          I [] (doff + SUM (MAP (\(nm,ty,sz). sz) fs))
            (soff + SUM (MAP (\(nm,ty,sz). sz) fs)) z H tf u
Proof
  rpt gen_tac >> disch_tac >> Induct_on `fs`
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >> conj_tac >- simp[cs_extends_def] >>
      rpt strip_tac >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `ALOOKUP fields h0 = SOME (h1,h2)` by metis_tac[MEM] >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed ce dp h1 sp h1 sc = (u,sd)` >>
  Cases_on `u` >>
  `!nm ty sz. MEM (nm,ty,sz) fs ==> ALOOKUP fields nm = SOME (ty,sz)`
    by metis_tac[MEM] >>
  qpat_x_assum `!doff soff a z.
    (_ /\ compile_struct_typed_copy _ _ _ fs _ _ _ _ = _) ==> _`
    drule_all >> strip_tac >>
  qpat_x_assum `!nm ty sz rest doff soff a b c d dp sp. _` drule_all >>
  disch_then (qspec_then `fs` strip_assume_tac) >>
  `h2 + soff = soff + h2` by decide_tac >> fs[] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `~z'.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `!G tn s. _` drule_all >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H'`, `tf'`, `u`] >>
  metis_tac[ADD_ASSOC, ADD_COMM]
QED
