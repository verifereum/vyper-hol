(* Zero-layout elements cannot select a counted dynamic copy. *)
Theory typedCopyFixedArrayCountBoundPtr
Ancestors
 typedMemoryCopy typedCopyDomain compileEnv loweringStateRelDefs
 vyperTypeExprSoundness vyperTypeSystem vyperValue vyperTypeABI
 valueEncodingProps valueEncodingDefs vfmConstants finite_map words list arithmetic pair

Theorem evaluated_zero_bytes_submap_static[local]:
 !cenv ty tenv tv sub.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name flds. FLOOKUP cenv.ce_struct_fields name = SOME flds ==>
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) flds) /\
 evaluate_type tenv ty = SOME tv /\ type_memory_bytes cenv ty = 0 /\
 sub SUBMAP cenv.ce_struct_fields ==>
 ~is_abi_dynamic sub ty
Proof
 gen_tac >> measureInduct_on `type_rank cenv.ce_struct_fields ty` >>
 rpt strip_tac >> Cases_on `ty`
 >- (Cases_on `b` >> gvs[is_abi_dynamic_def, type_memory_bytes_def] >>
     Cases_on `b'` >> gvs[is_abi_dynamic_def, type_memory_bytes_def, word_size_def])
 >- (rename1 `TupleT tys` >>
     gvs[is_abi_dynamic_def, EXISTS_MEM, type_memory_bytes_def,
         SUM_eq_0, MEM_MAP] >>
     rename1 `MEM elem tys` >>
     `?ctv. evaluate_type tenv elem = SOME ctv` by
       (gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP,
            vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MEM, MEM_MAP] >>
        metis_tac[optionTheory.IS_SOME_EXISTS]) >>
     `type_memory_bytes cenv elem = 0` by metis_tac[] >>
     `type_rank cenv.ce_struct_fields elem < type_rank cenv.ce_struct_fields (TupleT tys)` by
       metis_tac[member_rank_lt_tuple] >>
     first_x_assum drule >> disch_then (qspecl_then [`tenv`,`ctv`,`sub`] mp_tac) >>
     simp[] >> metis_tac[])
 >- (rename1 `ArrayT elem bd` >>
     `type_memory_bytes cenv (ArrayT elem bd) = type_memory_size tv` by
       (irule typed_copy_memory_size >> metis_tac[]) >>
     gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_slots] >>
     Cases_on `bd` >> gvs[type_slot_size_def, vyperASTTheory.bound_length_def])
 >- (rename1 `StructT nsid` >>
     Cases_on `FLOOKUP sub (nsid_to_string nsid)` >>
     gvs[is_abi_dynamic_def, EXISTS_MEM, MEM_MAP] >>
     rename1 `FLOOKUP sub (nsid_to_string nsid) = SOME flds` >>
     rename1 `MEM fld flds` >> PairCases_on `fld` >> gvs[] >>
     `FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME flds` by
       metis_tac[FLOOKUP_SUBMAP] >>
     `fld2 = 0` by
       (gvs[type_memory_bytes_def, get_struct_fields_def, SUM_eq_0, MEM_MAP] >>
        first_x_assum irule >> qexists_tac `(fld0,fld1,fld2)` >> simp[]) >>
     gvs[evaluate_type_def, AllCaseEqs()] >>
     `MEM fld1 (MAP SND args)` by
       (qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
        simp[sfields_tenv_consistent_def] >> strip_tac >>
        qpat_x_assum `!nid args. FLOOKUP tenv nid = SOME (StructArgs args) ==> _` drule >>
        strip_tac >> gvs[] >>
        qpat_x_assum `MAP (FST o SND) _ = MAP SND args` (fn th => rewrite_tac[GSYM th]) >>
        simp[MEM_MAP] >> qexists_tac `(fld0,fld1,0)` >> simp[]) >>
     `?ctv. evaluate_type (tenv \\ nsid) fld1 = SOME ctv` by
       (gvs[evaluate_types_OPT_MMAP, vyperMiscTheory.OPT_MMAP_SOME_IFF,
            EVERY_MEM, MEM_MAP] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
     `evaluate_type tenv fld1 = SOME ctv` by
       metis_tac[cj 1 evaluate_type_mono] >>
     `type_memory_size ctv = 0` by
       (qpat_x_assum `!name flds. _ ==> EVERY _ _` drule >>
        simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
     `type_memory_bytes cenv fld1 = 0` by
       (drule_all typed_copy_memory_size >> simp[]) >>
     `type_rank cenv.ce_struct_fields fld1 < type_rank cenv.ce_struct_fields (StructT nsid)` by
       (once_rewrite_tac[type_rank_nsid] >> irule member_rank_lt_struct >>
        simp[get_struct_fields_def] >> metis_tac[]) >>
     qpat_x_assum `!y. type_rank _ y < _ ==> _` drule >>
     disch_then (qspecl_then [`tenv`,`ctv`,`sub \\ nsid_to_string nsid`] mp_tac) >>
     simp[] >> metis_tac[SUBMAP_TRANS, SUBMAP_DOMSUB])
 >- gvs[is_abi_dynamic_def]
 >> gvs[is_abi_dynamic_def]
QED

Theorem typed_copy_sarray_slow_count_bound:
 !cenv tenv dty sty dtv N (a:bytes32) (b:bytes32).
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) fields) /\
 evaluate_type tenv dty = SOME dtv /\
 ~(type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
   ~is_abi_dynamic cenv.ce_struct_fields dty) /\
 w2n a + N * type_memory_bytes cenv sty < dimword(:256) /\
 w2n b + N * type_memory_bytes cenv dty < dimword(:256) ==>
 N < dimword(:256)
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `type_memory_bytes cenv dty = 0`
 >- (`~is_abi_dynamic cenv.ce_struct_fields dty` by
       (irule evaluated_zero_bytes_submap_static >>
        qexistsl_tac [`cenv`,`tenv`,`dtv`] >> simp[] >> metis_tac[]) >>
     `type_memory_bytes cenv sty <> 0` by metis_tac[] >>
     `N <= N * type_memory_bytes cenv sty` by
       (Cases_on `type_memory_bytes cenv sty` >> gvs[MULT_CLAUSES]) >>
     decide_tac) >>
 `N <= N * type_memory_bytes cenv dty` by
   (Cases_on `type_memory_bytes cenv dty` >> gvs[MULT_CLAUSES]) >>
 decide_tac
QED
