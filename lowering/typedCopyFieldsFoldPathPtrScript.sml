(* Paired field traversal over actual counted paths.  The invariant is
   deliberately abstract; semantic constructors discharge the head rule. *)
Theory typedCopyFieldsFoldPathPtr
Ancestors
 placeMemoryFieldsForward fragGasPathPtr context compileEnv emitHelper
 exprLoweringProps fragExec list arithmetic

Theorem compile_typed_copy_fields_path_invariant:
 !D ctx func PG cenv dst src I.
 (!dt ds st ss doff soff a b c d dp sp G tn s.
   LENGTH ds = LENGTH ss /\
   compile_with_byte_offset dst doff a = (dp,b) /\
   compile_with_byte_offset src soff b = (sp,c) /\
   compile_store_memory_typed cenv dp dt sp st c = ((),d) /\
   fn_has_code a d func /\
   s.vs_current_bb = a.cs_current_bb /\
   s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
   I (dt::ds) (st::ss) doff soff a G tn s ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = d.cs_current_bb /\
   sf.vs_inst_idx = LENGTH d.cs_current_insts /\ ~sf.vs_halted /\
   I ds ss (doff + type_memory_bytes cenv dt)
     (soff + type_memory_bytes cenv st) d Gf tnf sf) ==>
 !dts sts doff soff a z G tn s.
 LENGTH dts = LENGTH sts /\
 compile_typed_copy_fields cenv dst src dts sts doff soff a = ((),z) /\
 fn_has_code a z func /\
 s.vs_current_bb = a.cs_current_bb /\
 s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
 I dts sts doff soff a G tn s ==>
 cs_extends a z /\
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = z.cs_current_bb /\
 sf.vs_inst_idx = LENGTH z.cs_current_insts /\ ~sf.vs_halted /\
 I [] [] (doff + SUM (MAP (type_memory_bytes cenv) dts))
         (soff + SUM (MAP (type_memory_bytes cenv) sts)) z Gf tnf sf
Proof
 rpt gen_tac >> disch_tac >> Induct_on `dts`
 >- (Cases_on `sts` >> simp[] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, comp_return_def] >>
     strip_tac >> gvs[] >> conj_tac >- simp[cs_extends_def] >>
     qexistsl [`G`,`tn`,`s`] >> simp[] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
 rpt gen_tac >> Cases_on `sts` >> simp[] >> strip_tac >>
 drule typed_memory_fields_cons_compile >> strip_tac >>
 `cs_extends a c` by metis_tac[cs_extends_trans] >>
 `fn_has_code a c func /\ fn_has_code c z func` by
   metis_tac[fn_has_code_split] >>
 qpat_x_assum `!dt ds st ss doff soff a b c d dp sp G tn s. _`
   drule_all >> strip_tac >>
 qpat_x_assum `!sts doff soff a z G tn s. _` drule_all >> strip_tac >>
 conj_tac >- metis_tac[cs_extends_trans] >>
 qexistsl [`Gf'`,`tnf'`,`sf'`] >>
 conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
 gvs[]
QED
