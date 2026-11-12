(* Static-layout fixed arrays use the robust counted flat-copy boundary. *)
Theory typedCopyFixedArrayFastPathPtr
Ancestors
 typedCopyFlatPathPtr typedMemoryCopy exprSimProps bodyPtrDefs
 context compileEnv fragExec valueEncoding valueEncodingDefs valueEncodingProofs
 vyperTypeSystem vyperValue venomState ptrDiscipline finite_map words arithmetic

Theorem compile_copy_sarray_typed_fast_robust_path_ptr:
 !D ctx func PG cenv tenv dty sty N dst src sa sb G tn s a b dtv stv v.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
   sz = type_memory_size tv) fields) /\
 type_widens_to tenv sty dty /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
 ~is_abi_dynamic cenv.ce_struct_fields dty /\
 val_wf (ArrayTV stv (Fixed N)) v /\ val_wf (ArrayTV dtv (Fixed N)) v /\
 compile_copy_sarray_typed cenv (Var dst) dty (Var src) sty N sa = ((),sb) /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (N * type_memory_bytes cenv sty) /\
 ptr_covers G tn dst s (N * type_memory_bytes cenv dty) /\
 w2n a + N * type_memory_bytes cenv sty < dimword(:256) /\
 w2n b + N * type_memory_bytes cenv dty < dimword(:256) /\
 (w2n a + N * type_memory_bytes cenv sty <= w2n b \/
  w2n b + N * type_memory_bytes cenv dty <= w2n a) /\
 fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
  val_in_memory (ArrayTV stv (Fixed N)) v (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b + N * type_memory_bytes cenv dty) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory (ArrayTV dtv (Fixed N)) v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 `stv = dtv` by metis_tac[typed_copy_static_widening] >> gvs[] >>
 `type_memory_bytes cenv dty = type_memory_size dtv` by
  (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
 `compile_copy_memory (Var dst) (Var src) (N * type_memory_bytes cenv dty) sa = ((),sb)` by
  (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
   simp[Once compile_store_memory_typed_def]) >>
 `N * type_memory_bytes cenv dty < dimword(:256)` by (fs[] >> decide_tac) >>
 `val_footprint (ArrayTV dtv (Fixed N)) v <= N * type_memory_bytes cenv dty` by
  metis_tac[val_footprint_le, type_memory_size_def] >>
 drule compile_copy_memory_robust_path_ptr >>
 disch_then (qspecl_then [`D`,`ctx`,`func`,`PG`,`G`,`tn`,`s`,`a`,`b`,
   `ArrayTV dtv (Fixed N)`,`v`] mp_tac) >>
 (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
 qexistsl [`G`,`tnf`,`sf`] >> simp[] >>
 qpat_x_assum `sf with <|vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
 qpat_x_assum `tnf with t_mem := _ = tn` mp_tac >>
 simp[venom_state_component_equality, taint_component_equality,
      op_taint_def] >> strip_tac >> strip_tac >> simp[] >> metis_tac[]
QED
