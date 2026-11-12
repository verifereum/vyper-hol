(* Counted robust typed copying for identical-name structs. *)
Theory typedCopyStructPathPtr
Ancestors
 typedCopyFieldsPathPtr typedMemoryCopy typedNormalizeStructMetadata
 placeMemoryTypedBase context compileEnv exprLoweringProps fragExec abiEncoderInput
 vyperTypeSystem vyperValue vyperTyping valueEncodingProofs
 vyperTypeABI vyperTypeDefaults valueEncodingDefs valueEncoding
 typedCopyTuplePtr tupleMemoryLayout structFieldsProps
 venomState finite_map words list arithmetic alist

Theorem compile_store_memory_typed_struct_robust_path_ptr:
 !D ctx func PG cenv tenv name.
 (!dt. MEM dt (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string name))) ==>
  !cd cs sa sb Gh th sh aw bw dtv stv v.
   acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields tenv /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv dt dt /\ evaluate_type tenv dt = SOME stv /\
   evaluate_type tenv dt = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed cenv (Var cd) dt (Var cs) dt sa = ((),sb) /\
   not_fresh_at sa cd /\ not_fresh_at sa cs /\
   lookup_var cs sh = SOME aw /\ lookup_var cd sh = SOME bw /\
   ptr_covers Gh th cs sh (type_memory_bytes cenv dt) /\
   ptr_covers Gh th cd sh (type_memory_bytes cenv dt) /\
   w2n aw + type_memory_bytes cenv dt < dimword(:256) /\
   w2n bw + type_memory_bytes cenv dt < dimword(:256) /\
   (w2n aw + type_memory_bytes cenv dt <= w2n bw \/
    w2n bw + type_memory_bytes cenv dt <= w2n aw) /\
   fn_has_code sa sb func /\ sh.vs_current_bb = sa.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sh.vs_halted /\
   ~ctx_has_dalloca ctx /\
   (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx func PG Gh th sh 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := sh.vs_vars; vs_memory := sh.vs_memory;
    vs_prev_bb := sh.vs_prev_bb; vs_current_bb := sh.vs_current_bb;
    vs_inst_idx := sh.vs_inst_idx|>) = sh /\
   tnf.t_stor = th.t_stor /\ tnf.t_trans = th.t_trans /\ tnf.t_imm = th.t_imm /\
   (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p sh /\ FLOOKUP Gf p = FLOOKUP Gh p /\
    op_taint tnf (Var p) = op_taint th (Var p)) /\
   (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_bytes cenv dt) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 sh.vs_memory /\
    (i IN tnf.t_mem <=> i IN th.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n bw) m)) ==>
 !dst src sa sb G tn s a b dtv stv v.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) fields) /\
 type_widens_to tenv (StructT name) (StructT name) /\
 evaluate_type tenv (StructT name) = SOME stv /\
 evaluate_type tenv (StructT name) = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
 compile_store_memory_typed cenv (Var dst) (StructT name) (Var src) (StructT name) sa = ((),sb) /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (type_memory_bytes cenv (StructT name)) /\
 ptr_covers G tn dst s (type_memory_bytes cenv (StructT name)) /\
 w2n a + type_memory_bytes cenv (StructT name) < dimword(:256) /\
 w2n b + type_memory_bytes cenv (StructT name) < dimword(:256) /\
 (w2n a + type_memory_bytes cenv (StructT name) <= w2n b \/
  w2n b + type_memory_bytes cenv (StructT name) <= w2n a) /\
 fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory stv v (w2n a) m) ==>
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
 (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes cenv (StructT name)) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory dtv v (w2n b) m)
Proof
 ntac 7 gen_tac >> disch_then (mk_asm "children") >>
 rpt gen_tac >> strip_tac >>
 drule_all normalize_struct_metadata >> strip_tac >> gvs[] >>
 (`EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
   (simp[EVERY_MEM] >> rpt gen_tac >> PairCases_on `e` >> simp[] >> metis_tac[]) >>
 qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
 simp[Once compile_store_memory_typed_def, is_word_type_def,
   is_bytestring_type_def, get_struct_fields_def] >>
 `compile_struct_typed_copy cenv (Var dst) (Var src) fields fields 0 0 =
  compile_typed_copy_fields cenv (Var dst) (Var src)
   (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
   (irule typed_memory_struct_copy_fields >> simp[EVERY_MEM]) >>
 simp[] >> strip_tac >>
 `MAP (type_memory_bytes cenv) (MAP (FST o SND) fields) =
  MAP type_memory_size tvs` by
  (qpat_x_assum `children :- _` kall_tac >>
   irule LIST_EQ >> fs[LIST_REL_EL_EQN, EL_MAP]) >>
 `MAP (SND o SND) fields = MAP type_memory_size tvs` by
  (qpat_x_assum `children :- _` kall_tac >>
   qpat_x_assum `MAP (type_memory_bytes cenv) _ = _` (SUBST1_TAC o SYM) >>
   simp[MAP_MAP_o] >> irule MAP_CONG >> simp[] >>
   rpt gen_tac >> PairCases_on `x` >> simp[] >> metis_tac[]) >>
 `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
   (MAP (FST o SND) fields) tvs` by metis_tac[OPT_MMAP_LIST_REL] >>
 `!i. i < LENGTH fields ==>
   type_widens_to tenv (EL i (MAP (FST o SND) fields)) (EL i (MAP (FST o SND) fields)) /\
   evaluate_type tenv (EL i (MAP (FST o SND) fields)) = SOME (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs)` by
  (qpat_x_assum `children :- _` kall_tac >>
   fs[LIST_REL_EL_EQN, values_have_types_LIST_REL, type_widens_to_def]) >>
 `!i. i < LENGTH fields ==> !m.
   mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (EL i tvs) (EL i vs)
    (w2n a + 0 + SUM (MAP (type_memory_bytes cenv) (TAKE i (MAP (FST o SND) fields)))) m` by
  (rpt strip_tac >>
   `SUM (MAP (type_memory_bytes cenv) (TAKE i (MAP (FST o SND) fields))) =
    SUM (MAP type_memory_size (TAKE i tvs))` by metis_tac[MAP_TAKE] >>
   qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` drule >>
   simp_tac (srw_ss()) [val_in_memory_def] >>
   simp[typed_copy_fields_tuple_zip] >> strip_tac >>
   qpat_x_assum `children :- _` kall_tac >>
   metis_tac[tuple_in_memory_element, ADD_COMM]) >>
 qspecl_then [`D`,`ctx`,`func`,`PG`] mp_tac compile_typed_copy_fields_robust_path_ptr >>
 disch_then (qspecl_then [`cenv`,`tenv`,`dst`,`src`] mp_tac) >>
 disch_then (qspecl_then [`type_memory_bytes cenv (StructT name)`,
   `type_memory_bytes cenv (StructT name)`,`b`,`a`] mp_tac) >>
 disch_then (qspecl_then [`MAP (FST o SND) fields`,`MAP (FST o SND) fields`,`tvs`,`tvs`] mp_tac) >>
 disch_then (qspec_then `vs` mp_tac) >>
 disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
 disch_then (qspecl_then [`G`,`tn`,`s`] mp_tac) >>
 (impl_tac >- (
   ntac 4 (conj_tac >- simp[]) >>
   ntac 3 (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
   (conj_tac >- (rpt strip_tac >> fs[])) >>
   (conj_tac >- (
    rpt gen_tac >> strip_tac >>
    `dt = st /\ MEM dt (MAP (FST o SND) fields)` by
      gvs[MEM_ZIP, EL_MEM] >> gvs[] >>
    asm "children" (qspec_then `dt` mp_tac) >>
    simp[get_struct_fields_def])) >>
   qpat_x_assum `children :- _` kall_tac >>
   simp[type_memory_bytes_def, get_struct_fields_def] >>
   fs[type_memory_bytes_def, get_struct_fields_def] >> decide_tac)) >> strip_tac >>
 qexistsl [`Gf`,`tnf`,`sf`] >> qpat_x_assum `children :- _` kall_tac >>
 fs[val_in_memory_def, type_memory_bytes_def, get_struct_fields_def] >>
 (conj_tac >- metis_tac[]) >>
 (conj_tac >- metis_tac[]) >>
 rpt strip_tac >> simp[typed_copy_fields_tuple_zip] >>
 irule tuple_in_memory_from_elements >> simp[] >> rpt strip_tac >>
 `SUM (MAP (type_memory_bytes cenv) (TAKE i (MAP (FST o SND) fields))) =
  SUM (MAP type_memory_size (TAKE i tvs))` by metis_tac[MAP_TAKE] >>
 metis_tac[ADD_COMM, ADD_0])
QED
