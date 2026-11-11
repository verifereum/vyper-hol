(* Tuple constructor for counted robust typed copying. *)
Theory typedCopyTuplePathPtr
Ancestors
 typedCopyFieldsPathPtr typedMemoryCopy typedCopyPtr bodyPtrDefs
 context compileEnv exprLoweringProps fragExec abiEncoderInput
 vyperTypeSystem vyperValue vyperTyping valueEncodingProofs
 vyperTypeABI vyperTypeDefaults valueEncodingDefs valueEncoding
 typedCopyTuplePtr tupleMemoryLayout structFieldsProps
 venomState finite_map words list arithmetic

Theorem compile_store_memory_typed_tuple_robust_path_ptr:
 !D ctx func PG cenv tenv dts sts.
 (!dt st. MEM (dt,st) (ZIP (dts,sts)) ==>
  !cd cs sa sb Gh th sh aw bw dtv stv v.
   acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields tenv /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv st dt /\ evaluate_type tenv st = SOME stv /\
   evaluate_type tenv dt = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed cenv (Var cd) dt (Var cs) st sa = ((),sb) /\
   not_fresh_at sa cd /\ not_fresh_at sa cs /\
   lookup_var cs sh = SOME aw /\ lookup_var cd sh = SOME bw /\
   ptr_covers Gh th cs sh (type_memory_bytes cenv st) /\
   ptr_covers Gh th cd sh (type_memory_bytes cenv dt) /\
   w2n aw + type_memory_bytes cenv st < dimword(:256) /\
   w2n bw + type_memory_bytes cenv dt < dimword(:256) /\
   (w2n aw + type_memory_bytes cenv st <= w2n bw \/
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
 type_widens_to tenv (TupleT sts) (TupleT dts) /\
 evaluate_type tenv (TupleT sts) = SOME stv /\
 evaluate_type tenv (TupleT dts) = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
 compile_store_memory_typed cenv (Var dst) (TupleT dts) (Var src) (TupleT sts) sa = ((),sb) /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (type_memory_bytes cenv (TupleT sts)) /\
 ptr_covers G tn dst s (type_memory_bytes cenv (TupleT dts)) /\
 w2n a + type_memory_bytes cenv (TupleT sts) < dimword(:256) /\
 w2n b + type_memory_bytes cenv (TupleT dts) < dimword(:256) /\
 (w2n a + type_memory_bytes cenv (TupleT sts) <= w2n b \/
  w2n b + type_memory_bytes cenv (TupleT dts) <= w2n a) /\
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
 (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes cenv (TupleT dts)) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory dtv v (w2n b) m)
Proof
 ntac 8 gen_tac >> disch_then (mk_asm "children") >>
 rpt gen_tac >> strip_tac >>
 gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
 `LIST_REL (type_widens_to tenv) sts dts` by
   (irule typed_copy_tuple_children_widen >>
    (conj_tac >- metis_tac[]) >>
    drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
 Cases_on `v` >> gvs[value_has_type_def] >>
 rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
 (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
 simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def] >>
 strip_tac >>
 `!ty tv. evaluate_type tenv ty = SOME tv ==>
   type_memory_bytes cenv ty = type_memory_size tv` by
   (rpt strip_tac >> irule typed_copy_memory_size >>
    qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
 `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) dts tvs' /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) sts tvs` by
   metis_tac[OPT_MMAP_LIST_REL] >>
 `LENGTH sts = LENGTH dts /\ LENGTH tvs = LENGTH dts /\
  LENGTH tvs' = LENGTH dts /\ LENGTH l = LENGTH dts` by
   (fs[LIST_REL_EL_EQN] >> metis_tac[values_have_types_length]) >>
 `MAP (type_memory_bytes cenv) dts = MAP type_memory_size tvs' /\
  MAP (type_memory_bytes cenv) sts = MAP type_memory_size tvs` by
   (qpat_x_assum `children :- _` kall_tac >>
    conj_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
    fs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
 `!i. i < LENGTH dts ==>
   type_widens_to tenv (EL i sts) (EL i dts) /\
   evaluate_type tenv (EL i sts) = SOME (EL i tvs) /\
   evaluate_type tenv (EL i dts) = SOME (EL i tvs') /\
   value_has_type (EL i tvs) (EL i l) /\
   value_has_type (EL i tvs') (EL i l) /\
   val_wf (EL i tvs) (EL i l) /\ val_wf (EL i tvs') (EL i l)` by
   (fs[LIST_REL_EL_EQN, values_have_types_LIST_REL] >>
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
 `!i. i < LENGTH dts ==> !m.
   mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (EL i tvs) (EL i l)
     (w2n a + 0 + SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) m` by
   (rpt strip_tac >>
    `SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) =
     SUM (MAP type_memory_size (TAKE i tvs))` by
      metis_tac[MAP_TAKE] >>
    qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` drule >>
    simp_tac (srw_ss()) [val_in_memory_def] >> strip_tac >>
    qpat_x_assum `children :- _` kall_tac >>
    metis_tac[tuple_in_memory_element, ADD_0]) >>
 qspecl_then [`D`,`ctx`,`func`,`PG`] mp_tac compile_typed_copy_fields_robust_path_ptr >>
 disch_then (qspecl_then [`cenv`,`tenv`,`dst`,`src`] mp_tac) >>
 disch_then (qspecl_then [`type_memory_bytes cenv (TupleT dts)`,
  `type_memory_bytes cenv (TupleT sts)`,`b`,`a`] mp_tac) >>
 disch_then (qspecl_then [`dts`,`sts`,`tvs'`,`tvs`] mp_tac) >>
 disch_then (qspec_then `l` mp_tac) >>
 disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
 disch_then (qspecl_then [`G`,`tn`,`s`] mp_tac) >>
 (impl_tac >- (
   ntac 8 (conj_tac >- (first_assum MATCH_ACCEPT_TAC)) >>
   (conj_tac >- asm "children" MATCH_ACCEPT_TAC) >>
   simp[type_memory_bytes_def] >>
   qpat_x_assum `children :- _` kall_tac >>
   fs[ETA_THM, type_memory_bytes_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])) >> strip_tac >>
 qexistsl [`Gf`,`tnf`,`sf`] >>
 qpat_x_assum `children :- _` kall_tac >>
 fs[val_in_memory_def, type_memory_bytes_def] >>
 CONV_TAC (DEPTH_CONV ETA_CONV) >>
 rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> fs[] >>
 (conj_tac >- metis_tac[]) >>
 (conj_tac >- metis_tac[]) >>
 rpt strip_tac >> irule tuple_in_memory_from_elements >>
 simp[] >> rpt strip_tac >>
 `SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) =
  SUM (MAP type_memory_size (TAKE i tvs'))` by metis_tac[MAP_TAKE] >>
 metis_tac[ADD_0])
QED
