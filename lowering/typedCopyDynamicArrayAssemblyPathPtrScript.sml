(* Diagnostic for the capacity-check interface used by dynamic assembly. *)
Theory typedCopyDynamicArrayAssemblyPathPtr
Ancestors typedCopyDynamicArrayPathPtr typedCopyDynamicSetupPathPtr
 typedCopyDynamicSlowPathPtr typedCopyDynamicFastPathPtr typedCopyIndexedTransportPtr
 typedCopyDynamicLayout typedCopyDynamicFastLayout typedCopyDynamicReconstructionPtr

Theorem dynamic_capacity_bound_diagnostic[local]:
 value_has_type (ArrayTV (TupleTV []) (Dynamic (2 ** 256)))
   (ArrayV (DynArrayV [ArrayV (TupleV [])])) /\
 val_wf (ArrayTV (TupleTV []) (Dynamic (2 ** 256)))
   (ArrayV (DynArrayV [ArrayV (TupleV [])])) /\
 32 + (2 ** 256) * type_memory_size (TupleTV []) < dimword(:256) /\
 ~(2 ** 256 < dimword(:256))
Proof
 simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
   valueEncodingTheory.type_memory_size_def, wordsTheory.dimword_def]
QED

Theorem compile_copy_dynarray_typed_robust_path_ptr:
 !D ctx fn PG ce tenv dty sty.
 (!cd cs sa sb Gh th sh aw bw dtv stv v.
   acyclic_struct_metadata ce.ce_struct_fields /\
   sfields_tenv_consistent ce.ce_struct_fields tenv /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
   evaluate_type tenv dty = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed ce (Var cd) dty (Var cs) sty sa = ((),sb) /\
   not_fresh_at sa cd /\ not_fresh_at sa cs /\
   lookup_var cs sh = SOME aw /\ lookup_var cd sh = SOME bw /\
   ptr_covers Gh th cs sh (type_memory_bytes ce sty) /\
   ptr_covers Gh th cd sh (type_memory_bytes ce dty) /\
   w2n aw + type_memory_bytes ce sty < dimword(:256) /\
   w2n bw + type_memory_bytes ce dty < dimword(:256) /\
   (w2n aw + type_memory_bytes ce sty <= w2n bw \/
    w2n bw + type_memory_bytes ce dty <= w2n aw) /\
   fn_has_code sa sb fn /\ sh.vs_current_bb = sa.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sh.vs_halted /\
   ~ctx_has_dalloca ctx /\
   (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx fn PG Gh th sh 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := sh.vs_vars; vs_memory := sh.vs_memory;
    vs_prev_bb := sh.vs_prev_bb; vs_current_bb := sh.vs_current_bb;
    vs_inst_idx := sh.vs_inst_idx|>) = sh /\
   tnf.t_stor = th.t_stor /\ tnf.t_trans = th.t_trans /\ tnf.t_imm = th.t_imm /\
   (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p sh /\ FLOOKUP Gf p = FLOOKUP Gh p /\
    op_taint tnf (Var p) = op_taint th (Var p)) /\
   (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_bytes ce dty) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 sh.vs_memory /\
    (i IN tnf.t_mem <=> i IN th.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n bw) m)) ==>
 !sa sz G tn s dst src a b stv dtv vs sc dc.
 acyclic_struct_metadata ce.ce_struct_fields /\
 sfields_tenv_consistent ce.ce_struct_fields tenv /\
 (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
   sz = type_memory_size tv) fields) /\
 type_widens_to tenv sty dty /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 value_has_type (ArrayTV stv (Dynamic sc)) (ArrayV (DynArrayV vs)) /\
 value_has_type (ArrayTV dtv (Dynamic dc)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV stv (Dynamic sc)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV dtv (Dynamic dc)) (ArrayV (DynArrayV vs)) /\
 dc < dimword(:256) /\
 compile_copy_dynarray_typed ce (Var dst) dty dc (Var src) sty sa = ((),sz) /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (32 + sc * type_memory_bytes ce sty) /\
 ptr_covers G tn dst s (32 + dc * type_memory_bytes ce dty) /\
 w2n a + 32 + sc * type_memory_bytes ce sty < dimword(:256) /\
 w2n b + 32 + dc * type_memory_bytes ce dty < dimword(:256) /\
 (w2n a + 32 + sc * type_memory_bytes ce sty <= w2n b \/
  w2n b + 32 + dc * type_memory_bytes ce dty <= w2n a) /\
 fn_has_code sa sz fn /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
  val_in_memory (ArrayTV stv (Dynamic sc)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sz.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b + 32 + dc * type_memory_bytes ce dty) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory (ArrayTV dtv (Dynamic dc)) (ArrayV (DynArrayV vs)) (w2n b) m)
Proof
 ntac 8 gen_tac >> disch_then (mk_asm "child") >> rpt gen_tac >> strip_tac >>
 `LENGTH vs <= sc /\ LENGTH vs <= dc /\
  EVERY (value_has_type stv) vs /\ EVERY (value_has_type dtv) vs /\
  EVERY (val_wf stv) vs /\ EVERY (val_wf dtv) vs` by
   gvs[vyperTypingTheory.value_has_type_def, vyperTypingTheory.all_have_type_EVERY,
       valueEncodingDefsTheory.val_wf_def,
       typedMemoryCopyTheory.typed_copy_elems_wf_indexed, listTheory.EVERY_EL] >>
 `LENGTH vs < dimword(:256)` by decide_tac >>
 drule compile_copy_dynarray_typed_layout >> strip_tac >>
 `fn_has_code sa s1 fn /\ fn_has_code s1 s7 fn /\ fn_has_code s7 sz fn` by metis_tac[] >>
 `ptr_covers G tn src s 32` by
   (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
 drule_all typed_copy_dynarray_length_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t1)` >>
 `lookup_var src t1 = SOME a /\ lookup_var dst t1 = SOME b /\
  ptr_covers G1 tn1 src t1 (32 + sc * type_memory_bytes ce sty) /\
  ptr_covers G1 tn1 dst t1 (32 + dc * type_memory_bytes ce dty)` by
   metis_tac[annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr] >>
 `not_fresh_at s1 src /\ not_fresh_at s1 dst` by metis_tac[] >>
 `emit_inst ASSERT [Var ok] [] s3 = ((),s4) /\
  emit_inst MSTORE [Var dst;Var len] [] s4 = ((),s5)` by
   fs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
 drule_all typed_copy_dynarray_setup_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 t1 0 G2 tn2 (OK t2)` >>
 `type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv` by
   (conj_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
    qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
 `t1.vs_memory = s.vs_memory` by
   simp[venomStateTheory.update_var_def] >>
 `!j. j < LENGTH vs ==> !m. mem_agree_outside tn1.t_mem t1.vs_memory m ==>
   val_in_memory stv (EL j vs) (w2n a + 32 + j * type_memory_size stv) m` by
   (rpt strip_tac >>
    `mem_agree_outside tn.t_mem s.vs_memory m` by metis_tac[] >>
    qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` drule >>
    simp[valueEncodingDefsTheory.val_in_memory_def] >>
    strip_tac >>
    drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
    metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
 `!j. j < LENGTH vs ==> !m. mem_agree_outside tn2.t_mem t2.vs_memory m ==>
   val_in_memory stv (EL j vs) (w2n a + 32 + j * type_memory_bytes ce sty) m` by
   (rpt strip_tac >>
    irule typedCopyRobustTransportPtrTheory.robust_representation_exterior_frame >>
    (conj_tac >- metis_tac[listTheory.EVERY_EL]) >>
    qexistsl_tac [`w2n b`,`t1.vs_memory`,`t2.vs_memory`,`32`,`tn1.t_mem`,`tn2.t_mem`] >>
    `j * type_memory_size stv + type_memory_size stv <= sc * type_memory_size stv` by
     (`j+1 <= sc` by decide_tac >>
      qspecl_then [`j+1`,`sc`,`type_memory_size stv`] mp_tac
        arithmeticTheory.LESS_MONO_MULT >>
      pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
        arithmeticTheory.MULT_RIGHT_1] >>
      disch_then (fn th => mp_tac th) >> decide_tac) >>
    (conj_tac >- metis_tac[]) >>
    (conj_tac >- (rpt strip_tac >>
      `i < w2n b \/ w2n b + 32 <= i` by decide_tac >> metis_tac[])) >>
    (conj_tac >- (rpt strip_tac >>
      `i < w2n b \/ w2n b + 32 <= i` by decide_tac >> metis_tac[])) >>
    (conj_tac >-
      (qpat_x_assum `j * _ + _ <= sc * _` mp_tac >>
       qpat_x_assum `_ + 32 + _ <= _` mp_tac >>
       simp[] >> decide_tac)) >>
    first_assum ACCEPT_TAC) >>
 `w2n (n2w (w2n a+32):bytes32) = w2n a+32 /\
  w2n (n2w (w2n b+32):bytes32) = w2n b+32` by
   (conj_tac >> simp[wordsTheory.w2n_n2w] >> decide_tac) >>
 `w2n a+32+sc*type_memory_bytes ce sty <= w2n b+32 \/
  w2n b+32+dc*type_memory_bytes ce dty <= w2n a+32` by decide_tac >>
 `?G3 tn3 t3.
  gas_path_ptr D 0 ctx fn PG G2 tn2 t2 0 G3 tn3 (OK t3) /\
  t3.vs_current_bb = sz.cs_current_bb /\
  t3.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~t3.vs_halted /\
  (t3 with <|vs_vars := t2.vs_vars; vs_memory := t2.vs_memory;
    vs_prev_bb := t2.vs_prev_bb; vs_current_bb := t2.vs_current_bb;
    vs_inst_idx := t2.vs_inst_idx|>) = t2 /\
  tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
  (!p. not_fresh_at s7 p ==> lookup_var p t3 = lookup_var p t2 /\
    FLOOKUP G3 p = FLOOKUP G2 p /\ op_taint tn3 (Var p) = op_taint tn2 (Var p)) /\
  (!i. ~(w2n b+32 <= i /\ i < w2n b+32+dc*type_memory_bytes ce dty) ==>
    mem_bytes_at i 1 t3.vs_memory = mem_bytes_at i 1 t2.vs_memory /\
    (i IN tn3.t_mem <=> i IN tn2.t_mem)) /\
  (!j. j < LENGTH vs ==> !m. mem_agree_outside tn3.t_mem t3.vs_memory m ==>
    val_in_memory dtv (EL j vs) (w2n b+32+j*type_memory_bytes ce dty) m)` by
  (Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty`
   >- (`dty = sty` by metis_tac[] >>
       qpat_x_assum `dty = sty` SUBST_ALL_TAC >>
       `dtv = stv` by
        (qpat_x_assum `evaluate_type tenv sty = SOME dtv` mp_tac >> simp[]) >>
       qpat_x_assum `dtv = stv` SUBST_ALL_TAC >>
       qpat_x_assum `(if _ then _ else _) s7 = _` mp_tac >>
       simp[NoAsms] >> strip_tac >>
       drule compile_copy_dynarray_fast_tail_layout >> strip_tac >>
       `w2n (n2w (w2n a+32):bytes32) + sc*type_memory_size stv < dimword(:256) /\
        w2n (n2w (w2n b+32):bytes32) + dc*type_memory_size stv < dimword(:256)` by
         gvs[] >>
       `!j. j < LENGTH vs ==> !m. mem_agree_outside tn2.t_mem t2.vs_memory m ==>
         val_in_memory stv (EL j vs)
           (w2n (n2w (w2n a+32):bytes32)+j*type_memory_size stv) m` by
         (simp[] >> (bossLib.gvs [])) >>
       `type_memory_size stv = type_memory_bytes ce sty` by metis_tac[] >>
       `w2n (n2w (w2n a+32):bytes32) + sc*type_memory_bytes ce sty < dimword(:256) /\
        w2n (n2w (w2n b+32):bytes32) + dc*type_memory_bytes ce sty < dimword(:256) /\
        (w2n (n2w (w2n a+32):bytes32) + sc*type_memory_bytes ce sty <=
          w2n (n2w (w2n b+32):bytes32) \/
         w2n (n2w (w2n b+32):bytes32) + dc*type_memory_bytes ce sty <=
          w2n (n2w (w2n a+32):bytes32))` by
         (qpat_x_assum `w2n (n2w (w2n a+32):bytes32) = _` mp_tac >>
          qpat_x_assum `w2n (n2w (w2n b+32):bytes32) = _` mp_tac >>
          qpat_x_assum `w2n a + 32 + sc * _ < _` mp_tac >>
          qpat_x_assum `w2n b + 32 + dc * _ < _` mp_tac >>
          FIRST [qpat_x_assum `w2n a + 32 + sc * _ <= w2n b` mp_tac,
                 qpat_x_assum `w2n b + 32 + dc * _ <= w2n a` mp_tac] >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
       `!j. j < LENGTH vs ==> !m. mem_agree_outside tn2.t_mem t2.vs_memory m ==>
         val_in_memory stv (EL j vs)
           (w2n (n2w (w2n a+32):bytes32)+j*type_memory_bytes ce sty) m` by
         metis_tac[] >>
       (Q.SUBGOAL_THEN
         `w2n (n2w (w2n a+32):bytes32) + sc*type_memory_bytes ce sty <=
             w2n (n2w (w2n b+32):bytes32) \/
           w2n (n2w (w2n b+32):bytes32) + dc*type_memory_bytes ce sty <=
             w2n (n2w (w2n a+32):bytes32)` assume_tac
       >- metis_tac[]) >>
       drule_all typed_copy_dynarray_fast_tail_path_ptr >>
       disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
       qexistsl [`Gf`,`tnf`,`sf`] >>
       qpat_x_assum `type_memory_size stv = type_memory_bytes ce sty` kall_tac >>
       gvs[] >> metis_tac[]) >>
   qpat_x_assum `(if _ then _ else _) s7 = _` mp_tac >>
   simp[NoAsms] >> strip_tac >>
   assume_tac indexed_robust_copy_step >>
   asm "child" assume_tac >>
   `!j. j < LENGTH vs ==> value_has_type stv (EL j vs) /\
     value_has_type dtv (EL j vs) /\ val_wf stv (EL j vs) /\ val_wf dtv (EL j vs)` by
     metis_tac[listTheory.EVERY_EL] >>
   (Q.SUBGOAL_THEN
     `w2n (n2w (w2n a+32):bytes32) + sc*type_memory_bytes ce sty <=
         w2n (n2w (w2n b+32):bytes32) \/
       w2n (n2w (w2n b+32):bytes32) + dc*type_memory_bytes ce dty <=
         w2n (n2w (w2n a+32):bytes32)` assume_tac
     >- (qpat_x_assum `w2n (n2w (w2n a+32):bytes32) = _` mp_tac >>
         qpat_x_assum `w2n (n2w (w2n b+32):bytes32) = _` mp_tac >>
         FIRST [qpat_x_assum `w2n a + 32 + sc * _ <= w2n b` mp_tac,
                qpat_x_assum `w2n b + 32 + dc * _ <= w2n a` mp_tac] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> decide_tac)) >>
   `w2n (n2w (w2n a+32):bytes32) + sc*type_memory_bytes ce sty < dimword(:256) /\
    w2n (n2w (w2n b+32):bytes32) + dc*type_memory_bytes ce dty < dimword(:256)` by
     metis_tac[] >>
   `!j. j < LENGTH vs ==> !m. mem_agree_outside tn2.t_mem t2.vs_memory m ==>
     val_in_memory stv (EL j vs)
       (w2n (n2w (w2n a+32):bytes32)+j*type_memory_bytes ce sty) m` by
     metis_tac[] >>
   drule typed_copy_dynarray_slow_tail_path_ptr_conditional >>
   disch_then drule >>
   disch_then (drule_at (Pat `comp_bind _ _ _ = _`)) >>
   FAIL_TAC "slow-result") >>
 FAIL_TAC "compose"
QED
