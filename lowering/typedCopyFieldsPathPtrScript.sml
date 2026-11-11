(* Semantic suffix traversal with independent source and destination layouts. *)
Theory typedCopyFieldsPathPtr
Ancestors
 typedCopyFieldHeadPathPtr typedCopyFieldsFoldPathPtr typedCopyRobustTransportPtr
 typedMemoryCopy typedCopyPtr fragGasPathPtr placeMemoryFieldsForward
 context compileEnv exprLoweringProps fragExec bodyPtrDefs
 abiEncoderInput vyperTypeSystem venomState finite_map words list arithmetic

Theorem compile_typed_copy_fields_robust_path_ptr:
 !D ctx func PG cenv tenv dst src DN scap dw sw.
 !dts sts dtvs stvs vs doff soff a z G tn s.
 LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
 LENGTH stvs = LENGTH dts /\ LENGTH vs = LENGTH dts /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) fields) /\
 (!i. i < LENGTH dts ==>
   type_widens_to tenv (EL i sts) (EL i dts) /\
   evaluate_type tenv (EL i sts) = SOME (EL i stvs) /\
   evaluate_type tenv (EL i dts) = SOME (EL i dtvs) /\
   value_has_type (EL i stvs) (EL i vs) /\
   value_has_type (EL i dtvs) (EL i vs) /\
   val_wf (EL i stvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs)) /\
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
    val_in_memory dtv v (w2n bw) m)) /\
 compile_typed_copy_fields cenv (Var dst) (Var src) dts sts doff soff a = ((),z) /\
 not_fresh_at a dst /\ not_fresh_at a src /\
 lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
 ptr_covers G tn dst s DN /\ ptr_covers G tn src s scap /\
 doff + SUM (MAP (type_memory_bytes cenv) dts) <= DN /\
 soff + SUM (MAP (type_memory_bytes cenv) sts) <= scap /\
 w2n dw + DN < dimword(:256) /\ w2n sw + scap < dimword(:256) /\
 (w2n dw + DN <= w2n sw \/ w2n sw + scap <= w2n dw) /\
 fn_has_code a z func /\ s.vs_current_bb = a.cs_current_bb /\
 s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!i. i < LENGTH dts ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (EL i stvs) (EL i vs)
    (w2n sw + soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) m) ==>
 cs_extends a z /\ ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = z.cs_current_bb /\
 sf.vs_inst_idx = LENGTH z.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
  vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at a p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n dw+doff <= i /\
   i < w2n dw+doff+SUM (MAP (type_memory_bytes cenv) dts)) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!i. i < LENGTH dts ==> !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
   val_in_memory (EL i dtvs) (EL i vs)
    (w2n dw+doff+SUM (MAP (type_memory_bytes cenv) (TAKE i dts))) m) /\
 lookup_var dst sf = SOME dw /\ lookup_var src sf = SOME sw /\
 ptr_covers Gf tnf dst sf DN /\ ptr_covers Gf tnf src sf scap
Proof
 ntac 12 gen_tac >> Induct_on `dts`
 >- (rpt gen_tac >> strip_tac >> gvs[] >>
     qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, comp_return_def] >>
     strip_tac >> gvs[] >> simp[cs_extends_def] >>
     qexistsl [`G`,`tn`,`s`] >> simp[venom_state_component_equality] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
 pop_assum (mk_asm "ih") >> rpt gen_tac >>
 namedCases_on `sts` ["", "st sts0"] >- simp[] >>
 namedCases_on `dtvs` ["", "dtv dtvs0"] >- simp[] >>
 namedCases_on `stvs` ["", "stv stvs0"] >- simp[] >>
 namedCases_on `vs` ["", "v vs0"] >- simp[] >>
 simp_tac bool_ss [LENGTH, prim_recTheory.INV_SUC_EQ] >> strip_tac >>
 qpat_x_assum `!dt st. MEM (dt,st) _ ==> _` (mk_asm "children") >>
 qpat_assum `!i. i < _ ==> type_widens_to _ _ _ /\ _` (mk_asm "semantics") >>
 asm "semantics" (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
 qpat_assum `!i. i < _ ==> !m. _` (qspec_then `0` mp_tac) >>
 simp_tac (srw_ss()) [] >> strip_tac >>
 drule typed_memory_fields_cons_compile >> strip_tac >>
 `cs_extends a c /\ cs_extends a z` by metis_tac[cs_extends_trans] >>
 `fn_has_code a c func` by metis_tac[fn_has_code_split] >>
 `doff + type_memory_bytes cenv h <= DN /\
  soff + type_memory_bytes cenv st <= scap` by (fs[SUM, MAP] >> decide_tac) >>
 qspecl_then [`D`,`ctx`,`func`,`PG`] mp_tac compile_typed_copy_field_head_path_ptr >>
 disch_then (qspecl_then [`cenv`,`tenv`,`h`,`st`] mp_tac) >>
 (impl_tac
  >- (conj_tac
      >- MATCH_ACCEPT_TAC typedCopyOffsetClosedPathPtrTheory.compile_with_byte_offset_closed_path_ptr >>
      asm "children" (qspecl_then [`h`,`st`] mp_tac) >>
      simp_tac bool_ss [ZIP, MEM, pairTheory.PAIR_EQ, REFL_CLAUSE, OR_CLAUSES] >>
      disch_then MATCH_ACCEPT_TAC)) >>
 disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `compile_with_byte_offset (Var dst) _ _ = _`)) >>
 disch_then (drule_at (Pat `compile_with_byte_offset (Var src) _ _ = _`)) >>
 disch_then (qspecl_then [`G`,`tn`,`s`] mp_tac) >>
 simp[] >> disch_then (qspecl_then [`DN`,`scap`,`v`] mp_tac) >>
 (impl_tac >- (simp[] >> conj_tac
   >- (qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` MATCH_ACCEPT_TAC) >>
   qpat_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory stv v _ m` mp_tac >>
   rpt (pop_assum kall_tac) >> metis_tac[ADD_COMM])) >> strip_tac >>
 rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
 qpat_assum `!i. _ ==> mem_bytes_at i 1 s1.vs_memory = _ /\ _` (mk_asm "head_frame") >>
 `!j. ~(doff+w2n dw <= j /\ j < doff+w2n dw+type_memory_bytes cenv h) ==>
   mem_bytes_at j 1 s1.vs_memory = mem_bytes_at j 1 s.vs_memory` by
   (asm "head_frame" mp_tac >> rpt (pop_assum kall_tac) >>
    metis_tac[ADD_ASSOC]) >>
 drule robust_representation_exterior_frame >>
 disch_then (qspecl_then [`tn.t_mem`,`tn1.t_mem`] (mk_asm "head_transport")) >>
 `!i. i < LENGTH dts ==>
   type_widens_to tenv (EL i sts0) (EL i dts) /\
   evaluate_type tenv (EL i sts0) = SOME (EL i stvs0) /\
   evaluate_type tenv (EL i dts) = SOME (EL i dtvs0) /\
   value_has_type (EL i stvs0) (EL i vs0) /\
   value_has_type (EL i dtvs0) (EL i vs0) /\
   val_wf (EL i stvs0) (EL i vs0) /\ val_wf (EL i dtvs0) (EL i vs0)` by
  (gen_tac >> strip_tac >>
   asm "semantics" (qspec_then `SUC i` mp_tac) >>
   simp_tac (srw_ss()) [EL, HD, TL, prim_recTheory.LESS_MONO_EQ] >>
   simp[]) >>
 `!i. i < LENGTH dts ==> !m.
  mem_agree_outside tn1.t_mem s1.vs_memory m ==>
  val_in_memory (EL i stvs0) (EL i vs0)
   (w2n sw + (soff + type_memory_bytes cenv st) +
    SUM (MAP (type_memory_bytes cenv) (TAKE i sts0))) m` by
  (gen_tac >> strip_tac >> gen_tac >> strip_tac >>
   qpat_assum `!i. i < LENGTH dts ==> type_widens_to _ _ _ /\ _` drule >>
   strip_tac >>
   `type_memory_bytes cenv (EL i sts0) = type_memory_size (EL i stvs0)` by
    (irule typed_copy_memory_size >> qexists `tenv` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` drule >> simp[]) >>
   `SUM (MAP (type_memory_bytes cenv) (TAKE i sts0)) +
      type_memory_bytes cenv (EL i sts0) <= SUM (MAP (type_memory_bytes cenv) sts0)` by
     (irule abi_encoder_prefix_sum_bound >> simp[]) >>
   asm "head_transport" irule >>
   conj_tac
   >- (qpat_assum `!i. i < SUC _ ==> !m. _` (qspec_then `SUC i` mp_tac) >>
       simp_tac (srw_ss()) [EL, HD, TL, TAKE_def, MAP, SUM, prim_recTheory.LESS_MONO_EQ] >>
       qpat_assum `i < LENGTH dts` mp_tac >>
       rpt (pop_assum kall_tac) >> metis_tac[ADD_ASSOC]) >>
   conj_tac
   >- (asm "head_frame" mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[ADD_ASSOC]) >>
   conj_tac >- (fs[MAP, SUM] >> decide_tac) >> simp[]) >>
 `fn_has_code c z func` by metis_tac[fn_has_code_split] >>
 `a.cs_next_var <= c.cs_next_var` by
  (qpat_assum `compile_with_byte_offset (Var dst) _ _ = _`
    (mp_tac o MATCH_MP typed_copy_offset_mono) >>
   qpat_assum `compile_with_byte_offset (Var src) _ _ = _`
    (mp_tac o MATCH_MP typed_copy_offset_mono) >>
   qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
   rpt (pop_assum kall_tac) >> strip_tac >>
   qspecl_then [`cenv`,`dp`,`h`,`sp`,`st`,`b`] mp_tac
    (cj 1 ci_mono_typed_memory_family) >>
   asm_simp_tac bool_ss [pairTheory.SND, ci_mono_def] >> rpt strip_tac >> decide_tac) >>
 `not_fresh_at c dst /\ not_fresh_at c src` by
  (map_every (fn pat => qpat_assum pat mp_tac)
    [`not_fresh_at a dst`,`not_fresh_at a src`,`a.cs_next_var <= c.cs_next_var`] >>
   rpt (pop_assum kall_tac) >> simp_tac bool_ss [loweringStateRelDefsTheory.not_fresh_at_def] >>
   metis_tac[LESS_EQ_TRANS]) >>
 asm "ih" (qspecl_then [`sts0`,`dtvs0`,`stvs0`,`vs0`] mp_tac) >>
 disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
 disch_then (qspecl_then [`G1`,`tn1`,`s1`] mp_tac) >>
 (impl_tac >-
  (simp[] >> conj_tac
   >- (qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` MATCH_ACCEPT_TAC) >>
   conj_tac
   >- (map_every qx_gen_tac [`dt`,`st'`] >> strip_tac >>
       asm "children" (qspecl_then [`dt`,`st'`] mp_tac) >>
       simp_tac bool_ss [ZIP, MEM] >>
       (impl_tac >- simp[]) >> simp[]) >>
   fs[MAP, SUM] >> decide_tac)) >>
 strip_tac >>
 qpat_assum `!i. _ ==> mem_bytes_at i 1 sf.vs_memory = _ /\ _` (mk_asm "tail_frame") >>
 `!j. ~(w2n dw + (doff + type_memory_bytes cenv h) <= j /\
   j < w2n dw + (doff + type_memory_bytes cenv h) +
     SUM (MAP (type_memory_bytes cenv) dts)) ==>
   mem_bytes_at j 1 sf.vs_memory = mem_bytes_at j 1 s1.vs_memory` by
  (asm "tail_frame" mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
 drule robust_representation_exterior_frame >>
 disch_then (qspecl_then [`tn1.t_mem`,`tnf.t_mem`] (mk_asm "tail_transport")) >>
 `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
   val_in_memory dtv v (w2n dw + doff) m` by
  (rpt strip_tac >>
   `type_memory_bytes cenv h = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists `tenv` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` drule >> simp[]) >>
   asm "tail_transport" irule >> conj_tac
   >- (qpat_assum `!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==> val_in_memory dtv v _ m` mp_tac >>
       rpt (pop_assum kall_tac) >> metis_tac[ADD_COMM]) >>
   conj_tac >- (asm "tail_frame" mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
   conj_tac >- decide_tac >> simp[]) >>
 asm_x "ih" kall_tac >> asm_x "children" kall_tac >>
 asm_x "head_transport" kall_tac >> asm_x "tail_transport" kall_tac >>
 (qexistsl [`Gf`,`tnf`,`sf`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `(sf with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|>) = s1` mp_tac >>
      qpat_assum `(s1 with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|>) = s` mp_tac >>
      qpat_assum `s.vs_current_bb = _` mp_tac >>
      qpat_assum `s.vs_inst_idx = _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[venom_state_component_equality]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qx_gen_tac `p` >> strip_tac >>
      `not_fresh_at c p` by
       (qpat_assum `not_fresh_at a p` mp_tac >>
        qpat_assum `a.cs_next_var <= c.cs_next_var` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp_tac bool_ss [loweringStateRelDefsTheory.not_fresh_at_def] >>
        metis_tac[LESS_EQ_TRANS]) >>
      qpat_assum `!p. not_fresh_at c p ==> _` (qspec_then `p` mp_tac) >>
      qpat_assum `!p. not_fresh_at a p ==> _` (qspec_then `p` mp_tac) >>
      simp[]) >>
  conj_tac
  >- (qx_gen_tac `i` >> disch_tac >>
      asm "head_frame" (qspec_then `i` mp_tac) >>
      asm "tail_frame" (qspec_then `i` mp_tac) >>
      qpat_x_assum `_ \/ _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[MAP, SUM] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac
  >- (qx_gen_tac `i` >> Cases_on `i`
      >- (qpat_assum `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory dtv v _ m` mp_tac >>
          rpt (pop_assum kall_tac) >> simp[ADD_COMM]) >>
      simp_tac (srw_ss()) [TAKE_def, MAP, SUM, ADD_ASSOC] >>
      rpt strip_tac >>
      qpat_assum `!i. i < LENGTH dts ==> !m. _` drule >>
      disch_then (qspec_then `m` mp_tac) >>
      qpat_assum `mem_agree_outside tnf.t_mem sf.vs_memory m` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[]) >>
  simp[])
QED
