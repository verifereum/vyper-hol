Theory extRetAbiSourceComplexBytesPtr
Ancestors extRetAbiSourceChildPtr extRetBulkCopyCountedPtr abiEncoderMemberCode
  abiEncoder exprLowering emitHelperProps exprLoweringProps bodyPtrDefs
  fragGasPathPtr fragExec compileEnv emitHelper ptrDiscipline venomState
  valueEncoding vyperTyping words list finite_map pred_set arithmetic

Theorem exterior_frames_compose[local]:
  mem_agree_outside w1 m1 m0 /\ mem_agree_outside w2 m2 m1 /\
  (!i. i NOTIN w1 ==> (i IN t1 <=> i IN t0)) /\
  (!i. i NOTIN w2 ==> (i IN t2 <=> i IN t1)) /\
  w1 SUBSET w /\ w2 SUBSET w ==>
  mem_agree_outside w m2 m0 /\
  (!i. i NOTIN w ==> (i IN t2 <=> i IN t0))
Proof
  simp[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_complex_bytes_source_members_counted_ptr:
  !bss so h k sa sb out G tn s src dst ip a b cursor cap scap N msz tail.
  msz = type_memory_size (BaseTV (BytesT (Dynamic N))) /\
  tail = SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss) /\
  compile_abi_encode_complex_elems (Var dst) (Var src)
    (MAP (\bs. (AbiBytestring N,32,msz,T)) bss) so h (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  not_fresh_at sa src /\
  lookup_var src s = SOME (n2w a) /\ a+scap < dimword(:256) /\
  ptr_covers G tn src s scap /\ so+LENGTH bss*msz <= scap /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32*LENGTH bss <= k /\ k+tail <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor+32 < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  (a+scap <= b \/ b+cap <= a) /\
  (a+scap <= cursor \/ cursor+32 <= a) /\
  (b+cap <= cursor \/ cursor+32 <= b) /\ N < dimword(:256) /\
  (!j. j < LENGTH bss ==>
    32+LENGTH (EL j bss) <= msz /\
    LENGTH (EL j bss) <= dimword(:256)-32 /\
    value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+so+j*msz) mem')) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+tail) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+h <= i /\ i < b+h+32*LENGTH bss ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+tail ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside ({i | b+k <= i /\ i < b+k+tail} UNION
      {i | b+h <= i /\ i < b+h+32*LENGTH bss} UNION
      {i | cursor <= i /\ i < cursor+32}) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | b+k <= i /\ i < b+k+tail} UNION
      {i | b+h <= i /\ i < b+h+32*LENGTH bss} UNION
      {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!j mem'. j < LENGTH bss /\ mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+so+j*msz) mem')
Proof
  Induct_on `bss`
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once compile_abi_encode_child_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[gas_path_ptr_rules, mem_agree_outside_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!so h k sa sb out G tn s src dst ip a b cursor cap scap N msz tail. _`
    (mk_asm "ih") >>
  rename1 `MAP _ (bs::bss)` >>
  RULE_ASSUM_TAC (BETA_RULE o PURE_REWRITE_RULE [MAP, LENGTH, SUM]) >>
  `32+LENGTH bs <= msz /\ LENGTH bs <= dimword(:256)-32 /\
   value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\
   val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\
   (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
     val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (a+so) mem')` by
    (qpat_x_assum `!j. j < _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all abi_encoder_member_cons_context >> strip_tac >>
  `?child. elem_src = Var child` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `elem_src = _` SUBST_ALL_TAC >>
  `so+(32+LENGTH bs) <= scap /\ a+so < dimword(:256)` by
    (qpat_x_assum `so + SUC _ * msz <= scap` mp_tac >>
     simp[MULT_CLAUSES] >> strip_tac >> decide_tac) >>
  `w2n (n2w a : bytes32) = a` by (simp[w2n_n2w] >> decide_tac) >>
  drule emit_bulk_offset_ambient_counted_ptr >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ src _ scap`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (drule_at (Pat `lookup_var src _ = _`)) >>
  disch_then (qspecl_then [`32+LENGTH bs`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `not_fresh_at prepared child /\
   (!v. not_fresh_at sa v ==> not_fresh_at prepared v)` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  `lookup_var dst sf = SOME (n2w b) /\ lookup_var ip sf = SOME (n2w cursor) /\
   ptr_covers Gf tnf dst sf cap /\ ptr_covers Gf tnf ip sf 32` by
    (simp[] >> conj_tac
     >- (qpat_x_assum `ptr_covers G tn dst s cap` mp_tac >> simp[ptr_covers_def]) >>
     qpat_x_assum `ptr_covers G tn ip s 32` mp_tac >> simp[ptr_covers_def]) >>
  drule (SRULE [type_to_abi_enc_info_def] abi_dynamic_bytes_source_child_counted_ptr) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ child _ (32+LENGTH _)`)) >>
  disch_then (drule_at (Pat `lookup_var child _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var ip _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ dst _ cap`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`32+ceil32 (LENGTH bs)`, `k`, `cap`, `PG`, `D`] mp_tac) >>
  (impl_tac >-
    (`mload cursor sf = n2w k` by
       (qpat_x_assum `mload cursor s = _` mp_tac >> simp[mload_def]) >>
     simp[w2n_n2w])) >>
  strip_tac >>
  `!v. not_fresh_at sa v ==> not_fresh_at child_end v` by
    (simp[not_fresh_at_def] >> metis_tac[not_fresh_at_def, LESS_EQ_TRANS]) >>
  `lookup_var src sf' = SOME (n2w a) /\
   lookup_var dst sf' = SOME (n2w b) /\
   lookup_var ip sf' = SOME (n2w cursor) /\
   ptr_covers Gf' tnf' src sf' scap /\
   ptr_covers Gf' tnf' dst sf' cap /\
   ptr_covers Gf' tnf' ip sf' 32` by
    (simp[] >> rpt conj_tac
     >- (qpat_x_assum `ptr_covers G tn src s scap` mp_tac >> simp[ptr_covers_def])
     >- (qpat_x_assum `ptr_covers G tn dst s cap` mp_tac >> simp[ptr_covers_def]) >>
     qpat_x_assum `ptr_covers G tn ip s 32` mp_tac >> simp[ptr_covers_def]) >>
  `!j. j < LENGTH bss ==>
    32+LENGTH (EL j bss) <= msz /\
    LENGTH (EL j bss) <= dimword(:256)-32 /\
    value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    (!mem'. mem_agree_outside tnf'.t_mem sf'.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+(so+msz)+j*msz) mem')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!j. j < SUC _ ==> _` (qspec_then `SUC j` mp_tac) >>
     simp_tac bool_ss [EL, TL, prim_recTheory.LESS_MONO_EQ] >>
     (impl_tac >- simp[]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[GSYM ADD_ASSOC, MULT_CLAUSES] >>
     rpt strip_tac >>
     irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qmatch_asmsub_abbrev_tac `mem_agree_outside writes sf'.vs_memory sf.vs_memory` >>
     qexistsl_tac [`s.vs_memory`, `sf'.vs_memory`, `tn.t_mem`, `tnf'.t_mem`, `writes`] >>
     simp[] >> rpt conj_tac
     >- (qpat_x_assum `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==> _`
           mp_tac >> simp[GSYM ADD_ASSOC, MULT_CLAUSES])
     >- (qpat_x_assum `!i. _ ==> (i IN tnf'.t_mem <=> _)` mp_tac >>
         simp[Abbr `writes`, GSYM ADD_ASSOC])
     >- (qpat_x_assum `mem_agree_outside writes _ _` mp_tac >>
         simp[mem_agree_outside_def])
     >> `SUC j * msz <= LENGTH bss * msz` by simp[LE_MULT_RCANCEL] >>
     simp[Abbr `writes`, loweringPostsTheory.val_footprint_def] >>
     rpt strip_tac >>
     qpat_x_assum `so + SUC _ * msz <= scap` mp_tac >>
     simp_tac bool_ss [MULT_CLAUSES] >> strip_tac >>
     qpat_x_assum `msz = _` (SUBST_ALL_TAC o SYM) >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [MULT_CLAUSES]) >>
     qpat_x_assum `ih :- _` kall_tac >> decide_tac) >>
  asm "ih" (drule_at (Pat `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ src _ scap`)) >>
  disch_then (drule_at (Pat `lookup_var src sf' = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst sf' = _`)) >>
  disch_then (drule_at (Pat `lookup_var ip sf' = _`)) >>
  disch_then (drule_at (Pat `mload cursor sf' = _`)) >>
  disch_then (qspecl_then [`cap`, `scap`, `SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss)`] mp_tac) >>
  (impl_tac >-
    (simp[] >> qpat_x_assum `ih :- _` kall_tac >>
     qpat_x_assum `msz = _` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `k+tail <= cap` mp_tac >> simp[] >> strip_tac >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [MULT_CLAUSES]) >> decide_tac)) >>
  strip_tac >> qpat_x_assum `ih :- _` kall_tac >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf' tnf' (OK sf')` by
        (irule gas_path_ptr_then >> metis_tac[]) >>
      pop_assum (assume_tac o SRULE []) >>
      `gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf'' tnf'' (OK sf'')` by
        (irule gas_path_ptr_then >> qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
      pop_assum (mp_tac o SRULE []) >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `mload cursor sf'' = _` mp_tac >>
     qpat_x_assum `tail = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [ADD_ASSOC] >> simp[]) >>
  conj_tac >- simp[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  conj_tac
  >- (simp_tac bool_ss [LENGTH, MULT_CLAUSES] >> rpt strip_tac >>
      Cases_on `i < b+h'+32`
      >- (`i NOTIN ({i | b+(k+(32+ceil32 (LENGTH bs))) <= i /\
                    i < b+(k+(32+ceil32 (LENGTH bs)))+SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss)} UNION
                  {i | b+(h'+32) <= i /\ i < b+(h'+32)+32*LENGTH bss} UNION
                  {i | cursor <= i /\ i < cursor+32})` by
            (simp[] >> decide_tac) >>
          qpat_x_assum `!i. i NOTIN _ ==> (i IN tnf''.t_mem <=> _)`
            (qspec_then `i` mp_tac) >> simp[] >>
          qpat_x_assum `!i. b+h' <= i /\ i < b+h'+32 ==> _`
            (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_x_assum `!i. b+(h'+32) <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `i < b+k+(32+ceil32 (LENGTH bs))`
      >- (`i NOTIN ({i | b+(k+(32+ceil32 (LENGTH bs))) <= i /\
                    i < b+(k+(32+ceil32 (LENGTH bs)))+SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss)} UNION
                  {i | b+(h'+32) <= i /\ i < b+(h'+32)+32*LENGTH bss} UNION
                  {i | cursor <= i /\ i < cursor+32})` by
            (simp[] >> decide_tac) >>
          qpat_x_assum `!i. i NOTIN _ ==> (i IN tnf''.t_mem <=> _)`
            (qspec_then `i` mp_tac) >> simp[] >>
          qpat_x_assum `!i. b+k <= i /\ _ ==> _`
            (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_x_assum `!i. b+(k+_) <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `mem_agree_outside writes sf''.vs_memory s.vs_memory` >>
  `mem_agree_outside writes sf''.vs_memory s.vs_memory /\
   (!i. i NOTIN writes ==> (i IN tnf''.t_mem <=> i IN tn.t_mem))` by
    (irule exterior_frames_compose >>
     qexistsl_tac [`sf'.vs_memory`, `tnf'.t_mem`,
       `{i | b+k <= i /\ i < b+k+(32+ceil32 (LENGTH bs))} UNION
        {i | b+h' <= i /\ i < b+h'+32} UNION {i | cursor <= i /\ i < cursor+32}`,
       `{i | b+(k+(32+ceil32 (LENGTH bs))) <= i /\
              i < b+(k+(32+ceil32 (LENGTH bs)))+SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss)} UNION
        {i | b+(h'+32) <= i /\ i < b+(h'+32)+32*LENGTH bss} UNION
        {i | cursor <= i /\ i < cursor+32}`] >>
     conj_tac
     >- (qpat_x_assum `!i. _ ==> (i IN tnf'.t_mem <=> _)` mp_tac >>
         qpat_x_assum `tnf.t_mem = tn.t_mem` SUBST1_TAC >>
         POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     conj_tac >- (qpat_x_assum `!i. _ ==> (i IN tnf''.t_mem <=> _)` ACCEPT_TAC) >>
     conj_tac >- (simp[Abbr `writes`, SUBSET_DEF, LENGTH, MULT_CLAUSES] >>
                  rpt strip_tac >> decide_tac) >>
     conj_tac >- (simp[Abbr `writes`, SUBSET_DEF, LENGTH, MULT_CLAUSES] >>
                  rpt strip_tac >> decide_tac) >>
     conj_tac
     >- (qpat_x_assum `mem_agree_outside _ sf'.vs_memory sf.vs_memory` mp_tac >> simp[]) >>
     qpat_x_assum `mem_agree_outside _ sf''.vs_memory sf'.vs_memory` ACCEPT_TAC) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  ntac 6 (conj_tac >- simp[]) >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < SUC _ ==> _` (qspec_then `j` mp_tac) >>
  (impl_tac >- fs[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf''.vs_memory`, `tn.t_mem`, `tnf''.t_mem`, `writes`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `mem_agree_outside writes sf''.vs_memory s.vs_memory`
        mp_tac >> simp[mem_agree_outside_def]) >>
  `SUC j * msz <= SUC (LENGTH bss) * msz` by
    (qpat_x_assum `j < LENGTH (bs::bss)` mp_tac >> simp[LENGTH, LE_MULT_RCANCEL]) >>
  qpat_x_assum `msz = _` (SUBST_ALL_TAC o SYM) >>
  simp_tac (srw_ss()) [Abbr `writes`, loweringPostsTheory.val_footprint_def,
    IN_UNION, GSPECIFICATION, LENGTH, MULT_CLAUSES] >>
  rpt strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [MULT_CLAUSES]) >> decide_tac
QED
