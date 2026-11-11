(* Zero-size-safe addresses for recursive typed field copies. *)
Theory bodyPtrTypedCopyFieldStep
Ancestors
  bodyPtrTypedCopyBoundary bodyPtrPopNestedLiveAddressFrame externalEntryShape
  typedMemoryCopy
  assignBasePtrFieldOffsets appendStorageGhostPtr stmtFragPtr context compileEnv emitHelper
  fragExec fragGasPathPtr bodyPtrDefs ptrDiscipline venomState words
  finite_map arithmetic pred_set

Theorem typed_field_offset_counted:
  !root off sa op sb G tn s a total n fn ctx D PG.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a + off < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?p Gf tf u.
      op = Var p /\ not_fresh_at sb p /\
      lookup_var p u = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tf p u n /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_offset_extends >> strip_tac >> simp[] >>
  Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[cj 1 gas_path_ptr_rules] >>
      gvs[ptr_covers_def] >> decide_tac) >>
  `emit_op ADD [Var root; Lit (n2w off)] sa = (op,sb)` by
    gvs[compile_with_byte_offset_def] >>
  drule (SIMP_RULE (srw_ss()) [eval_operand_def, op_taint_def]
    (Q.INST [`offset` |-> `Lit (n2w off)`]
      (SPEC_ALL pop_emit_offset_endpoint_framed_path))) >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`out`, `H`, `tf`, `t`] >> simp[op_taint_def, ADD_COMM]
QED

Theorem typed_field_offsets_counted:
  !dst src doff soff sa dop sm sop sb G tn s d a dtot stot dn sn fn ctx D PG.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtot /\ ptr_covers G tn src s stot /\
    doff+dn <= dtot /\ soff+sn <= stot /\
    w2n d+doff < dimword (:256) /\ w2n a+soff < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?dp sp Gf tf u.
      dop = Var dp /\ sop = Var sp /\
      not_fresh_at sb dp /\ not_fresh_at sb sp /\
      lookup_var dp u = SOME (n2w (w2n d+doff)) /\
      lookup_var sp u = SOME (n2w (w2n a+soff)) /\
      ptr_covers Gf tf dp u dn /\ ptr_covers Gf tf sp u sn /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[assign_base_offset_extends] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (drule_all assign_base_offset_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[cs_extends_trans, LESS_EQ_TRANS] >> simp[] >>
  drule_all typed_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK v)` >>
  rename1 `dop = Var dp` >>
  `not_fresh_at sm src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src v = SOME a` by metis_tac[] >>
  `ptr_covers Gm tm src v stot` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> metis_tac[]) >>
  drule_all typed_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gm tm v 0 Gf tf (OK u)` >>
  rename1 `sop = Var sp` >>
  `not_fresh_at sb dp` by metis_tac[not_fresh_at_mono] >>
  `lookup_var dp u = lookup_var dp v` by metis_tac[] >>
  `ptr_covers Gf tf dp u dn` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`Gm`, `v`, `sm`, `tm`] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  qexistsl_tac [`dp`, `sp`, `Gf`, `tf`, `u`] >> simp[ADD_COMM] >>
  conj_tac >- fs[venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Theorem typed_field_copy_step:
  !ce dt st.
  (!tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv st dt /\
    evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
    type_memory_bytes ce st = type_memory_size stv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) dt (Var src) st sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce st) /\
    ptr_covers G tn dst s (type_memory_bytes ce dt) /\
    w2n a + type_memory_bytes ce st < dimword(:256) /\
    w2n b + type_memory_bytes ce dt < dimword(:256) /\
    (type_memory_bytes ce st <> 0 /\ type_memory_bytes ce dt <> 0 ==>
      w2n a + type_memory_bytes ce st <= w2n b \/
      w2n b + type_memory_bytes ce dt <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce dt) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce dt) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)) ==>
  !tenv dtv stv v dst src doff soff sa dop sm sop sb sc ctx fn D PG G tn s a b dtot stot.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv st dt /\
    evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
    type_memory_bytes ce st = type_memory_size stv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sb) /\
    compile_store_memory_typed ce dop dt sop st sb = ((),sc) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s stot /\ ptr_covers G tn dst s dtot /\
    soff + type_memory_bytes ce st <= stot /\
    doff + type_memory_bytes ce dt <= dtot /\
    w2n a + stot < dimword(:256) /\ w2n b + dtot < dimword(:256) /\
    (type_memory_bytes ce st <> 0 /\ type_memory_bytes ce dt <> 0 ==>
      w2n a + soff + type_memory_bytes ce st <= w2n b + doff \/
      w2n b + doff + type_memory_bytes ce dt <= w2n a + soff) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a + soff) m) /\
    fn_has_code sa sc fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sc /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sc.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b + doff) (type_memory_bytes ce dt) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_bytes ce dt) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b + doff) m)
Proof
  rpt gen_tac >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[assign_base_offset_extends] >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sb sc` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`ce`, `dop`, `dt`, `sop`, `st`, `sb`] mp_tac
       (cj 1 typed_memory_family_labels) >> strip_tac >>
     disch_then SUBST_ALL_TAC >> fs[]) >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >> simp[] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    metis_tac[fn_has_code_split] >>
  `w2n a + soff < dimword(:256) /\ w2n b + doff < dimword(:256)` by decide_tac >>
  drule_all typed_field_offsets_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK u)` >>
  `u.vs_memory = s.vs_memory` by fs[venom_state_component_equality] >>
  `w2n (n2w (w2n a + soff) : bytes32) = w2n a + soff /\
   w2n (n2w (w2n b + doff) : bytes32) = w2n b + doff` by
    simp[w2n_n2w] >>
  qpat_x_assum `dop = Var _` SUBST_ALL_TAC >>
  qpat_x_assum `sop = Var _` SUBST_ALL_TAC >>
  `w2n (n2w (w2n a + soff) : bytes32) + type_memory_bytes ce st < dimword(:256) /\
   w2n (n2w (w2n b + doff) : bytes32) + type_memory_bytes ce dt < dimword(:256)` by
    (simp[] >> decide_tac) >>
  `(type_memory_bytes ce st <> 0 /\ type_memory_bytes ce dt <> 0 ==>
    w2n (n2w (w2n a + soff) : bytes32) + type_memory_bytes ce st <=
      w2n (n2w (w2n b + doff) : bytes32) \/
    w2n (n2w (w2n b + doff) : bytes32) + type_memory_bytes ce dt <=
      w2n (n2w (w2n a + soff) : bytes32))` by simp[] >>
  `!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
    val_in_memory stv v (w2n (n2w (w2n a + soff) : bytes32)) m` by
    (qpat_x_assum `!m. mem_agree_outside tn.t_mem _ _ ==> _` mp_tac >>
     simp[ADD_COMM]) >>
  first_x_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "compose"
QED

Resume typed_field_copy_step[compose]:
  qpat_assum `w2n (n2w (w2n b + doff)) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  qexistsl_tac [`H`, `tf`, `sf`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (fs[typed_copy_state_frame_def, venom_state_component_equality] >>
      metis_tac[not_fresh_at_mono]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> (i IN tf.t_mem <=> _)` mp_tac >>
      simp[ADD_COMM]) >>
  conj_tac
  >- (qx_gen_tac `p` >> strip_tac >>
      `not_fresh_at sb p` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!p. not_fresh_at sb p ==> _` (qspec_then `p` mp_tac) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >>
      simp[]) >>
  qpat_x_assum `!m. mem_agree_outside tf.t_mem _ _ ==> _` mp_tac >>
  simp[ADD_COMM]
QED

Finalise typed_field_copy_step
