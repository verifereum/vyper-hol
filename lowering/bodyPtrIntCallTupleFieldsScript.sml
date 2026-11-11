(* Concrete field-store preparation.  Unlike the older paired-offset boundary,
   endpoint zero-size fields are allowed and immutable taint is preserved. *)
Theory bodyPtrIntCallTupleFields
Ancestors bodyPtrIntCallFieldOffset bodyPtrIntCallStoreFields
  assignBasePtrFieldOffsets appendStorageGhostPtr stmtFragPtr
  typedCopyLayoutPtr typedCopyTuplePtr exprSimPtrTopLevelStorageFrame
  context compileEnv fragExec fragGasPathPtr venomState words finite_map arithmetic

Theorem intcall_field_offsets_counted:
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
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      tf.t_imm = tn.t_imm /\
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
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK v)` >>
  rename1 `dop = Var dp` >>
  `not_fresh_at sm src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src v = SOME a` by metis_tac[] >>
  `ptr_covers Gm tm src v stot` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> metis_tac[]) >>
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gm tm v 0 Gf tf (OK u)` >>
  rename1 `sop = Var sp` >>
  qexistsl_tac [`dp`, `sp`, `Gf`, `tf`, `u`] >>
  `not_fresh_at sb dp` by metis_tac[not_fresh_at_mono] >>
  `lookup_var dp u = lookup_var dp v` by metis_tac[] >>
  `ptr_covers Gf tf dp u dn` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`Gm`, `v`, `sm`, `tm`] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  simp[ADD_COMM] >> conj_tac
  >- fs[venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED
