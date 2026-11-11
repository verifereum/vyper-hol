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

(* One concrete head: prepare the two addresses, then consume the recursive
   store contract.  The recursive premise is at the emitted child cursor;
   numeric resources are independent of provenance coverage. *)
Theorem intcall_field_store_counted:
  !D ctx fn PG dst src doff soff sa sm sc dop sop G tn s b a
    dtotal stotal stv dtv v sd.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sc) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    doff + type_memory_size dtv <= dtotal /\
    soff + type_memory_size stv <= stotal /\
    w2n b + doff + type_memory_size dtv < dimword (:256) /\
    w2n a + soff + val_footprint stv v < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a + soff) m) /\
    fn_has_code sa sc fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    (!dp sp H t u.
      dop = Var dp /\ sop = Var sp /\
      not_fresh_at sc dp /\ not_fresh_at sc sp /\
      lookup_var dp u = SOME (n2w (w2n b + doff)) /\
      lookup_var sp u = SOME (n2w (w2n a + soff)) /\
      ptr_covers H t dp u (type_memory_size dtv) /\
      ptr_covers H t sp u (type_memory_size stv) /\
      w2n (n2w (w2n b + doff):256 word) + type_memory_size dtv < dimword (:256) /\
      w2n (n2w (w2n a + soff):256 word) + val_footprint stv v < dimword (:256) /\
      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
        val_in_memory stv v (w2n (n2w (w2n a + soff):256 word)) m) /\
      u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted ==>
      ?K tf z.
        gas_path_ptr D 0 ctx fn PG H t u 0 K tf (OK z) /\
        z.vs_current_bb = sd.cs_current_bb /\
        z.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~z.vs_halted /\
        (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
          val_in_memory dtv v (w2n b + doff) m) /\
        tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\ tf.t_imm = t.t_imm /\
        z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
        z.vs_fmp = u.vs_fmp /\ z.vs_accounts = u.vs_accounts /\
        z.vs_transient = u.vs_transient /\ z.vs_call_ctx = u.vs_call_ctx /\
        (!x. not_fresh_at sc x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tf (Var x) = op_taint t (Var x)) /\
        (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size dtv) ==>
          mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
          (i IN tf.t_mem <=> i IN t.t_mem))) ==>
    ?K tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK z) /\
      z.vs_current_bb = sd.cs_current_bb /\
      z.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory dtv v (w2n b + doff) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size dtv) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n b + doff < dimword (:256) /\ w2n a + soff < dimword (:256)`
    by decide_tac >>
  drule_all intcall_field_offsets_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H t (OK u)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_fmp = s.vs_fmp /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx` by
    fs[venom_state_component_equality] >>
  `w2n (n2w (w2n b + doff):256 word) = w2n b + doff /\
   w2n (n2w (w2n a + soff):256 word) = w2n a + soff` by simp[] >>
  fs[] >>
  qpat_x_assum `!H t u. _` (qspecl_then [`H`, `t`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H t u 0 Hf tf (OK z)` >>
  qexistsl_tac [`Hf`, `tf`, `z`] >> simp[] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED
