(* Inclusive offset endpoints and same-witness immutable-taint framing. *)
Theory typedCopyReturnFieldAddressPtr
Ancestors assignBasePtrFieldOffsets assignBasePtrByteOffset assignBasePtrStoragePath
  typedCopyPtr context compileEnv emitHelper contextCodegenRelProps
  appendStorageGhostPtr stmtFragPtr
  fragExec fragGasPathPtr bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  venomInst words finite_map list ghostPcTransportPtr decoderGhostFramePtr

(* Unlike the older strict-interior boundary, this includes empty children at
   the endpoint. ptr_covers itself permits a zero-sized endpoint window. *)
Theorem typed_copy_offset_endpoint_coverage[local]:
  !G tn root s total a off n PG id p.
  ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
  off+n <= total /\ w2n a+off < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;Lit (n2w off)] [p])
      (update_var p (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root;Lit (n2w off)] [p]) s
      (update_var p (a+n2w off) s) tn)
    p (update_var p (a+n2w off) s) n
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root;Lit (n2w off)] [p]) s
      (update_var p (a+n2w off) s) tn) (Var p) = {}` by
    simp[copy_len_binop_ghost_frame, op_taint_def] >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def,
       update_var_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

Theorem typed_copy_byte_offset_counted:
  !root off sa op sb G tn s a total n fn ctx D PG.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a+off < dimword(:256) /\
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
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      simp[cs_extends_def] >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >>
      gvs[ptr_covers_def, venom_state_component_equality] >> decide_tac) >>
  drule_all assign_base_with_byte_offset_code >> strip_tac >>
  drule_all assign_base_with_byte_offset_layout >> strip_tac >> simp[] >>
  qabbrev_tac `v = update_var p (a+n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) v` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) s v tn` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) s =
    OK v` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `v`]) >>
  `ptr_covers gf tf p v n` by
    (simp[Abbr `gf`, Abbr `tf`, Abbr `v`] >>
     irule typed_copy_offset_endpoint_coverage >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl_tac [`gf`, `tf`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
                  GSYM word_add_n2w, WORD_ADD_COMM] >>
  simp[] >> conj_tac
  >- (simp[Abbr `gf`, Abbr `tf`, Abbr `v`] >>
      mp_tac (Q.SPEC `s` assign_base_copy_binop_counted) >>
      simp[] >> disch_then irule >> simp[op_taint_def] >>
      conj_tac >- gvs[ptr_covers_def, op_taint_def] >>
      qexists_tac `bb` >> gvs[]) >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `v`, update_var_def,
       copy_len_binop_ghost_frame, lookup_var_def, FLOOKUP_UPDATE,
       step_prov_other_output, mk_inst_def] >>
  conj_tac >- fs[venom_state_component_equality] >>
  simp[step_taint_def, set_var_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def]
QED

Theorem typed_copy_field_addresses_counted:
  !dst src doff soff sa dop sm sop sb G tn s d a dtot stot dn sn fn ctx D PG.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtot /\ ptr_covers G tn src s stot /\
    doff+dn <= dtot /\ soff+sn <= stot /\
    w2n d+doff < dimword(:256) /\ w2n a+soff < dimword(:256) /\
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
    metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS] >> simp[] >>
  drule_all typed_copy_byte_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK v)` >>
  rename1 `dop = Var dp` >>
  `not_fresh_at sm src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src v = SOME a` by metis_tac[] >>
  `ptr_covers Gm tm src v stot` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> metis_tac[]) >>
  drule_all typed_copy_byte_offset_counted >>
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
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac >- fs[venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED
