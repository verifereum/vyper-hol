Theory extRetComplexMembersInvariantPtr
Ancestors
  abiEncoderMemberCode abiEncoder emitHelper fragExec compileEnv
  fragGasPathPtr venomState list arithmetic pair

(* Conditional execution fold over actual member code.  A consumer invariant
   can include evaluated source offsets, numeric head/tail ledgers, robust
   unread children, resources and all ambient frames.  In particular the
   callback must explicitly preserve already-clean destination prefixes;
   an exterior frame for the whole destination envelope does NOT imply this.
   Discharging that callback from recursive encoding is an outer obligation,
   not an additional premise on either frozen external-frame theorem.
   No cursor is accessed by the NIL case or required for static instances. *)

Theorem encoder_complex_members_invariant_counted_ptr:
  !infos j so ho sa sb out G tn s.
  compile_abi_encode_complex_elems dst src infos so ho dp sa = (out,sb) /\
  fn_has_code sa sb fn /\ member_inv j infos so ho sa G tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!l ei az mz dy rest x y st G0 tn0 s0 elem_src prepared child_out child_end.
    member_inv l ((ei,az,mz,dy)::rest) x y st G0 tn0 s0 /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
    emit_op ADD [src; Lit (n2w x)] st = (elem_src,prepared) /\
    compile_abi_encode_child dst elem_src ei dy y dp prepared = (child_out,child_end) /\
    fn_has_code st prepared fn /\ fn_has_code prepared child_end fn ==>
    ?Gp tnp sp G1 tn1 s1.
      gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 Gp tnp (OK sp) /\
      sp.vs_current_bb = prepared.cs_current_bb /\
      sp.vs_inst_idx = LENGTH prepared.cs_current_insts /\ ~sp.vs_halted /\
      gas_path_ptr D 0 ctx fn PG Gp tnp sp ((cost:num->num) l) G1 tn1 (OK s1) /\
      s1.vs_current_bb = child_end.cs_current_bb /\
      s1.vs_inst_idx = LENGTH child_end.cs_current_insts /\ ~s1.vs_halted /\
      member_inv (l+1) rest (x+mz) (y+az) child_end G1 tn1 s1) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s
      (SUM (GENLIST (\i. cost (j+i)) (LENGTH infos))) Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    member_inv (j+LENGTH infos) []
      (so+SUM (MAP (\(ei,az,mz,dy). mz) infos))
      (ho+SUM (MAP (\(ei,az,mz,dy). az) infos)) sb Gf tnf sf
Proof
  Induct_on `infos`
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once compile_abi_encode_child_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[gas_path_ptr_rules]) >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  drule_all abi_encoder_member_cons_context >> strip_tac >>
  qpat_assum `!l ei az mz dy rest x y st G0 tn0 s0 elem_src prepared child_out child_end. _`
    (drule_at (Pat `member_inv _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_child _ _ _ _ _ _ _ = _`)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `member_inv _ _ _ _ _ _ _ _`)) >>
  (impl_tac >- (gvs[ADD_COMM] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  pure_rewrite_tac [LENGTH, MAP, SUM, GENLIST_CONS, combinTheory.o_DEF,
    pairTheory.pair_case_thm, ADD_ASSOC, ADD_CLAUSES] >>
  simp_tac bool_ss [pairTheory.pair_case_thm, ADD_CLAUSES,
    GSYM ADD_ASSOC, arithmeticTheory.ADD1] >>
  reverse conj_tac >- gvs[] >>
  irule gas_path_ptr_then >>
  qexistsl_tac [`G1`, `s1`, `tn1`] >>
  reverse conj_tac >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G1 _ _ _ _ _ _` mp_tac >>
    simp_tac bool_ss [GSYM ADD1, ADD_CLAUSES]) >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gp`, `sp`, `tnp`] >> simp[]
QED
