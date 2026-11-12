(* Literal pointer offsets include zero-sized windows at the allocation endpoint. *)
Theory appendDynamicPointerAddPtr
Ancestors typedCopyPtr exprSimPtrLiteralOps ghostPcTransportPtr
  bodyPtrDefs loweringStateRelDefs
  ptrDiscipline venomInst venomState venomExecSemantics compileEnv
  context emitHelper codegenRel contextCodegenRel finite_map words

Theorem dynamic_pointer_add_step_ptr:
  !G tn s root out off n total a id PG.
    lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
    off+n <= total /\ w2n a+off < dimword(:256) ==>
    ?u Gf tf.
      u = update_var out (n2w (w2n a+off)) s /\
      step_inst_base (mk_inst id ADD [Var root;Lit (n2w off)] [out]) s = OK u /\
      Gf = step_prov PG G (mk_inst id ADD [Var root;Lit (n2w off)] [out]) u /\
      tf = step_taint (mk_inst id ADD [Var root;Lit (n2w off)] [out]) s u tn /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn
          (mk_inst id ADD [Var root;Lit (n2w off)] [out]) s) /\
      (u with vs_vars := s.vs_vars) = s /\
      lookup_var out u = SOME (n2w (w2n a+off)) /\ ptr_covers Gf tf out u n /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. p <> out ==> lookup_var p u = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var out (n2w (w2n a+off)) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst id ADD [Var root;Lit (n2w off)] [out]) u` >>
  qabbrev_tac `tf = step_taint
    (mk_inst id ADD [Var root;Lit (n2w off)] [out]) s u tn` >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> simp[] >>
  conj_tac >-
    simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def, GSYM word_add_n2w] >>
  conj_tac >- (rpt strip_tac >> irule literal_add_ptr_inst_ok >>
    gvs[ptr_covers_def]) >>
  conj_tac >- simp[Abbr `u`, update_var_def] >>
  conj_tac >- simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >-
    (simp[Abbr `Gf`, Abbr `tf`, Abbr `u`] >>
     irule (SRULE[arithmeticTheory.ADD_COMM] literal_add_ptr_covers) >>
     gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `new_site_bytes s u = {}` by
    simp[Abbr `u`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `u`, Abbr `Gf`, Abbr `tf`, lookup_var_def, update_var_def,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `first_prov G [Var root; Lit (n2w off)]` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem emit_dynamic_pointer_add_ptr:
  !G cx ctx PG R sa sb root out off n total tn s a.
    emit_op ADD [Var root; Lit (n2w off)] sa = (Var out,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a+off < dimword(:256) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tnf out sf n /\ not_fresh_at sb out /\ cs_extends sa sb /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out]] /\
   not_fresh_at sb out /\ cs_extends sa sb /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
         cs_extends_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all dynamic_pointer_add_step_ptr >>
  disch_then (qspecl_then [`out`, `sa.cs_next_id`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (irule ptr_fragment_step >> simp[is_terminator_def] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  simp[lookup_var_def] >> gvs[update_var_def] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `p <> out` by metis_tac[] >> simp[]
QED
