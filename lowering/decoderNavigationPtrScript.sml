(* Pointer destination navigation, including stale output registers. *)
Theory decoderNavigationPtr
Ancestors typedCopyPtr bodyPtrDefs fragExecPtr words venomState finite_map
  ptrDiscipline venomInst arithmetic

Theorem emitted_ptr_offset_frag_ptr:
  !cx ctx PG sa sb id root out off s a G tn total n R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id ADD [Var root; Lit (n2w off)] [out]] /\
    lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
    off + n <= total /\ w2n a + off < dimword(:256) ==>
    ?Gf tnf sf.
      sf = ((update_var out (a + n2w off) s) with
        vs_inst_idx := SUC s.vs_inst_idx) /\
      lookup_var out sf = SOME (n2w (w2n a + off)) /\
      ptr_covers Gf tnf out sf n /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = s.vs_memory /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. q <> out ==>
        lookup_var q sf = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst id ADD [Var root; Lit (n2w off)] [out]) t` >>
  qabbrev_tac `tf = step_taint
    (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s t tn` >>
  qexistsl_tac [`gf`, `tf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >>
  conj_tac >-
    simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      GSYM word_add_n2w, ADD_COMM, WORD_ADD_COMM] >>
  conj_tac >-
    ( `op_taint tf (Var out) = {}` by
        simp[Abbr `tf`, Abbr `t`, copy_len_binop_ghost_frame] >>
      gvs[ptr_covers_def] >>
      `off < dimword(:256)` by decide_tac >>
      simp[Abbr `gf`, Abbr `t`, step_prov_def, set_prov_def, out_prov_def,
        first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
        lookup_var_def, update_var_def, w2n_add_2, w2n_n2w, LESS_MOD] >>
      decide_tac) >>
  conj_tac >-
    (irule copy_len_binop_frag_ptr >> simp[mk_inst_def] >>
     simp[Abbr `gf`, Abbr `tf`, Abbr `t`, eval_operand_def, mk_inst_def,
       op_taint_def] >> gvs[ptr_covers_def, op_taint_def]) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `t`, copy_len_binop_ghost_frame,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
