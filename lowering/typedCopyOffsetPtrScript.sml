(* Executed pointer offsets, preserving the exterior semantic state. *)
Theory typedCopyOffsetPtr
Ancestors typedCopyPtr exprLoweringProps context compileEnv loweringStateRelDefs emitHelper
  contextCodegenRelProps bodyPtrDefs fragExecPtr words venomState finite_map
  ptrDiscipline venomInst

Theorem compile_with_byte_offset_frag_ptr:
  !cx ctx PG R root off sa op sb G tn s a total n.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
    w2n a + off < dimword(:256) ==>
    cs_extends sa sb /\
    ?p Gf tnf sf.
      op = Var p /\ lookup_var p sf = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tnf p sf n /\ not_fresh_at sb p /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[contextTheory.compile_with_byte_offset_def, comp_return_def] >>
      conj_tac >- simp[cs_extends_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[] >>
      conj_tac >- (gvs[ptr_covers_def] >> decide_tac) >>
      simp[frag_exec_ptr_def] >> rpt strip_tac >> disj1_tac >>
      rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  gvs[compile_with_byte_offset_def] >>
  `?out. op = Var out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def] >> metis_tac[]) >>
  gvs[] >>
  `cs_extends sa sb /\ not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]] /\
   (!q. not_fresh_at sa q ==> q <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, cs_extends_def,
         not_fresh_at_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) t` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) s t tn` >>
  qexistsl_tac [`gf`, `tf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          GSYM wordsTheory.word_add_n2w, arithmeticTheory.ADD_COMM,
          wordsTheory.WORD_ADD_COMM]) >>
  conj_tac >- suspend "coverage" >>
  conj_tac >-
    (irule copy_len_binop_frag_ptr >> simp[mk_inst_def] >>
     simp[Abbr `gf`, Abbr `tf`, Abbr `t`, eval_operand_def, mk_inst_def,
          op_taint_def] >>
     gvs[ptr_covers_def, op_taint_def]) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `t`, copy_len_binop_ghost_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `q <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Resume compile_with_byte_offset_frag_ptr[coverage]:
  `op_taint tf (Var out) = {}` by
    simp[Abbr `tf`, Abbr `t`, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[Abbr `gf`, Abbr `t`, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, wordsTheory.w2n_add_2,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Finalise compile_with_byte_offset_frag_ptr
