(* Clean field addresses, including empty one-past-end fields. *)
Theory widenedAssignPtrCopyOffsets
Ancestors assignBasePtrByteOffset assignBasePtrStoragePath typedCopyPtr
  decoderGhostFramePtr bodyPtrAttributeAdd typedCopyLoopHeaderPtr
  context compileEnv emitHelper emitHelperProps fragExec fragGasPathPtr
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics venomInst
  words finite_map pred_set list arithmetic

Theorem widened_assign_with_byte_offset_counted:
  !root off sa op sb G tn s a total n fn ctx D PG.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    op_taint tn (Var root) = {} /\
    (0 < n ==> ptr_covers G tn root s total) /\ off+n <= total /\
    w2n a + off < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?p Gf tf u.
      op = Var p /\ not_fresh_at sb p /\
      lookup_var p u = SOME (n2w (w2n a+off)) /\
      op_taint tf (Var p) = {} /\
      (0 < n ==> ptr_covers Gf tf p u n) /\
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
      simp[cj 1 gas_path_ptr_rules, venom_state_component_equality] >>
      rpt strip_tac >> gvs[ptr_covers_def] >> decide_tac) >>
  drule_all assign_base_with_byte_offset_code >> strip_tac >>
  drule_all assign_base_with_byte_offset_layout >> strip_tac >> simp[] >>
  qabbrev_tac `v = update_var p (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) v` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) s v tn` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [p]) s =
    OK v` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def, Abbr `v`] >>
  `0 < n ==> ptr_covers gf tf p v n` by
    (strip_tac >> simp[Abbr `gf`, Abbr `tf`, Abbr `v`] >>
     irule assign_base_with_byte_offset_coverage >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac) >>
  qexistsl_tac [`gf`, `tf`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
                  GSYM word_add_n2w, WORD_ADD_COMM] >>
  conj_tac >- simp[Abbr `tf`, Abbr `v`, copy_len_binop_ghost_frame, op_taint_def] >>
  conj_tac >- gvs[ptr_covers_def] >>
  conj_tac
  >- (simp[Abbr `gf`, Abbr `tf`, Abbr `v`] >>
      mp_tac (Q.SPEC `s` assign_base_copy_binop_counted) >>
      simp[] >> disch_then irule >> simp[op_taint_def] >>
      qexists_tac `bb` >> gvs[]) >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `v`, update_var_def,
       copy_len_binop_ghost_frame, lookup_var_def, FLOOKUP_UPDATE,
       step_prov_other_output, mk_inst_def] >>
  fs[venom_state_component_equality] >>
  simp[step_taint_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def,
       mem_taint_def, update_var_def, new_site_bytes_def, FLOOKUP_DEF,
       EXTENSION, SF CONJ_ss]
QED
