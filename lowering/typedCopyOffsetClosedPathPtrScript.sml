(* Closed pointer offsets, including zero-capacity endpoint children. *)
Theory typedCopyOffsetClosedPathPtr
Ancestors
 typedCopyOffsetPathPtr typedCopyPtr annAssignPtrLength fragGasPathPtr
 fragExec arithmetic context compileEnv loweringStateRelDefs emitHelper
 emitHelperProps exprLoweringProps bodyPtrDefs words venomState finite_map
 ptrDiscipline venomInst

Theorem compile_with_byte_offset_closed_path_ptr:
 !D ctx func PG root off sa op sb G tn s a cap n.
 compile_with_byte_offset (Var root) off sa = (op,sb) /\
 not_fresh_at sa root /\ lookup_var root s = SOME a /\
 ptr_covers G tn root s cap /\ off <= cap /\ off+n <= cap /\
 w2n a + off < dimword(:256) /\ fn_has_code sa sb func /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
 cs_extends sa sb /\
 ?p Gf tnf sf.
 op = Var p /\ lookup_var p sf = SOME (n2w (w2n a+off)) /\
 ptr_covers Gf tnf p sf n /\ not_fresh_at sb p /\
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!q. not_fresh_at sa q ==>
 lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
 op_taint tnf (Var q) = op_taint tn (Var q))
Proof
 rpt gen_tac >> strip_tac >> Cases_on `off < cap`
 >- (irule compile_with_byte_offset_path_ptr >> simp[] >>
     qexistsl [`root`,`cap`] >> simp[]) >>
 `off = cap /\ n = 0` by decide_tac >>
 Cases_on `off = 0`
 >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
     conj_tac >- simp[cs_extends_def] >>
     qexistsl [`G`,`tn`,`s`] >> simp[] >>
     conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
     qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
 gvs[compile_with_byte_offset_def] >>
 `?out. op = Var out` by
  (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> metis_tac[]) >>
 gvs[] >>
 `cs_extends sa sb /\ not_fresh_at sb out /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w cap)] [out]] /\
  (!q. not_fresh_at sa q ==> q <> out)` by
  (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, cs_extends_def,
       not_fresh_at_def] >> metis_tac[]) >>
 asm_rewrite_tac[] >>
 qabbrev_tac `t = update_var out (a + n2w cap) s` >>
 qabbrev_tac `gf = step_prov PG G
   (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w cap)] [out]) t` >>
 qabbrev_tac `tf = step_taint
   (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w cap)] [out]) s t tn` >>
 qexistsl [`gf`,`tf`,`t with vs_inst_idx := SUC s.vs_inst_idx`] >>
 conj_tac >-
  simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       GSYM word_add_n2w, ADD_COMM, WORD_ADD_COMM] >>
 conj_tac >- suspend "coverage" >>
 simp[] >> conj_tac >- suspend "path" >>
 simp[Abbr `tf`, Abbr `gf`, Abbr `t`, copy_len_binop_ghost_frame,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
 conj_tac >-
  (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
 simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Resume compile_with_byte_offset_closed_path_ptr[coverage]:
 `op_taint tf (Var out) = {}` by
  simp[Abbr `tf`, Abbr `t`, copy_len_binop_ghost_frame] >>
 gvs[ptr_covers_def] >>
 `cap < dimword(:256)` by decide_tac >>
 simp[Abbr `gf`, Abbr `t`, step_prov_def, set_prov_def, out_prov_def,
      first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
      lookup_var_def, update_var_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac
QED

Resume compile_with_byte_offset_closed_path_ptr[path]:
 `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx =
 SOME (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w cap)] [out])` by
  (drule_all fn_has_code_same_block >> strip_tac >> qexists `bb` >>
   simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
 simp[Abbr `gf`, Abbr `tf`, Abbr `t`] >>
 qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
 irule annassign_copy_len_binop_path_ptr >>
 simp[eval_operand_def, op_taint_def] >>
 gvs[ptr_covers_def, op_taint_def] >> metis_tac[]
QED

Finalise compile_with_byte_offset_closed_path_ptr
