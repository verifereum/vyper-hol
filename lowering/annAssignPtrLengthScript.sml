(* Counted straight-line length calculation.  Fixed-run facts are used
   only for instruction safety and ghost projections. *)
Theory annAssignPtrLength
Ancestors
 annAssignPtrSetup typedCopyPtr fragGasSeqPtr fragGasPathPtr
 bodyPtrDefs ptrDiscipline venomInst venomInstProofs venomExecSemantics
 venomState finite_map emitHelper emitHelperProps context compileEnv loweringStateRelDefs
 exprLoweringProps fragExec

Theorem annassign_mload_path_ptr:
 !D ctx func PG G tn s bb id src out a.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
 ptr_covers G tn src s 32 /\ lookup_var src s = SOME a ==>
 gas_path_ptr D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MLOAD [Var src] [out])
     (update_var out (mload (w2n a) s) s))
   (step_taint (mk_inst id MLOAD [Var src] [out]) s
     (update_var out (mload (w2n a) s) s) tn)
   (OK (update_var out (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
    OK (update_var out (mload (w2n a) s) s)` by
   (irule step_MLOAD >> simp[eval_operand_def]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MLOAD [Var src] [out])
     (update_var out (mload (w2n a) s) s))
   (step_taint (mk_inst id MLOAD [Var src] [out]) s
     (update_var out (mload (w2n a) s) s) tn)
   (OK (update_var out (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_mload >> simp[]) >>
 drule (cj 2 gas_path_ptr_rules) >>
 simp[update_var_def] >> disch_then irule >>
 irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem annassign_copy_len_binop_path_ptr:
 !D ctx func PG G tn s bb id opc left right out f a b.
 (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [left;right] [out]) /\
 eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
 op_taint tn left = {} /\ op_taint tn right = {} ==>
 gas_path_ptr D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out (f a b) s))
   (step_taint (mk_inst id opc [left;right] [out]) s (update_var out (f a b) s) tn)
   (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out (f a b) s)` by
   (gvs[] >> FIRST [irule step_ADD, irule step_AND] >> simp[]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out (f a b) s))
   (step_taint (mk_inst id opc [left;right] [out]) s (update_var out (f a b) s) tn)
   (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))` by
   (gvs[] >> drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
 drule (cj 2 gas_path_ptr_rules) >>
 simp[update_var_def] >> disch_then irule >>
 irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem annassign_copy_len_not_path_ptr:
 !D ctx func PG G tn s bb id x out a.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id NOT [x] [out]) /\
 eval_operand x s = SOME a /\ op_taint tn x = {} ==>
 gas_path_ptr D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id NOT [x] [out]) (update_var out (~a) s))
   (step_taint (mk_inst id NOT [x] [out]) s (update_var out (~a) s) tn)
   (OK (update_var out (~a) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id NOT [x] [out]) s = OK (update_var out (~a) s)` by
   (irule step_NOT >> simp[]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id NOT [x] [out]) (update_var out (~a) s))
   (step_taint (mk_inst id NOT [x] [out]) s (update_var out (~a) s) tn)
   (OK (update_var out (~a) s with vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_copy_len_not >> simp[]) >>
 drule (cj 2 gas_path_ptr_rules) >>
 simp[update_var_def] >> disch_then irule >>
 irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem annassign_emit_op_instruction_ptr:
 !opc args out sa sb func.
 emit_op opc args sa = (Var out,sb) /\ fn_has_code sa sb func ==>
 sb.cs_current_bb = sa.cs_current_bb /\
 LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
 ~not_fresh_at sa out /\
 ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH sa.cs_current_insts) =
        SOME (mk_inst sa.cs_next_id opc args [out])
Proof
 rpt gen_tac >> strip_tac >>
 `sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id opc args [out]] /\ ~not_fresh_at sa out` by
   gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       not_fresh_at_def] >>
 drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
 first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem annassign_emit_len_binop_path_ptr:
 !opc f D ctx func PG G tn s sa sb left right out a b.
 (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
 emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
 op_taint tn left = {} /\ op_taint tn right = {} ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\ lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >> (
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 qexistsl [
  `step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out]) (update_var out (f a b) s)`,
  `step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s (update_var out (f a b) s) tn`,
  `update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx`] >>
 conj_tac >- (irule annassign_copy_len_binop_path_ptr >> simp[] >> metis_tac[]) >>
 qspecl_then [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`] mp_tac copy_len_binop_ghost_frame >>
 disch_then (qspecl_then [`opc`,`left`,`right`,`out`,`f a b`] mp_tac) >>
 simp[update_var_def, lookup_var_def] >> strip_tac >> gvs[] >>
 simp[FLOOKUP_UPDATE, venom_state_component_equality] >>
 conj_tac >- simp[step_taint_def, set_var_taint_def, adopt_reset_def,
                  imm_taint_def, mk_inst_def] >>
 rpt strip_tac >>
 `p <> out` by metis_tac[] >> simp[])
QED

Theorem annassign_emit_len_not_path_ptr:
 !D ctx func PG G tn s sa sb x out a.
 emit_op NOT [x] sa = (Var out,sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 eval_operand x s = SOME a /\ op_taint tn x = {} ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\ lookup_var out sf = SOME (~a) /\ op_taint tnf (Var out) = {} /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 qexistsl [
  `step_prov PG G (mk_inst sa.cs_next_id NOT [x] [out]) (update_var out (~a) s)`,
  `step_taint (mk_inst sa.cs_next_id NOT [x] [out]) s (update_var out (~a) s) tn`,
  `update_var out (~a) s with vs_inst_idx := SUC s.vs_inst_idx`] >>
 conj_tac >- (irule annassign_copy_len_not_path_ptr >> simp[] >> metis_tac[]) >>
 qspecl_then [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`,`x`,`out`,`~a`] mp_tac
   copy_len_not_ghost_frame >>
 simp[update_var_def, lookup_var_def] >> strip_tac >> gvs[] >>
 simp[FLOOKUP_UPDATE, venom_state_component_equality] >>
 conj_tac >- simp[step_taint_def, set_var_taint_def, adopt_reset_def,
                  imm_taint_def, mk_inst_def] >>
 rpt strip_tac >>
 `p <> out` by metis_tac[] >> simp[]
QED

Theorem annassign_emit_mload_clean_path_ptr:
 !D ctx func PG G tn s sa sb src out a.
 emit_op MLOAD [Var src] sa = (Var out,sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
 (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\ lookup_var out sf = SOME (mload (w2n a) s) /\
 op_taint tnf (Var out) = {} /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
 qabbrev_tac `Gf = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
 qabbrev_tac `tnf = step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
 qexistsl [`Gf`,`tnf`,`t with vs_inst_idx := SUC s.vs_inst_idx`] >>
 conj_tac >-
  (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >> qunabbrev_tac `t` >>
   irule annassign_mload_path_ptr >> simp[] >> metis_tac[]) >>
 `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
  (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >> simp[eval_operand_def]) >>
 `tnf.t_imm = tn.t_imm` by
  simp[Abbr `tnf`, step_taint_def, set_var_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
 gvs[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
     venom_state_component_equality] >>
 rpt strip_tac >> `p <> out` by metis_tac[] >>
 simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
      out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
      op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem annassign_copy_len_decompose_ptr:
 !src count_op sa sb.
 compile_bytestring_copy_len src sa = (count_op,sb) ==>
 ?v1 vm v2 v3 v4 sc1 scm sc2 sc3.
 count_op = Var v4 /\
 emit_op MLOAD [src] sa = (Var v1,sc1) /\
 emit_op NOT [Lit 31w] sc1 = (Var vm,scm) /\
 emit_op ADD [Var v1;Lit 31w] scm = (Var v2,sc2) /\
 emit_op AND [Var v2;Var vm] sc2 = (Var v3,sc3) /\
 emit_op ADD [Var v3;Lit 32w] sc3 = (Var v4,sb) /\
 cs_extends sa sc1 /\ cs_extends sc1 scm /\ cs_extends scm sc2 /\
 cs_extends sc2 sc3 /\ cs_extends sc3 sb /\
 not_fresh_at sc1 v1 /\ not_fresh_at scm vm /\
 (!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\ not_fresh_at scm p /\
    not_fresh_at sc2 p /\ not_fresh_at sc3 p)
Proof
 rpt gen_tac >>
 simp[compile_bytestring_copy_len_def, comp_bind_def] >>
 ntac 4 (pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def]) >> strip_tac >>
 `?v1. src_len = Var v1` by
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >>
 `?vm. mask = Var vm` by
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >>
 `?v2. padded_len = Var v2` by
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >>
 `?v3. rounded = Var v3` by
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >>
 `?v4. count_op = Var v4` by
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >>
 gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
     fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
     cs_extends_def, ASCIInumbersTheory.toString_11] >>
 rpt strip_tac >> decide_tac
QED


Theorem annassign_length_prefix_extend_ptr:
 !opc f D ctx func PG G0 tn0 s0 sa G tn s sc sd left right out a b.
 gas_path_ptr D 0 ctx func PG G0 tn0 s0 0 G tn (OK s) /\
 (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
 emit_op opc [left;right] sc = (Var out,sd) /\ fn_has_code sc sd func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
 eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
 op_taint tn left = {} /\ op_taint tn right = {} /\
 (s with <|vs_vars := s0.vs_vars; vs_inst_idx := s0.vs_inst_idx|>) = s0 /\
 s.vs_memory = s0.vs_memory /\ tn.t_mem = tn0.t_mem /\
 tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p s = lookup_var p s0 /\
   FLOOKUP G p = FLOOKUP G0 p /\ op_taint tn (Var p) = op_taint tn0 (Var p)) /\
 (!p. not_fresh_at sa p ==> not_fresh_at sc p) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G0 tn0 s0 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sd.cs_current_bb /\ sf.vs_inst_idx = LENGTH sd.cs_current_insts /\
 ~sf.vs_halted /\ lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
 (sf with <|vs_vars := s0.vs_vars; vs_inst_idx := s0.vs_inst_idx|>) = s0 /\
 sf.vs_memory = s0.vs_memory /\ tnf.t_mem = tn0.t_mem /\
 tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s0 /\
   FLOOKUP Gf p = FLOOKUP G0 p /\ op_taint tnf (Var p) = op_taint tn0 (Var p))
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all annassign_emit_len_binop_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`,`G`] strip_assume_tac) >>
 qexistsl [`Gf`,`tnf`,`sf`] >>
 conj_tac >-
  (drule_all gas_path_ptr_then >> simp[]) >>
 `(sf with <|vs_vars := s0.vs_vars; vs_inst_idx := s0.vs_inst_idx|>) = s0` by
   fs[venom_state_component_equality] >>
 simp[] >> rpt strip_tac >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
 metis_tac[]
QED

Theorem annassign_bytestring_copy_len_path_ptr:
 !D ctx func PG G tn s sa sb src count_op a.
 compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\ fn_has_code sa sb func /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
 (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 eval_operand count_op sf = SOME ((mload (w2n a) s + 31w && ~31w) + 32w) /\
 op_taint tnf count_op = {} /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = s.vs_memory /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule annassign_copy_len_decompose_ptr >> strip_tac >> gvs[] >>
 `cs_extends sc1 sb /\ cs_extends scm sb /\ cs_extends sc2 sb` by
  metis_tac[cs_extends_trans] >>
 `fn_has_code sa sc1 func /\ fn_has_code sc1 sb func` by
  metis_tac[fn_has_code_split] >>
 `fn_has_code sc1 scm func /\ fn_has_code scm sb func` by
  metis_tac[fn_has_code_split] >>
 `fn_has_code scm sc2 func /\ fn_has_code sc2 sb func` by
  metis_tac[fn_has_code_split] >>
 `fn_has_code sc2 sc3 func /\ fn_has_code sc3 sb func` by
  metis_tac[fn_has_code_split] >>
 drule_all annassign_emit_mload_clean_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`]
   (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac)) >>
 qpat_x_assum `compile_bytestring_copy_len _ _ = _` kall_tac >>
 qpat_x_assum `emit_op MLOAD _ _ = _` kall_tac >>
 qpat_x_assum `ptr_covers _ _ _ _ _` kall_tac >>
 qpat_x_assum `!i. _ ==> i NOTIN _` kall_tac >>
 (* the mask *)
 `op_taint tn1 (Lit 31w) = {}` by simp[op_taint_def] >>
 qspecl_then [`D`,`ctx`,`func`,`PG`,`G1`,`tn1`,`s1`,`sc1`,`scm`,`Lit 31w`,
              `vm`,`31w`] mp_tac annassign_emit_len_not_path_ptr >>
 (impl_tac >- simp[eval_operand_def]) >>
 disch_then (qx_choosel_then [`Gm`,`tnm`,`sm`] strip_assume_tac) >>
 (* padded length *)
 `lookup_var v1 sm = SOME (mload (w2n a) s) /\ op_taint tnm (Var v1) = {} /\
  op_taint tnm (Lit 31w) = {}` by
  (qpat_assum `!p. not_fresh_at sc1 p ==> _` (qspec_then `v1` mp_tac) >>
   simp[op_taint_def]) >>
 qspecl_then [`ADD`,`word_add`,`D`,`ctx`,`func`,`PG`,`Gm`,`tnm`,`sm`,`scm`,
              `sc2`,`Var v1`,`Lit 31w`,`v2`,`mload (w2n a) s`,`31w`] mp_tac
   annassign_emit_len_binop_path_ptr >>
 (impl_tac >- simp[eval_operand_def]) >>
 disch_then (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac) >>
 (* rounded length *)
 `lookup_var vm s2 = SOME (~31w) /\ op_taint tn2 (Var vm) = {}` by
  (qpat_assum `!p. not_fresh_at scm p ==> _` (qspec_then `vm` mp_tac) >>
   simp[]) >>
 qspecl_then [`AND`,`word_and`,`D`,`ctx`,`func`,`PG`,`G2`,`tn2`,`s2`,`sc2`,
              `sc3`,`Var v2`,`Var vm`,`v3`,`mload (w2n a) s + 31w`,`~31w`] mp_tac
   annassign_emit_len_binop_path_ptr >>
 (impl_tac >- simp[eval_operand_def]) >>
 disch_then (qx_choosel_then [`G3`,`tn3`,`s3`] strip_assume_tac) >>
 (* count *)
 `op_taint tn3 (Lit 32w) = {}` by simp[op_taint_def] >>
 qspecl_then [`ADD`,`word_add`,`D`,`ctx`,`func`,`PG`,`G3`,`tn3`,`s3`,`sc3`,
              `sb`,`Var v3`,`Lit 32w`,`v4`,`mload (w2n a) s + 31w && ~31w`,`32w`]
   mp_tac annassign_emit_len_binop_path_ptr >>
 (impl_tac >- simp[eval_operand_def]) >>
 disch_then (qx_choosel_then [`G4`,`tn4`,`s4`] strip_assume_tac) >>
 `gas_path_ptr D 0 ctx func PG G tn s 0 G4 tn4 (OK s4)` by
  (ntac 4 (irule (SRULE [] (INST [``n:num`` |-> ``0:num``, ``m:num`` |-> ``0:num``]
                     gas_path_ptr_then)) >>
           first_assum (irule_at Any)) >>
   first_assum ACCEPT_TAC) >>
 `!p. not_fresh_at sa p ==> lookup_var p s4 = lookup_var p s /\
    FLOOKUP G4 p = FLOOKUP G p /\ op_taint tn4 (Var p) = op_taint tn (Var p)` by
  (gen_tac >> strip_tac >>
   `not_fresh_at sc1 p /\ not_fresh_at scm p /\ not_fresh_at sc2 p /\
    not_fresh_at sc3 p` by metis_tac[] >>
   qpat_x_assum `!p. not_fresh_at sa p ==> lookup_var _ _ = _ /\ _`
     (qspec_then `p` mp_tac) >>
   qpat_x_assum `!p. not_fresh_at sc1 p ==> _` (qspec_then `p` mp_tac) >>
   qpat_x_assum `!p. not_fresh_at scm p ==> _` (qspec_then `p` mp_tac) >>
   qpat_x_assum `!p. not_fresh_at sc2 p ==> _` (qspec_then `p` mp_tac) >>
   qpat_x_assum `!p. not_fresh_at sc3 p ==> _` (qspec_then `p` mp_tac) >>
   simp[]) >>
 `(s4 with <|vs_vars := s.vs_vars;
              vs_inst_idx := LENGTH sa.cs_current_insts|>) = s` by
  fs[venom_state_component_equality] >>
 qexistsl [`G4`,`tn4`,`s4`] >> simp[eval_operand_def]
QED
