(* Straight-line setup for typed dynamic-array copying. *)
Theory typedCopyDynamicSetupPathPtr
Ancestors
 annAssignPtrLength typedCopyLoopHeaderPathPtr bodyPtrAttributeAdd
 exprSimPtrProps emitHelperProps exprSendPtr
 compileEnv emitHelper loweringStateRelDefs freshWrites
 bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
 finite_map words arithmetic list

Theorem typed_copy_emit_gt_path_ptr:
 !D ctx fn PG G tn s sa sb left right out a b.
 emit_op GT [left;right] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
 op_taint tn left = {} /\ op_taint tn right = {} /\
 op_prov G left = NONE /\ op_prov G right = NONE ==>
 ?sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
   (tn with t_var := tn.t_var |+ (out,{})) (OK sf) /\
 sf = (update_var out (bool_to_word (w2n a > w2n b)) s
        with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP (DRESTRICT G (COMPL {out})) p = FLOOKUP G p /\
   op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 `step_inst_base (mk_inst sa.cs_next_id GT [left;right] [out]) s =
   OK (update_var out (bool_to_word (w2n a > w2n b)) s)` by
   (irule step_GT >> simp[]) >>
 qexists_tac `update_var out (bool_to_word (w2n a > w2n b)) s
              with vs_inst_idx := SUC s.vs_inst_idx` >>
 conj_tac
 >- (qmatch_goalsub_abbrev_tac `OK (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     `step_prov PG G (mk_inst sa.cs_next_id GT [left;right] [out]) u =
        DRESTRICT G (COMPL {out}) /\
      step_taint (mk_inst sa.cs_next_id GT [left;right] [out]) s u tn =
        (tn with t_var := tn.t_var |+ (out,{}))` by
       simp[Abbr `u`, update_var_def, step_prov_def, set_prov_def,
         out_prov_def, step_taint_def, set_var_taint_def, mem_taint_def,
         step_writes_def, written_taint_def, store_taint_def, adopt_reset_def,
         imm_taint_def, range_bytes_def, new_site_bytes_def, out_taint_def,
         mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
         taint_component_equality, FLOOKUP_DEF, pred_setTheory.EXTENSION,
         SF CONJ_ss] >>
     qpat_x_assum `step_prov _ _ _ _ = _` (once_rewrite_tac o single o GSYM) >>
     qpat_x_assum `step_taint _ _ _ _ = _` (once_rewrite_tac o single o GSYM) >>
     irule gas_path_ptr_one_step >>
     simp[instruction_accessors, is_terminator_def, Abbr `u`, update_var_def,
       step_GT] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       step_inst_non_invoke, update_var_def] >>
     simp[GSYM mk_inst_def, update_var_def] >>
     rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
 simp[update_var_def, venom_state_component_equality] >> rpt strip_tac >>
 `p <> out` by metis_tac[] >>
 simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem typed_copy_emit_iszero_path_ptr:
 !D ctx fn PG G tn s sa sb arg out w.
 emit_op ISZERO [arg] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 eval_operand arg s = SOME w /\ op_taint tn arg = {} ==>
 ?sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
   (tn with t_var := tn.t_var |+ (out,{})) (OK sf) /\
 sf = (update_var out (bool_to_word (w = 0w)) s
        with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP (DRESTRICT G (COMPL {out})) p = FLOOKUP G p /\
   op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 qexists_tac `update_var out (bool_to_word (w = 0w)) s
              with vs_inst_idx := SUC s.vs_inst_idx` >>
 conj_tac
 >- (irule typed_copy_header_arith_path_ptr >> simp[] >>
     qexistsl [`sa.cs_next_id`, `ISZERO`, `[arg]`, `out`,
       `update_var out (bool_to_word (w = 0w)) s`] >>
     simp[update_var_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def]) >>
 simp[update_var_def, venom_state_component_equality] >> rpt strip_tac >>
 `p <> out` by metis_tac[] >>
 simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem typed_copy_capacity_check_path_ptr:
 !D ctx fn PG G tn s sa sb sc sd len gt ok n dc.
 emit_op GT [Var len; Lit (n2w dc)] sa = (Var gt,sb) /\
 emit_op ISZERO [Var gt] sb = (Var ok,sc) /\
 emit_inst ASSERT [Var ok] [] sc = ((),sd) /\
 fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
 op_prov G (Var len) = NONE /\ n <= dc /\ dc < dimword(:256) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sd.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 `n < dimword(:256)` by decide_tac >>
 `?u. gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {gt}))
    (tn with t_var := tn.t_var |+ (gt,{})) (OK u) /\
    u = (update_var gt 0w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted` by
   (drule typed_copy_emit_gt_path_ptr >>
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
    disch_then (drule_at Any) >>
    simp[w2n_n2w, LESS_MOD, bool_to_word_def] >>
    disch_then (qspecl_then [`D`,`ctx`,`fn`,`PG`,`G`,`tn`] mp_tac) >>
    gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
 qabbrev_tac `g1 = DRESTRICT G (COMPL {gt})` >>
 qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (gt,{})` >>
 qabbrev_tac `g2 = DRESTRICT g1 (COMPL {ok})` >>
 qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (ok,{})` >>
 qabbrev_tac `v = update_var ok 1w u with vs_inst_idx := SUC u.vs_inst_idx` >>
 `sc.cs_current_bb = sb.cs_current_bb /\
  LENGTH sc.cs_current_insts = SUC (LENGTH sb.cs_current_insts) /\
  ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb (LENGTH sb.cs_current_insts) =
    SOME (mk_inst sb.cs_next_id ISZERO [Var gt] [ok])` by
   metis_tac[annassign_emit_op_instruction_ptr] >>
 `gas_path_ptr D 0 ctx fn PG g1 t1 u 0 g2 t2 (OK v)` by
  (irule typed_copy_header_arith_path_ptr >> simp[] >>
   qexistsl [`sb.cs_next_id`, `ISZERO`, `[Var gt]`, `ok`, `update_var ok 1w u`] >>
   simp[Abbr `g2`, Abbr `t2`, Abbr `v`, update_var_def,
     Abbr `t1`, op_taint_def, FLOOKUP_UPDATE] >>
   simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
     eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def,
     FLOOKUP_UPDATE]) >>
 `v.vs_current_bb = sc.cs_current_bb /\
  v.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~v.vs_halted` by
   gvs[Abbr `v`, update_var_def] >>
 `gas_path_ptr D 0 ctx fn PG g2 t2 v 0 g2 t2
    (OK (v with vs_inst_idx := SUC v.vs_inst_idx))` by
  (drule_all annAssignPtrSetupTheory.annassign_emit_instruction_ptr >> strip_tac >>
   irule assert_ok_path_ptr >> simp[] >>
   qexistsl [`sc.cs_next_id`, `Var ok`, `1w`] >>
   gvs[Abbr `t2`, Abbr `v`, update_var_def, op_taint_def,
     FLOOKUP_UPDATE, eval_operand_def, lookup_var_def]) >>
 qexistsl [`g2`, `t2`, `v with vs_inst_idx := SUC v.vs_inst_idx`] >>
 conj_tac
 >- (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`g1`, `u`, `t1`] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`g2`, `v`, `t2`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
 `sd.cs_current_bb = sc.cs_current_bb /\
  LENGTH sd.cs_current_insts = SUC (LENGTH sc.cs_current_insts)` by
  gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
    emit_def, comp_return_def] >>
 `!p. not_fresh_at sa p ==> p <> gt /\ p <> ok` by
  (`~not_fresh_at sa gt /\ ~not_fresh_at sb ok` by
     metis_tac[annassign_emit_op_instruction_ptr] >>
   `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_op GT _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >> strip_tac >>
     qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _; cs_current_insts := _|> = sb`
       (once_rewrite_tac o single o GSYM) >> simp[]) >>
   rpt strip_tac >>
   `not_fresh_at sb p` by metis_tac[not_fresh_at_mono] >>
   metis_tac[]) >>
 simp[Abbr `v`, Abbr `t2`, Abbr `t1`, Abbr `g2`, Abbr `g1`,
   update_var_def, venom_state_component_equality] >>
 (conj_tac >- metis_tac[annassign_emit_op_instruction_ptr]) >>
 rpt strip_tac >>
 `p <> gt /\ p <> ok` by metis_tac[] >>
 simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

(* A clean store makes the entire written word robust, not just its
   current concrete contents. *)
Theorem typed_copy_clean_store_word:
 !off w s tm m.
 mem_agree_outside (tm DIFF {i | off <= i /\ i < off+32})
   (mstore off w s).vs_memory m ==> mem_word_at off m = w
Proof
 rpt gen_tac >> strip_tac >>
 `mem_bytes_at off 32 (mstore off w (s with vs_memory := m)).vs_memory =
  mem_bytes_at off 32 m` by
   (irule annAssignPtrStoreTheory.annassign_clean_store_observation_ptr >>
    metis_tac[]) >>
 `mem_word_at off (mstore off w (s with vs_memory := m)).vs_memory =
  mem_word_at off m` by
   gvs[valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def] >>
 gvs[valueEncodingPropsTheory.mstore_mem_word_at_same]
QED

Theorem typed_copy_emit_clean_mstore_path_ptr:
 !D ctx fn PG G tn s sa sb dst value a w.
 emit_inst MSTORE [Var dst;value] [] sa = ((),sb) /\ fn_has_code sa sb fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
 eval_operand value s = SOME w /\ op_taint tn value = {} ==>
 ?sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 G
  (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) (OK sf) /\
 sf = (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!m. mem_agree_outside
    (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) sf.vs_memory m ==>
    mem_word_at (w2n a) m = w) /\
 (!i. i < w2n a \/ w2n a+32 <= i ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annAssignPtrSetupTheory.annassign_emit_instruction_ptr >> strip_tac >>
 `step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
    (mstore (w2n a) w s) = G /\
  step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
    (mstore (w2n a) w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})` by
   (irule exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame >>
    simp[]) >>
 qexists_tac `mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx` >>
 conj_tac
 >- (`gas_path_ptr D 0 ctx fn PG G tn s 0
       (step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
         (mstore (w2n a) w s))
       (step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
         (mstore (w2n a) w s) tn)
       (OK (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx))` by
       (irule annAssignPtrStoreTheory.annassign_mstore_path_ptr >> simp[] >>
        metis_tac[]) >> gvs[]) >>
 `sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
   (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
    simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      emit_def, comp_return_def] >> strip_tac >> gvs[]) >>
 `!m. mem_agree_outside
    (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
    (mstore (w2n a) w s).vs_memory m ==> mem_word_at (w2n a) m = w` by
   (rpt strip_tac >> irule typed_copy_clean_store_word >> metis_tac[]) >>
 `!i. i < w2n a \/ w2n a+32 <= i ==>
   mem_bytes_at i 1 (mstore (w2n a) w s).vs_memory =
   mem_bytes_at i 1 s.vs_memory` by
   (rpt strip_tac >>
    irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
 simp[] >> gvs[venomStateTheory.mstore_def, venom_state_component_equality] >>
 first_assum ACCEPT_TAC
QED

Theorem typed_copy_emit_offset_path_ptr:
 !D ctx fn PG G tn s sa sb root out a off sz.
 emit_op ADD [Var root;Lit(n2w off)] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ptr_covers G tn root s (off+sz) /\ lookup_var root s = SOME a /\
 w2n a+off+sz < dimword(:256) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf = (update_var out (n2w(w2n a+off)) s with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 lookup_var out sf = SOME(n2w(w2n a+off)) /\ ptr_covers Gf tnf out sf sz /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
 `a + n2w off = n2w(w2n a+off)` by simp[GSYM word_add_n2w] >>
 `?Gf tnf sf.
   gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
   sf = (update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
   Gf = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root;Lit(n2w off)] [out])
      (update_var out (a+n2w off) s) /\
   tnf = step_taint (mk_inst sa.cs_next_id ADD [Var root;Lit(n2w off)] [out]) s
      (update_var out (a+n2w off) s) tn /\
   tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p))` by
   (drule (attribute_emit_binop_path_ptr |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
    simp[eval_operand_def, op_taint_def] >>
    disch_then (drule_at Any) >>
    disch_then (qspecl_then [`tn`,`fn`,`ctx`,`PG`,`G`,`D`] mp_tac) >>
    gvs[op_taint_def] >> metis_tac[]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >>
 `sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
  ~not_fresh_at sa out` by metis_tac[annassign_emit_op_instruction_ptr] >>
 `ptr_covers Gf tnf out sf sz` by
   (pure_asm_rewrite_tac[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
    irule exprSimPtrLiteralOpsTheory.literal_add_ptr_covers >>
    gvs[ptr_covers_def] >> qexistsl [`b`,`sz'`] >> simp[] >> decide_tac) >>
 simp[] >>
 simp[update_var_def, venom_state_component_equality, lookup_var_def, FLOOKUP_UPDATE] >>
 rpt strip_tac >> `p <> out` by metis_tac[] >>
 gvs[update_var_def] >> metis_tac[]
QED

Theorem typed_copy_dynarray_setup_path_ptr:
 !D ctx fn PG G tn s sa sb sc sd se sf sg len gt ok src dst sp dp n dc scap ss ds a b.
 emit_op GT [Var len;Lit(n2w dc)] sa = (Var gt,sb) /\
 emit_op ISZERO [Var gt] sb = (Var ok,sc) /\
 emit_inst ASSERT [Var ok] [] sc = ((),sd) /\
 emit_inst MSTORE [Var dst;Var len] [] sd = ((),se) /\
 emit_op ADD [Var src;Lit 32w] se = (Var sp,sf) /\
 emit_op ADD [Var dst;Lit 32w] sf = (Var dp,sg) /\
 fn_has_code sa sg fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa len /\
 lookup_var len s = SOME(n2w n) /\ op_taint tn (Var len) = {} /\
 op_prov G (Var len) = NONE /\ n <= dc /\ dc < dimword(:256) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (32+scap*ss) /\ ptr_covers G tn dst s (32+dc*ds) /\
 w2n a+32+scap*ss < dimword(:256) /\ w2n b+32+dc*ds < dimword(:256) ==>
 ?Gf tnf t.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
 t.vs_current_bb = sg.cs_current_bb /\
 t.vs_inst_idx = LENGTH sg.cs_current_insts /\ ~t.vs_halted /\
 lookup_var len t = SOME(n2w n) /\ op_taint tnf (Var len) = {} /\
 op_prov Gf (Var len) = NONE /\
 lookup_var sp t = SOME(n2w(w2n a+32)) /\
 lookup_var dp t = SOME(n2w(w2n b+32)) /\
 ptr_covers Gf tnf sp t (scap*ss) /\ ptr_covers Gf tnf dp t (dc*ds) /\
 (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
   mem_word_at (w2n b) m = n2w n) /\
 (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. i < w2n b \/ w2n b+32 <= i ==>
   mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
 rpt gen_tac >> strip_tac >>
 `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\
  cs_extends sd se /\ cs_extends se sf /\ cs_extends sf sg` by
   metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
             fragExecTheory.cs_extends_emit_inst] >>
 `cs_extends se sg /\ cs_extends sd sg /\ cs_extends sc sg /\
  cs_extends sb sg` by metis_tac[cs_extends_trans] >>
 qspecl_then [`sa`,`sb`,`sg`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
 simp[] >> strip_tac >>
 qspecl_then [`sb`,`sc`,`sg`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
 simp[] >> strip_tac >>
 qspecl_then [`sc`,`sd`,`sg`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
 simp[] >> strip_tac >>
 qspecl_then [`sd`,`se`,`sg`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
 simp[] >> strip_tac >>
 qspecl_then [`se`,`sf`,`sg`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
 simp[] >> strip_tac >>
 `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var = sd.cs_next_var /\ sd.cs_next_var = se.cs_next_var /\
  se.cs_next_var <= sf.cs_next_var` by
   metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
             placeMemoryCodeLayoutTheory.emit_inst_next_var] >>
 `!p. not_fresh_at sa p ==> not_fresh_at sd p /\ not_fresh_at se p /\
   not_fresh_at sf p` by
   (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
    simp[] >> decide_tac) >>
 drule_all typed_copy_capacity_check_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`]
   (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `u` strip_assume_tac)))) >>
 `lookup_var dst u = SOME b /\ lookup_var src u = SOME a /\
  lookup_var len u = SOME(n2w n) /\ op_taint t1 (Var len) = {}` by metis_tac[] >>
 `ptr_covers g1 t1 dst u 32 /\ ptr_covers g1 t1 src u (32+scap*ss) /\
  ptr_covers g1 t1 dst u (32+dc*ds)` by
   (gvs[ptr_covers_def] >> rpt conj_tac >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
 `eval_operand (Var len) u = SOME(n2w n)` by simp[eval_operand_def] >>
 drule_all typed_copy_emit_clean_mstore_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] (qx_choose_then `r` strip_assume_tac)) >>
 qabbrev_tac `t2 = t1 with t_mem := t1.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32}` >>
 `ptr_covers g1 t2 src r (scap*ss+32) /\
  ptr_covers g1 t2 dst r (dc*ds+32) /\
  lookup_var src r = SOME a /\ lookup_var dst r = SOME b` by
   (gvs[ptr_covers_def, Abbr `t2`, venomStateTheory.mstore_def, lookup_var_def, op_taint_def] >>
    metis_tac[]) >>
 qpat_assum `emit_op ADD [Var src;Lit 32w] se = _` mp_tac >>
 disch_then (mp_then Any mp_tac (typed_copy_emit_offset_path_ptr |> SPEC_ALL |> Q.INST [`off` |-> `32`] |> SRULE [])) >>
 disch_then (qspecl_then [`t2`,`scap*ss`,`r`,`fn`,`ctx`,`a`,`PG`,`g1`,`D`] mp_tac) >>
 (impl_tac >- (simp[GSYM ghostPcTransportPtrTheory.ptr_covers_inst_idx] >> metis_tac[ghostPcTransportPtrTheory.ptr_covers_inst_idx])) >>
 qmatch_goalsub_abbrev_tac `OK v` >>
 disch_then (qx_choose_then `g2` (qx_choose_then `t3` strip_assume_tac)) >>
 `lookup_var dst v = SOME b /\ ptr_covers g2 t3 dst v (dc*ds+32)` by
   (gvs[ptr_covers_def] >> metis_tac[]) >>
 qpat_assum `emit_op ADD [Var dst;Lit 32w] sf = _` mp_tac >>
 disch_then (mp_then Any mp_tac (typed_copy_emit_offset_path_ptr |> SPEC_ALL |> Q.INST [`off` |-> `32`] |> SRULE [])) >>
 disch_then (qspecl_then [`t3`,`dc*ds`,`v`,`fn`,`ctx`,`b`,`PG`,`g2`,`D`] mp_tac) >>
 (impl_tac >- (simp[Abbr `v`,update_var_def,ptr_covers_def,lookup_var_def] >> gvs[ptr_covers_def,lookup_var_def])) >>
 qmatch_goalsub_abbrev_tac `OK w` >>
 disch_then (qx_choose_then `g3` (qx_choose_then `t4` strip_assume_tac)) >>
 qexistsl [`g3`,`t4`,`w`] >>
 conj_tac >-
   (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
    qexistsl [`g1`,`u`,`t1`] >> conj_tac >- first_assum ACCEPT_TAC >>
    irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
    qexistsl [`g1`,`r`,`t2`] >> conj_tac >- first_assum ACCEPT_TAC >>
    irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
    qexistsl [`g2`,`v`,`t3`] >> conj_tac >> first_assum ACCEPT_TAC) >>
 `!p. not_fresh_at sa p ==> lookup_var p w = lookup_var p s /\
   FLOOKUP g3 p = FLOOKUP G p /\ op_taint t4 (Var p) = op_taint tn (Var p)` by
   (gen_tac >> disch_tac >>
    `lookup_var p r = lookup_var p u /\ op_taint t2 (Var p) = op_taint t1 (Var p)` by
      gvs[Abbr `t2`,op_taint_def,lookup_var_def,venomStateTheory.mstore_def] >>
    metis_tac[]) >>
 `not_fresh_at sf sp` by metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
 `ptr_covers g3 t4 sp w (scap*ss)` by
   (gvs[ptr_covers_def,Abbr `w`,Abbr `v`,lookup_var_def,update_var_def] >> metis_tac[]) >>
 simp[Abbr `w`,Abbr `v`,update_var_def,Abbr `t2`,op_taint_def,op_prov_def,
      ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
 conj_tac >- gvs[op_prov_def] >>
 conj_tac >-
   (gvs[venomStateTheory.mstore_def,venom_state_component_equality]) >>
 gvs[venom_state_component_equality]
QED
