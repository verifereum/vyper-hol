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
