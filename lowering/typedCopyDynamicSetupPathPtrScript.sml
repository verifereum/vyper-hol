(* Straight-line setup for typed dynamic-array copying. *)
Theory typedCopyDynamicSetupPathPtr
Ancestors
 annAssignPtrLength typedCopyLoopHeaderPathPtr bodyPtrAttributeAdd
 exprSimPtrProps emitHelperProps
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
