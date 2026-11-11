(* Checked runtime data reads and their resource frame for immutable copies. *)
Theory reasonCodeLoadPtr
Ancestors
  reasonCodePtr reasonCodeOffsetPtr reasonTupleCopyPtr emitHelper
  venomExecSemantics venomInst venomInstProofs venomState finite_map words ptrSafeRun
  ptrDiscipline context compileEnv loweringStateRelDefs fragExec codegenRel

Theorem reason_code_dload_resources_ptr:
  emit_inst DLOAD [src] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from 0 s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf (Var out) = {} /\ FLOOKUP Gf out = NONE /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_memory = s.vs_memory /\
    sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. p <> out ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `t = update_var out (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id DLOAD [src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id DLOAD [src] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (unabbrev_all_tac >> irule reason_code_dload_path_ptr >> simp[] >>
      simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  `new_site_bytes s t = {}` by
    simp[Abbr `t`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `Gf`, Abbr `tnf`, mem_taint_def] >>
  simp[Abbr `t`, update_var_def, lookup_var_def,
       step_prov_def, set_prov_def, dload_output_clean,
       step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, store_taint_def, adopt_reset_def,
       step_writes_def, written_taint_def, source_memory_write_ranges_def,
       range_bytes_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >> simp[]
QED

Theorem reason_code_emit_dload_shape:
  emit_op DLOAD [src] sa = (r,sb) ==>
  ?out. r = Var out /\
    emit_inst DLOAD [src] [out]
      (sa with cs_next_var := sa.cs_next_var + 1) = ((),sb) /\
    (!p. not_fresh_at sa p ==> p <> out)
Proof
  simp[emit_op_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
       emit_inst_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >> simp[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem reason_code_load_path_ptr:
  emit_op DLOAD [src] sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from 0 s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand r sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf r = {} /\ op_prov Gf r = NONE /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_memory = s.vs_memory /\
    sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule reason_code_emit_dload_shape >> strip_tac >> gvs[] >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var + 1) sb func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) reason_code_dload_resources_ptr >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[eval_operand_def, op_prov_def] >>
  gen_tac >> strip_tac >> `p <> out` by metis_tac[] >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[]
QED
