(* Runtime-count control for memory-to-slot word loops. *)
Theory fullStoreSlotsWordCode
Ancestors
  fullStoreSlotsProbe fragGasCopyLoop context emitHelperProps
  fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport instMemFrontier fragExecMem
  fragExec memSafeRun bodyPtrDefs ptrDiscipline venomState venomInst
  ptrSafeRun codegenRel contextCodegenRel unitTransformDefs
  venomExecSemantics venomExecProofs
  finite_map pred_set list rich_list arithmetic words

Theorem store_slots_word_eq_origin_ptr:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [left;right] [out]) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out (bool_to_word (x=y)) s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  `step_inst_base (mk_inst id EQ [left;right] [out]) s =
    OK (update_var out (bool_to_word (x=y)) s)` by
    (irule step_EQ >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id EQ [left;right] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     rpt strip_tac >> Cases_on `left` >> Cases_on `right` >>
     gvs[op_prov_def, FLOOKUP_DEF, allocas_from_def] >>
     metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst id EQ [left;right] [out]) s /\
   inst_dload_in_section (mk_inst id EQ [left;right] [out]) s` by
    simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `step_prov PG G (mk_inst id EQ [left;right] [out])
      (update_var out (bool_to_word (x=y)) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id EQ [left;right] [out]) s
      (update_var out (bool_to_word (x=y)) s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
      step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
      imm_taint_def, store_taint_def, adopt_reset_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      new_site_bytes_def, eval_operand_def, update_var_def,
      FLOOKUP_DEF, SF CONJ_ss, taint_component_equality]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out (bool_to_word (x=y)) s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >> strip_tac >>
     gvs[mk_inst_def] >> first_x_assum drule_all >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules, update_var_def]
QED
