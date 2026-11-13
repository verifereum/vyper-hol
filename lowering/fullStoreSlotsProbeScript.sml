(* Robust control loads for recursive live-slot stores.  The endpoint and
   ghosts are independent of the dead mask and the reserved constructor frame. *)
Theory fullStoreSlotsProbe
Ancestors
  fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport wordLoadStorePtr
  representationCleanPtr typedCopyLayoutPtr instMemFrontier fragExecMem
  bodyPtrDefs ptrDiscipline ptrCoverage venomState venomInst venomExecSemantics
  unitTransformDefs codegenRel contextCodegenRel memSafeRun valueEncodingDefs
  finite_map pred_set list arithmetic words

Theorem store_slots_robust_load_origin_ptr:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       mem_word_at (w2n a) m = w) ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  `mload (w2n a) s = w` by
    (qpat_x_assum `!m. mem_agree_outside _ _ m ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[ptr_inst_ok_mload]) >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s = OK (update_var out w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
  `inst_mem_below_frontier (mk_inst id MLOAD [Var src] [out]) s /\
   inst_dload_in_section (mk_inst id MLOAD [Var src] [out]) s` by
    simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      eval_operand_def] >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
     Cases_on `x < 32` >> simp[] >> first_x_assum irule >> decide_tac) >>
  `step_prov PG G (mk_inst id MLOAD [Var src] [out]) (update_var out w s) =
       DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id MLOAD [Var src] [out]) s (update_var out w s) tn =
       (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, mem_taint_def,
      imm_taint_def, store_taint_def, adopt_reset_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      new_site_bytes_def, eval_operand_def, update_var_def,
      FLOOKUP_DEF, SF CONJ_ss, taint_component_equality]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >> strip_tac >>
     gvs[mk_inst_def] >> first_x_assum drule_all >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules, update_var_def]
QED
