(* Use the exact base run to delimit the successful, memory-checked
   origin edges of the installed code copy. *)
Theory rawCreateCodeCopySpine
Ancestors
  rawCreateAdminSpine fragGasOriginPtr fragGasOrigin fragExec instIdxIndep
  createSizeLocationCode createSizeCutCode exprSimAbiEncodeObliviousCode
  abiBufferAllocationCode exprSimCopy abiEncoderProps exprLoweringProps pred_set
  venomExecSemantics venomInstProofs venomState venomInst
  list rich_list arithmetic

Theorem straight_origin_successor[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK u /\ gas_origin_edge T E C f s [] (OK t) ==>
  t = u with vs_inst_idx := SUC s.vs_inst_idx
Proof
  simp[gas_origin_edge_def] >> strip_tac >> gvs[step_inst_non_invoke,exit_result_def]
QED

Theorem raw_code_run_spine[local]:
  !is s t bb.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH is /\
    (!j. j < LENGTH is ==>
      get_instruction bb (s.vs_inst_idx + j) = SOME (EL j is)) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) is /\
    run_inst_seq is s = OK t /\
    gas_origin_path T E C f s [] (OK (t with vs_inst_idx := LENGTH b.cs_current_insts)) ==>
    admin_ok_spine a b E C f s (t with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK v` >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. j < SUC (LENGTH is) ==> _`
      (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once gas_origin_path_cases,exit_result_def]) >>
  gvs[] >>
  drule_all straight_origin_successor >> disch_then SUBST_ALL_TAC >>
  irule admin_ok_spine_trans >>
  qexists_tac `v with vs_inst_idx := SUC s.vs_inst_idx` >> conj_tac
  >- (irule admin_ok_spine_single >> simp[] >>
      qexistsl_tac [`bb`,`h`] >> simp[]) >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow,step_inst_non_invoke] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`,`bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx,exec_result_map_def,ADD_CLAUSES] >>
  disch_then irule >> reverse conj_tac >- fs[ADD_CLAUSES] >>
  gen_tac >> disch_tac >>
  qpat_assum `!j. j < SUC (LENGTH is) ==> _`
    (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >> simp[]
QED

Theorem raw_code_copy_spine:
  compile_alloc_buffer cap a = (buf,m) /\
  compile_imm_copy_to_memory ctor imm src buf.buf_operand n off m = ((),b) /\
  fn_has_code a b f /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a m) s = OK alloc /\
  u = alloc with vs_inst_idx := LENGTH m.cs_current_insts /\
  copy_runtime_frame m u b r /\
  gas_origin_path T E C f s [] (OK u) /\
  gas_origin_path T E C f u [] (OK (r with vs_inst_idx := LENGTH b.cs_current_insts)) ==>
  admin_ok_spine a b E C f s (r with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  `?is. same_blocks m b /\ b.cs_current_insts = m.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; ILOAD; MSTORE]) is` by
    (Cases_on `ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> simp[EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> simp[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts m b = is` by
    (qpat_assum `b.cs_current_insts = _` (fn th =>
      simp[NoAsms,emitted_insts_def,th,DROP_LENGTH_APPEND])) >>
  `create_cut_code {} m b` by metis_tac[create_imm_copy_cut_code,pairTheory.SND] >>
  `frag_code m b = is` by fs[same_blocks_def,frag_code_open] >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
                  ~is_terminator i.inst_opcode) is` by
    (fs[create_cut_code_def,EVERY_MEM,frag_ids_def] >>
     gen_tac >> disch_tac >>
     `a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id` by
       (qpat_assum `!x. MEM x _ ==> _ /\ _` (drule_then (strip_assume_tac o CONJUNCT1)) >>
        qpat_assum `m.cs_next_id = _` SUBST_ALL_TAC >> decide_tac) >>
     `i.inst_opcode = ADD \/ i.inst_opcode = DLOAD \/
      i.inst_opcode = ILOAD \/ i.inst_opcode = MSTORE` by metis_tac[] >>
     asm_rewrite_tac[] >> gvs[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  `LENGTH m.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts a m)` by simp[] >>
  `run_inst_seq (emitted_insts a m ++ is) s = OK (r with vs_inst_idx := alloc.vs_inst_idx)` by
    (irule logInstSeqPtrTheory.run_inst_seq_append_advanced >>
     qpat_assum `copy_runtime_frame m u b r`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [copy_runtime_frame_def]) >>
     qpat_assum `u = _` SUBST1_TAC >>
     qpat_assum `LENGTH m.cs_current_insts = s.vs_inst_idx + _` (fn th => simp[Once th])) >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++ (emitted_insts a m ++ is)` by
    fs[same_blocks_def,APPEND_ASSOC] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `gas_origin_path T E C f s [] (OK (r with vs_inst_idx := LENGTH b.cs_current_insts))` by
    metis_tac[gas_origin_path_append,APPEND] >>
  pop_assum (mk_asm "combined") >>
  qspecl_then [`emitted_insts a m ++ is`,`s`,
    `r with vs_inst_idx := alloc.vs_inst_idx`,`bb`] mp_tac raw_code_run_spine >>
  simp[EVERY_APPEND,ADD_COMM] >> disch_then irule >>
  `m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  fs[frag_ids_def,mk_inst_def,is_terminator_def] >>
  `LENGTH b.cs_current_insts = LENGTH is + (LENGTH a.cs_current_insts + 1)` by
    (qpat_assum `b.cs_current_insts = _` (fn th => simp[th,LENGTH_APPEND])) >>
  asm "combined" mp_tac >> asm_rewrite_tac[]
QED
