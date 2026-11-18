(* Generated SHA256 calls retain the origin of their internal GAS on failure. *)
Theory bodyFullHashShaOrigin
Ancestors
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr gasCount ptrSafeRun
  bodyPtrHashBuiltinsShaTail bodyPtrHashBuiltinsShaTailSteps fragExecMem memSafeRun gasEvents
  venomExecProofs venomExecSemantics venomState venomInstProofs venomInst
  instIdxIndep fragExec exprLoweringProps fragGasSeqMem fragGasSeqAbort
  ptrDiscipline list rich_list arithmetic

Theorem sha_gas_head_origin_abort:
  !code s t a G tn G' tn' ctx fn bb id gv.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (mk_inst id GAS [] [gv]::code) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code /\
    (fn.fn_name,id) NOTIN explicit /\
    run_inst_seq_mem_ok (mk_inst id GAS [] [gv]::code) s /\
    inst_seq_ptr D lo ctx fn PG G tn (mk_inst id GAS [] [gv]::code) s G' tn' /\
    run_inst_seq (mk_inst id GAS [] [gv]::code) s = Abort a t ==>
    ?j. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [F]
      (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  `step_inst_base (mk_inst id GAS [] [gv]) s = OK u` by
    simp[Abbr `u`, hash_gas_step] >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, run_inst_seq_mem_ok_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    gvs[Abbr `u`, update_var_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `run_inst_seq code (u with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort a (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted /\
   lookup_block (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX code (DROP (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx bb.bb_instructions)` by simp[] >>
  `run_inst_seq_mem_ok code (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_mem_ok_inst_idx] >>
  drule_all sha_zero_origin_abort >>
  disch_then (qspec_then `explicit` strip_assume_tac) >> qexists_tac `j` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn)
    [(fn.fn_name,id) IN explicit]
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G (mk_inst id GAS [] [gv]) u,
      step_taint (mk_inst id GAS [] [gv]) s u tn)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id GAS [] [gv]`, `bb` |-> `bb`,
       `func` |-> `fn`, `s` |-> `s`, `u` |-> `u`, `D` |-> `D`,
       `lo` |-> `lo`, `ctx` |-> `ctx`, `G` |-> `G`, `tn` |-> `tn`,
       `PG` |-> `PG`, `explicit` |-> `explicit`] straight_line_origin_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Theorem sha_one_prefix_gas_abort:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (h::mk_inst id GAS [] [gv]::code)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  h.inst_opcode <> GAS /\ h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) code /\
  (fn.fn_name,id) NOTIN explicit /\ step_inst_base h s = OK u /\
  run_inst_seq_mem_ok (h::mk_inst id GAS [] [gv]::code) s /\
  inst_seq_ptr D lo ctx fn PG G tn (h::mk_inst id GAS [] [gv]::code) s G' tn' /\
  run_inst_seq (h::mk_inst id GAS [] [gv]::code) s = Abort a t ==>
  ?j. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [F]
    (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  fs[Once run_inst_seq_def, Once inst_seq_ptr_def, Once run_inst_seq_mem_ok_def] >>
  qpat_assum `step_inst_base h s = OK u`
    (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >> assume_tac th) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (mk_inst id GAS [] [gv]::code)` by
    fs[mk_inst_def, is_terminator_def, EVERY_MEM] >>
  `run_inst_seq (mk_inst id GAS [] [gv]::code)
    (u with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort a (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `run_inst_seq_mem_ok (mk_inst id GAS [] [gv]::code)
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by simp[run_inst_seq_mem_ok_inst_idx] >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted /\
   lookup_block (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (mk_inst id GAS [] [gv]::code)
     (DROP (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all sha_gas_head_origin_abort >> strip_tac >> qexists_tac `j` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G h u,step_taint h s u tn)` by
    (drule_all straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED
