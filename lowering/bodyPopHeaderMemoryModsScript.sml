(* The covered header load at the reached memory Pop cursor. *)
Theory bodyPopHeaderMemoryMods
Ancestors
  exprPtrCtorCodeLoad exprPtrCtorImmStore decoderGhostFramePtr
  ghostPcTransportPtr fragGasSeqPtr fragGasSeqAbort fragExecMem instMemFrontier
  emitHelperProps memSafeRun unitTransformDefs allocaHistory
  ptrDiscipline bodyPtrDefs fragExec context instIdxIndep exprLoweringProps
  venomExecSemantics
  venomInst venomState words finite_map rich_list list arithmetic

Theorem pop_header_memory_load_mods:
  s.vs_inst_idx = k /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var p] [x0]] (DROP k bb.bb_instructions) /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\ w2n w + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q u G' tn'.
    q = update_var x0 (mload (w2n w) s) s /\
    run_inst_seq [mk_inst id MLOAD [Var p] [x0]] s = OK q /\
    u = q with vs_inst_idx := k + 1 /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [mk_inst id MLOAD [Var p] [x0]]
             (s with vs_inst_idx := j) G' tn') /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')) /\
    lookup_var x0 u = SOME (mload (w2n w) s) /\
    op_taint tn' (Var x0) = {} /\ op_prov G' (Var x0) = NONE /\
    u = s with <| vs_vars := u.vs_vars; vs_inst_idx := k + 1 |> /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (alloca_history func s ==> alloca_history func u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> x0 ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id MLOAD [Var p] [x0]` >>
  qabbrev_tac `q = update_var x0 (mload (w2n w) s) s` >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `step_inst_base i s = OK q` by
    (simp[Abbr `i`, Abbr `q`] >> irule step_MLOAD >> simp[]) >>
  `i.inst_opcode = MLOAD` by simp[Abbr `i`, mk_inst_def] >>
  `!D j. inst_seq_ptr D lo ctx func PG G tn [i] (s with vs_inst_idx := j)
            (step_prov PG G i q) (step_taint i s q tn)` by
    (rpt gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
       exec_result_map_def, is_terminator_def] >>
     simp[Abbr `i`] >> irule ptr_inst_ok_mload_lo >>
     simp[NoAsms, ptr_covers_def, lookup_var_def, allocas_from_def,
          allocas_below_fmp_def] >> fs[ptr_covers_def, lookup_var_def,
          allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `run_inst_seq [i] s = OK q` by simp[run_inst_seq_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (q with vs_inst_idx := k + 1),step_prov PG G i q,step_taint i s q tn)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn [i] s
        (step_prov PG G i q) (step_taint i s q tn)` by
       (first_x_assum (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
       (MAP (\j. (func.fn_name,j.inst_id) IN explicit)
          (FILTER (\j. j.inst_opcode = GAS) [i]))
       (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH [i]),
        step_prov PG G i q,step_taint i s q tn)` suffices_by simp[] >>
     irule run_inst_seq_gas_origin_ptr_path >>
     simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def,
          dalloca_no_wrap_def, is_terminator_def, APPEND_EQ_CONS] >>
     fs[Abbr `i`, below_frontier_MLOAD]) >>
  `get_instruction bb k = SOME i` by
    (irule (cj 1 instruction_prefix_cursor) >> qexists_tac `[]` >> simp[]) >>
  qexistsl_tac [`q`, `q with vs_inst_idx := k + 1`,
    `step_prov PG G i q`, `step_taint i s q tn`] >>
  simp[] >> simp[Abbr `i`, Abbr `q`, load_word_taint_frame] >>
  conj_tac >- simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (drule (GEN_ALL (SRULE [] (Q.INST [`opc` |-> `MLOAD`] load_word_output_taint))) >>
      simp[]) >>
  conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[allocas_from_def, allocas_below_fmp_def] >>
  conj_tac
  >- (simp[alloca_history_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
      rename1 `get_instruction _ j = SOME inst` >>
      Cases_on `j < k` >- metis_tac[] >>
      `j = k` by decide_tac >> gvs[mk_inst_def]) >>
  rpt strip_tac >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED
