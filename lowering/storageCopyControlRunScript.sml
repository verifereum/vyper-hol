(* Joint storage-copy control segments, retaining the list and jump at
   the very same successor as the invariant and ghost post. *)
Theory storageCopyControlRun
Ancestors
  fragGasStorageCopyHeaderProps fragGasCopySeqLiftProps fragGasOriginPtrLoop
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy exprLoweringProps fragGasOriginPtr fragGasOrigin
  fragGasSeqAbort fragGasSeqPtr fragExec fragExecMem ptrDiscipline ptrSafeRun
  instMemFrontier memSafeRun contextCodegenRel codegenRel unitTransformDefs
  gasEvents venomExecSemantics venomExecProofs venomState venomInst
  words arithmetic list rich_list

Theorem storage_copy_init_origin_run:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id ASSIGN [Lit 0w] [cv]; mk_inst (id+1) JMP [Label hdr] []] ==>
  !loc D explicit PG. ?t G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    ?raw mid.
      isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
      run_inst_seq [mk_inst id ASSIGN [Lit 0w] [cv]] s = OK raw /\
      mid = raw with vs_inst_idx := s.vs_inst_idx + 1 /\
      mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted /\
      get_instruction bb mid.vs_inst_idx = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
      gas_origin_edge F explicit ctx func mid [] (OK t)
Proof
  rpt strip_tac >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s = OK (update_var cv 0w s)` by
    simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst id ASSIGN [Lit 0w] [cv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst id ASSIGN [Lit 0w] [cv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by
    (`DROP (s.vs_inst_idx+1) bb.bb_instructions =
        [mk_inst (id+1) JMP [Label hdr] []]` by
       (`s.vs_inst_idx+1 <= LENGTH bb.bb_instructions` by
          (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
           simp[]) >>
        qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
        simp[rich_listTheory.DROP_DROP, arithmeticTheory.ADD_COMM]) >>
     `isPREFIX [mk_inst (id+1) JMP [Label hdr] []]
        (DROP (s.vs_inst_idx+1) bb.bb_instructions)` by simp[] >>
     drule instruction_prefix_cursor >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id ASSIGN [Lit 0w] [cv]` >>
  qabbrev_tac `u0 = update_var cv 0w s` >>
  qabbrev_tac `G1 = step_prov PG G i0 u0` >>
  qabbrev_tac `tn1 = step_taint i0 s u0 tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s = OK u0` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post v. [i0] = pre ++ i::post /\
       run_inst_seq pre s = OK v ==> dalloca_no_wrap i v)` by
    (rpt strip_tac >> Cases_on `pre` >> gvs[Abbr `i0`, mk_inst_def]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t0 = u0 with vs_inst_idx := s.vs_inst_idx + LENGTH [i0]` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t0,G1,tn1) []
     (OK (jump_to hdr t0),G1,tn1)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  `gas_origin_edge F explicit ctx func t0 [] (OK (jump_to hdr t0))` by
    (simp[gas_origin_edge_def, Abbr `t0`, Abbr `u0`, update_var_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, mk_inst_def, step_jmp_behavior,
          is_terminator_def] >> metis_tac[]) >>
  `(?raw mid.
       isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
       run_inst_seq [mk_inst id ASSIGN [Lit 0w] [cv]] s = OK raw /\
       mid = raw with vs_inst_idx := s.vs_inst_idx + 1 /\
       mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted /\
       get_instruction bb mid.vs_inst_idx = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
       gas_origin_edge F explicit ctx func mid [] (OK (jump_to hdr t0)))` by
    (qexistsl_tac [`u0`,`t0`] >>
     conj_tac >- simp[] >>
     conj_tac >- fs[Abbr `i0`] >>
     conj_tac >- simp[Abbr `t0`] >>
     conj_tac >- simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     conj_tac >- simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     conj_tac >- simp[Abbr `t0`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`jump_to hdr t0`, `G1`, `tn1`] >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`,`t0`,`tn1`] >> gvs[]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `t0`, Abbr `u0`, Abbr `G1`, Abbr `tn1`, Abbr `i0`] >>
  rpt conj_tac
  >- (pure_rewrite_tac[GSYM update_var_def] >>
      irule toplevel_copy_init_inv >> simp[] >> metis_tac[])
  >- (gvs[allocas_from_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  gvs[jump_to_def, update_var_def, allocas_below_fmp_def] >> metis_tac[]
QED

Theorem storage_copy_header_origin_run:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 r /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)) /\
    ~r.vs_halted /\ r.vs_inst_idx = 0 /\
    r.vs_current_bb = (if k=n then exit_lbl else body_lbl) /\
    ?raw mid.
      isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
      run_inst_seq [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s = OK raw /\
      mid = raw with vs_inst_idx := s.vs_inst_idx + 1 /\
      mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted /\
      get_instruction bb mid.vs_inst_idx = SOME
        (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) /\
      gas_origin_edge F explicit ctx func mid [] (OK r)
Proof
  rpt strip_tac >>
  drule_all storage_copy_header_ptr_run >>
  disch_then (qspecl_then [`D`,`PG`]
    (qx_choosel_then [`u`,`t`,`G1`,`tn1`] strip_assume_tac)) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qpat_x_assum `t = _ with vs_inst_idx := _`
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qabbrev_tac `r = jump_to (if k=n then exit_lbl else body_lbl) t` >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t = OK r` by
    (Cases_on `k=n` >>
     simp[Abbr `r`, step_inst_base_def, mk_inst_def, eval_operand_def, bool_to_word_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK r,G1,tn1)` by
    (simp[Abbr `r`] >>
     `((bool_to_word (k=n)):bytes32 <> 0w) = (k=n)` by simp[bool_to_word_def] >>
     qpat_assum `_ = (k=n)` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule jnz_origin_ptr_path >> simp[] >>
     qexistsl_tac [`Var tv`,`id+1`] >> simp[eval_operand_def]) >>
  `gas_origin_edge F explicit ctx func t [] (OK r)` by
    (simp[gas_origin_edge_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, mk_inst_def, is_terminator_def] >>
     metis_tac[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`r`, `G1`, `tn1`] >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`, `t`, `tn1`] >> gvs[]) >>
  conj_tac
  >- (gvs[Abbr `r`, jump_to_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `~r.vs_halted /\ r.vs_inst_idx = 0 /\ r.vs_current_bb = (if k=n then exit_lbl else body_lbl)` by
    simp[Abbr `r`, jump_to_def] >>
  asm_rewrite_tac[] >> qexistsl_tac [`u`,`t`] >> simp[Abbr `t`] >>
  metis_tac[]
QED
