(* Representation-independent complete SHA256 tail. *)
Theory bodyPtrHashBuiltinsShaTail
Ancestors bodyPtrHashBuiltinsShaTailCall bodyPtrHashBuiltinsShaTailSteps
  bodyPtrHashBuiltinsShaCall bodyPtrDefs fragGasSeqPtr ptrDiscipline
  exprSimHash valueEncoding valueEncodingDefs venomExecSemantics venomInst venomState finite_map pred_set words
  fragExec fragGasSeqAbort exprLoweringProps instIdxIndep venomInstProofs list

Theorem hash_sha256_tail_success_check:
  !D ctx fn PG G tn s i0 i1 i2 i3 gv p len q sv out w n r bs outcome rest.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\ q <> sv /\
    ~ctx_has_dalloca ctx /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i0 GAS [] [gv];
       mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
       mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s
      (DRESTRICT G (COMPL {gv;sv;out}))
      (tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (out,{});
        t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|>)
Proof
  rpt gen_tac >> strip_tac >> irule hash_gas_prefix_check >> simp[] >>
  qabbrev_tac `sg = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gg = DRESTRICT G (COMPL {gv})` >>
  qabbrev_tac `tg = tn with t_var := tn.t_var |+ (gv,{})` >>
  suspend "call"
QED

Resume hash_sha256_tail_success_check[call]:
  `eval_operand (Var p) sg = SOME w /\ eval_operand len sg = SOME n /\
   eval_operand (Var q) sg = SOME r /\
   eval_operand (Var gv) sg = SOME (HD (s.vs_gas_readings ++ [0w]))` by
    (Cases_on `len` >>
     gvs[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers Gg tg p sg (w2n n) /\ ptr_covers Gg tg q sg 32 /\
   op_taint tg len = {} /\ op_taint tg (Var gv) = {}` by
    (Cases_on `len` >>
     gvs[ptr_covers_def, Abbr `sg`, Abbr `Gg`, Abbr `tg`,
       op_taint_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qabbrev_tac `t = update_var sv 1w
    ((write_memory_with_expansion (w2n r)
      (word_to_bytes (SHA_256_bytes bs) T) sg) with
      <|vs_returndata := word_to_bytes (SHA_256_bytes bs) T; vs_outcomes := rest|>)` >>
  `step_inst_base (mk_inst i1 STATICCALL
     [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg = OK t` by
    (simp[Abbr `t`] >> irule step_STATICCALL_sha256 >>
     gvs[Abbr `sg`, read_memory_def, mem_bytes_at_def, update_var_def] >>
     metis_tac[]) >>
  suspend "finish"
QED

Resume hash_sha256_tail_success_check[finish]:
  `t.vs_requests = sg.vs_requests /\ t.vs_allocas = sg.vs_allocas /\
   t.vs_fmp = sg.vs_fmp /\ LENGTH t.vs_returndata = 32 /\
   lookup_var sv t = SOME 1w /\ eval_operand (Var q) t = SOME r` by
    gvs[Abbr `t`, update_var_def, write_memory_with_expansion_def,
      eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr D 0 ctx fn PG Gg tg
    [mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
     mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] sg
    (DRESTRICT (DRESTRICT Gg (COMPL {sv})) (COMPL {out}))
    ((step_taint (mk_inst i1 STATICCALL
      [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg t tg)
      with t_var := tg.t_var |+ (sv,{}) |+ (out,{}))` by
    (irule hash_sha256_call_load_check >>
     gvs[ptr_covers_def, eval_operand_def, Abbr `tg`, op_taint_def] >>
     rpt strip_tac >> gvs[]) >>
  suspend "ghost"
QED

Resume hash_sha256_tail_success_check[ghost]:
  `step_taint (mk_inst i1 STATICCALL
     [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg t tg =
     tg with <|t_var := tg.t_var |+ (sv,{});
       t_mem := tg.t_mem DIFF range_bytes [(w2n r,MIN 32 (LENGTH t.vs_returndata))]|>` by
    (SIMP_TAC (srw_ss()) [] >>
     irule (SRULE [] (cj 2 hash_staticcall_ghost)) >> metis_tac[]) >>
  `COMPL {gv} INTER (COMPL {sv} INTER COMPL {out}) = COMPL {gv;sv;out}` by (simp[EXTENSION] >> metis_tac[]) >>
  gvs[Abbr `Gg`, Abbr `tg`, Abbr `sg`]
QED

Finalise hash_sha256_tail_success_check

Theorem hash_sha256_tail_success_path:
  !D ctx fn PG G tn s bb code i0 i1 i2 i3 gv p len q sv out w n r bs outcome rest.
    code = [mk_inst i0 GAS [] [gv];
      mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
      mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\ q <> sv /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
    ?t. run_inst_seq code s = OK t /\
      gas_path_ptr D 0 ctx fn PG G tn s 1
        (DRESTRICT G (COMPL {gv;sv;out}))
        (tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (out,{});
          t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|>)
        (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
      eval_operand (Var out) t = SOME (SHA_256_bytes bs)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule_at Any sha256_tail_run >>
  simp[] >> reverse conj_tac >-
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `OK (t with vs_inst_idx := s.vs_inst_idx+4)` >>
  qabbrev_tac `code = [mk_inst i0 GAS [] [gv];
    mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
    mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]]` >>
  `run_inst_seq code s = OK t` by
    (simp[Abbr `code`, Abbr `t`] >>
     irule (SRULE [] sha256_tail_run) >> simp[] >> metis_tac[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s
    (DRESTRICT G (COMPL {gv;sv;out}))
    (tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (out,{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|>)` by
    (simp[Abbr `code`] >> irule (SRULE [] hash_sha256_tail_success_check) >> simp[] >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[Abbr `code`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[Abbr `code`, mk_inst_def]
QED

Theorem hash_sha256_tail_abort_check:
  !D ctx fn PG G tn s i0 i1 i2 i3 gv p len q sv out w n r.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\
    ~ctx_has_dalloca ctx /\
    ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i0 GAS [] [gv];
       mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
       mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s
      (DRESTRICT G (COMPL {gv;sv}))
      (tn with t_var := tn.t_var |+ (gv,{}) |+ (sv,{}))
Proof
  rpt gen_tac >> strip_tac >> irule hash_gas_prefix_check >> simp[] >>
  qabbrev_tac `sg = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gg = DRESTRICT G (COMPL {gv})` >>
  qabbrev_tac `tg = tn with t_var := tn.t_var |+ (gv,{})` >>
  suspend "call"
QED

Resume hash_sha256_tail_abort_check[call]:
  `eval_operand (Var p) sg = SOME w /\ eval_operand len sg = SOME n /\
   eval_operand (Var q) sg = SOME r /\
   eval_operand (Var gv) sg = SOME (HD (s.vs_gas_readings ++ [0w]))` by
    (Cases_on `len` >>
     gvs[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers Gg tg p sg (w2n n) /\ ptr_covers Gg tg q sg 32 /\
   op_taint tg len = {} /\ op_taint tg (Var gv) = {}` by
    (Cases_on `len` >>
     gvs[ptr_covers_def, Abbr `sg`, Abbr `Gg`, Abbr `tg`,
       op_taint_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qabbrev_tac `t = update_var sv 0w
    ((write_memory_with_expansion (w2n r) [] sg) with
      <|vs_returndata := []; vs_outcomes := DROP 1 sg.vs_outcomes|>)` >>
  `step_inst_base (mk_inst i1 STATICCALL
     [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg = OK t` by
    (simp[Abbr `t`] >> irule step_STATICCALL_sha256_fail >>
     gvs[Abbr `sg`, update_var_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume hash_sha256_tail_abort_check[finish]:
  `t.vs_requests = sg.vs_requests /\ t.vs_allocas = sg.vs_allocas /\
   t.vs_fmp = sg.vs_fmp /\ LENGTH t.vs_returndata = 0 /\
   lookup_var sv t = SOME 0w` by
    gvs[Abbr `t`, update_var_def, write_memory_with_expansion_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
  `inst_seq_ptr D 0 ctx fn PG Gg tg
    [mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
     mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] sg
    (DRESTRICT Gg (COMPL {sv}))
    (step_taint (mk_inst i1 STATICCALL
      [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg t tg)` by
    (irule hash_sha256_call_abort_check >>
     gvs[ptr_covers_def, eval_operand_def, Abbr `tg`, op_taint_def] >>
     rpt strip_tac >> gvs[]) >>
  `step_taint (mk_inst i1 STATICCALL
     [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv]) sg t tg =
     tg with <|t_var := tg.t_var |+ (sv,{});
       t_mem := tg.t_mem DIFF range_bytes [(w2n r,MIN 32 (LENGTH t.vs_returndata))]|>` by
    (SIMP_TAC (srw_ss()) [] >>
     irule (SRULE [] (cj 2 hash_staticcall_ghost)) >> metis_tac[]) >>
  `COMPL {gv} INTER COMPL {sv} = COMPL {gv;sv}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  gvs[Abbr `Gg`, Abbr `tg`, Abbr `sg`, range_bytes_def, EXTENSION] >>
  `tn with <|t_mem := tn.t_mem; t_var := tn.t_var |+ (gv,{}) |+ (sv,{})|> =
   tn with t_var := tn.t_var |+ (gv,{}) |+ (sv,{})` by
    simp[taint_component_equality] >> metis_tac[]
QED

Finalise hash_sha256_tail_abort_check

(* Zero-GAS abort lifting is needed because generic abort lifting hides its count. *)
Theorem hash_inst_seq_abort_zero_path:
  !code s t a G tn G' tn' ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      disch_then drule_all >> strip_tac >> qexists `j` >>
      drule_at (Pat `step_inst_base _ _ = OK _`) gas_path_ptr_step >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qexists `t.vs_inst_idx` >> simp[] >>
  drule gas_path_ptr_abort >> simp[] >> metis_tac[]
QED

Theorem hash_gas_head_abort_path:
  !code s t a G tn G' tn' ctx fn bb id gv.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (mk_inst id GAS [] [gv]::code) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn (mk_inst id GAS [] [gv]::code) s G' tn' /\
    run_inst_seq (mk_inst id GAS [] [gv]::code) s = Abort a t ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
      (Abort a (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  `step_inst_base (mk_inst id GAS [] [gv]) s = OK u` by
    simp[Abbr `u`, hash_gas_step] >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    gvs[Abbr `u`, update_var_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `run_inst_seq code (u with vs_inst_idx := SUC s.vs_inst_idx) =
     Abort a (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted /\
   lookup_block (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb /\
   isPREFIX code (DROP (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
     bb.bb_instructions)` by simp[] >>
  drule_all hash_inst_seq_abort_zero_path >> strip_tac >>
  qexists `j` >>
  irule (SRULE [mk_inst_def] (Q.INST
    [`i` |-> `mk_inst id GAS [] [gv]`, `n` |-> `0`] gas_path_ptr_step)) >>
  gvs[mk_inst_def, is_terminator_def] >> metis_tac[]
QED

Theorem hash_sha256_tail_abort_path:
  !D ctx fn PG G tn s bb code i0 i1 i2 i3 gv p len q sv out w n r.
    code = [mk_inst i0 GAS [] [gv];
      mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
      mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
    ?t j. run_inst_seq code s = Abort Revert_abort t /\
      gas_path_ptr D 0 ctx fn PG G tn s 1
        (DRESTRICT G (COMPL {gv;sv}))
        (tn with t_var := tn.t_var |+ (gv,{}) |+ (sv,{}))
        (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `?t. run_inst_seq [mk_inst i0 GAS [] [gv];
    mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
    mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s =
    Abort Revert_abort t` by (irule sha256_tail_fail >> simp[] >> metis_tac[]) >>
  qexists `t` >> simp[] >> irule hash_gas_head_abort_path >> simp[] >>
  qexistsl [`[mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
    mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]]`, `gv`, `i0`] >>
  gvs[mk_inst_def, is_terminator_def] >>
  irule (SRULE [mk_inst_def] hash_sha256_tail_abort_check) >> simp[] >> metis_tac[]
QED
