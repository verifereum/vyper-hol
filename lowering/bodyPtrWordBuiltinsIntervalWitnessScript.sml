(* Interval-local fetch interface; no restriction on unrelated function code. *)
Theory bodyPtrWordBuiltinsIntervalWitness
Ancestors wordLoadStorePtr bodyPtrWordBuiltinsIntervalDataflow fragExec fragGasSeqPtr typedCopyPtr
  venomExecSemantics venomInst venomState venomInstProofs ptrSafeRun ptrDiscipline
  gasCount fragGasPathPtr contextCodegenRel codegenRel venomExecProofs finite_map
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem word_interval_operand_embedding:
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) /\
  fn_has_code (SND word_interval_start) sm fn ==>
  ?entry then_bb else_bb join_bb.
    lookup_block "entry" fn.fn_blocks = SOME entry /\
    lookup_block "@then_0" fn.fn_blocks = SOME then_bb /\
    lookup_block "@else_1" fn.fn_blocks = SOME else_bb /\
    lookup_block "@exit_2" fn.fn_blocks = SOME join_bb /\
    then_bb.bb_label = "@then_0" /\ else_bb.bb_label = "@else_1" /\
    get_instruction entry 7 = SOME (mk_inst 7 MLOAD [Var "%0"] ["%5"]) /\
    get_instruction entry 8 =
      SOME (mk_inst 8 JNZ [Var "%5"; Label "@then_0"; Label "@else_1"] []) /\
    get_instruction then_bb 0 = SOME (mk_inst 9 ASSIGN [Lit 1w] ["%6"]) /\
    get_instruction then_bb 1 = SOME (mk_inst 10 JMP [Label "@exit_2"] []) /\
    get_instruction else_bb 0 = SOME (mk_inst 11 ASSIGN [Lit 2w] ["%6"]) /\
    get_instruction else_bb 1 = SOME (mk_inst 12 JMP [Label "@exit_2"] [])
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[fn_has_code_def, emitted_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``lookup_block``]) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

(* The final empty prefix does not restrict instructions run on join entry. *)
Theorem word_interval_operand_join_unrestricted:
  !op sm insts.
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) ==>
  fn_has_code (SND word_interval_start) sm
    (word_interval_function with fn_blocks :=
      <|bb_label := "@exit_2"; bb_instructions := insts|> ::
      FILTER (\bb. bb.bb_label <> "@exit_2") word_interval_function.fn_blocks)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[fn_has_code_def, emitted_blocks_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

(* A covered local load is a counted edge in any containing function. *)
Theorem word_interval_mload_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  eval_operand (Var src) s = SOME a ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (OK ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MLOAD [Var src] [tmp]) s`
    by metis_tac[ptr_inst_ok_mload] >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def]) >>
  `(mk_inst id MLOAD [Var src] [tmp]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id MLOAD [Var src] [tmp]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def]
QED

(* Fetch-based form: neither branch nor destination code is restricted. *)
Theorem word_interval_jnz_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label lt; Label lf] []) /\
  ~ctx_has_dalloca ctx /\
  eval_operand op s = SOME (if b then 1w else 0w) /\ op_taint tn op = {} ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JNZ [op; Label lt; Label lf] []) s =
     OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
     (mk_inst id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[mk_inst_def, op_taint_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  `gas_count_step 0 ctx (mk_inst id JNZ [op; Label lt; Label lf] []) s = 0`
    by simp[gas_count_step_def, mk_inst_def] >>
  qexists_tac `0` >> simp[is_terminator_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `if b then lt else lf` >> simp[]
QED

Theorem word_interval_jmp_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
     (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       step_jmp_behavior, is_terminator_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

Theorem word_interval_assign_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit w] [tmp]) /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [Lit w] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id ASSIGN [Lit w] [tmp]) s (update_var tmp w s) tn)
    (OK ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit w] [tmp]) s = OK (update_var tmp w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Lit w] [tmp]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          step_inst_non_invoke, update_var_def] >>
     simp[mk_inst_def, op_taint_def]) >>
  `(mk_inst id ASSIGN [Lit w] [tmp]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id ASSIGN [Lit w] [tmp]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def]
QED

Theorem word_interval_literal_branch_path:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME (mk_inst id ASSIGN [Lit w] [tmp]) /\
  get_instruction bb 1 = SOME (mk_inst jid JMP [Label lbl] []) /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\
    lookup_var tmp t = SOME w /\ op_prov G' (Var tmp) = NONE /\
    t = jump_to lbl (update_var tmp w s) /\
    G' = DRESTRICT G (COMPL {tmp}) /\ tn' = tn with t_var := set_var_taint tn.t_var [tmp] {}
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [Lit w] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id ASSIGN [Lit w] [tmp]) s (update_var tmp w s) tn)
    (OK ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule word_interval_assign_edge >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ Ga ta (OK u)` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 1`
    by simp[Abbr `u`, update_var_def] >>
  `gas_path_ptr_edge D 0 ctx fn PG Ga ta u 0 Ga ta (OK (jump_to lbl u))`
    by (irule word_interval_jmp_edge >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG Ga ta (jump_to lbl u) 0 Ga ta
    (OK (jump_to lbl u))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[jump_to_def]) >>
  `gas_path_ptr D 0 ctx fn PG Ga ta u 0 Ga ta (OK (jump_to lbl u))`
    by metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  qexistsl_tac [`jump_to lbl u`, `Ga`, `ta`] >>
  conj_tac >- metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  simp[jump_to_def, Abbr `u`, lookup_var_def, update_var_def,
       Abbr `Ga`, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       Abbr `ta`, step_taint_def, out_taint_def, written_taint_def,
       step_writes_def, store_taint_def, adopt_reset_def, new_site_bytes_def,
       source_memory_write_ranges_def, mem_taint_def, imm_taint_def,
       eval_operand_def, taint_component_equality] >>
  simp[op_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem word_interval_selected_branch_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME entry /\
  get_instruction entry s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label lt; Label lf] []) /\
  ~ctx_has_dalloca ctx /\
  eval_operand op s = SOME (if b then 1w else 0w) /\ op_taint tn op = {} /\
  lookup_block (if b then lt else lf) fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME (mk_inst aid ASSIGN [Lit w] [tmp]) /\
  get_instruction bb 1 = SOME (mk_inst jid JMP [Label lbl] []) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\
    lookup_var tmp t = SOME w /\ op_prov G' (Var tmp) = NONE /\
    t = jump_to lbl (update_var tmp w (jump_to (if b then lt else lf) s)) /\
    G' = DRESTRICT G (COMPL {tmp}) /\
    tn' = tn with t_var := set_var_taint tn.t_var [tmp] {}
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if b then lt else lf) s))` by
    (irule word_interval_jnz_edge >> metis_tac[]) >>
  `?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn
      (jump_to (if b then lt else lf) s) 0 G' tn' (OK t) /\
      t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\
      lookup_var tmp t = SOME w /\ op_prov G' (Var tmp) = NONE /\
      t = jump_to lbl (update_var tmp w (jump_to (if b then lt else lf) s)) /\
      G' = DRESTRICT G (COMPL {tmp}) /\
      tn' = tn with t_var := set_var_taint tn.t_var [tmp] {}` by
    (irule word_interval_literal_branch_path >>
     simp[jump_to_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem word_interval_mload_taint_snapshot:
  eval_operand src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  step_taint (mk_inst id MLOAD [src] [tmp]) s
    (update_var tmp (mload (w2n a) s) s) tn =
    tn with t_var := set_var_taint tn.t_var [tmp] {}
Proof
  strip_tac >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
     gen_tac >> Cases_on `x < 32` >> simp[] >>
     first_x_assum irule >> decide_tac) >>
  simp[step_taint_def, out_taint_def, mem_taint_def, imm_taint_def,
       written_taint_def, step_writes_def, store_taint_def, adopt_reset_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       mk_inst_def, update_var_def, taint_component_equality,
       FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem word_interval_condition_load:
  ~s.vs_halted /\ s.vs_inst_idx = 7 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 7 = SOME (mk_inst 7 MLOAD [Var "%0"] ["%5"]) /\
  ptr_covers G tn "%0" s 32 /\ ~ctx_has_dalloca ctx /\
  eval_operand (Var "%0") s = SOME a /\
  mload (w2n a) s = (if b then 1w else 0w) /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?u Ga ta. gas_path_ptr_edge D 0 ctx fn PG G tn s 0 Ga ta (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 8 /\
    eval_operand (Var "%5") u = SOME (if b then 1w else 0w) /\
    op_taint ta (Var "%5") = {} /\
    u = ((update_var "%5" (if b then 1w else 0w) s) with vs_inst_idx := 8) /\
    Ga = DRESTRICT G (COMPL {"%5"}) /\
    ta = tn with t_var := set_var_taint tn.t_var ["%5"] {}
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst 7 MLOAD [Var "%0"] ["%5"])
      (update_var "%5" (mload (w2n a) s) s))
    (step_taint (mk_inst 7 MLOAD [Var "%0"] ["%5"]) s
      (update_var "%5" (mload (w2n a) s) s) tn)
    (OK ((update_var "%5" (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule word_interval_mload_edge >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ Ga ta (OK u)` >>
  qexistsl_tac [`u`, `Ga`, `ta`] >> simp[] >>
  conj_tac >- simp[Abbr `u`, update_var_def] >>
  conj_tac >- simp[Abbr `u`, update_var_def] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac >- simp[Abbr `u`, eval_operand_def, lookup_var_def,
                   update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (simp[Abbr `ta`] >> metis_tac[mload_ghost_clean]) >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac >- simp[Abbr `Ga`, step_prov_def, set_prov_def,
                   out_prov_def, mk_inst_def] >>
  simp[Abbr `ta`] >> metis_tac[word_interval_mload_taint_snapshot]
QED

Theorem word_interval_operand_scalar_path:
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) /\
  fn_has_code (SND word_interval_start) sm fn /\
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 7 /\
  ptr_covers G tn "%0" s 32 /\ ~ctx_has_dalloca ctx /\
  eval_operand (Var "%0") s = SOME a /\
  mload (w2n a) s = (if b then 1w else 0w) /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = "@exit_2" /\ t.vs_inst_idx = 0 /\
    lookup_var "%6" t = SOME (if b then 1w else 2w) /\
    op_prov G' (Var "%6") = NONE /\
    t = jump_to "@exit_2" (update_var "%6" (if b then 1w else 2w)
      (jump_to (if b then "@then_0" else "@else_1")
        ((update_var "%5" (if b then 1w else 0w) s) with vs_inst_idx := 8))) /\
    G' = DRESTRICT (DRESTRICT G (COMPL {"%5"})) (COMPL {"%6"}) /\
    tn' = tn with t_var :=
      set_var_taint (set_var_taint tn.t_var ["%5"] {}) ["%6"] {}
Proof
  strip_tac >> drule_all word_interval_operand_embedding >> strip_tac >>
  `?u Ga ta. gas_path_ptr_edge D 0 ctx fn PG G tn s 0 Ga ta (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 8 /\
    eval_operand (Var "%5") u = SOME (if b then 1w else 0w) /\
    op_taint ta (Var "%5") = {} /\
    u = ((update_var "%5" (if b then 1w else 0w) s) with vs_inst_idx := 8) /\
    Ga = DRESTRICT G (COMPL {"%5"}) /\
    ta = tn with t_var := set_var_taint tn.t_var ["%5"] {}` by
    (irule word_interval_condition_load >> metis_tac[]) >>
  `?t G' tn'. gas_path_ptr D 0 ctx fn PG Ga ta u 0 G' tn' (OK t) /\
    t.vs_current_bb = "@exit_2" /\ t.vs_inst_idx = 0 /\
    lookup_var "%6" t = SOME (if b then 1w else 2w) /\
    op_prov G' (Var "%6") = NONE /\
    t = jump_to "@exit_2" (update_var "%6" (if b then 1w else 2w)
      (jump_to (if b then "@then_0" else "@else_1") u)) /\
    G' = DRESTRICT Ga (COMPL {"%6"}) /\
    tn' = ta with t_var := set_var_taint ta.t_var ["%6"] {}` by
    (irule word_interval_selected_branch_path >> simp[] >>
     Cases_on `b` >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  conj_tac >- (drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]) >>
  simp[]
QED
