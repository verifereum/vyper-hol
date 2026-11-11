(* Ghost posts on the constructed path, not on arbitrary operand witnesses. *)
Theory bodyPtrWordBuiltinsIntervalPosts
Ancestors bodyPtrWordBuiltinsIntervalGhost bodyPtrWordBuiltinsIntervalWitness
  bodyPtrWordBuiltinsIntervalSource bodyPtrWordBuiltinsIntervalProjections
  finite_map compileEnv loweringStateRelDefs venomState
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem word_interval_temp_exclusions:
  (!n p sz. FLOOKUP (FST word_interval_start).ce_vars n =
    SOME (PtrVar (Var p) sz) ==> p <> "%5" /\ p <> "%6") /\
  (!p sz. (FST word_interval_start).ce_return_buf =
    SOME (PtrVar (Var p) sz) ==> p <> "%5" /\ p <> "%6") /\
  (!p sz. (FST word_interval_start).ce_return_pc =
    SOME (PtrVar (Var p) sz) ==> p <> "%5" /\ p <> "%6") /\
  (!p. not_fresh_at (SND word_interval_start) p ==> p <> "%5" /\ p <> "%6")
Proof
  simp[word_interval_vars, word_interval_return_buf, word_interval_return_pc,
       FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  simp[not_fresh_at_def, word_interval_next_var] >>
  gen_tac >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `5` mp_tac) >> EVAL_TAC >> metis_tac[]) >>
  first_x_assum (qspec_then `6` mp_tac) >> EVAL_TAC >> metis_tac[]
QED

Theorem word_interval_snapshot_ghost_inv:
  ghost_inv d (FST word_interval_start) cx es G tn s ==>
  ghost_inv d (FST word_interval_start) cx es
    (DRESTRICT (DRESTRICT G (COMPL {"%5"})) (COMPL {"%6"}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var ["%5"] {}) ["%6"] {})
    (jump_to "@exit_2" (update_var "%6" w
      (jump_to l ((update_var "%5" v s) with vs_inst_idx := 8))))
Proof
  strip_tac >>
  `ghost_inv d (FST word_interval_start) cx es
    (DRESTRICT G (COMPL {"%5"}))
    (tn with t_var := set_var_taint tn.t_var ["%5"] {})
    (update_var "%5" v s)` by
    (irule word_interval_ghost_inv_temp >> simp[] >>
     metis_tac[word_interval_temp_exclusions]) >>
  drule (Q.INST [`x` |-> `"%6"`] word_interval_ghost_inv_temp) >>
  simp[word_interval_vars, word_interval_return_buf, word_interval_return_pc,
       FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  disch_then (qspec_then `w` mp_tac) >>
  simp[jump_to_def, update_var_def, stmtFragPtrTheory.ghost_inv_jump_to,
       word_interval_ghost_inv_index] >>
  qmatch_goalsub_abbrev_tac `s with vs_vars := vars` >>
  mp_tac (Q.GENL [`cenv`, `G`, `tn`]
    (Q.INST [`s` |-> `s with vs_vars := vars`,
      `p` |-> `SOME l`, `l` |-> `"@exit_2"`, `i` |-> `0`]
      stmtFragPtrTheory.ghost_inv_jump_to)) >> simp[] >> metis_tac[]
QED

Theorem word_interval_snapshot_ghost_kept:
  ghost_kept cenv es (SND word_interval_start) G0 tn0 s0 G tn ==>
  ghost_kept cenv es (SND word_interval_start) G0 tn0 s0
    (DRESTRICT (DRESTRICT G (COMPL {"%5"})) (COMPL {"%6"}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var ["%5"] {}) ["%6"] {})
Proof
  strip_tac >>
  `ghost_kept cenv es (SND word_interval_start) G0 tn0 s0
    (DRESTRICT G (COMPL {"%5"}))
    (tn with t_var := set_var_taint tn.t_var ["%5"] {})` by
    (irule word_interval_ghost_kept_temp >> simp[] >>
     metis_tac[word_interval_temp_exclusions]) >>
  drule (Q.INST [`x` |-> `"%6"`] word_interval_ghost_kept_temp) >>
  impl_tac >- metis_tac[word_interval_temp_exclusions] >> simp[]
QED

Theorem word_interval_operand_framed_path:
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
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ghost_inv d (FST word_interval_start) cx es G tn s /\
  ghost_kept (FST word_interval_start) es (SND word_interval_start) G0 tn0 s0 G tn /\
  lookup_scopes "b" es.scopes = SOME entry /\
  read_place cx (MemoryPlace "b" []) es = (INL (BoolV b), es) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = "@exit_2" /\ t.vs_inst_idx = 0 /\
    lookup_var "%6" t = SOME (if b then 1w else 2w) /\
    op_prov G' (Var "%6") = NONE /\
    ghost_inv d (FST word_interval_start) cx es G' tn' t /\
    ghost_kept (FST word_interval_start) es (SND word_interval_start) G0 tn0 s0 G' tn' /\
    eval_expr cx
      (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
        (Literal (BaseT (IntT 256)) (IntL 1))
        (Literal (BaseT (IntT 256)) (IntL 2))) es =
      (INL (Value (IntV (if b then 1 else 2))), es)
Proof
  strip_tac >> drule_all word_interval_operand_scalar_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >>
  conj_tac >- (gvs[] >> irule (SRULE [] word_interval_snapshot_ghost_inv) >> simp[]) >>
  conj_tac >- (gvs[] >> irule (SRULE [] word_interval_snapshot_ghost_kept) >> simp[]) >>
  irule word_interval_operand_source >> metis_tac[]
QED
