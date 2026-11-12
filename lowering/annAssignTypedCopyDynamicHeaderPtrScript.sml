(* Counted dynamic-array length guard and header setup. *)
Theory annAssignTypedCopyDynamicHeaderPtr
Ancestors
  bodyPtrBopScalarSeq annAssignPtrLength annAssignPtrStore
  typedMemoryCopy typedNormalizeDynarray fragGasPathPtr bodyPtrDefs
  venomState venomExecSemantics venomInst ptrDiscipline finite_map
  words arithmetic list pred_set emitHelper compileEnv fragExec exprLoweringProps
  assignBasePtrStoragePath representationCleanPtr valueEncoding
  wordLoadStorePtr bodyPtrMakeArrayWordStore valueEncodingProps

Theorem annassign_dynamic_capacity_guard_counted:
  !s fn bb id len too_long ok n cap tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst id GT [Var len;Lit (n2w cap)] [too_long];
       mk_inst (id+1) ISZERO [Var too_long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []]
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    lookup_var len s = SOME (n2w n) /\ n <= cap /\ cap < dimword (:256) /\
    op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
    ALL_DISTINCT [len;too_long;ok] ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t = (update_var ok 1w (update_var too_long 0w s)
        with vs_inst_idx := s.vs_inst_idx+3) /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> too_long /\ x <> ok ==>
        FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len;Lit (n2w cap)] [too_long];
     mk_inst (id+1) ISZERO [Var too_long] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var too_long 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
      mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, w2n_n2w,
      bool_to_word_def] >>
     `n < dimword (:256)` by decide_tac >>
     simp[LESS_MOD] >> `~(cap < n)` by decide_tac >> simp[]) >>
  `bop_scalar_seq (COMPL {too_long;ok}) {Var len;Lit (n2w cap)} code
    {Var ok;Var too_long;Var len;Lit (n2w cap)}` by
    (simp[Abbr `code`, Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id`,`GT`,`[Var len;Lit (n2w cap)]`,`too_long`] >> simp[] >>
     simp[Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id+1`,`ISZERO`,`[Var too_long]`,`ok`] >> simp[] >>
     simp[Once bop_scalar_seq_def] >> disj2_tac >>
     qexistsl_tac [`id+2`,`ASSERT`,`Var ok`] >> simp[]) >>
  `!op. op IN {Var len;Lit (n2w cap)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,
    `update_var ok 1w (update_var too_long 0w s) with vs_inst_idx := s.vs_inst_idx+3`] >>
  gvs[Abbr `code`, op_taint_def] >> metis_tac[]
QED

Theorem annassign_dynamic_length_checked_counted:
  !s fn bb id src len too_long ok a n cap tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [len]) /\
    isPREFIX
      [mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too_long];
       mk_inst (id+2) ISZERO [Var too_long] [ok];
       mk_inst (id+3) ASSERT [Var ok] []]
      (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n a) mem = n2w n) /\
    n <= cap /\ cap < dimword (:256) /\ ALL_DISTINCT [len;too_long;ok] ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t = (update_var ok 1w (update_var too_long 0w
            (update_var len (n2w n) s))
           with vs_inst_idx := s.vs_inst_idx+4) /\
      lookup_var len t = SOME (n2w n) /\
      FLOOKUP H len = NONE /\ op_taint tm (Var len) = {} /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. ~MEM x [len;too_long;ok] ==>
        FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `mload (w2n a) s = n2w n` by
    (qpat_x_assum `!mem. _` (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (drule robust_mem_word_at_clean >> strip_tac >>
     simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     first_x_assum (qspec_then `w2n a + x` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule assign_base_mload_ghost >>
  disch_then (qspecl_then [`PG`,`G`,`tn`,`id`,`len`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {len}))
    (tn with t_var := tn.t_var |+ (len,{}))
    (OK (update_var len (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (metis_tac[annassign_mload_path_ptr]) >>
  qabbrev_tac `u = update_var len (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  `?H tm t.
    gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {len}))
      (tn with t_var := tn.t_var |+ (len,{})) u 0 H tm (OK t) /\
    t = (update_var ok 1w (update_var too_long 0w u)
      with vs_inst_idx := u.vs_inst_idx+3) /\
    tm.t_mem = (tn with t_var := tn.t_var |+ (len,{})).t_mem /\
    tm.t_stor = (tn with t_var := tn.t_var |+ (len,{})).t_stor /\
    tm.t_trans = (tn with t_var := tn.t_var |+ (len,{})).t_trans /\
    tm.t_imm = (tn with t_var := tn.t_var |+ (len,{})).t_imm /\
    (!x. x <> too_long /\ x <> ok ==>
      FLOOKUP H x = FLOOKUP (DRESTRICT G (COMPL {len})) x /\
      op_taint tm (Var x) = op_taint (tn with t_var := tn.t_var |+ (len,{})) (Var x))` by
    (irule annassign_dynamic_capacity_guard_counted >>
     simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       op_prov_def, op_taint_def, FLOOKUP_DRESTRICT] >>
     qexistsl_tac [`cap`,`id+1`,`len`,`n`] >>
     gvs[ALL_DISTINCT, op_taint_def, ADD_ASSOC]) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
    goal_assum (drule_at Any) >> simp[Abbr `u`]) >>
  `SUC s.vs_inst_idx + 3 = s.vs_inst_idx + 4` by decide_tac >>
  gvs[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT, op_taint_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem annassign_dynamic_header_copy_counted:
  !s fn bb id src dst len too_long ok a b n cap tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [len]) /\
    isPREFIX
      [mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too_long];
       mk_inst (id+2) ISZERO [Var too_long] [ok];
       mk_inst (id+3) ASSERT [Var ok] []]
      (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (id+4) MSTORE [Var dst;Var len] []) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME b /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n a) mem = n2w n) /\
    n <= cap /\ cap < dimword (:256) /\ ALL_DISTINCT [len;too_long;ok] /\
    ~MEM dst [len;too_long;ok] ==>
    ?H tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
      u = (mstore (w2n b) (n2w n)
         (update_var ok 1w (update_var too_long 0w (update_var len (n2w n) s)))
         with vs_inst_idx := s.vs_inst_idx+5) /\
      lookup_var len u = SOME (n2w n) /\
      FLOOKUP H len = NONE /\ op_taint tf (Var len) = {} /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
        mem_word_at (w2n b) mem = n2w n) /\
      (!x. ~MEM x [len;too_long;ok] ==>
        FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_length_checked_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `lookup_var dst t = SOME b /\ ptr_covers H tm dst t 32 /\
   ~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb t.vs_inst_idx =
     SOME (mk_inst (id+4) MSTORE [Var dst;Var len] [])` by
    (gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `eval_operand (Var len) t = SOME (n2w n)` by simp[eval_operand_def] >>
  `gas_path_ptr D 0 ctx fn PG H tm t 0
    (step_prov PG H (mk_inst (id+4) MSTORE [Var dst;Var len] [])
      (mstore (w2n b) (n2w n) t))
    (step_taint (mk_inst (id+4) MSTORE [Var dst;Var len] []) t
      (mstore (w2n b) (n2w n) t) tm)
    (OK (mstore (w2n b) (n2w n) t with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule annassign_mstore_path_ptr >> simp[] >> metis_tac[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`H`,`id+4`] strip_assume_tac) >>
  qabbrev_tac `tf = step_taint (mk_inst (id+4) MSTORE [Var dst;Var len] []) t
      (mstore (w2n b) (n2w n) t) tm` >>
  qexistsl_tac [`H`,`tf`,`mstore (w2n b) (n2w n) t with vs_inst_idx := SUC t.vs_inst_idx`] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
    goal_assum (drule_at Any) >> gvs[]) >>
  `tf.t_imm = tm.t_imm` by
    simp[Abbr `tf`, step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  `!mem. mem_agree_outside tf.t_mem (mstore (w2n b) (n2w n) t).vs_memory mem ==>
    mem_word_at (w2n b) mem = n2w n` by
    (rpt strip_tac >> irule mstore_raw_robust_word >>
     goal_assum (drule_at Any) >> simp[Abbr `tf`] >>
     qexistsl_tac [`dst`,`id+4`,`tm`,`Var len`] >> gvs[]) >>
  `SUC (s.vs_inst_idx+4) = s.vs_inst_idx+5` by decide_tac >>
  gvs[op_taint_def, Abbr `tf`] >>
  conj_tac >- simp[mstore_def, update_var_def, write_memory_with_expansion_def,
    venom_state_component_equality] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  irule EQ_TRANS >>
  irule_at Any mstore_mem_bytes_at_disjoint >>
  simp[update_var_def] >> decide_tac
QED
