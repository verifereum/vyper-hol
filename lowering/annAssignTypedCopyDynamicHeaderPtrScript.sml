(* Counted dynamic-array length guard and header setup. *)
Theory annAssignTypedCopyDynamicHeaderPtr
Ancestors
  bodyPtrBopScalarSeq annAssignPtrLength annAssignPtrStore
  typedMemoryCopy typedNormalizeDynarray fragGasPathPtr bodyPtrDefs
  venomState venomExecSemantics venomInst ptrDiscipline finite_map
  words arithmetic list pred_set emitHelper compileEnv fragExec exprLoweringProps
  assignBasePtrStoragePath representationCleanPtr valueEncoding
  wordLoadStorePtr bodyPtrMakeArrayWordStore valueEncodingProps
  augAssignPtrFieldLoad bodyPtrSubscriptCountedAdd typedCopyPtr

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

Theorem annassign_dynamic_payload_addresses_counted:
  !s fn bb id src dst sp dp a b S T G tn ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var src;Lit 32w] [sp]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var dst;Lit 32w] [dp]) /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+S) /\ ptr_covers G tn dst s (32+T) /\
    w2n a+32 < dimword (:256) /\ w2n b+32 < dimword (:256) /\
    sp <> dst /\ sp <> dp ==>
    ?H tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
      u = (update_var dp (b+32w) (update_var sp (a+32w) s)
        with vs_inst_idx := s.vs_inst_idx+2) /\
      lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
      ptr_covers H tf sp u S /\ ptr_covers H tf dp u T /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. x <> sp /\ x <> dp ==>
        FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `ptr_covers G tn src s (32+sspan)` >>
  rename1 `ptr_covers G tn dst s (32+dspan)` >>
  `op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {}` by
    gvs[ptr_covers_def] >>
  drule_all add_literal_path_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)` >>
  `lookup_var dst t = SOME b /\ ~t.vs_halted /\
   lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb t.vs_inst_idx =
     SOME (mk_inst (id+1) ADD [Var dst;Lit 32w] [dp])` by
    gvs[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE, ADD1] >>
  `op_taint tm (Var dst) = {}` by
    gvs[Abbr `tm`, step_taint_def, mk_inst_def, set_var_taint_def,
      op_taint_def, FLOOKUP_UPDATE] >>
  drule_all add_literal_path_ptr >>
  disch_then (qspecl_then [`PG`,`H`,`D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG H tm t 0 J tf (OK u)` >>
  `ptr_covers H tm sp t sspan` by
    (simp[Abbr `H`, Abbr `tm`, Abbr `t`] >>
     irule (SRULE [] (Q.INST [`off` |-> `32`] add_displacement_coverage)) >> simp[] >>
     qexists_tac `32+sspan` >> simp[]) >>
  `ptr_covers H tm dst t (32+dspan)` by
    (gvs[Abbr `H`, Abbr `tm`, Abbr `t`, ptr_covers_def,
      step_prov_def, out_prov_def, set_prov_def, first_prov_def, op_prov_def, mk_inst_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      step_taint_def, set_var_taint_def, op_taint_def] >> metis_tac[]) >>
  `ptr_covers J tf dp u dspan` by
    (simp[Abbr `J`, Abbr `tf`, Abbr `u`] >>
     irule (SRULE [] (Q.INST [`off` |-> `32`] add_displacement_coverage)) >>
     simp[] >> qexists_tac `32+dspan` >> simp[]) >>
  `ptr_covers J tf sp u sspan` by
    (gvs[Abbr `J`, Abbr `tf`, Abbr `u`, ptr_covers_def,
      step_prov_def, out_prov_def, set_prov_def, first_prov_def, op_prov_def, mk_inst_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      step_taint_def, set_var_taint_def, op_taint_def] >> metis_tac[]) >>
  qexistsl_tac [`J`,`tf`,`u`] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)) >>
  `tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans` by
    simp[Abbr `tf`, Abbr `tm`, copy_len_binop_ghost_frame] >>
  simp[] >>
  simp[Abbr `u`, Abbr `t`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, venom_state_component_equality] >>
  simp[Abbr `tf`, Abbr `tm`, Abbr `J`, Abbr `H`,
    step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
    update_var_def, out_taint_def,
    step_prov_def, out_prov_def, set_prov_def, first_prov_def, op_prov_def,
    mk_inst_def, set_var_taint_def, op_taint_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  gvs[ptr_covers_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem annassign_dynamic_header_counted:
  !s fn bb id src dst len too_long ok sp dp a b ss ds n cap sa tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [len]) /\
    isPREFIX
      [mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too_long];
       mk_inst (id+2) ISZERO [Var too_long] [ok];
       mk_inst (id+3) ASSERT [Var ok] []]
      (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (id+4) MSTORE [Var dst;Var len] []) /\
    get_instruction bb (s.vs_inst_idx+5) =
      SOME (mk_inst (id+5) ADD [Var src;Lit 32w] [sp]) /\
    get_instruction bb (s.vs_inst_idx+6) =
      SOME (mk_inst (id+6) ADD [Var dst;Lit 32w] [dp]) /\
    ptr_covers G tn src s (32+ss) /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s (32+ds) /\ lookup_var dst s = SOME b /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n a) mem = n2w n) /\
    n <= cap /\ cap < dimword (:256) /\
    w2n a+32 < dimword (:256) /\ w2n b+32 < dimword (:256) /\
    ALL_DISTINCT [len;too_long;ok;sp;dp] /\
    ~MEM src [len;too_long;ok] /\ ~MEM dst [len;too_long;ok;sp] /\
    (!x. not_fresh_at sa x ==> ~MEM x [len;too_long;ok;sp;dp]) ==>
    ?H tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+7 /\
      ~u.vs_halted /\ typed_copy_state_frame sa (w2n b) 32 s u /\
      lookup_var len u = SOME (n2w n) /\ FLOOKUP H len = NONE /\
      op_taint tf (Var len) = {} /\
      lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
      ptr_covers H tf sp u ss /\ ptr_covers H tf dp u ds /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
        mem_word_at (w2n b) mem = n2w n) /\
      (!x. ~MEM x [len;too_long;ok;sp;dp] ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32` by
    (gvs[ptr_covers_def] >> conj_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  `ALL_DISTINCT [len;too_long;ok] /\ ~MEM dst [len;too_long;ok]` by
    gvs[ALL_DISTINCT] >>
  drule_all annassign_dynamic_header_copy_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
   ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb u.vs_inst_idx =
     SOME (mk_inst (id+5) ADD [Var src;Lit 32w] [sp]) /\
   get_instruction bb (u.vs_inst_idx+1) =
     SOME (mk_inst ((id+5)+1) ADD [Var dst;Lit 32w] [dp])` by
    gvs[mstore_def, write_memory_with_expansion_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers H tf src u (32+ss) /\ ptr_covers H tf dst u (32+ds)` by
    (gvs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `sp <> dst /\ sp <> dp` by gvs[ALL_DISTINCT] >>
  drule_all annassign_dynamic_payload_addresses_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H'`,`tf'`,`u'`] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)) >>
  `u'.vs_memory = u.vs_memory` by gvs[update_var_def] >>
  `lookup_var len u' = SOME (n2w n) /\ FLOOKUP H' len = NONE /\
   op_taint tf' (Var len) = {}` by
    (gvs[ALL_DISTINCT, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[] >>
  `!x. ~MEM x [len;too_long;ok;sp;dp] ==>
    lookup_var x u' = lookup_var x s /\ FLOOKUP H' x = FLOOKUP G x /\
    op_taint tf' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> fs[] >>
     gvs[mstore_def, write_memory_with_expansion_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[] >>
  conj_tac >- gvs[update_var_def, mstore_def, write_memory_with_expansion_def] >>
  reverse conj_tac >- (rpt strip_tac >>
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      mstore_def, write_memory_with_expansion_def]) >>
  simp[typed_copy_state_frame_def] >>
  conj_tac >- gvs[update_var_def, mstore_def, write_memory_with_expansion_def,
    venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      mstore_def, write_memory_with_expansion_def]) >>
  simp[update_var_def, typed_copy_frame_def] >>
  conj_tac >- (rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
  simp[mstore_def, write_memory_with_expansion_def, byteTheory.LENGTH_word_to_bytes,
    fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  Cases_on `w2n b+32 > LENGTH s.vs_memory` >> simp[] >> decide_tac
QED
