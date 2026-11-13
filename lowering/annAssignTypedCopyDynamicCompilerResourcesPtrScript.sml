(* Shared compiler-relative resource adapters for dynamic typed copies. *)
Theory annAssignTypedCopyDynamicCompilerResourcesPtr
Ancestors
  annAssignTypedCopyDynamicHeaderPtr annAssignTypedCopyDynamicLoopPtr
  annAssignTypedCopyDynamicTestPtr annAssignTypedCopyFixedControlPtr
  typedNormalizeDynarrayLoop typedNormalizeDynarray
  typedMemoryCopy bodyPtrDefs compileEnv emitHelper fragExec exprLoweringProps
  venomState venomInst venomExecSemantics words arithmetic list rich_list
  freshWrites ASCIInumbers loweringStateRelDefs

Theorem annassign_dynamic_compiler_header:
  !ce dst dt cap src st sa sb fn s a b ss ds n tn G ctx D PG
    len long ok sp dp.
    compile_copy_dynarray_typed ce (Var dst) dt cap (Var src) st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    len = "%" ++ toString sa.cs_next_var /\
    long = "%" ++ toString (sa.cs_next_var+1) /\
    ok = "%" ++ toString (sa.cs_next_var+2) /\
    sp = "%" ++ toString (sa.cs_next_var+3) /\
    dp = "%" ++ toString (sa.cs_next_var+4) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    ptr_covers G tn src s (32+ss) /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s (32+ds) /\ lookup_var dst s = SOME b /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n a) mem = n2w n) /\
    n <= cap /\ cap < dimword (:256) /\
    w2n a+32 < dimword (:256) /\ w2n b+32 < dimword (:256) ==>
    ?H tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
      u.vs_current_bb = sa.cs_current_bb /\
      u.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
      ~u.vs_halted /\ typed_copy_state_frame sa (w2n b) 32 s u /\
      lookup_var len u = SOME (n2w n) /\ FLOOKUP H len = NONE /\
      op_taint tf (Var len) = {} /\
      lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
      ptr_covers H tf sp u ss /\ ptr_covers H tf dp u ds /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
        mem_word_at (w2n b) mem = n2w n) /\
      (!x. ~MEM x [len;long;ok;sp;dp] ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_dynarray_compiler_prefix >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `fn_has_code sa sm fn` mp_tac >>
  pure_rewrite_tac[fn_has_code_def] >> strip_tac >>
  qpat_x_assum `isPREFIX sm.cs_current_insts _` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  `ALL_DISTINCT [len;long;ok;sp;dp] /\
   ~MEM src [len;long;ok] /\ ~MEM dst [len;long;ok;sp] /\
   (!x. not_fresh_at sa x ==> ~MEM x [len;long;ok;sp;dp])` by
    (gvs[not_fresh_at_def, toString_inj] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [len]) /\
   isPREFIX [mk_inst (sa.cs_next_id+1) GT [Var len;Lit (n2w cap)] [long];
     mk_inst (sa.cs_next_id+2) ISZERO [Var long] [ok];
     mk_inst (sa.cs_next_id+3) ASSERT [Var ok] []]
     (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
   get_instruction bb (s.vs_inst_idx+4) =
     SOME (mk_inst (sa.cs_next_id+4) MSTORE [Var dst;Var len] []) /\
   get_instruction bb (s.vs_inst_idx+5) =
     SOME (mk_inst (sa.cs_next_id+5) ADD [Var src;Lit 32w] [sp]) /\
   get_instruction bb (s.vs_inst_idx+6) =
     SOME (mk_inst (sa.cs_next_id+6) ADD [Var dst;Lit 32w] [dp])` by
    (simp[get_instruction_def, EL_APPEND_EQN, DROP_APPEND, ADD1,
          DROP_LENGTH_TOO_LONG] >> metis_tac[]) >>
  drule_all (Q.INST [`sa` |-> `sa`] annassign_dynamic_header_counted) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tf`,`u`] >> gvs[] >> gvs[]
QED

Theorem annassign_dynamic_entry_locations[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts+7) =
      SOME (mk_inst (sa.cs_next_id+7) ASSIGN [Lit 0w]
        ["%" ++ toString (sa.cs_next_var+5)]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+8) =
      SOME (mk_inst (sa.cs_next_id+8) JMP
        [Label (fresh_label_output "typed_dyn_cond" sa.cs_next_label)] [])
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  qexists_tac `initial` >> simp[get_instruction_def] >>
  conj_tac
  >- (qpat_x_assum `DROP _ initial.bb_instructions = _`
        (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_DROP]) >>
  qpat_x_assum `DROP _ initial.bb_instructions = _`
    (mp_tac o Q.AP_TERM `EL 1`) >> simp[EL_DROP, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_entry:
  !ce dst dt cap src st sa sb fn s ctr cond off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME 0w /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\ typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_entry_locations >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> ctr` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var+5` mp_tac) >> simp[]) >>
  irule annassign_dynamic_entry_resources >> simp[] >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  qexists_tac `sa.cs_next_id+7` >> simp[ADD1, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_test[local]:
  !ce dst dt cap src st sa sb fn s ctr bound lt done cond body exit
    k count off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    bound = "%" ++ toString sa.cs_next_var /\
    lt = "%" ++ toString (sa.cs_next_var+6) /\
    done = "%" ++ toString (sa.cs_next_var+7) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    body = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    exit = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    k <= count /\ count < dimword (:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = (if k<count then body else exit) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_dynarray_child_states >> strip_tac >>
  `ALL_DISTINCT [ctr;lt;done] /\ bound <> lt /\ bound <> done /\
   (!x. not_fresh_at sa x ==> x <> lt /\ x <> done)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
      ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  irule annassign_dynamic_test_resources >> simp[] >>
  qexists_tac `sa.cs_next_id+9` >>
  gvs[get_instruction_def, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_backedge[local]:
  !sa se fn back ctr tmp cond s k off size G tn ctx D PG.
    cs_extends sa se /\ sa.cs_next_var+12 <= se.cs_next_var /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    tmp = "%" ++ toString se.cs_next_var /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = se.cs_current_insts ++
      typed_sa_backedge_insts se.cs_next_id ctr tmp cond /\
    s.vs_current_bb = se.cs_current_bb /\
    s.vs_inst_idx = LENGTH se.cs_current_insts /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    FLOOKUP G ctr = NONE ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w (k+1)) /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\ typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr /\ x <> tmp ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ctr <> tmp /\ (!x. not_fresh_at sa x ==> x <> ctr /\ x <> tmp)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  irule annassign_dynamic_backedge_resources >> simp[] >>
  qexists_tac `se.cs_next_id` >>
  simp[get_instruction_def, typedArrayLoopControlMemTheory.typed_sa_backedge_insts_def, EL_APPEND_EQN,
    ADD_ASSOC, ADD1]
QED

Theorem annassign_dynamic_loop_test:
  !ce dst dt cap src st sa sb fn s ctr bound lt done cond body exit
    k count off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    bound = "%" ++ toString sa.cs_next_var /\
    lt = "%" ++ toString (sa.cs_next_var+6) /\
    done = "%" ++ toString (sa.cs_next_var+7) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    body = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    exit = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    k <= count /\ count < dimword (:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = (if k<count then body else exit) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
        x = "%" ++ toString (sa.cs_next_var+4) \/ x = bound ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_compiler_test >>
  disch_then (qspecl_then [`off`,`size'`,`D`,`PG`] strip_assume_tac) >>
  qexistsl [`H`,`tm`,`t`] >> simp[] >>
  gen_tac >> disch_tac >>
  `x <> lt /\ x <> done` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem annassign_dynamic_loop_backedge:
  !sa se fn back ctr tmp bound cond s k count off size G tn ctx D PG.
    cs_extends sa se /\ sa.cs_next_var+12 <= se.cs_next_var /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    tmp = "%" ++ toString se.cs_next_var /\
    bound = "%" ++ toString sa.cs_next_var /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = se.cs_current_insts ++
      typed_sa_backedge_insts se.cs_next_id ctr tmp cond /\
    s.vs_current_bb = se.cs_current_bb /\
    s.vs_inst_idx = LENGTH se.cs_current_insts /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    FLOOKUP G ctr = NONE /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var bound) = {} /\ FLOOKUP G bound = NONE ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w (SUC k)) /\
      lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
        x = "%" ++ toString (sa.cs_next_var+4) \/ x = bound ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_compiler_backedge >>
  disch_then (qspecl_then [`off`,`size'`,`D`,`PG`] strip_assume_tac) >>
  `bound <> ctr /\ bound <> tmp /\
   (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
     x = "%" ++ toString (sa.cs_next_var+4) \/ x = bound ==>
     x <> ctr /\ x <> tmp)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  qexistsl [`H`,`tm`,`t`] >> gvs[ADD1] >> metis_tac[]
QED

Theorem annassign_dynamic_address_locations[local]:
  !ce dst dt cap src st sa sb fn.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn ==>
    ?bb. lookup_block (fresh_label_output "typed_dyn_body" (sa.cs_next_label+1))
      fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst (sa.cs_next_id+12) MUL
      [Var ("%" ++ toString (sa.cs_next_var+5));Lit (n2w (type_memory_bytes ce st))]
      ["%" ++ toString (sa.cs_next_var+8)]) /\
    get_instruction bb 1 = SOME (mk_inst (sa.cs_next_id+13) MUL
      [Var ("%" ++ toString (sa.cs_next_var+5));Lit (n2w (type_memory_bytes ce dt))]
      ["%" ++ toString (sa.cs_next_var+9)]) /\
    get_instruction bb 2 = SOME (mk_inst (sa.cs_next_id+14) ADD
      [Var ("%" ++ toString (sa.cs_next_var+3));Var ("%" ++ toString (sa.cs_next_var+8))]
      ["%" ++ toString (sa.cs_next_var+10)]) /\
    get_instruction bb 3 = SOME (mk_inst (sa.cs_next_id+15) ADD
      [Var ("%" ++ toString (sa.cs_next_var+4));Var ("%" ++ toString (sa.cs_next_var+9))]
      ["%" ++ toString (sa.cs_next_var+11)])
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_dynarray_child_states >> strip_tac >>
  `cs_extends sc ec` by gvs[ci_mono_def] >>
  drule_all fn_has_code_start >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `isPREFIX sc.cs_current_insts bb.bb_instructions` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN]
QED

Theorem annassign_dynamic_compiler_address[local]:
  !ce dst dt cap src st sa sb fn s ctr sr dr so doff sp dp k ss ds a b S T
    off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    sr = "%" ++ toString (sa.cs_next_var+3) /\
    dr = "%" ++ toString (sa.cs_next_var+4) /\
    so = "%" ++ toString (sa.cs_next_var+8) /\
    doff = "%" ++ toString (sa.cs_next_var+9) /\
    sp = "%" ++ toString (sa.cs_next_var+10) /\
    dp = "%" ++ toString (sa.cs_next_var+11) /\
    ss = type_memory_bytes ce st /\ ds = type_memory_bytes ce dt /\
    s.vs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    k*ss < S /\ k*ss+ss <= S /\ k*ds < T /\ k*ds+ds <= T /\
    w2n a+k*ss < dimword(:256) /\ w2n b+k*ds < dimword(:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+4 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
      lookup_var sp t = SOME (n2w (w2n a+k*ss)) /\
      lookup_var dp t = SOME (n2w (w2n b+k*ds)) /\
      ptr_covers H tm sp t ss /\ ptr_covers H tm dp t ds /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. ~MEM x [so;doff;sp;dp] ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_address_locations >> strip_tac >>
  `ALL_DISTINCT [so;doff;sp;dp] /\
   (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
   (!v. not_fresh_at sa v ==> ~MEM v [so;doff;sp;dp])` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  rename1 `ptr_covers G tn sr s source_size` >>
  rename1 `ptr_covers G tn dr s dest_size` >>
  irule annassign_loop_address_resources >> simp[] >>
  qexistsl_tac [`source_size`, `dest_size`, `dr`, `sa.cs_next_id+12`, `sr`] >>
  gvs[ADD_ASSOC] >> metis_tac[]
QED

Theorem annassign_dynamic_loop_address:
  !ce dst dt cap src st sa sb fn s ctr sr dr so doff sp dp bound
    k count ss ds a b S T off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    sr = "%" ++ toString (sa.cs_next_var+3) /\
    dr = "%" ++ toString (sa.cs_next_var+4) /\
    so = "%" ++ toString (sa.cs_next_var+8) /\
    doff = "%" ++ toString (sa.cs_next_var+9) /\
    sp = "%" ++ toString (sa.cs_next_var+10) /\
    dp = "%" ++ toString (sa.cs_next_var+11) /\
    bound = "%" ++ toString sa.cs_next_var /\
    ss = type_memory_bytes ce st /\ ds = type_memory_bytes ce dt /\
    s.vs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    FLOOKUP G ctr = NONE /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var bound) = {} /\ FLOOKUP G bound = NONE /\
    lookup_var sr s = SOME (n2w a) /\ lookup_var dr s = SOME (n2w b) /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    k*ss < S /\ k*ss+ss <= S /\ k*ds < T /\ k*ds+ds <= T /\
    a+k*ss < dimword(:256) /\ b+k*ds < dimword(:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\ t.vs_inst_idx = 4 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      lookup_var sp t = SOME (n2w (a+k*ss)) /\
      lookup_var dp t = SOME (n2w (b+k*ds)) /\
      ptr_covers H tm sp t ss /\ ptr_covers H tm dp t ds /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `a < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  `w2n (n2w a : bytes32) = a /\ w2n (n2w b : bytes32) = b` by simp[] >>
  `w2n (n2w a : bytes32) + k*ss < dimword(:256) /\
   w2n (n2w b : bytes32) + k*ds < dimword(:256)` by metis_tac[] >>
  drule_all annassign_dynamic_compiler_address >>
  disch_then (qspecl_then [`off`,`size'`,`D`,`PG`] strip_assume_tac) >>
  `~MEM ctr [so;doff;sp;dp] /\ ~MEM bound [so;doff;sp;dp] /\
   (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
      ~MEM x [so;doff;sp;dp])` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  qexistsl [`H`,`tm`,`t`] >> gvs[] >> metis_tac[]
QED
