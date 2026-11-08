(* Memory-safe primitive paths for live-slot storage stores. *)
Theory storeSlotsMemoryPaths
Ancestors
  bodyMemAssignTopCopyPaths placeStoreStorage typedMemoryCopy
  fragGasSeqMem fragGasSeqAbort fragGasMode fragExecMem instMemFrontier
  emitHelper emitHelperProps exprLoweringProps context compileEnv
  venomExecSemantics venomState venomInst list rich_list finite_map words
  arithmetic valueEncoding valueEncodingProps

Theorem store_slots_emitted_seq_path_mem:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_path T ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> rewrite_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[gas_marked_path_def]
QED

Theorem store_slots_emit_op_path_mem:
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. inst_mem_below_frontier (mk_inst sa.cs_next_id opc args [out]) s /\
         inst_dload_in_section (mk_inst sa.cs_next_id opc args [out]) s) /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
    OK (update_var out w s)) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
      t.vs_alloca_next = s.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path T ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var)) w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule store_slots_emitted_seq_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[run_inst_seq_def, run_inst_seq_mem_ok_last] >>
     gvs[mk_inst_def]) >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var)) w s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def] >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
       venom_state_component_equality, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >> simp[]
QED

Theorem store_slots_bytes_count_path_mem:
  compile_bytestring_word_count src sa = (cnt,sm) /\
  eval_operand src s = SOME sw /\
  mem_word_at (w2n sw) s.vs_memory = n2w L /\
  w2n sw + 32 <= s.vs_alloca_next /\
  L + 63 < dimword (:256) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
      u.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s u) /\
      u.vs_alloca_next = s.vs_alloca_next /\
      ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] sa = (loaded,a)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [loaded; Lit 63w] a = (sum,b)` >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sm` by
    metis_tac[typed_copy_emit_op_mono] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sm func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                                  cs_extends_trans]) >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       eval_operand loaded t = SOME (n2w L) /\
       t.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
       t.vs_alloca_next = s.vs_alloca_next /\
       ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
       t.vs_inst_idx = LENGTH a.cs_current_insts` by
    (irule store_slots_emit_op_path_mem >> simp[] >>
     qexistsl_tac [`[src]`, `MLOAD`] >>
     simp[is_terminator_def, below_frontier_MLOAD, mk_inst_def,
          step_inst_base_opcode_eqs, exec_read1_def,
          GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  suspend "rest"
QED

Resume store_slots_bytes_count_path_mem[rest]:
  `?r. gas_marked_path T ctx func t 0 (OK r) /\
       eval_operand sum r = SOME (n2w (L + 63)) /\
       r.vs_memory = t.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len t r) /\
       r.vs_alloca_next = t.vs_alloca_next /\
       ~r.vs_halted /\ r.vs_current_bb = b.cs_current_bb /\
       r.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule store_slots_emit_op_path_mem >> simp[] >>
     qexistsl_tac [`[loaded; Lit 63w]`, `ADD`] >>
     simp[is_terminator_def, below_frontier_no_ranges, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, eval_operand_def,
          GSYM wordsTheory.word_add_n2w]) >>
  `(n2w (L + 63):bytes32) >>> 5 = n2w (1 + word_size L)` by
    (once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
     simp[Excl "w2n_11", wordsTheory.w2n_lsr, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD, vfmConstantsTheory.word_size_def] >>
     qspec_then `L + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     qspec_then `L + 63` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     rpt strip_tac >>
     `(L + 31) DIV 32 + 1 < dimword (:256)` by intLib.ARITH_TAC >>
     simp[arithmeticTheory.LESS_MOD] >> intLib.ARITH_TAC) >>
  `?u. gas_marked_path T ctx func r 0 (OK u) /\
       eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
       u.vs_memory = r.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame b off len r u) /\
       u.vs_alloca_next = r.vs_alloca_next /\
       ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (irule store_slots_emit_op_path_mem >> simp[] >>
     qexistsl_tac [`[Lit 5w; sum]`, `SHR`] >>
     simp[is_terminator_def, below_frontier_no_ranges, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `t` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  rpt gen_tac >>
  metis_tac[typed_copy_state_frame_trans, typed_copy_state_frame_mono]
QED
Finalise store_slots_bytes_count_path_mem

Theorem store_slots_runtime_test_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; countop] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  store_copy_frame sa loc b k s0 i s /\
  eval_operand (Var cv) s = SOME (n2w i) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  eval_operand countop s = SOME (n2w n) /\
  i <= n /\ n < dimword (:256) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s0 i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var tv) t = SOME (if i = n then 1w else 0w) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  `bool_to_word (n2w i = n2w n : bytes32) =
   (if i = n then 1w else 0w)` by
    (Cases_on `i = n` >> simp[n2w_11, LESS_MOD, bool_to_word_def]) >>
  `run_inst_seq [mk_inst id EQ [Var cv; countop] [tv]] s =
   OK (update_var tv (if i = n then 1w else 0w) s)` by
    simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``EQ``,
         mk_inst_def, exec_pure2_def] >>
  `run_inst_seq_mem_ok [mk_inst id EQ [Var cv; countop] [tv]] s` by
    (simp[run_inst_seq_mem_ok_last] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  qexists_tac `(update_var tv (if i = n then 1w else 0w) s)
    with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac >- simp[] >>
  `store_copy_frame sa loc b k s0 i
     (update_var tv (if i = n then 1w else 0w) s)` by
    (irule topcopy_frame_update >> metis_tac[]) >>
  gvs[eval_operand_def, lookup_var_update_var, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem store_slots_runtime_header_path_mem:
  store_copy_frame sa loc b k s0 i s /\
  eval_operand (Var cv) s = SOME (n2w i) /\
  eval_operand countop s = SOME (n2w n) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  i <= n /\ n < dimword (:256) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; countop] [tv];
    mk_inst (id+1) JNZ [Var tv; Label exit; Label bodylbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s0 i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = (if i = n then exit else bodylbl) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `isPREFIX [mk_inst id EQ [Var cv; countop] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX [_; _] _` mp_tac >>
     pure_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     simp[Excl "isPREFIX"] >> qexists_tac `_::l` >> simp[]) >>
  drule_all store_slots_runtime_test_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb t.vs_inst_idx =
    SOME (mk_inst (id+1) JNZ [Var tv; Label exit; Label bodylbl] [])` by
    (qpat_assum `isPREFIX [_; _] _`
      (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv; Label exit; Label bodylbl] []) t =
    OK (jump_to (if i = n then exit else bodylbl) t)` by
    (simp[stepInstBaseLib.simp_opcode_clause ``JNZ``, mk_inst_def] >>
     Cases_on `i = n` >> gvs[]) >>
  `gas_marked_path T ctx func t 0
    (OK (jump_to (if i = n then exit else bodylbl) t))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists_tac `mk_inst (id+1) JNZ [Var tv; Label exit; Label bodylbl] []` >>
     gvs[mk_inst_def]) >>
  qexists_tac `jump_to (if i = n then exit else bodylbl) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  gvs[topcopy_frame_jump, jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem store_slots_runtime_init_path_mem:
  ~s.vs_halted /\ (!x. not_fresh_at sa x ==> x <> cv) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv];
    mk_inst (id+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s 0 t /\
      eval_operand (Var cv) t = SOME 0w /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
  drule_all topcopy_init_path >>
  disch_then (qspecl_then [`ctx`, `loc`, `b`, `k`] strip_assume_tac) >>
  `get_instruction bb t.vs_inst_idx =
    SOME (mk_inst (id+1) JMP [Label hdr] [])` by
    (drule instruction_prefix_cursor >> simp[]) >>
  `step_inst_base (mk_inst (id+1) JMP [Label hdr] []) t =
    OK (jump_to hdr t)` by
    simp[stepInstBaseLib.simp_opcode_clause ``JMP``, mk_inst_def] >>
  `gas_marked_path T ctx func t 0 (OK (jump_to hdr t))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists_tac `mk_inst (id+1) JMP [Label hdr] []` >> gvs[mk_inst_def]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  gvs[topcopy_frame_jump, jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem store_slots_runtime_body_path_mem:
  store_copy_frame sa loc b k s0 i s /\ ~s0.vs_call_ctx.cc_static /\
  (loc = LocStorage \/ loc = LocTransient) /\
  w2n b + 32*(i+1) <= s0.vs_alloca_next /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand (Var cv) s = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv];
     mk_inst (id+7) JMP [Label hdr] []] bb.bb_instructions ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s0 (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `isPREFIX _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa loc b k s0 (SUC i) t /\
       eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
       t.vs_current_bb = s.vs_current_bb /\
       t.vs_inst_idx = s.vs_inst_idx+7 /\ ~t.vs_halted` by
    (irule topcopy_body_path >>
     rpt (goal_assum (drule_at Any)) >>
     simp[get_instruction_def, mk_inst_def] >> gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `get_instruction bb t.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] [])` by
    simp[get_instruction_def] >>
  `step_inst_base (mk_inst (id+7) JMP [Label hdr] []) t = OK (jump_to hdr t)` by
    simp[stepInstBaseLib.simp_opcode_clause ``JMP``, mk_inst_def] >>
  `gas_marked_path T ctx func t 0 (OK (jump_to hdr t))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists_tac `mk_inst (id+7) JMP [Label hdr] []` >> gvs[mk_inst_def]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  gvs[topcopy_frame_jump, jump_to_def, eval_operand_def, lookup_var_def]
QED
