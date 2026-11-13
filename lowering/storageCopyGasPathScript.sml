(* Actual counted paths for storage/transient word-copy loops. *)
Theory storageCopyGasPath
Ancestors
  exprSimStorageCopy bodyStorageCopyMemory gasSummary fragGasMode
  fragGasPath fragGasPathMem fragGasSeq fragGasSeqMem
  fragExec fragExecMem gasCount context compileEnv emitHelper emitHelperProps
  exprLoweringProps loweringSlice instMemFrontier
  memSafeRun venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem storage_copy_seq_path:
  !code s t memory ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    EVERY (\i. i.inst_opcode <> GAS) code /\
    (memory ==> run_inst_seq_mem_ok code s) /\
    run_inst_seq code s = OK t ==>
    gas_marked_path memory ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  rpt strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM]) >>
  Cases_on `memory` >> gvs[gas_marked_path_def]
  >- (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  drule_all tuple_run_inst_seq_gas_path >> simp[]
QED

Theorem storage_copy_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path memory ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  `inst_mem_below_frontier inst s` by
    (irule below_frontier_no_ranges >> gvs[]) >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def, mem_safe_step_non_invoke] >>
     metis_tac[]) >>
  irule gas_marked_path_from_mem >>
  `gas_path_mem ctx func (jump_to lbl s) 0 (OK (jump_to lbl s))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_mem_rules) >> disch_then drule >> simp[]
QED

Theorem storage_copy_inv_control[local]:
  storage_copy_inv cv ds loc a b n sbase k s ==>
  storage_copy_inv cv ds loc a b n sbase k (jump_to lbl s) /\
  storage_copy_inv cv ds loc a b n sbase k (s with vs_inst_idx := idx)
Proof
  simp[storage_copy_inv_def, eval_operand_def, lookup_var_def,
       jump_to_def, storage_copy_frame_def, copy_prefix_jump, copy_prefix_idx]
QED

Theorem storage_copy_init_path[local]:
  ~s.vs_halted /\ MEM cv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_inv cv ds loc a b n s 0 t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  qexists_tac `(update_var cv 0w s) with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac
  >- (qspec_then `[mk_inst id ASSIGN [Lit 0w] [cv]]` mp_tac storage_copy_seq_path >>
      simp_tac bool_ss [LENGTH, ONE] >> disch_then irule >>
      simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
           step_inst_base_opcode_eqs, eval_operand_def, run_inst_seq_mem_ok_def] >>
      conj_tac
      >- (strip_tac >> irule below_frontier_no_ranges >> simp[]) >>
      gvs[mk_inst_def]) >>
  simp[storage_copy_inv_def, eval_operand_def, eval_operand_update_var,
       lookup_var_update_var, copy_prefix_idx, copy_prefix_zero,
       storage_copy_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       copy_prefix_def, copy_static_def] >>
  metis_tac[]
QED

Theorem storage_copy_test_path[local]:
  ~s.vs_halted /\ cv <> tv /\ MEM tv ds /\ k <= n /\ n < 2**256 /\
  storage_copy_inv cv ds loc a b n sbase k s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_test cv tv ds loc a b n sbase k t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  `k < 2**256` by decide_tac >>
  `((n2w k : bytes32) = n2w n) = (k = n)` by
    (gvs[storage_copy_inv_def] >> gvs[n2w_11, dimword_def]) >>
  `step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s =
   OK (update_var tv (bool_to_word (k = n)) s)` by
    (qpat_assum `(n2w k = n2w n) = (k = n)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> gvs[storage_copy_inv_def, eval_operand_def]) >>
  qexists_tac `(update_var tv (bool_to_word (k = n)) s)
                with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac
  >- (qspec_then `[mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]`
        mp_tac storage_copy_seq_path >>
      simp_tac bool_ss [LENGTH, ONE] >> disch_then irule >>
      simp[run_inst_seq_def, run_inst_seq_mem_ok_def] >>
      conj_tac
      >- (strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
      simp[mk_inst_def, is_terminator_def] >> gvs[mk_inst_def]) >>
  gvs[storage_copy_test_def, storage_copy_inv_def, eval_operand_def,
      eval_operand_update_var, lookup_var_update_var, copy_prefix_idx,
      storage_copy_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      copy_prefix_def, copy_static_def] >>
  metis_tac[]
QED

Theorem storage_copy_body_run_inv[local]:
  run_inst_seq
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t ==>
  storage_copy_inv cv ds loc a b n sbase k s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> MEM x ds) /\
  k < n /\ b+32*n < 2**256 /\
  eval_operand (Var cv) t = SOME (n2w k + 1w) /\
  (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s) ==>
  storage_copy_inv cv ds loc a b n sbase (k+1) t
Proof
  disch_tac >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) storage_copy_body_prefix >>
  disch_then assume_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) storage_copy_body_run_effect >>
  disch_then assume_tac >>
  gvs[storage_copy_inv_def] >>
  qpat_x_assum `!sbase n k b. _`
    (qspecl_then [`sbase`, `n`, `k`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `_ ==> copy_static t = _ /\ _` drule_all >> strip_tac >>
  qpat_x_assum `_ ==> copy_prefix _ _ _ _ _ _ _` drule_all >> strip_tac >>
  drule copy_static_fields >> strip_tac >>
  gvs[storage_copy_frame_def,
      immutableMemoryFrameTheory.immutable_mstore_capacity, word_add_n2w] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!x. x = cv \/ _ ==> MEM x ds`
    (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem storage_copy_body_path[local]:
  code =
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  ~s.vs_halted /\ storage_copy_inv cv ds loc a b n sbase k s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> MEM x ds) /\
  k < n /\ b+32*n < 2**256 /\
  (memory ==> b+32*n <= s.vs_alloca_next) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_inv cv ds loc a b n sbase (k+1) t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 7
Proof
  strip_tac >> (
  `eval_operand (Var cv) s = SOME (n2w k)` by
    gvs[storage_copy_inv_def] >>
  `?r. run_inst_seq code s = OK r /\
       eval_operand (Var cv) r = SOME (n2w k + 1w) /\
       eval_operand src r = SOME a /\ eval_operand dst r = SOME (n2w b) /\
       (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x r = lookup_var x s) /\
       r.vs_current_bb = s.vs_current_bb /\ r.vs_inst_idx = s.vs_inst_idx /\
       r.vs_halted = s.vs_halted /\ r.vs_labels = s.vs_labels` by
    (qpat_assum `code = _` (fn th => rewrite_tac [th]) >>
     irule storage_copy_body_run >> gvs[] >> metis_tac[]) >>
  qpat_assum `code = _` (fn th =>
    qpat_assum `run_inst_seq code s = OK r`
      (assume_tac o REWRITE_RULE [th])) >>
  `storage_copy_inv cv ds loc a b n sbase (k+1) r` by
    (drule storage_copy_body_run_inv >> disch_then irule >>
     asm_rewrite_tac[] >> simp[]) >>
  `memory ==> run_inst_seq_mem_ok code s` by
    (strip_tac >>
     qpat_assum `code = _` (fn th => pure_rewrite_tac [th]) >>
     irule body_storage_iteration_mem_ok >> asm_rewrite_tac[] >>
     qexistsl [`b`, `k`] >> gvs[dimword_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> GAS) code` by
    (simp[mk_inst_def, is_terminator_def] >>
     Cases_on `loc = LocStorage` >> simp[]) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + 7` >>
  conj_tac
  >- (qspec_then `code` mp_tac storage_copy_seq_path >>
      `LENGTH code = 7` by simp[] >>
      qpat_assum `LENGTH code = 7` (fn th => pure_rewrite_tac [th]) >>
      disch_then irule >>
      qpat_x_assum `code = _` kall_tac >> asm_rewrite_tac[] >>
      qexists_tac `bb` >> simp[]) >>
  drule storage_copy_inv_control >> simp[])
QED

Theorem storage_copy_path_jmp[local]:
  gas_marked_path memory ctx func s 0 (OK r) /\
  storage_copy_inv cv ds loc a b n sbase k r /\ ~r.vs_halted /\
  lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb r.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) ==>
  gas_marked_path memory ctx func s 0 (OK (jump_to hdr r)) /\
  storage_copy_inv cv ds loc a b n sbase k (jump_to hdr r) /\
  ~(jump_to hdr r).vs_halted /\
  (jump_to hdr r).vs_current_bb = hdr /\ (jump_to hdr r).vs_inst_idx = 0
Proof
  strip_tac >>
  `gas_marked_path memory ctx func r 0 (OK (jump_to hdr r))` by
    (irule storage_copy_jump_path >> (conj_tac >- simp[]) >>
     qexistsl [`bb`, `mk_inst id JMP [Label hdr] []`] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs]) >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  drule storage_copy_inv_control >> simp[jump_to_def]
QED

Theorem storage_copy_path_jnz[local]:
  gas_marked_path memory ctx func s 0 (OK r) /\
  storage_copy_test cv tv ds loc a b n sbase k r /\ ~r.vs_halted /\
  lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb r.vs_inst_idx =
    SOME (mk_inst id JNZ [Var tv; Label exit; Label loop_body] []) ==>
  gas_marked_path memory ctx func s 0
    (OK (jump_to (if k = n then exit else loop_body) r)) /\
  storage_copy_inv cv ds loc a b n sbase k
    (jump_to (if k = n then exit else loop_body) r) /\
  ~(jump_to (if k = n then exit else loop_body) r).vs_halted /\
  (jump_to (if k = n then exit else loop_body) r).vs_current_bb =
    (if k = n then exit else loop_body) /\
  (jump_to (if k = n then exit else loop_body) r).vs_inst_idx = 0
Proof
  strip_tac >>
  `storage_copy_inv cv ds loc a b n sbase k r /\
   eval_operand (Var tv) r = SOME (bool_to_word (k = n))` by
    gvs[storage_copy_test_def] >>
  `gas_marked_path memory ctx func r 0
     (OK (jump_to (if k = n then exit else loop_body) r))` by
    (irule storage_copy_jump_path >> (conj_tac >- simp[]) >>
     qexistsl [`bb`, `mk_inst id JNZ [Var tv; Label exit; Label loop_body] []`] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs] >>
     Cases_on `k = n` >> simp[bool_to_word_def]) >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  drule storage_copy_inv_control >> simp[jump_to_def]
QED

Theorem storage_copy_iterate_path[local]:
  !(remaining:num) k s.
  (!j q. j <= n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body)) /\
  (!j q. j < n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\ Inv n t /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> qpat_x_assum `!j q. j <= k /\ _ ==> _`
        (qspecl_then [`k`, `s`] mp_tac) >> simp[] >> metis_tac[]) >>
  `k < n` by decide_tac >>
  qpat_assum `!j q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  qpat_assum `!j q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `r`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  qpat_x_assum `!k s. _ /\ _ /\ k + remaining = n /\ _ ==> _`
    (qspecl_then [`k+1`, `v`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD]
QED

Theorem storage_copy_code_prefix:
  !sa sb func. fn_has_code sa sb func /\ same_blocks sa sb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts ==>
  ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb)
         (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  rpt strip_tac >> gvs[fn_has_code_def, same_blocks_def] >>
  gvs[IS_PREFIX_APPEND] >>
  simp[emitted_insts_def, DROP_APPEND1, DROP_APPEND2]
QED

(* The exit block may have PHIs: its compiled instruction prefix is empty.
   The actual final jump can therefore land at index zero. *)
Theorem compile_storage_copy_content_capacity_path:
  !memory (ctx,func) loc src dst n sa u sb sbase a b.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    fn_has_code sa sb func /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\
    eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 /\
    (memory ==> b+32*n <= sbase.vs_alloca_next) /\
    ~sbase.vs_halted /\
    sbase.vs_current_bb = sa.cs_current_bb /\
    sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path memory ctx func sbase 0 (OK t) /\
        copy_prefix loc a b n sbase n t /\
        LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  gen_tac >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qx_gen_tac `cf` >> Cases_on `cf` >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF] >> rpt gen_tac >> strip_tac >> (
  rename1 `gas_marked_path memory ctx func sbase 0 _` >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_storage_copy_certificate >>
  (impl_tac >- simp[]) >> strip_tac >>
  `fn_has_code sa s0 func /\ fn_has_code s0 sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  drule_all frag_exec_loop_layout >> strip_tac >>
  qspecl_then [`sa`, `s0`, `func`] mp_tac storage_copy_code_prefix >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`sth`, `stj`, `func`] mp_tac storage_copy_code_prefix >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`stb`, `ste`, `func`] mp_tac storage_copy_code_prefix >>
  (impl_tac >- simp[]) >> strip_tac >>
  `s0.cs_current_bb = sa.cs_current_bb /\
   stj.cs_current_bb = hdr /\ ste.cs_current_bb = loop_body` by
    gvs[same_blocks_def] >>
  `LENGTH s0.cs_current_insts = LENGTH sa.cs_current_insts + 1 /\
   LENGTH stj.cs_current_insts = 1 /\ LENGTH ste.cs_current_insts = 7` by
    (gvs[emitted_insts_def] >>
     qpat_x_assum `sa.cs_current_insts ≼ s0.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[DROP_APPEND2]) >>
  qabbrev_tac `ds = [cv;tv;sv;vv;mv;dv;nv]` >>
  `?si. gas_marked_path memory ctx func sbase 0 (OK si) /\
        storage_copy_inv cv ds loc a b n sbase 0 si /\
        ~si.vs_halted /\ si.vs_current_bb = sbase.vs_current_bb /\
        si.vs_inst_idx = sbase.vs_inst_idx + 1` by
    (irule storage_copy_init_path >> simp[Abbr `ds`] >>
     qexists_tac `sa.cs_next_id` >> gvs[]) >>
  `?s. gas_marked_path memory ctx func sbase 0 (OK s) /\
       storage_copy_inv cv ds loc a b n sbase 0 s /\
       ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0` by
    (qexists_tac `jump_to hdr si` >> irule storage_copy_path_jmp >>
     asm_rewrite_tac[] >> qexistsl [`bb`, `s0.cs_next_id`] >> gvs[]) >>
  `!j q. j <= n /\ storage_copy_inv cv ds loc a b n sbase j q /\
         ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
      ?r. gas_marked_path memory ctx func q 0 (OK r) /\
          storage_copy_inv cv ds loc a b n sbase j r /\
          ~r.vs_halted /\ r.vs_inst_idx = 0 /\
          r.vs_current_bb = (if j = n then exit else loop_body)` by
    (rpt strip_tac >>
     `?r. gas_marked_path memory ctx func q 0 (OK r) /\
          storage_copy_test cv tv ds loc a b n sbase j r /\
          ~r.vs_halted /\ r.vs_current_bb = q.vs_current_bb /\
          r.vs_inst_idx = q.vs_inst_idx + 1` by
       (irule storage_copy_test_path >> simp[Abbr `ds`] >>
        (conj_tac >- gvs[ALL_DISTINCT]) >>
        qexistsl [`bb'`, `sth.cs_next_id`] >> gvs[]) >>
     `lookup_block r.vs_current_bb func.fn_blocks = SOME bb' /\
      get_instruction bb' r.vs_inst_idx =
        SOME (mk_inst stj.cs_next_id JNZ [Var tv; Label exit; Label loop_body] [])` by
       gvs[] >>
     drule_all storage_copy_path_jnz >> strip_tac >>
     qexists_tac `jump_to (if j = n then exit else loop_body) r` >>
     asm_rewrite_tac[]) >>
  `!j q. j < n /\ storage_copy_inv cv ds loc a b n sbase j q /\
         ~q.vs_halted /\ q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
      ?r. gas_marked_path memory ctx func q 0 (OK r) /\
          storage_copy_inv cv ds loc a b n sbase (j+1) r /\
          ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (rpt strip_tac >>
     `eval_operand src q = SOME a /\ eval_operand dst q = SOME (n2w b) /\
      (memory ==> b+32*n <= q.vs_alloca_next)` by
       (gvs[storage_copy_inv_def, storage_copy_frame_def, copy_prefix_def] >>
        drule copy_static_fields >> strip_tac >>
        conj_tac >- (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
        conj_tac >- (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
        metis_tac[]) >>
     `?r. gas_marked_path memory ctx func q 0 (OK r) /\
          storage_copy_inv cv ds loc a b n sbase (j+1) r /\
          ~r.vs_halted /\ r.vs_current_bb = q.vs_current_bb /\
          r.vs_inst_idx = q.vs_inst_idx + 7` by
       (irule storage_copy_body_path >> asm_rewrite_tac[] >>
        qpat_assum `loc = _` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
        goal_assum (drule_at (Pat `_ = [mk_inst _ ADD _ _;_;_;_;_;_;_]`)) >>
        qpat_assum `stb.cs_current_bb = _`
          (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
        goal_assum (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
        simp[Abbr `ds`] >> gvs[ALL_DISTINCT] >> metis_tac[]) >>
     qexists_tac `jump_to hdr r` >> irule storage_copy_path_jmp >>
     asm_rewrite_tac[] >> qexistsl [`bb''`, `ste.cs_next_id`] >> gvs[]) >>
  `?t. gas_marked_path memory ctx func s 0 (OK t) /\
       storage_copy_inv cv ds loc a b n sbase n t /\
       ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule storage_copy_iterate_path >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl [`hdr`, `loop_body`] >> gvs[]) >>
     qexistsl [`0`, `n`] >> gvs[]) >>
  qexists_tac `t` >>
  `gas_marked_path memory ctx func sbase 0 (OK t)` by
    metis_tac[gas_marked_path_then, ADD] >>
  gvs[storage_copy_inv_def, storage_copy_frame_def, Abbr `ds`] >>
  metis_tac[])
QED
