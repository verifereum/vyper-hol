(* Counted storage-copy paths without memory-content or address bounds. *)
Theory stmtSimReasonStoragePath
Ancestors
  exprSimStorageCopy storageCopyGasPath fragGasPath fragGasSeq gasCount
  fragExec exprLoweringProps emitHelperProps venomInstProps loweringHalt
  context compileEnv loweringStateRelDefs
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem storage_reason_modular_test[local]:
  k <= w2n (n2w n : bytes32) ==>
  ((n2w k : bytes32) = n2w n <=> k = w2n (n2w n : bytes32))
Proof
  strip_tac >>
  `k < dimword (:256)` by
    (qspec_then `n2w n : bytes32` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  metis_tac[w2n_n2w, LESS_MOD, n2w_w2n]
QED

Theorem storage_reason_jump_path[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def] >>
     gvs[is_terminator_def] >> metis_tac[]) >>
  `gas_path ctx func (jump_to lbl s) 0 (OK (jump_to lbl s))` by
    (irule (cj 1 gas_path_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[]
QED

Theorem storage_reason_body_path[local]:
  code =
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) opc [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  (opc = SLOAD \/ opc = TLOAD) /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand (Var cv) s = SOME k /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (k+1w) /\
      eval_operand src t = SOME a /\ eval_operand dst t = SOME b /\
      (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 7 /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> (
  `?r. run_inst_seq code s = OK r /\
       eval_operand (Var cv) r = SOME (k+1w) /\
       eval_operand src r = SOME a /\ eval_operand dst r = SOME b /\
       (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x r = lookup_var x s) /\
       r.vs_current_bb = s.vs_current_bb /\ r.vs_inst_idx = s.vs_inst_idx /\
       r.vs_halted = s.vs_halted /\ r.vs_labels = s.vs_labels` by
    (qpat_assum `code = _` (fn th => rewrite_tac [th]) >>
     irule storage_copy_body_run >> gvs[] >> metis_tac[]) >>
  rename1 `run_inst_seq _ s = OK r` >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + 7` >>
  conj_tac
  >- (qspec_then `code` mp_tac tuple_run_inst_seq_gas_path >>
      `LENGTH code = 7 /\ FILTER (\i. i.inst_opcode = GAS) code = []` by
        (gvs[mk_inst_def]) >>
      asm_rewrite_tac[LENGTH] >> disch_then irule >>
      gvs[mk_inst_def, is_terminator_def]) >>
  gvs[eval_operand_def, lookup_var_def])
QED

Theorem storage_reason_init_path[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME 0w /\
      (!x. x <> cv ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1 /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  qexists_tac `(update_var cv 0w s) with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac
  >- (qspec_then `[mk_inst id ASSIGN [Lit 0w] [cv]]`
        mp_tac tuple_run_inst_seq_gas_path >>
      simp_tac (srw_ss()) [LENGTH, FILTER, mk_inst_def] >>
      disch_then irule >>
      gvs[mk_inst_def, is_terminator_def, run_inst_seq_def,
          step_inst_base_opcode_eqs, eval_operand_def]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem storage_reason_test_path[local]:
  ~s.vs_halted /\ cv <> tv /\ k <= w2n (n2w n : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (n2w k) /\
      eval_operand (Var tv) t = SOME (bool_to_word (k = w2n (n2w n : bytes32))) /\
      (!x. x <> tv ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1 /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `((n2w k : bytes32) = n2w n) = (k = w2n (n2w n : bytes32))` by
    (irule storage_reason_modular_test >> simp[]) >>
  `step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s =
   OK (update_var tv (bool_to_word (k = w2n (n2w n : bytes32))) s)` by
    (qpat_assum `(n2w k = n2w n) = _`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> simp[eval_operand_def]) >>
  qexists_tac `(update_var tv (bool_to_word (k = w2n (n2w n : bytes32))) s)
                 with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac
  >- (qspec_then `[mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]`
        mp_tac tuple_run_inst_seq_gas_path >>
      simp_tac (srw_ss()) [LENGTH, FILTER, mk_inst_def] >>
      disch_then irule >>
      gvs[mk_inst_def, is_terminator_def, run_inst_seq_def]) >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem storage_reason_branch_path[local]:
  ~s.vs_halted /\ eval_operand (Var tv) s = SOME (bool_to_word test) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [Var tv; Label exit; Label loop_body] []) ==>
  gas_path ctx func s 0 (OK (jump_to (if test then exit else loop_body) s))
Proof
  strip_tac >> irule storage_reason_jump_path >> simp[] >>
  simp[mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp_tac (srw_ss()) [] >>
  asm_rewrite_tac[] >>
  Cases_on `test` >>
  gvs[step_inst_base_opcode_eqs, eval_operand_def, bool_to_word_def]
QED

(* One cycle includes the test and, unless finished, the copy and back-edge. *)
Theorem storage_reason_cycles_path[local]:
  !remaining k s.
  (!j q. j <= w2n (n2w n : bytes32) /\
         eval_operand (Var cv) q = SOME (n2w j) /\
         (!x. ~MEM x ds ==> lookup_var x q = lookup_var x sbase) /\
         q.vs_labels = sbase.vs_labels /\ ~q.vs_halted /\
         q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_path ctx func q 0 (OK r) /\
         eval_operand (Var cv) r = SOME (n2w (if j = w2n (n2w n : bytes32) then j else j+1)) /\
         (!x. ~MEM x ds ==> lookup_var x r = lookup_var x sbase) /\
         r.vs_labels = sbase.vs_labels /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = w2n (n2w n : bytes32) then exit else hdr)) /\
  k + remaining = w2n (n2w n : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  (!x. ~MEM x ds ==> lookup_var x s = lookup_var x sbase) /\
  s.vs_labels = sbase.vs_labels /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      (!x. ~MEM x ds ==> lookup_var x t = lookup_var x sbase) /\
      t.vs_labels = sbase.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!j q. _` (qspecl_then [`k`, `s`] mp_tac) >>
      gvs[] >> metis_tac[]) >>
  `k < w2n (n2w n : bytes32)` by decide_tac >>
  qpat_assum `!j q. _` (qspecl_then [`k`, `s`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  `k <> w2n (n2w n : bytes32)` by decide_tac >>
  gvs[Excl "w2n_n2w"] >>
  qpat_x_assum `!k' s'. k' + remaining = _ /\ _ ==> _`
    (qspecl_then [`k+1`, `r`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  drule_all gas_path_then >> simp[]
QED

Theorem storage_reason_header_path[local]:
  ~s.vs_halted /\ cv <> tv /\ MEM tv ds /\
  k <= w2n (n2w n : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+1) =
    SOME (mk_inst jid JNZ [Var tv; Label exit; Label loop_body] []) ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (n2w k) /\
      (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if k = w2n (n2w n : bytes32) then exit else loop_body)
Proof
  strip_tac >> drule_all storage_reason_test_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `r` strip_assume_tac)) >>
  `gas_path ctx func r 0
     (OK (jump_to (if k = w2n (n2w n : bytes32) then exit else loop_body) r))` by
    (irule storage_reason_branch_path >> simp[] >>
     qexistsl [`jid`, `tv`] >> gvs[]) >>
  qexists_tac `jump_to (if k = w2n (n2w n : bytes32) then exit else loop_body) r` >>
  conj_tac >- (drule_all gas_path_then >> simp[]) >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem storage_reason_back_path[local]:
  code =
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) opc [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  (opc = SLOAD \/ opc = TLOAD) /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> MEM x ds) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst jid JMP [Label hdr] []) ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (n2w (k+1)) /\
      (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >> (
  `?r. gas_path ctx func s 0 (OK r) /\
       eval_operand (Var cv) r = SOME (n2w k+1w) /\
       eval_operand src r = SOME a /\ eval_operand dst r = SOME b /\
       (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x r = lookup_var x s) /\
       ~r.vs_halted /\ r.vs_current_bb = s.vs_current_bb /\
       r.vs_inst_idx = s.vs_inst_idx + 7 /\ r.vs_labels = s.vs_labels` by
    (irule storage_reason_body_path >> asm_rewrite_tac[] >>
     qexistsl [`bb`, `code`, `id`, `opc`] >> gvs[]) >>
  `gas_path ctx func r 0 (OK (jump_to hdr r))` by
    (irule storage_reason_jump_path >> (conj_tac >- simp[]) >>
     qexistsl [`bb`, `mk_inst jid JMP [Label hdr] []`] >>
     gvs[mk_inst_def, step_inst_base_opcode_eqs]) >>
  qexists_tac `jump_to hdr r` >> conj_tac
  >- (drule_all gas_path_then >> simp[]) >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def, word_add_n2w] >>
  metis_tac[])
QED

(* Eliminate compiler states once, exposing only executable block slices. *)
Theorem storage_reason_copy_layout[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb func ==>
  ?bbi bbh bbb hdr loop_body exit cv tv sv vv mv dv nv hi bi ji jh jb.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bbi /\
    isPREFIX [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]]
      (DROP (LENGTH sa.cs_current_insts) bbi.bb_instructions) /\
    get_instruction bbi (LENGTH sa.cs_current_insts+1) =
      SOME (mk_inst ji JMP [Label hdr] []) /\
    lookup_block hdr func.fn_blocks = SOME bbh /\
    isPREFIX [mk_inst hi EQ [Var cv; Lit (n2w n)] [tv]] bbh.bb_instructions /\
    get_instruction bbh 1 =
      SOME (mk_inst jh JNZ [Var tv; Label exit; Label loop_body] []) /\
    lookup_block loop_body func.fn_blocks = SOME bbb /\
    isPREFIX
      [mk_inst bi ADD [src; Var cv] [sv];
       mk_inst (bi+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (bi+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (bi+3) ADD [dst; Var mv] [dv];
       mk_inst (bi+4) MSTORE [Var dv; Var vv] [];
       mk_inst (bi+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (bi+6) ASSIGN [Var nv] [cv]] bbb.bb_instructions /\
    get_instruction bbb 7 = SOME (mk_inst jb JMP [Label hdr] []) /\
    ALL_DISTINCT [cv;tv;sv;vv;mv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;sv;vv;mv;dv;nv]) /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  rename1 `emit_inst JMP [Label hdr] [] si = ((),sj)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sh = (Var tv,st)` >>
  rename1 `new_block loop_body _ = (_,sc)` >>
  rename1 `emit_inst JMP [Label hdr] [] se = ((),_)` >>
  `fn_has_code sa si func /\ fn_has_code si sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  drule_all frag_exec_loop_layout >> strip_tac >>
  `!a b. fn_has_code a b func /\ same_blocks a b /\
         isPREFIX a.cs_current_insts b.cs_current_insts ==>
     ?bb. lookup_block a.cs_current_bb func.fn_blocks = SOME bb /\
          isPREFIX (emitted_insts a b)
            (DROP (LENGTH a.cs_current_insts) bb.bb_instructions)` by
    (rpt strip_tac >> gvs[fn_has_code_def, same_blocks_def] >>
     gvs[IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_APPEND1, DROP_APPEND2]) >>
  first_assum (qspecl_then [`sa`, `si`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_assum (qspecl_then [`sh`, `st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (qspecl_then [`sc`, `se`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `si.cs_current_bb = sa.cs_current_bb /\ st.cs_current_bb = hdr /\
   se.cs_current_bb = loop_body` by gvs[same_blocks_def] >>
  `LENGTH si.cs_current_insts = LENGTH sa.cs_current_insts+1 /\
   LENGTH st.cs_current_insts = 1 /\ LENGTH se.cs_current_insts = 7` by
    (gvs[emitted_insts_def] >>
     qpat_x_assum `sa.cs_current_insts ≼ si.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[DROP_APPEND2]) >>
  rpt (qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `fn_has_code _ _ _` kall_tac) >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `cs_extends _ _` kall_tac) >>
  rpt (qpat_x_assum `same_blocks _ _` kall_tac) >>
  gvs[Excl "isPREFIX"] >>
  rename1 `get_instruction bbi (LENGTH sa.cs_current_insts+1) =
    SOME (mk_inst _ JMP [Label hdr] [])` >>
  rename1 `get_instruction bbh 1 = SOME (mk_inst _ JNZ _ [])` >>
  rename1 `get_instruction bbb 7 = SOME (mk_inst _ JMP _ [])` >>
  qexistsl [`bbh`, `bbb`, `hdr`, `sc.cs_current_bb`,
    `cv`, `tv`, `sv`, `vv`, `mv`, `dv`, `nv`, `sh.cs_next_id`, `sc.cs_next_id`,
    `si.cs_next_id`, `st.cs_next_id`, `se.cs_next_id`] >>
  asm_rewrite_tac[]
QED

Theorem compile_storage_reason_copy_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
  ~sbase.vs_halted /\ sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func sbase 0 (OK t) /\ ~t.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      t.vs_labels = sbase.vs_labels /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_reason_copy_layout >> strip_tac >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qabbrev_tac `ds = [cv;tv;sv;vv;mv;dv;nv]` >>
  `?si. gas_path ctx func sbase 0 (OK si) /\
        eval_operand (Var cv) si = SOME 0w /\
        (!x. ~MEM x ds ==> lookup_var x si = lookup_var x sbase) /\
        si.vs_labels = sbase.vs_labels /\ ~si.vs_halted /\
        si.vs_current_bb = hdr /\ si.vs_inst_idx = 0` by suspend "init" >>
  `!j q. j <= w2n (n2w n : bytes32) /\
         eval_operand (Var cv) q = SOME (n2w j) /\
         (!x. ~MEM x ds ==> lookup_var x q = lookup_var x sbase) /\
         q.vs_labels = sbase.vs_labels /\ ~q.vs_halted /\
         q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_path ctx func q 0 (OK r) /\
         eval_operand (Var cv) r = SOME (n2w (if j = w2n (n2w n : bytes32) then j else j+1)) /\
         (!x. ~MEM x ds ==> lookup_var x r = lookup_var x sbase) /\
         r.vs_labels = sbase.vs_labels /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = w2n (n2w n : bytes32) then exit else hdr)` by
    suspend "cycle" >>
  `?t. gas_path ctx func si 0 (OK t) /\
       (!x. ~MEM x ds ==> lookup_var x t = lookup_var x sbase) /\
       t.vs_labels = sbase.vs_labels /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule storage_reason_cycles_path >> asm_rewrite_tac[] >>
     qexistsl [`cv`, `hdr`, `0`, `n`, `w2n (n2w n : bytes32)`] >> simp[]) >>
  qexists_tac `t` >>
  `gas_path ctx func sbase 0 (OK t)` by
    (drule_all gas_path_then >> simp[]) >>
  gvs[Abbr `ds`] >> metis_tac[]
QED

Resume compile_storage_reason_copy_path[init]:
  `?r. gas_path ctx func sbase 0 (OK r) /\
       eval_operand (Var cv) r = SOME 0w /\
       (!x. x <> cv ==> lookup_var x r = lookup_var x sbase) /\
       ~r.vs_halted /\ r.vs_current_bb = sbase.vs_current_bb /\
       r.vs_inst_idx = sbase.vs_inst_idx + 1 /\ r.vs_labels = sbase.vs_labels` by
    (irule storage_reason_init_path >> asm_rewrite_tac[] >>
     qexistsl [`bbi`, `sa.cs_next_id`] >> simp[]) >>
  `gas_path ctx func r 0 (OK (jump_to hdr r))` by
    (irule storage_reason_jump_path >> (conj_tac >- simp[]) >>
     qexistsl [`bbi`, `mk_inst ji JMP [Label hdr] []`] >>
     gvs[mk_inst_def, step_inst_base_opcode_eqs]) >>
  qexists_tac `jump_to hdr r` >> conj_tac
  >- (drule_all gas_path_then >> simp[]) >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def, Abbr `ds`] >> metis_tac[]
QED

Resume compile_storage_reason_copy_path[cycle]:
  qpat_x_assum `gas_path _ _ sbase _ _` kall_tac >>
  rpt (qpat_x_assum `_ si = _` kall_tac) >>
  rpt (qpat_x_assum `si.vs_labels = _` kall_tac) >>
  rpt (qpat_x_assum `~si.vs_halted` kall_tac) >>
  rpt gen_tac >> strip_tac >>
  `cv <> tv /\ MEM tv ds` by gvs[Abbr `ds`, ALL_DISTINCT] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh /\
   isPREFIX [mk_inst hi EQ [Var cv; Lit (n2w n)] [tv]]
     (DROP q.vs_inst_idx bbh.bb_instructions) /\
   get_instruction bbh (q.vs_inst_idx+1) =
     SOME (mk_inst jh JNZ [Var tv; Label exit; Label loop_body] [])` by
    simp[Excl "isPREFIX"] >>
  drule_all storage_reason_header_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `r` strip_assume_tac)) >>
  `(!x. ~MEM x ds ==> lookup_var x r = lookup_var x sbase) /\
   r.vs_labels = sbase.vs_labels` by metis_tac[] >>
  Cases_on `j = w2n (n2w n : bytes32)`
  >- (qexists_tac `r` >> simp[]) >>
  `eval_operand src r = SOME a /\ eval_operand dst r = SOME b` by
    (conj_tac >> irule storage_copy_operand_frame >>
     qexistsl [`ds`, `sbase`] >> metis_tac[]) >>
  `?t. gas_path ctx func r 0 (OK t) /\
       eval_operand (Var cv) t = SOME (n2w (j+1)) /\
       (!x. ~MEM x ds ==> lookup_var x t = lookup_var x r) /\
       t.vs_labels = r.vs_labels /\ ~t.vs_halted /\
       t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    (qmatch_asmsub_abbrev_tac `isPREFIX body_code bbb.bb_instructions` >>
     irule storage_reason_back_path >> asm_rewrite_tac[] >>
     qexistsl [`a`, `b`, `bbb`, `body_code`, `dst`, `dv`, `bi`, `jb`, `mv`, `nv`,
       `if loc = LocStorage then SLOAD else TLOAD`, `src`, `sv`, `vv`] >>
     gvs[Abbr `body_code`, Abbr `ds`, ALL_DISTINCT] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  drule_all gas_path_then >> simp[]
QED

Finalise compile_storage_reason_copy_path

Theorem storage_reason_alloc_path[local]:
  compile_alloc_buffer nb sa = (buf,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      (?w. eval_operand buf.buf_operand t = SOME w) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  qspecl_then [`sa.cs_next_id`, `n2w nb`,
    `STRING #"%" (toString sa.cs_next_var)`, `s`]
    strip_assume_tac loweringHaltTheory.step_alloca_frame >>
  rename1 `step_inst_base _ s = OK r` >>
  `r.vs_halted = s.vs_halted` by
    (irule step_preserves_halted >>
     qexistsl_tac [`ctx`, `0`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_terminator_def]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 1` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND]) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac
  >- (
      qspec_then `[mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
        [STRING #"%" (toString sa.cs_next_var)]]`
        mp_tac tuple_run_inst_seq_gas_path >>
      simp_tac (srw_ss()) [LENGTH, FILTER, mk_inst_def] >>
      disch_then irule >>
      simp[mk_inst_def, is_terminator_def, run_inst_seq_def] >>
      gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
      gvs[emitted_insts_def, DROP_APPEND, GSYM mk_inst_def]) >>
  gvs[eval_operand_def, lookup_var_def, same_blocks_def] >> metis_tac[]
QED

Theorem storage_reason_word_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `eval_operand dst (update_var out w s) = SOME b` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >>
     metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n b) w (update_var out w s))` by
    (gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         exec_read1_def, exec_write2_def, eval_operand_def,
         lookup_var_update_var, copy_runtime_word_def, Abbr `w`]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND]) >>
  qexists_tac `(mstore (w2n b) w (update_var out w s))
    with vs_inst_idx := s.vs_inst_idx + 2` >>
  conj_tac
  >- (qspec_then `emitted_insts sa sb` mp_tac tuple_run_inst_seq_gas_path >>
      qpat_assum `emitted_insts _ _ = _` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [LENGTH, FILTER, mk_inst_def] >>
      simp_tac (srw_ss()) [COND_RAND, COND_RATOR, LENGTH, FILTER] >>
      disch_then irule >>
      gvs[is_terminator_def, GSYM mk_inst_def] >>
      gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND,
          emitted_insts_def, DROP_APPEND]) >>
  gvs[mstore_def, write_memory_with_expansion_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, same_blocks_def] >>
  rpt strip_tac >> `out <> x` by metis_tac[] >> simp[]
QED

Theorem ensure_storage_memory_defined_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      (?w. eval_operand op t = SOME w) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (qspecl_then [`src`, `nb`, `n`, `ctor`, `imm`] SUBST1_TAC) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer nb sa = (buf,sm)` >>
  rename1 `_ sm = (_,sb)` >>
  `cs_extends sm sb` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `loc`, `n`, `src`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `cs_extends sa sm` by
    (gvs[cs_extends_def, same_blocks_def] >> qexists_tac `[]` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    simp[not_fresh_at_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all storage_reason_alloc_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func s 0 (OK r)` >>
  `eval_operand src r = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `?t. gas_path ctx func r 0 (OK t) /\
       (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x r) /\
       t.vs_labels = r.vs_labels /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    suspend "suffix" >>
  qexists_tac `t` >>
  conj_tac >- (drule_all gas_path_then >> simp[]) >>
  simp[] >> gvs[eval_operand_def] >> metis_tac[]
QED

Resume ensure_storage_memory_defined_path[suffix]:
  qpat_x_assum `r.vs_labels = _` kall_tac >>
  Cases_on `n = 1` >> gnvs[]
  >- (irule storage_reason_word_path >> simp[] >>
      goal_assum (drule_at (Pat `comp_bind _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `!x. src = Var x \/
       Var (STRING #"%" (toString sa.cs_next_var)) = Var x ==>
       not_fresh_at sm x` by (simp[] >> metis_tac[]) >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_storage_reason_copy_path >>
  disch_then (qspecl_then [`r`, `func`, `ctx`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Finalise ensure_storage_memory_defined_path
