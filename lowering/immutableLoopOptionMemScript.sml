(* Constructor immutable loops reuse the existing SOME path and prove the NONE body. *)
Theory immutableLoopOptionMem
Ancestors
  immutableLoopOptionCode immutableLoopOptionBodyMem immutableLoopStoreMem
  immutableCopyExecution immutableWordExecution placeCopyControlPath
  fragGasSeqMem fragGasMode fragGasSeqAbort fragGasPathMem fragExec memContinuation
  instMemFrontier memSafeRun fragExecMem context compileEnv
  emitHelper emitHelperProps loweringStateRelDefs exprLoweringProps
  venomExecSemantics venomState venomInst words arithmetic list rich_list finite_map

Theorem immutable_loop_none_run_mem_path[local]:
  lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
  isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv];
    mk_inst (id0+1) JMP [Label hdr] []]
    (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
  lookup_block hdr func.fn_blocks = SOME bbh /\
  isPREFIX [mk_inst idh EQ [Var cv; cnt] [tv];
    mk_inst (idh+1) JNZ [Var tv; Label sb.cs_current_bb; Label body_lbl] []]
    bbh.bb_instructions /\
  LENGTH sb.cs_current_insts = 0 /\ sa.cs_next_var <= sb.cs_next_var /\ cv <> tv /\
  not_fresh_at sb cv /\ not_fresh_at sb tv /\
  (!x. not_fresh_at sa x ==> x <> cv /\ x <> tv) /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w n) /\ n < dimword (:256) /\
  (!j q. j < n /\ immutable_loop_frame sa sb s a b j q /\
    eval_operand (Var cv) q = SOME (n2w j) /\
    ~q.vs_halted /\ q.vs_current_bb = body_lbl /\ q.vs_inst_idx = 0 ==>
    ?t. gas_path_mem ctx func q 0 (OK t) /\
      immutable_loop_frame sa sb s a b (SUC j) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC j)) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b n 0 s /\
      (fresh_vars_wrt sa s ==> immutable_operand_frame sa s sb t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `(!x. not_fresh_at sa x ==> x <> cv) /\
   (!x. not_fresh_at sa x ==> x <> tv)` by metis_tac[] >>
  `?r. gas_path_mem ctx func s 0 (OK r) /\
       immutable_loop_frame sa sb s a b 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       immutable_loop_frame sa sb s a b n t /\
       eval_operand (Var cv) t = SOME (n2w n) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0` by
    suspend "iterate" >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `mem_cont_sim ctx func s t` by metis_tac[immutable_loop_path_mem_cont] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[immutable_loop_allocation_frame] >>
  qexists_tac `t` >> simp[] >>
  `t.vs_labels = s.vs_labels` by metis_tac[immutable_loop_frame_shared] >>
  fs[immutable_loop_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  metis_tac[immutable_loop_operand_frame]
QED

Resume immutable_loop_none_run_mem_path[iterate]:
  qabbrev_tac `Inv = \j q. immutable_loop_frame sa sb s a b j q /\
    eval_operand (Var cv) q = SOME (n2w j)` >>
  `?t. gas_marked_path T ctx func r 0 (OK t) /\ Inv n t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0`
    suffices_by (simp[gas_marked_path_def, Abbr `Inv`] >> metis_tac[]) >>
  irule place_copy_iterate_path >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`0`, `n`] >> simp[Abbr `Inv`]) >>
  qexists_tac `body_lbl` >> simp[] >>
  conj_tac
  >- (simp[Abbr `Inv`, gas_marked_path_def, GSYM ADD1] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!j q. j < n /\ _ ==> _`
        (qspecl_then [`j`,`q`] mp_tac) >> simp[] >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      qexists_tac `t` >> simp[]) >>
  simp[Abbr `Inv`] >> rpt gen_tac >> strip_tac >>
  `eval_operand cnt q = SOME (n2w n)` by
    (drule immutable_loop_frame_operand >>
     disch_then (qspec_then `cnt` mp_tac) >> simp[] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  drule_all immutable_loop_header_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r'` >> simp[gas_marked_path_def]
QED

Resume immutable_loop_none_run_mem_path[init]:
  `immutable_loop_frame sa sb s a b 0 s` by
    (simp[immutable_loop_frame_def, immutable_transfers_def, fresh_vars_wrt_def,
          stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `run_inst_seq [mk_inst id0 ASSIGN [Lit 0w] [cv]] s =
    OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, mk_inst_def,
         step_inst_base_opcode_eqs, eval_operand_lit] >>
  `run_inst_seq_mem_ok [mk_inst id0 ASSIGN [Lit 0w] [cv]] s` by
    simp[run_inst_seq_mem_ok_def, mk_inst_def, step_inst_base_opcode_eqs,
         eval_operand_lit, below_frontier_no_ranges, inst_dload_in_section_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id0 ASSIGN [Lit 0w] [cv]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  qabbrev_tac `t = update_var cv 0w s with
    vs_inst_idx := LENGTH sa.cs_current_insts + 1` >>
  `gas_path_mem ctx func s 0 (OK t)` by simp[Abbr `t`] >>
  `~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
   t.vs_inst_idx = LENGTH sa.cs_current_insts + 1` by
    simp[Abbr `t`, update_var_def] >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_path_mem ctx func t 0 (OK (jump_to hdr t))` by
    (irule immutable_loop_jump_mem_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  conj_tac >- (simp[immutable_loop_frame_control, Abbr `t`] >>
               irule immutable_loop_frame_write >> simp[] >> metis_tac[]) >>
  simp[Abbr `t`, jump_to_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Finalise immutable_loop_none_run_mem_path

Theorem compile_imm_store_loop_mem_path_option:
  compile_word_copy_loop_base src dst cnt LocMemory LocCode T
    imm sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x \/
       (?region. imm = SOME region /\ region = Var x) ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand cnt s = SOME (n2w n) /\ (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  (!j. j < n ==> w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
                  w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b n 0 s /\
      (fresh_vars_wrt sa s ==> immutable_operand_frame sa s sb t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `imm`
  >- (gvs[] >> drule_all immutable_loop_none_code >> strip_tac >>
      suspend "none_runner") >>
  gvs[] >> drule_all compile_imm_store_loop_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> fs[] >>
  qpat_x_assum `_ = immutable_transfers T T a b n 0 s` mp_tac >>
  simp[venom_state_component_equality]
QED

Resume compile_imm_store_loop_mem_path_option[none_runner]:
  `sb.cs_current_insts = []` by metis_tac[LENGTH_NIL] >>
  `cv <> tv /\ not_fresh_at sb cv /\ not_fresh_at sb tv /\
   (!x. not_fresh_at sa x ==> x <> cv /\ x <> tv) /\
   (!x. cnt = Var x ==> not_fresh_at sa x)` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`sa` |-> `sa`, `sb` |-> `sb`, `s` |-> `s`,
    `a` |-> `a`, `b` |-> `b`, `ctx` |-> `ctx`, `func` |-> `func`,
    `hdr` |-> `hdr`, `body_lbl` |-> `body_lbl`, `cv` |-> `cv`, `tv` |-> `tv`,
    `id0` |-> `id0`, `idh` |-> `idh`, `bb0` |-> `bb0`, `bbh` |-> `bbh`,
    `cnt` |-> `cnt`, `n` |-> `n`] (SPEC_ALL immutable_loop_none_run_mem_path)) >>
  impl_tac >- (simp[] >> suspend "none_body") >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> fs[] >>
  qpat_x_assum `_ = immutable_transfers T T a b n 0 s` mp_tac >>
  simp[venom_state_component_equality]
QED

Resume compile_imm_store_loop_mem_path_option[none_body]:
  rpt gen_tac >> strip_tac >>
  `eval_operand src q = SOME a /\ eval_operand dst q = SOME b` by
    (conj_tac >> drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand
     >- (disch_then (qspec_then `src` mp_tac) >> simp[] >> metis_tac[]) >>
     disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bbb.bb_instructions` >>
  `isPREFIX (TAKE 8 code) (DROP q.vs_inst_idx bbb.bb_instructions)` by
    simp[Abbr `code`] >>
  `ALL_DISTINCT [cv;mv;sv;vv;dm;dv;nv] /\
   (!x. MEM x [cv;mv;sv;vv;dm;dv;nv] ==>
     src <> Var x /\ dst <> Var x /\ not_fresh_at sb x) /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;nv])` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  `w2n (a+n2w (32*j)) + 32 <= q.vs_alloca_next /\
   w2n (b+n2w (32*j)) + 32 <= q.vs_alloca_next` by
    (drule immutable_loop_allocation_frame >> metis_tac[]) >>
  suspend "none_body_finish"
QED

Resume compile_imm_store_loop_mem_path_option[none_body_finish]:
  qunabbrev_tac `code` >>
  qpat_x_assum `isPREFIX (TAKE 8 _) _`
    (assume_tac o SIMP_RULE (srw_ss()) [TAKE_def, Excl "isPREFIX"]) >>
  drule_all immutable_loop_body_none_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func t 0 (OK (jump_to hdr t))` by
    (irule immutable_loop_jump_mem_path >> simp[] >>
     qexists_tac `idb+8` >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[immutable_loop_frame_control, jump_to_def, eval_operand_def,
       lookup_var_def, GSYM ADD1]
QED

Finalise compile_imm_store_loop_mem_path_option
