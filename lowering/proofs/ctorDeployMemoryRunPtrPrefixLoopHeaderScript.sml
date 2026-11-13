(* Concrete paired header boundary; the semantic and ghost trace share t. *)
Theory ctorDeployMemoryRunPtrPrefixLoopHeader
Ancestors
  ctorDeployMemoryRunPtrPrefixBoolHeader ctorDeployMemoryRunPtrPrefixLoopSetup
  ctorAbiActualArrayHeader ctorAbiActualArrayInvariant abiDecoderExecution abiDecoderContract abiDecoderLoop
  abiDecoderReentry abiDecoderArrayBackedge
  ctorDeployMemoryRunPtrPrefixBoolWord instIdxIndep venomExecProofs
  ctorDeployMemoryRunPtrPrefixHeader ctorDeployMemoryRunPtrPrefixWordRead
  ctorDeployMemoryRunPtrPrefixSteps emitHelperProps codegenRel contextCodegenRel
  ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
  words arithmetic list finite_map pred_set analysisSimProofsBase

Theorem prefix_loop_header_old_taint:
  let ins = abi_decode_header_insts hid (Var ip) (Var src) DLOAD iv cv cmp done body_lbl exit_lbl;
      u1 = update_var iv (n2w j) s;
      u2 = update_var cv (n2w n) u1;
      u3 = update_var cmp (bool_to_word (j<n)) u2;
      u4 = update_var done (bool_to_word (~(j<n))) u3;
      q1 = step_taint (EL 0 ins) s u1 tn;
      q2 = step_taint (EL 1 ins) (u1 with vs_inst_idx := 1) (u2 with vs_inst_idx := 1) q1;
      q3 = step_taint (EL 2 ins) (u2 with vs_inst_idx := 2) (u3 with vs_inst_idx := 2) q2;
      qt = step_taint (EL 3 ins) (u3 with vs_inst_idx := 3) (u4 with vs_inst_idx := 3) q3
  in !x. ~MEM x [iv;cv;cmp;done] ==> op_taint qt (Var x) = op_taint tn (Var x)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> rpt strip_tac >>
  gvs[] >>
  simp[abi_decode_header_insts_def,
    SRULE [LET_THM] prefix_boolword_pure_taint_frame,update_var_def]
QED

Theorem prefix_loop_header_concrete_pair:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = hdr /\
  ALL_DISTINCT [ip;src;dst;iv;cv;cmp;done] /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  mload slot s = n2w j /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w n /\
  j <= n /\ n < dimword(:256) /\
  FLOOKUP G ip = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var src) = {} /\
  (!k. k < 32 ==> slot+k NOTIN tn.t_mem) /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions := abi_decode_header_insts hid
       (Var ip) (Var src) DLOAD iv cv cmp done body_lbl exit_lbl|> /\
  (!lbl. MEM lbl [body_lbl;exit_lbl] ==> ?bb.
    lookup_block lbl fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0) ==>
  let t = jump_to (if j<n then body_lbl else exit_lbl)
            (abi_decode_header_state iv cv cmp done j n s)
  in ?H qt.
    abi_decode_sim ctx fn s t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
      eval_operand (Var x) t = eval_operand (Var x) s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    op_taint qt (Var iv) = {} /\ op_taint qt (Var cv) = {} /\
    op_taint qt (Var cmp) = {} /\ op_taint qt (Var done) = {} /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM,abi_decode_header_state_def] >> BETA_TAC >>
  mp_tac (Q.INST [`id` |-> `hid`, `scratch` |-> `slot`, `i` |-> `j`,
    `ncount` |-> `n`] (SRULE [LET_THM] prefix_bool_header_closed)) >>
  (impl_tac >- gvs[ALL_DISTINCT]) >> (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `exec_block _ _ _ _ = OK t` >>
  qmatch_asmsub_abbrev_tac `entry_prov fn t gh` >>
  qmatch_asmsub_abbrev_tac `th.t_mem = tn.t_mem` >>
  `?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (simp[Abbr `t`,jump_to_def] >> Cases_on `j<n` >> gvs[]) >>
  `entry_prov fn t gh = gh /\ entry_taint_vars fn t th = th` by
    (irule prefix_loop_header_no_phis >> metis_tac[]) >>
  qexistsl [`gh`,`th`] >>
  conj_tac >- (irule abi_decode_edge_sim >> simp[] >>
    simp[Abbr `t`,jump_to_def,update_var_def]) >>
  `~t.vs_halted /\ t.vs_inst_idx = 0 /\
   t.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\ allocas_from lo t /\
   lo <= t.vs_alloca_next` by
    (simp[Abbr `t`,jump_to_def,update_var_def,allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "old" >>
  strip_tac >>
  `!fuel. ptr_safe_blocks D lo fuel ctx fn PG gh th t` by
    (Cases >- simp[Once ptr_safe_blocks_def] >>
     simp[Once ptr_safe_blocks_def,phi_prefix_length_zero_eval_phis_ok] >>
     `t with vs_inst_idx := 0 = t` by
       simp[fetch "venomState" "venom_state_component_equality"] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ _ _ _`
       (qspec_then `n'` mp_tac) >> simp[ptr_safe_run_def]) >>
  `!fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s` by
    (Cases >> simp[Once ptr_safe_blocks_def] >> metis_tac[]) >>
  gen_tac >>
  qpat_x_assum `!fuel. ptr_safe_blocks _ _ fuel _ _ _ G tn s`
    (qspec_then `SUC fuel` mp_tac) >>
  pure_once_rewrite_tac[ptr_safe_blocks_def] >>
  simp_tac (srw_ss()) [ptr_safe_run_def,abi_decode_header_insts_def,
    eval_phis_def,mk_inst_def,phi_prefix_length_def] >>
  `s with vs_inst_idx := 0 = s` by
    simp[fetch "venomState" "venom_state_component_equality"] >>
  simp[abi_decode_header_insts_def,eval_phis_def,mk_inst_def,phi_prefix_length_def]
QED

Resume prefix_loop_header_concrete_pair[old]:
  gen_tac >> strip_tac >> gvs[] >>
  simp[Abbr `gh`,Abbr `t`,jump_to_def,update_var_def,
    eval_operand_def,lookup_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] >>
  simp[Abbr `th`] >> irule (SRULE [LET_THM] prefix_loop_header_old_taint) >> simp[]
QED

Finalise prefix_loop_header_concrete_pair

(* Live operands need not be distinct or variables. Only outputs are fresh. *)
Theorem prefix_loop_operand_update_frame:
  opc IN {MLOAD; DLOAD; LT; SHR; ISZERO} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\ opr <> Var x ==>
  eval_operand opr (update_var x w s) = eval_operand opr s /\
  op_taint (step_taint (mk_inst iid opc args [x]) s t tn) opr =
    op_taint tn opr
Proof
  Cases_on `opr` >> simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  TRY (simp[op_taint_def] >> NO_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`ops` |-> `args`] (SRULE [LET_THM] prefix_boolword_pure_taint_frame)) >>
  simp[]
QED

Theorem prefix_loop_header_trace:
  ~ctx_has_dalloca ctx /\ s.vs_inst_idx = 0 /\ ALL_DISTINCT [iv;cv;cmp;done] /\
  ~MEM ip [iv;cv;cmp;done] /\
  (!x. MEM x [iv;cv;cmp;done] ==> src <> Var x) /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand src s = SOME (n2w a) /\
  mload slot s = n2w j /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w n /\
  j <= n /\ n < dimword(:256) /\
  FLOOKUP G ip = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\
  op_taint tn (Var ip) = {} /\ op_taint tn src = {} /\
  (!k. k < 32 ==> slot+k NOTIN tn.t_mem) ==>
  let ins = abi_decode_header_insts hid (Var ip) src DLOAD iv cv cmp done body_lbl exit_lbl;
      u1 = update_var iv (n2w j) s;
      u2 = update_var cv (n2w n) u1;
      u3 = update_var cmp (bool_to_word (j<n)) u2;
      u4 = update_var done (bool_to_word (~(j<n))) u3;
      g1 = DRESTRICT G (COMPL {iv});
      g2 = DRESTRICT g1 (COMPL {cv});
      g3 = DRESTRICT g2 (COMPL {cmp});
      g4 = DRESTRICT g3 (COMPL {done});
      q1 = step_taint (EL 0 ins) s u1 tn;
      q2 = step_taint (EL 1 ins) (u1 with vs_inst_idx := 1) (u2 with vs_inst_idx := 1) q1;
      q3 = step_taint (EL 2 ins) (u2 with vs_inst_idx := 2) (u3 with vs_inst_idx := 2) q2;
      q4 = step_taint (EL 3 ins) (u3 with vs_inst_idx := 3) (u4 with vs_inst_idx := 3) q3;
      u = (\k. EL k [s;u1;u2;u3;u4]);
      g = (\k. EL k [G;g1;g2;g3;g4]);
      q = (\k. EL k [tn;q1;q2;q3;q4])
  in !f k. k < 4 ==>
    step_inst_base (EL k (TAKE 4 ins)) (u k) = OK (u (SUC k)) /\
    step_inst f ctx (EL k (TAKE 4 ins)) ((u k) with vs_inst_idx := k) =
      OK ((u (SUC k)) with vs_inst_idx := k) /\
    ptr_safe_step D lo f ctx fn PG (g k) (q k) (EL k (TAKE 4 ins))
      ((u k) with vs_inst_idx := k) /\
    ghost_step f ctx PG (g k) (q k) (EL k (TAKE 4 ins))
      ((u k) with vs_inst_idx := k) = (g (SUC k),q (SUC k))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `u1 = update_var iv (n2w j) s` >>
  qabbrev_tac `u2 = update_var cv (n2w n) u1` >>
  qabbrev_tac `u3 = update_var cmp (bool_to_word (j<n)) u2` >>
  qabbrev_tac `u4 = update_var done (bool_to_word (~(j<n))) u3` >>
  rpt gen_tac >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >>
  gvs[abi_decode_header_insts_def]
  >- suspend "load"
  >- suspend "data"
  >- suspend "compare"
  >> suspend "zero"
QED

Resume prefix_loop_header_trace[load]:
  `slot < dimword(:256)` by decide_tac >>
  `s with vs_inst_idx := 0 = s` by
    simp[fetch "venomState" "venom_state_component_equality"] >>
  qpat_assum `eval_operand (Var ip) s = _` (mp_then Any assume_tac prefix_mload_step) >>
  qpat_assum `eval_operand (Var ip) s = _`
    (mp_then Any assume_tac (SRULE [LET_THM] prefix_mload_ghost_step)) >>
  simp[step_inst_non_invoke,Abbr `u1`,w2n_n2w,update_var_def] >>
  irule prefix_mload_ptr_step >> simp[w2n_n2w] >> metis_tac[]
QED

Resume prefix_loop_header_trace[data]:
  `eval_operand src u1 = SOME (n2w a)` by
    (simp[Abbr `u1`] >>
     irule EQ_TRANS >> qexists_tac `eval_operand src s` >> simp[] >>
     Cases_on `src` >> gvs[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `op_taint (step_taint (mk_inst hid MLOAD [Var ip] [iv]) s u1 tn) src = {}` by
    (`src <> Var iv` by metis_tac[] >>
     simp[SRULE [LET_THM] prefix_loop_operand_update_frame,Abbr `u1`,update_var_def]) >>
  `step_inst_base (mk_inst (hid+1) DLOAD [src] [cv]) u1 = OK u2` by
    (qpat_assum `eval_operand src u1 = _` (mp_then Any mp_tac prefix_dload_step) >>
     gvs[Abbr `u2`,Abbr `u1`,abi_decode_load_def,abi_decode_source_def,update_var_def]) >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def] >>
  conj_tac >- (irule (REWRITE_RULE[mk_inst_def] prefix_dload_ptr_step) >>
    gvs[Abbr `u1`,update_var_def,allocas_from_def,mk_inst_def] >> metis_tac[]) >>
  simp[ghost_step_def,step_inst_non_invoke,step_prov_def,set_prov_def,out_prov_def,mk_inst_def] >>
  gvs[step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def,INTER_ASSOC]
QED

Resume prefix_loop_header_trace[compare]:
  `slot < dimword(:256) /\ j < dimword(:256)` by decide_tac >>
  `op_taint (step_taint (mk_inst hid MLOAD [Var ip] [iv]) s u1 tn) (Var iv) = {}` by
    (irule prefix_mload_output_clean >> simp[w2n_n2w] >> metis_tac[ADD_COMM]) >>
  `step_inst_base (mk_inst (hid+2) LT [Var iv;Var cv] [cmp]) u2 = OK u3` by
    (gvs[] >> simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
      Abbr `u3`,Abbr `u2`,Abbr `u1`,eval_operand_def,lookup_var_def,update_var_def,
      FLOOKUP_UPDATE,WORD_LO,w2n_n2w]) >>
  simp[step_inst_non_invoke,step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def] >>
  conj_tac >-
    (irule (REWRITE_RULE[mk_inst_def] prefix_compare_ptr_step) >>
     gvs[Abbr `u2`,Abbr `u1`,op_prov_def,FLOOKUP_DRESTRICT,allocas_from_def,
       update_var_def,mk_inst_def,op_taint_def,step_taint_def,set_var_taint_def,
       out_taint_def,FLOOKUP_UPDATE] >>
     Cases_on `eval_operand src (update_var iv (n2w j) s)` >> gvs[update_var_def] >> metis_tac[]) >>
  simp[ghost_step_def,step_inst_non_invoke,step_prov_def,set_prov_def,out_prov_def,mk_inst_def] >>
  gvs[step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def,INTER_ASSOC]
QED

Resume prefix_loop_header_trace[zero]:
  `step_inst_base (mk_inst (hid+3) ISZERO [Var cmp] [done]) u3 = OK u4` by
    (gvs[] >> simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure1_def,
      Abbr `u4`,Abbr `u3`,Abbr `u2`,Abbr `u1`,eval_operand_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE] >>
     Cases_on `j<n` >> simp[bool_to_word_def]) >>
  simp[step_inst_non_invoke,step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def] >>
  conj_tac >-
    (irule (REWRITE_RULE[mk_inst_def] prefix_iszero_ptr_step) >>
     gvs[Abbr `u3`,Abbr `u2`,Abbr `u1`,allocas_from_def,update_var_def,
       prefix_guard_output_taint,mk_inst_def,op_taint_def,step_taint_def,
       set_var_taint_def,out_taint_def,FLOOKUP_UPDATE,eval_operand_def,lookup_var_def] >> metis_tac[]) >>
  simp[ghost_step_def,step_inst_non_invoke,step_prov_def,set_prov_def,out_prov_def,mk_inst_def] >>
  gvs[step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def,INTER_ASSOC]
QED

Finalise prefix_loop_header_trace

Theorem prefix_loop_header_operand_pair:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = hdr /\ ALL_DISTINCT [iv;cv;cmp;done] /\
  ~MEM ip [iv;cv;cmp;done] /\
  (!x. MEM x [iv;cv;cmp;done] ==> src <> Var x) /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand src s = SOME (n2w a) /\ mload slot s = n2w j /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w n /\
  j <= n /\ n < dimword(:256) /\ FLOOKUP G ip = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\
  op_taint tn (Var ip) = {} /\ op_taint tn src = {} /\
  (!k. k < 32 ==> slot+k NOTIN tn.t_mem) /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions := abi_decode_header_insts hid
       (Var ip) src DLOAD iv cv cmp done body_lbl exit_lbl|> /\
  (!lbl. MEM lbl [body_lbl;exit_lbl] ==> ?bb.
    lookup_block lbl fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0) ==>
  let t = jump_to (if j<n then body_lbl else exit_lbl)
            (abi_decode_header_state iv cv cmp done j n s)
  in ?H qt.
    abi_decode_sim ctx fn s t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
      eval_operand (Var x) t = eval_operand (Var x) s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    op_taint qt (Var iv) = {} /\ op_taint qt (Var cv) = {} /\
    op_taint qt (Var cmp) = {} /\ op_taint qt (Var done) = {} /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `ins = abi_decode_header_insts hid (Var ip) src DLOAD iv cv cmp done body_lbl exit_lbl` >>
  qabbrev_tac `u1 = update_var iv (n2w j) s` >>
  qabbrev_tac `u2 = update_var cv (n2w n) u1` >>
  qabbrev_tac `u3 = update_var cmp (bool_to_word (j<n)) u2` >>
  qabbrev_tac `u4 = update_var done (bool_to_word (~(j<n))) u3` >>
  qabbrev_tac `t = jump_to (if j<n then body_lbl else exit_lbl) u4` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {iv})` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {cv})` >>
  qabbrev_tac `g3 = DRESTRICT g2 (COMPL {cmp})` >>
  qabbrev_tac `g4 = DRESTRICT g3 (COMPL {done})` >>
  qabbrev_tac `q1 = step_taint (EL 0 ins) s u1 tn` >>
  qabbrev_tac `q2 = step_taint (EL 1 ins) (u1 with vs_inst_idx := 1) (u2 with vs_inst_idx := 1) q1` >>
  qabbrev_tac `q3 = step_taint (EL 2 ins) (u2 with vs_inst_idx := 2) (u3 with vs_inst_idx := 2) q2` >>
  qabbrev_tac `q4 = step_taint (EL 3 ins) (u3 with vs_inst_idx := 3) (u4 with vs_inst_idx := 3) q3` >>
  `abi_decode_header_state iv cv cmp done j n s = u4` by
    simp[abi_decode_header_state_def,Abbr `u4`,Abbr `u3`,Abbr `u2`,Abbr `u1`] >>
  simp[] >> qexistsl [`g4`,`q4`] >>
  `!f. exec_block f ctx <|bb_label := hdr;bb_instructions := ins|> s = OK t` by
    (gen_tac >> unabbrev_all_tac >>
     pure_rewrite_tac[GSYM abi_decode_header_state_def] >>
     irule abi_decode_header_control >>
     `slot < dimword(:256)` by decide_tac >>
     gvs[abi_decode_source_opcode_def,w2n_n2w] >> metis_tac[]) >>
  conj_tac >- (irule abi_decode_edge_sim >> simp[] >>
    simp[Abbr `t`,jump_to_def,Abbr `u4`,Abbr `u3`,Abbr `u2`,Abbr `u1`,update_var_def] >>
    Cases_on `j<n` >> gvs[] >> metis_tac[]) >>
  `~t.vs_halted /\ t.vs_inst_idx = 0 /\
   t.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
   t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (simp[Abbr `t`,jump_to_def,Abbr `u4`,Abbr `u3`,Abbr `u2`,Abbr `u1`,update_var_def,
       allocas_from_def] >> gvs[allocas_from_def] >> metis_tac[]) >>
  simp[] >> reverse (rpt conj_tac) >- suspend "safety" >>
  `slot < dimword(:256)` by decide_tac >>
  `op_taint q1 (Var iv) = {}` by
    (simp[Abbr `q1`,Abbr `ins`,abi_decode_header_insts_def] >>
     irule prefix_mload_output_clean >> simp[w2n_n2w] >> metis_tac[ADD_COMM]) >>
  `op_taint q2 (Var cv) = {} /\ op_taint q3 (Var cmp) = {} /\
   op_taint q4 (Var done) = {}` by
    simp[Abbr `q2`,Abbr `q3`,Abbr `q4`,Abbr `ins`,abi_decode_header_insts_def,
      prefix_dload_output_taint,prefix_guard_output_taint] >>
  simp[Abbr `q4`,Abbr `q3`,Abbr `q2`,Abbr `q1`,Abbr `ins`,abi_decode_header_insts_def,
    Abbr `g4`,Abbr `g3`,Abbr `g2`,Abbr `g1`,FLOOKUP_DRESTRICT,
    Abbr `t`,jump_to_def,Abbr `u4`,Abbr `u3`,Abbr `u2`,Abbr `u1`,
    update_var_def,eval_operand_def,lookup_var_def,FLOOKUP_UPDATE,
    SRULE [LET_THM] prefix_boolword_pure_taint_frame,
    prefix_dload_output_taint,prefix_guard_output_taint,prefix_guard_taint_other] >>
  rpt strip_tac >> gvs[abi_decode_header_insts_def,update_var_def] >>
  simp[SRULE [LET_THM] prefix_boolword_pure_taint_frame,update_var_def]
QED

Resume prefix_loop_header_operand_pair[safety]:
  strip_tac >>
  `?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0` by
    (simp[Abbr `t`,jump_to_def] >> Cases_on `j<n` >> gvs[]) >>
  `entry_prov fn t g4 = g4 /\ entry_taint_vars fn t q4 = q4` by
    (irule prefix_loop_header_no_phis >> metis_tac[]) >>
  `!fuel. ptr_safe_blocks D lo fuel ctx fn PG g4 q4 t` by
    (Cases >- simp[Once ptr_safe_blocks_def] >>
     simp[Once ptr_safe_blocks_def,phi_prefix_length_zero_eval_phis_ok] >>
     `t with vs_inst_idx := 0 = t` by
       simp[fetch "venomState" "venom_state_component_equality"] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ fuel _ _ _ _ _ _`
       (qspec_then `n'` mp_tac) >> simp[ptr_safe_run_def]) >>
  `!fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s` by suspend "blocks" >>
  gen_tac >>
  qpat_x_assum `!fuel. ptr_safe_blocks _ _ fuel _ _ _ G tn s`
    (qspec_then `SUC fuel` mp_tac) >>
  pure_once_rewrite_tac[ptr_safe_blocks_def] >>
  simp_tac (srw_ss()) [ptr_safe_run_def,abi_decode_header_insts_def,
    eval_phis_def,mk_inst_def,phi_prefix_length_def] >>
  `s with vs_inst_idx := 0 = s` by
    simp[fetch "venomState" "venom_state_component_equality"] >>
  simp[Abbr `ins`,abi_decode_header_insts_def,eval_phis_def,mk_inst_def,phi_prefix_length_def]
QED

Resume prefix_loop_header_operand_pair[blocks]:
  Cases >- simp[Once ptr_safe_blocks_def] >>
  irule (cj 2 (SRULE [LET_THM] prefix_decode_dload_header_entry_pair)) >>
  simp[] >>
  qexistsl [`n2w a:bytes32`,`body_lbl`,`cmp`,`cv`,`done`,`exit_lbl`,
    `\k. EL k [G;g1;g2;g3;g4]`,`j`,`hid`,`Var ip`,`iv`,`n`,
    `n2w slot:bytes32`,`\k. EL k [tn;q1;q2;q3;q4]`,`src`,
    `\k. EL k [s;u1;u2;u3;u4]`] >>
  `slot < dimword(:256)` by decide_tac >>
  qpat_assum `abi_decode_header_state _ _ _ _ _ _ _ = u4`
    (fn th => pure_rewrite_tac[th]) >>
  simp[Abbr `t`,Abbr `ins`,w2n_n2w] >>
  conj_tac >-
    (unabbrev_all_tac >> gen_tac >> strip_tac >>
     drule_all prefix_loop_header_trace >>
     simp[LET_THM] >> disch_then (qspecl_then [`n'`,`j'`] mp_tac) >> simp[]) >>
  conj_tac >- gvs[] >> suspend "branch"
QED

Resume prefix_loop_header_operand_pair[branch]:
  `op_taint q4 (Var done) = {}` by
    simp[Abbr `q4`,abi_decode_header_insts_def,prefix_guard_output_taint] >>
  simp[abi_decode_header_insts_def,ptr_safe_step_def,ptr_inst_ok_def,access_ok_def,
    taint_ok_def,step_inst_non_invoke,source_memory_read_ranges_def,
    source_memory_write_ranges_def,mk_inst_def,step_inst_base_opcode_eqs,
    Abbr `u4`,eval_operand_def,lookup_var_update_var,update_var_def,jump_to_def] >>
  conj_tac >- (Cases >> gvs[op_taint_def]) >>
  gvs[Abbr `u3`,Abbr `u2`,Abbr `u1`,allocas_from_def,update_var_def,
    lookup_var_def,FLOOKUP_UPDATE] >>
  Cases_on `j<n` >> gvs[bool_to_word_def] >> metis_tac[]
QED

Finalise prefix_loop_header_operand_pair

(* Compiled recursive header: operands need only be older than its outputs. *)
Theorem prefix_loop_header_compiled_pair:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid (Var slot_var) src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next (Var slot_var) /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand (Var slot_var) s = SOME (n2w slot) /\
  eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  LENGTH vs < dimword(:256) /\ FLOOKUP G slot_var = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\ ~ctx_has_dalloca ctx /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn src = {} /\
  (!k. k<32 ==> slot+k NOTIN tn.t_mem) ==>
  let t = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)
  in ?H qt.
    ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j t /\
    abi_decode_sim ctx func s t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. abi_decoder_older_vars next x ==> FLOOKUP H x = FLOOKUP G x) /\
    (!opr. abi_decoder_operand_live next opr ==>
      eval_operand opr t = eval_operand opr s /\ op_taint qt opr = op_taint tn opr) /\
    op_taint qt (Var (STRING #"%" (toString first))) = {} /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `iv = STRING #"%" (toString first)` >>
  qabbrev_tac `cv = STRING #"%" (toString (first+1))` >>
  qabbrev_tac `cmp = STRING #"%" (toString (first+2))` >>
  qabbrev_tac `done = STRING #"%" (toString (first+3))` >>
  `ALL_DISTINCT [iv;cv;cmp;done]` by
    simp[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
  `!opr x. abi_decoder_operand_live next opr /\ MEM x [iv;cv;cmp;done] ==>
    opr <> Var x` by
    (pure_rewrite_tac[MEM] >> rpt gen_tac >> strip_tac >>
     gvs[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
     irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `~MEM slot_var [iv;cv;cmp;done] /\
   (!x. MEM x [iv;cv;cmp;done] ==> src <> Var x)` by metis_tac[] >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by
    fs[ctor_actual_array_observation_def] >>
  `eval_operand src s = SOME (n2w (w2n srcaddr)) /\
   abi_decode_load DLOAD (n2w (w2n srcaddr):bytes32) s = n2w (LENGTH vs)` by simp[n2w_w2n] >>
  `lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr;bb_instructions := abi_decode_header_insts hid
      (Var slot_var) src DLOAD iv cv cmp done body_lbl exit_lbl|> /\
   (!lbl. MEM lbl [body_lbl;exit_lbl] ==> ?bb.
     lookup_block lbl func.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0)` by
    (gvs[abi_decode_loop_cfg_def,Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >> metis_tac[]) >>
  drule_all prefix_loop_header_operand_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexistsl [`H`,`qt`] >> simp[] >>
  conj_tac >- (simp[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
    irule ctor_actual_array_header_observation >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `abi_decoder_operand_live next (Var x)` by
      simp[abi_decoder_operand_live_def,IN_DEF] >>
    `~MEM x [iv;cv;cmp;done]` by metis_tac[] >>
    qpat_x_assum `!x. ~MEM x _ ==> _` drule >> simp[]) >>
  gen_tac >> strip_tac >> namedCases_on `opr` ["w","x","lab"]
  >- simp[eval_operand_def,op_taint_def]
  >- (`~MEM x [iv;cv;cmp;done]` by
        (qpat_x_assum `!opr x. _` (qspecl_then [`Var x`,`x`] mp_tac) >> simp[]) >>
      qpat_x_assum `!x. ~MEM x _ ==> _` drule >> simp[]) >>
  simp[eval_operand_def,op_taint_def,jump_to_def,abi_decode_header_state_def,update_var_def]
QED

val _ = export_theory();
