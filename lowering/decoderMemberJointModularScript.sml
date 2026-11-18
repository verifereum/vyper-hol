(* Raw calldata member navigation at a shared ambient freshness limit. *)
Theory decoderMemberJointModular
Ancestors decoderMemberPrefixPtr fragGasOriginPtrLoop
  fragGasOriginPtr fragGasOrigin fragGasSeqPtr fragGasSeqMem memSafeRun unitTransformDefs codegenRel venomInstProps contextCodegenRel decoderNavigationPtr calldataOverwritePtr calldataClampPtr entryDispatchPtr
  decoderGhostFramePtr fragExecPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  venomExecSemantics venomInst venomState compileEnv loweringStateRelDefs emitHelper fragExec
  words finite_map pred_set list arithmetic instIdxIndep
  emitHelperProps exprLoweringProps abiDecoderLoop ghostPcTransportPtr exprLowering abiEncoder decoderArraySetupPtr
  abiDecoderMemberSetup abiDecoderReentryPointer abiDecoderReentry abiMalformedConstructorContract freshWrites

Theorem calldata_member_source_live[local]:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\ abi_decoder_operand_live sb.cs_next_var ep
Proof
  Cases_on `dyn` >>
  simp_tac bool_ss [compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac emitted_insts_emit_op >> gvs[]
QED

Theorem calldata_member_source_modular[local]:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,sb) /\
  eval_operand src s = SOME p /\
  abi_decoder_operand_live sa.cs_next_var src /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s else p + n2w ao) /\
    fresh_vars_wrt limit t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (?vars. t = s with vs_vars := vars) /\ inst_extends sa sb
Proof
  Cases_on `dyn` >>
  simp_tac bool_ss [compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[]
  >- suspend "dynamic"
  >> suspend "static"
QED

Resume calldata_member_source_modular[static]:
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abiDecoderReentryAddressTheory.abi_decoder_binary_reentry)) >>
  strip_tac >> goal_assum (drule_at Any) >>
  gvs[update_var_def] >> metis_tac[]
QED

Resume calldata_member_source_modular[dynamic]:
  rename1 `emit_op ADD [src; Lit (n2w ao)] sa = (head,c1)` >>
  rename1 `emit_op CALLDATALOAD [head] c1 = (off,c2)` >>
  rename1 `emit_op ADD [src; off] c2 = (ep,sb)` >>
  `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= sb.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `c1.cs_next_var <= limit.cs_next_var` by decide_tac >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abiDecoderReentryAddressTheory.abi_decoder_binary_reentry)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `c2.cs_next_var <= limit.cs_next_var /\ abi_decode_source_opcode CALLDATALOAD` by
    (simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >> decide_tac) >>
  drule_all (Q.INST [`opc` |-> `CALLDATALOAD`] abiDecoderReentryAddressTheory.abi_decoder_read_reentry) >>
  strip_tac >>
  `sa.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `emit_op ADD [src; Lit (n2w ao)] sa = _` mp_tac >>
     disch_then (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `abi_decoder_operand_live c1.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand src t = SOME p` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abiDecoderReentryAddressTheory.abi_decoder_binary_reentry)) >>
  strip_tac >>
  `run_inst_seq (emitted_insts sa c2) s = OK t /\ inst_extends sa c2` by
    metis_tac[abiDecoderRangeTheory.abi_decode_sequence_chain] >>
  drule_all abiDecoderRangeTheory.abi_decode_sequence_chain >>
  strip_tac >> goal_assum (drule_at Any) >>
  `abi_decode_load CALLDATALOAD (p + n2w ao) s1 =
   abi_decode_load CALLDATALOAD (p + n2w ao) s` by
    simp[abiDecoderContractTheory.abi_decode_load_def,
         abiDecoderContractTheory.abi_decode_source_def] >>
  gvs[] >> conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live c1.cs_next_var op /\
       abi_decoder_operand_live c2.cs_next_var op` by
        (conj_tac >> irule abi_decoder_operand_live_mono >>
         qexists_tac `sa.cs_next_var` >> simp[] >> decide_tac) >>
      simp[]) >>
  simp[Abbr `s1`, update_var_def] >> metis_tac[]
QED

Finalise calldata_member_source_modular

Theorem calldata_member_setup_modular_run[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,sb) /\
  eval_operand src s = SOME p /\ lookup_var root s = SOME a /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand (FST ops) t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s else p + n2w ao) /\
    eval_operand (SND ops) t = SOME (a + n2w vo) /\
    fresh_vars_wrt limit t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (?vars. t = s with vs_vars := vars) /\ inst_extends sa sb
Proof
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,mid)` >>
  rename1 `emit_op ADD [Var root; Lit (n2w vo)] mid = (dst,sb)` >>
  `mid.cs_next_var <= sb.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `mid.cs_next_var <= limit.cs_next_var` by decide_tac >>
  drule_all calldata_member_source_modular >> strip_tac >>
  `eval_operand (Var root) t = SOME a /\
   eval_operand (Lit (n2w vo)) t = SOME (n2w vo)` by
    (conj_tac >- metis_tac[eval_operand_def] >> simp[eval_operand_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abiDecoderReentryAddressTheory.abi_decoder_binary_reentry)) >>
  strip_tac >>
  drule calldata_member_source_live >> strip_tac >>
  drule_all abiDecoderRangeTheory.abi_decode_sequence_chain >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[] >> conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live mid.cs_next_var op` by
        (irule abi_decoder_operand_live_mono >>
         qexists_tac `sa.cs_next_var` >> simp[]) >> simp[]) >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem member_navigation_emit_origin[local]:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (Var x,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),
     step_prov PG G (mk_inst sa.cs_next_id opc ops [x]) t,
     step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops [x]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [mk_inst sa.cs_next_id opc ops [x]] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) =
        SOME (EL k [mk_inst sa.cs_next_id opc ops [x]])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> fs[same_blocks_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id opc ops [x])` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    fs[MEM, is_terminator_def] >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id opc ops [x]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `t = s with vs_vars := t.vs_vars` by
    (irule (cj 1 abi_malformed_read_step_frame) >>
     qexists_tac `mk_inst sa.cs_next_id opc ops [x]` >>
     gvs[MEM, mk_inst_def, fresh_write_op_def, abiDecoderContractTheory.abi_decode_source_opcode_def]) >>
  `t.vs_requests = s.vs_requests` by
    (qpat_assum `t = s with vs_vars := _` (fn th => simp[Once th])) >>
  `ptr_safe_step D lo 0 ctx func PG G tn (mk_inst sa.cs_next_id opc ops [x]) s` by
    (fs[MEM] >>
     gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       EVERY_MEM] >> metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst sa.cs_next_id opc ops [x]) s /\
   inst_dload_in_section (mk_inst sa.cs_next_id opc ops [x]) s` by
    (fs[MEM] >> gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def]) >>
  `ghost_step 0 ctx PG G tn (mk_inst sa.cs_next_id opc ops [x]) s =
   (step_prov PG G (mk_inst sa.cs_next_id opc ops [x]) t,
    step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn)` by
    (irule ghost_step_non_invoke >> simp[mk_inst_def]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  qpat_x_assum `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx`
    (fn th => pure_once_rewrite_tac [th]) >>
  irule step_origin_ptr_path >> (conj_tac >- simp[]) >>
  qexistsl_tac [`bb`, `mk_inst sa.cs_next_id opc ops [x]`] >> simp[mk_inst_def]
QED

Theorem member_navigation_emit_joint_pc[local]:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\ op_taint u out = {} /\
    (EVERY (\op. op_prov G op = NONE) ops ==> op_prov H out = NONE) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q) /\
      FLOOKUP u.t_var q = FLOOKUP tn.t_var q) /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
    (~s.vs_halted ==> !D explicit.
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
        (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  `~is_terminator opc` by fs[MEM, is_terminator_def] >>
  `run_inst_seq (emitted_insts sa sb)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule_all emit_op_run_pc >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `allocas_from lower (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `(s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_current_bb = sa.cs_current_bb /\
   (s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_inst_idx = LENGTH sa.cs_current_insts` by simp[] >>
  drule_all member_navigation_emit_endpoint_uniform >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `x` strip_assume_tac)) >>
  `!q. not_fresh_at sa q ==> FLOOKUP u.t_var q = FLOOKUP tn.t_var q` by
    (rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
     `q <> x` by (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     simp[step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`x`,`H`,`u`] >> gvs[lookup_var_def] >>
  rpt strip_tac >>
  irule (SRULE [] (Q.INST
    [`s` |-> `s with vs_inst_idx := LENGTH sa.cs_current_insts`,
     `t` |-> `t with vs_inst_idx := LENGTH sa.cs_current_insts`]
    member_navigation_emit_origin)) >> simp[MEM]
QED

Theorem member_navigation_source_joint[local]:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,sb) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u. op_taint u ep = {} /\ op_prov H ep = NONE /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
    FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q) /\
    FLOOKUP u.t_var q = FLOOKUP tn.t_var q) /\
  (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
  (~s.vs_halted ==> !D explicit.
    gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  Cases_on `dyn`
  >- suspend "dynamic"
  >> simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `MEM ADD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint tn op = {}) [src; Lit (n2w ao)]` by
    simp[op_taint_def] >>
  drule_all member_navigation_emit_joint_pc >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         AllCaseEqs(), update_var_def]) >>
  qexistsl_tac [`H`,`u`] >> simp[op_prov_def]
QED

Resume member_navigation_source_joint[dynamic]:
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] sa = (head,c1)` >>
  rename1 `emit_op CALLDATALOAD [head] c1 = (off,c2)` >>
  pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 cs'` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends c1 cs'` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa cs' = emitted_insts sa c1 ++ emitted_insts c1 cs' /\
   emitted_insts c1 cs' = emitted_insts c1 c2 ++ emitted_insts c2 cs'` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?s1. run_inst_seq (emitted_insts sa c1) s = OK s1 /\
         run_inst_seq (emitted_insts c1 cs') s1 = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  `?s2. run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
         run_inst_seq (emitted_insts c2 cs') s2 = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 cs'` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends c1 cs'` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 cs' func` by
    metis_tac[fn_has_code_split] >>
  `MEM ADD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint tn op = {}) [src; Lit (n2w ao)]` by simp[op_taint_def] >>
  drule_all member_navigation_emit_joint_pc >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  rename1 `op_taint u1 head = {}` >> rename1 `FLOOKUP H1 _ = FLOOKUP G _` >>
  `op_prov H1 head = NONE` by fs[op_prov_def] >>
  `?vars. s1 = s with vs_vars := vars` by
    (qpat_assum `emit_op ADD [src; Lit (n2w ao)] sa = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
     `step_inst_base (mk_inst sa.cs_next_id ADD [src; Lit (n2w ao)] [x]) s = OK s1` by
       gvs[run_inst_seq_def, AllCaseEqs()] >>
     qexists_tac `s1.vs_vars` >> irule (cj 1 abi_malformed_read_step_frame) >>
     qexists_tac `mk_inst sa.cs_next_id ADD [src; Lit (n2w ao)] [x]` >>
     gvs[mk_inst_def, fresh_write_op_def]) >>
  `allocas_from lower s1 /\ s1.vs_current_bb = c1.cs_current_bb` by
    (gvs[allocas_from_def] >> metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `MEM CALLDATALOAD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint u1 op = {}) [head]` by simp[] >>
  drule_all member_navigation_emit_joint_pc >>
  disch_then (qspecl_then [`PG`,`H1`] strip_assume_tac) >>
  rename1 `op_taint u2 off = {}` >> rename1 `FLOOKUP H2 _ = FLOOKUP H1 _` >>
  `op_prov H2 off = NONE` by fs[] >>
  `?vars. s2 = s1 with vs_vars := vars` by
    (qpat_assum `emit_op CALLDATALOAD [head] c1 = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
     `step_inst_base (mk_inst c1.cs_next_id CALLDATALOAD [head] [x']) s1 = OK s2` by
       gvs[run_inst_seq_def, AllCaseEqs()] >>
     qexists_tac `s2.vs_vars` >> irule (cj 1 abi_malformed_read_step_frame) >>
     qexists_tac `mk_inst c1.cs_next_id CALLDATALOAD [head] [x']` >>
     gvs[mk_inst_def, abiDecoderContractTheory.abi_decode_source_opcode_def]) >>
  `allocas_from lower s2 /\ s2.vs_current_bb = c2.cs_current_bb` by
    (gvs[allocas_from_def] >> metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!q. not_fresh_at sa q ==> not_fresh_at c1 q /\ not_fresh_at c2 q` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `op_taint u2 src = {} /\ op_prov H2 src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa cs') _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 cs') _ = _` kall_tac >>
  qpat_x_assum `emitted_insts sa cs' = _` kall_tac >>
  qpat_x_assum `emitted_insts c1 cs' = _` kall_tac >>
  `EVERY (\op. op_taint u2 op = {}) [src; off]` by simp[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] member_navigation_emit_joint_pc)) >>
  disch_then (qspecl_then [`PG`,`H2`] strip_assume_tac) >>
  `t.vs_current_bb = s2.vs_current_bb` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         AllCaseEqs(), update_var_def]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> gvs[] >>
  rpt strip_tac >> metis_tac[gas_origin_ptr_path_trans]
QED

Finalise member_navigation_source_joint

Theorem member_navigation_emit_pointer_joint_pc[local]:
  emit_op ADD [Var root; offset] sa = (out,sb) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ op_prov G offset = NONE /\
  off + n <= cap /\ w2n a + off < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\
    lookup_var x t = SOME (n2w (w2n a + off)) /\ ptr_covers H u x t n /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q) /\
      FLOOKUP u.t_var q = FLOOKUP tn.t_var q) /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
    (~s.vs_halted ==> !D explicit.
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
        (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >> simp[is_terminator_def] >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `allocas_from lower (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `lookup_var root (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a /\
   ptr_covers G tn root (s with vs_inst_idx := LENGTH sa.cs_current_insts) cap /\
   eval_operand offset (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME (n2w off)` by
    (gvs[ptr_covers_def, lookup_var_def] >> Cases_on `offset` >> gvs[eval_operand_def, lookup_var_def]) >>
  `(s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_current_bb = sa.cs_current_bb /\
   (s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_inst_idx = LENGTH sa.cs_current_insts` by simp[] >>
  drule_all member_navigation_emit_pointer_uniform >>
  disch_then (qspec_then `PG` (qx_choose_then `x` strip_assume_tac)) >>
  `!q. not_fresh_at sa q ==> FLOOKUP u.t_var q = FLOOKUP tn.t_var q` by
    (rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
     `q <> x` by (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     simp[step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`x`,`H`,`u`] >> gvs[ptr_covers_def, lookup_var_def] >>
  rpt strip_tac >>
  irule (SRULE [] (Q.INST
    [`s` |-> `s with vs_inst_idx := LENGTH sa.cs_current_insts`,
     `t` |-> `t with vs_inst_idx := LENGTH sa.cs_current_insts`]
    member_navigation_emit_origin)) >> simp[op_taint_def]
QED

Theorem calldata_member_setup_joint[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo sa = (ops,sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + n <= cap /\ w2n a + vo < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u q. SND ops = Var q /\
  lookup_var q t = SOME (n2w (w2n a + vo)) /\ ptr_covers H u q t n /\
  op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
  (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
  (!x. not_fresh_at sa x ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
  (~s.vs_halted ==> !D explicit.
    gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,mid)` >>
  rename1 `emit_op ADD [Var root; Lit (n2w vo)] mid = (dst,sb)` >>
  `inst_extends sa mid /\ same_blocks sa mid` by
    (Cases_on `dyn` >>
     qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     (conj_tac >- metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
     imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `inst_extends mid sb /\ same_blocks mid sb` by
    metis_tac[inst_extends_emit_op, emit_op_same_blocks] >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by metis_tac[fn_has_code_split] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?prepared. run_inst_seq (emitted_insts sa mid) s = OK prepared /\
              run_inst_seq (emitted_insts mid sb) prepared = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  drule_all member_navigation_source_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_taint u1 ep = {}` >> rename1 `op_prov H1 ep = NONE` >>
  `lookup_var root prepared = SOME a /\ ptr_covers H1 u1 root prepared cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lower prepared /\ prepared.vs_current_bb = mid.cs_current_bb` by
    (gvs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w vo)) prepared = SOME (n2w vo) /\
   op_taint u1 (Lit (n2w vo)) = {} /\ op_prov H1 (Lit (n2w vo)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `vo + n <= cap /\ w2n a + vo < dimword(:256)` by decide_tac >>
  `prepared.vs_halted = s.vs_halted` by
    (irule run_inst_seq_preserves_halted >>
     qexists_tac `emitted_insts sa mid` >> simp[] >>
     `abi_decode_source_opcode CALLDATALOAD` by
       simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
     drule_all abi_decoder_member_pointer_code >> strip_tac >>
     drule abiDecoderReservationTheory.abi_decode_member_pointer_allocation_shape >>
     simp[] >> strip_tac >>
     gvs[EVERY_MEM, abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
     rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ \/ _` drule >> simp[]) >>
  drule_all member_navigation_emit_pointer_joint_pc >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at mid x` by
    (drule abi_decoder_member_pointer_counters >> strip_tac >>
     Cases_on `dyn` >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `!x. ep = Var x ==> not_fresh_at mid x` by
    (drule abi_decoder_member_pointer_counters >> strip_tac >>
     Cases_on `ep` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `op_taint u ep = {} /\ op_prov H ep = NONE` by
    (Cases_on `ep` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  qexistsl_tac [`H`,`u`,`x`] >> simp[ADD_COMM] >>
  metis_tac[gas_origin_ptr_path_trans, APPEND_NIL]
QED

Theorem calldata_member_setup_joint_modular:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\ eval_operand src s = SOME p /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\
  mid.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    r = s with <| vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx |> /\
    abi_decode_sim ctx fn s r /\ gas_path_mem ctx fn s 0 (OK r) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,H,u)) /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt limit r /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s else p + n2w ao) /\
    ptr_covers H u q r C /\ op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    r.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all calldata_member_setup_modular_run >> strip_tac >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[] >>
  drule_all calldata_member_setup_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderMemberCodeTheory.abi_decode_member_setup_shape >> strip_tac >>
  `frag_exec ctx sa mid (\s'. s' = s)
    (\r. r = t with vs_inst_idx := LENGTH mid.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >>
     fs[EVERY_CONJ] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`,`H`,`u`,`q`] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  gvs[abiDecoderDynamicLoopSetupTheory.abi_decoder_address_frame_def, fresh_vars_wrt_def, lookup_var_def,
      ptr_covers_def, eval_operand_def, word_add_n2w] >>
  `LENGTH sa.cs_current_insts + SUC (LENGTH rest) =
   LENGTH rest + (LENGTH sa.cs_current_insts + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`ARB`,`{}`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  strip_tac >> drule fragGasOriginTheory.gas_origin_path_erase >>
  simp[fragGasModeTheory.gas_marked_path_def]
QED
