(* Compiler-boundary execution normalization; pointer checks stay at their
   actual program counters. *)
Theory abiDecodePtrNormalized
Ancestors
  abiDecodePtrScalarReplay bodyPtrBopScalarSeq bodyPtrBopHashSuffix fragExec
  stmtReasonLitFragMemory exprLoweringProps emitHelperProps compileEnv
  venomExecSemantics venomState instIdxIndep list rich_list
  assignTuplePtrLocalBytesCopy

Theorem abi_decode_run_split_normalized:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq (xs ++ ys) s = OK u ==>
  ?t. t.vs_inst_idx = s.vs_inst_idx + LENGTH xs /\
    run_inst_seq xs s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq ys t = OK (u with vs_inst_idx := t.vs_inst_idx)
Proof
  strip_tac >> fs[bop_run_inst_seq_append_ok] >>
  rename1 `run_inst_seq xs s = OK r` >>
  `r with vs_inst_idx := s.vs_inst_idx = r` by
    (qspec_then `xs` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`, `s.vs_inst_idx`] mp_tac) >>
     simp[exec_result_map_def, venom_state_component_equality]) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + LENGTH xs` >>
  simp[] >>
  qspec_then `ys` mp_tac run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`r`, `s.vs_inst_idx + LENGTH xs`] mp_tac) >>
  simp[exec_result_map_def]
QED

Theorem abi_decode_scalar_compile_replay_ptr:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  inst_extends sa sb /\ same_blocks sa sb /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[same_blocks_def, inst_extends_def] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  drule_all scalar_seq_success_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts = t` by
    (qpat_assum `t.vs_inst_idx = _` mp_tac >>
     simp[NoAsms, venom_state_component_equality]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `s.vs_inst_idx + LENGTH _ = _` mp_tac >>
      qpat_x_assum `t with vs_inst_idx := LENGTH _ = t` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `t with vs_inst_idx := _ = s with vs_vars := _` mp_tac >>
      qpat_x_assum `t.vs_inst_idx = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[venom_state_component_equality]) >>
  fs[lookup_var_def]
QED

(* Interface probe: two compiler scalar phases compose at their own PCs. *)
Theorem abi_decode_scalar_compile_pair_ptr[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  bop_scalar_seq R B (emitted_insts sb sc) C /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  inst_extends sa sb /\ same_blocks sa sb /\ fn_has_code sa sb func /\
  inst_extends sb sc /\ same_blocks sb sc /\ fn_has_code sb sc func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  run_inst_seq (emitted_insts sb sc) t = OK (u with vs_inst_idx := t.vs_inst_idx) ==>
  ?G2 tn2. inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sb ++ emitted_insts sb sc) s G2 tn2
Proof
  strip_tac >>
  drule_all abi_decode_scalar_compile_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     fs[same_blocks_def] >> simp[venom_state_component_equality]) >>
  drule_all abi_decode_scalar_compile_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    (imp_res_tac bop_scalar_seq_opcodes >> fs[EVERY_MEM]) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
   u.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts sb sc)` by
    fs[inst_extends_def] >>
  drule_all inst_seq_ptr_append_normalized >>
  strip_tac >> goal_assum (drule_at Any)
QED
