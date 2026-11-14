(* The SHA bytes header read preserves the complete bounded ghost. *)
Theory bodyFullHashShaPrefix
Ancestors
  bodyFullGhostFrame bodyPtrHashBuiltinsShaPrefix bodyPtrHashBuiltinsGhostFrame
  bodyPtrHashBuiltinsKeccakBytesRun instSeqPtrLo fragGasSeqPtr
  fragGasOriginPtr fragExecMem exprSimHash exprSimHashBoundary exprSimProps
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  exprLoweringProps loweringStateRelDefs compileEnv finite_map pred_set words
  list rich_list arithmetic ASCIInumbers

Theorem sha_bytes_prepare_frame_at:
  !D lo H ctx fn PG G tn s bb x sa len_op sl data_op sm b base cap n d cenv cx es.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x;Lit 32w] sl = (data_op,sm) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq_mem_ok (emitted_insts sa sm) s /\
  stmt_state_rel H ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) ==>
  ?t G1 tn1 p.
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s G1 tn1 /\
  (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx+2),G1,tn1)) /\
  (t with vs_vars := s.vs_vars) = s /\
  stmt_state_rel H ctx fn cenv cx es t /\
  ghost_inv_at D lo d cenv cx es G1 tn1 t /\
  ghost_kept_at lo cenv es sa G tn s G1 tn1 /\ data_op = Var p /\
  eval_operand data_op t = SOME (n2w (b+32)) /\ eval_operand len_op t = SOME (n2w n) /\
  ptr_covers G1 tn1 p t n /\ op_taint tn1 len_op = {} /\
  (!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn1.t_mem) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
  (!z. len_op = Var z \/ data_op = Var z ==> not_fresh_at sm z) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+2 /\ sm.cs_next_id = sa.cs_next_id+2
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all hash_data_prefix_run >> strip_tac >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all hash_bytes_prepare_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  `!z. not_fresh_at sa z ==> FLOOKUP G1 z = FLOOKUP G z /\
     op_taint tn1 (Var z) = op_taint tn (Var z)` by
    (rpt strip_tac >> gvs[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv_at D lo d cenv cx es G1 tn1 t` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G tn s G1 tn1` by
    (simp[ghost_kept_at_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx fn cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  `!D'. inst_seq_ptr D' lo ctx fn PG G tn (emitted_insts sa sm) s G1 tn1` by
    (gen_tac >>
     `inst_seq_ptr D' 0 ctx fn PG G tn (emitted_insts sa sm) s G1 tn1` by
       (gvs[] >> irule hash_bytes_prepare_inst_seq >>
        simp[ALL_DISTINCT, toString_inj] >>
        qexistsl_tac [`b`, `n`] >> simp[] >> decide_tac) >>
     irule (Q.SPECL [`emitted_insts sa sm`, `D'`, `D'`, `lo`,
       `ctx`, `fn`, `PG`, `G`, `tn`, `s`, `G1`, `tn1`] inst_seq_ptr_zero_to_lo) >>
     fs[ghost_inv_at_def]) >>
  `!D'. gas_origin_ptr_path (D',lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx+2),G1,tn1)` by
    (gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts sa sm) /\
      FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sm) = []` by
       simp[mk_inst_def, is_terminator_def] >>
     `inst_seq_ptr D' lo ctx fn PG G tn (emitted_insts sa sm) s G1 tn1` by simp[] >>
     drule_all (Q.INST [`D` |-> `D'`, `lo` |-> `lo`]
       run_inst_seq_gas_origin_ptr_path) >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  `not_fresh_at sm (STRING #"%" (toString sa.cs_next_var)) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+1)))` by
    (qpat_x_assum `!z. len_op = Var z \/ data_op = Var z ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G1`, `tn1`, `STRING #"%" (toString (sa.cs_next_var+1))`] >>
  simp[] >> conj_tac >-
    (simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, toString_inj] >>
     qexists_tac `n2w (b+32)` >> gvs[eval_operand_def] >> decide_tac) >>
  conj_tac >- simp[op_taint_def, FLOOKUP_UPDATE, toString_inj] >>
  rpt strip_tac >> gvs[]
QED
