Theory bodyPtrBopHashEndpoint
Ancestors
  bodyPtrBopHashSuffix bodyPtrBopHashCompile bodyPtrBopHashSemantic bodyPtrBopHashFootprint
  bodyPtrBopHashCoverage bodyPtrBopHashRun bodyPtrIfExpBytesFrame
  bodyPtrHashBuiltinsGhostFrame fragGasSeqPtr ghostPcTransportPtr
  bodyPtrDefs loweringPosts venomState venomInst ptrDiscipline localPtrsProps compileEnv exprLoweringProps emitHelper loweringStateRelDefs

Theorem bop_hash_semantic_read_ranges[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) ==>
  ?n b sz. n < dimword(:256) /\ ptr_covers G tn p s 32 /\
    mem_word_at (w2n w) s.vs_memory = n2w n /\ FLOOKUP G p = SOME (b,sz) /\
    (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
    (!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> gvs[]
  >- (`val_wf tv (BytesV bs)` by metis_tac[expr_val_at_def] >>
      `32 + LENGTH bs <= val_footprint tv (BytesV bs)` by
        metis_tac[bop_bytes_payload_footprint] >>
      drule_all bop_hash_semantic_ranges >> strip_tac >>
      `ptr_mem_ok cx ty (BytesV bs) (Var p) G tn s` by gvs[ptr_val_ok_def] >>
      `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
      drule_all ptr_mem_ok_bytes_length >> strip_tac >>
      drule_all ptr_mem_ok_bytes_clean >> strip_tac >>
      qexistsl_tac [`LENGTH bs`, `b`, `sz`] >> simp[] >>
      Cases_on `LENGTH bs = 0` >- simp[] >>
      `0 < LENGTH bs` by decide_tac >>
      drule_all bop_payload_offset_no_wrap >> simp[]) >>
  `val_wf tv (StringV str)` by metis_tac[expr_val_at_def] >>
  `32 + LENGTH str <= val_footprint tv (StringV str)` by
    metis_tac[bop_string_payload_footprint] >>
  drule_all bop_hash_semantic_ranges >> strip_tac >>
  `ptr_mem_ok cx ty (StringV str) (Var p) G tn s` by gvs[ptr_val_ok_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all ptr_mem_ok_string_length >> strip_tac >>
  drule_all ptr_mem_ok_string_clean >> strip_tac >>
  qexistsl_tac [`LENGTH str`, `b`, `sz`] >> simp[] >>
  Cases_on `LENGTH str = 0` >- simp[] >>
  `0 < LENGTH str` by decide_tac >>
  drule_all bop_payload_offset_no_wrap >> simp[]
QED

Theorem bop_hash_compile_endpoint:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    ghost_inv d cenv cx es H un (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    local_ptrs_reserved cenv sd /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
    ghost_kept cenv es sc G tn s H un /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_imm = tn.t_imm /\ un.t_mem = tn.t_mem /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_hash_semantic_read_ranges >> strip_tac >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  drule_all bop_hash_compile_placement >> strip_tac >>
  `?H un. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sc sd) s H un /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP un.t_var x = FLOOKUP tn.t_var x)` by
    (asm_rewrite_tac[] >>
     qpat_assum `emitted_insts _ _ = _` (fn th =>
       rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     drule_all (GEN_ALL (REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]
      (Q.INST [`iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
               `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
               `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h]`]
        (SPEC_ALL bop_hash_run_checked)))) >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sc sd)` by simp[mk_inst_def] >>
  `un.t_imm = tn.t_imm` by metis_tac[inst_seq_ptr_immutable_frame] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sc sd)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  drule_all bop_hash_compile_readonly >> strip_tac >>
  drule_all bodyPtrBopHashFrameTheory.bop_hash_compile_run_frame >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  `ghost_inv d cenv cx es H un t` by
    (irule hash_readonly_ghost_inv >>
     qexistsl_tac [`G`, `s`, `sc`, `tn`] >> simp[op_taint_def]) >>
  `stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (irule bop_hash_compile_state_rel >> metis_tac[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
  `ghost_kept cenv es sc G tn s H un` by
    (irule hash_ghost_kept_frame >> simp[op_taint_def]) >>
  `!x. not_fresh_at sc x ==> not_fresh_at sd x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `LENGTH sd.cs_current_insts = s.vs_inst_idx + 3` by simp[] >>
  qexistsl_tac [`H`, `un`] >> simp[hash_ghost_inv_inst_idx] >>
  qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED
