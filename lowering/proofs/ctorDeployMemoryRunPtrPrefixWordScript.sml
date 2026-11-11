(* The first concrete consumer of the checked instruction-trace boundary. *)
Theory ctorDeployMemoryRunPtrPrefixWord
Ancestors
  ctorDeployMemoryRunPtrPrefixSequence ctorDeployMemoryRunPtrPrefixSteps
  abiEncoder emitHelper compileEnv exprLoweringProps finite_map
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst memLocDefs instIdxIndep

Theorem prefix_decoder_noclamp_code:
  compile_abi_decode_to_buf (Var dst) src DLOAD hi (DecPrimWord NoClamp) st =
    ((),st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id+1) MSTORE
       [Var dst; Var ("%" ++ toString st.cs_next_var)] []]
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt strip_tac >> gvs[listTheory.DROP_APPEND]
QED

Theorem prefix_noclamp_steps:
  !iid src dst x s a w b sz G tn D lo fuel ctx fn PG.
    x <> dst /\ eval_operand src s = SOME w /\
    eval_operand (Var dst) s = SOME a /\
    FLOOKUP G dst = SOME (b,sz) /\ b <= w2n a /\
    w2n a + 32 <= b+sz /\ op_taint tn src = {} /\
    op_taint tn (Var dst) = {} /\ allocas_from lo s /\
    ~ctx_has_dalloca ctx ==>
    let i = mk_inst iid DLOAD [src] [x];
        j = mk_inst (iid+1) MSTORE [Var dst; Var x] [];
        l = update_var x (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) s;
        G1 = DRESTRICT G (COMPL {x});
        tn1 = step_taint i s l tn;
        t = mstore (w2n a) (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) l
    in
      step_inst_base i s = OK l /\
      step_inst_base j l = OK t /\
      ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
      ghost_step fuel ctx PG G1 tn1 j l =
        (G1,step_taint j l t tn1) /\
      ptr_safe_step D lo fuel ctx fn PG G tn i s /\
      ptr_safe_step D lo fuel ctx fn PG G1 tn1 j l /\
      eval_operand (Var dst) l = SOME a /\ eval_operand (Var x) l = SOME
        (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) /\
      FLOOKUP G1 dst = SOME (b,sz) /\ op_taint tn1 (Var dst) = {} /\
      allocas_from lo l
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `update_var x v s` >>
  `eval_operand (Var dst) (update_var x v s) = SOME a /\
   eval_operand (Var x) (update_var x v s) = SOME v` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP (DRESTRICT G (COMPL {x})) dst = SOME (b,sz)` by
    simp[FLOOKUP_DRESTRICT] >>
  `op_taint (step_taint (mk_inst iid DLOAD [src] [x]) s
      (update_var x v s) tn) (Var dst) = {}` by
    gvs[op_taint_def, step_taint_def, set_var_taint_def, mk_inst_def,
         FLOOKUP_UPDATE] >>
  `allocas_from lo (update_var x v s)` by
    (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s =
     OK (update_var x v s)` by simp[prefix_dload_step, Abbr `v`] >>
  `ghost_step fuel ctx PG G tn (mk_inst iid DLOAD [src] [x]) s =
     (DRESTRICT G (COMPL {x}),
      step_taint (mk_inst iid DLOAD [src] [x]) s (update_var x v s) tn)` by
    (qpat_assum `eval_operand src s = SOME w`
       (mp_then Any mp_tac prefix_dload_ghost_step) >> simp[Abbr `v`]) >>
  simp[prefix_mstore_step, prefix_dload_ptr_step] >>
  conj_tac
  >- (irule prefix_mstore_ghost_step >> simp[prefix_mstore_endpoint]) >>
  irule prefix_mstore_ptr_step >>
  simp[prefix_dload_output_taint] >> metis_tac[]
QED

Theorem prefix_decoder_noclamp_ptr:
  !st st' src dst hi x bb s a w b sz G tn D lo fuel ctx fn PG.
    compile_abi_decode_to_buf (Var dst) src DLOAD hi (DecPrimWord NoClamp) st =
      ((),st') /\ x = "%" ++ toString st.cs_next_var /\ x <> dst /\
    isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
    eval_operand src s = SOME w /\ eval_operand (Var dst) s = SOME a /\
    FLOOKUP G dst = SOME (b,sz) /\ b <= w2n a /\ w2n a + 32 <= b+sz /\
    op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ?l t G1 tn1 tn2.
      let i = mk_inst st.cs_next_id DLOAD [src] [x];
          j = mk_inst (st.cs_next_id+1) MSTORE [Var dst;Var x] [];
          l1 = l with vs_inst_idx := s.vs_inst_idx+1;
          t1 = t with vs_inst_idx := s.vs_inst_idx+1
      in
      step_inst_base i s = OK l /\ step_inst_base j l = OK t /\
      ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
      ghost_step fuel ctx PG G1 tn1 j l1 = (G1,tn2) /\
      tn2 = step_taint j l1 t1 tn1 /\
      run_inst_seq (emitted_insts st st') s = OK t /\
      (ptr_safe_block D lo fuel ctx fn PG G1 tn2 bb
         (t with vs_inst_idx := s.vs_inst_idx+2) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt gen_tac >> strip_tac >>
  drule prefix_decoder_noclamp_code >> strip_tac >>
  qpat_assum `eval_operand src s = SOME w`
    (mp_then Any (drule_all_then mp_tac) prefix_noclamp_steps) >>
  disch_then (qspec_then `st.cs_next_id` mp_tac) >>
  disch_then (qspecl_then [`D`,`fuel`,`fn`,`PG`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `update_var x v s` >>
  qmatch_asmsub_abbrev_tac `step_inst_base i s = OK l` >>
  qmatch_asmsub_abbrev_tac `step_inst_base j l = OK t` >>
  qmatch_asmsub_abbrev_tac `ghost_step fuel ctx PG G tn i s = (G1,tn1)` >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  `emitted_insts st st' = [i;j]` by
    gvs[Abbr `i`, Abbr `j`] >>
  qpat_x_assum `x = _` kall_tac >>
  qabbrev_tac `l1 = l with vs_inst_idx := s.vs_inst_idx+1` >>
  qabbrev_tac `t1 = t with vs_inst_idx := s.vs_inst_idx+1` >>
  `i.inst_opcode = DLOAD /\ j.inst_opcode = MSTORE` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def] >>
  `step_inst fuel ctx j l1 = OK t1` by
    simp[Abbr `l1`, Abbr `t1`, step_inst_non_invoke,
         step_inst_inst_idx_indep, exec_result_map_def, is_terminator_def] >>
  `allocas_from lo l1` by
    (gvs[allocas_from_def, Abbr `l1`] >> metis_tac[]) >>
  `op_taint tn1 (Var x) = {}` by
    simp[Abbr `tn1`, Abbr `i`, prefix_dload_output_taint] >>
  `ptr_safe_step D lo fuel ctx fn PG G1 tn1 j l1` by
    (simp[Abbr `j`] >> irule prefix_mstore_ptr_step >>
     simp[Abbr `l1`, eval_op_inst_idx] >> metis_tac[]) >>
  qabbrev_tac `tn2 = step_taint j l1 t1 tn1` >>
  `ghost_step fuel ctx PG G1 tn1 j l1 = (G1,tn2)` by
    (simp[Abbr `tn2`, Abbr `j`] >> irule prefix_mstore_ghost_step >>
     simp[]) >>
  qexistsl [`l`,`t`,`G1`,`tn1`,`tn2`] >>
  simp[] >>
  qabbrev_tac `u = \n:num. if n=0 then s else if n=1 then l else t` >>
  qabbrev_tac `g = \n:num. if n=0 then G else G1` >>
  qabbrev_tac `q = \n:num. if n=0 then tn else if n=1 then tn1 else tn2` >>
  drule prefix_trace_ptr_safe_block >>
  disch_then (qspecl_then [`G`,`tn`] mp_tac) >>
  disch_then (qspecl_then [`u`,`g`,`q`] mp_tac) >>
  simp[Abbr `u`, Abbr `g`, Abbr `q`] >> disch_then irule >>
  simp[is_terminator_def] >> qx_gen_tac `n` >> strip_tac >>
  `n=0 \/ n=1` by decide_tac >>
  gvs[Abbr `l1`, Abbr `t1`, arithmeticTheory.ADD_COMM,
      step_inst_non_invoke] >> simp[Abbr `l`, update_var_def]
QED
