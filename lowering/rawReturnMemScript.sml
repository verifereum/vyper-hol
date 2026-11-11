Theory rawReturnMem
Ancestors
  rawReturnHalt fragExec fragExecMem memSafeRun instMemFrontier
  allocaFootprint loweringHalt compileEnv stmtLowering context venomState
  venomInst venomExecSemantics emitHelper emitHelperProps

(* An instruction that aborts ends the run, so the run is memory safe
   when that instruction is. *)
Theorem mem_safe_run_abort_step[local]:
  !fuel ctx fn s bb inst a t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = Abort a t /\
    mem_safe_step fuel ctx inst s ==>
    mem_safe_run fuel ctx fn s
Proof
  rw[mem_safe_run_def] >>
  simp[Once mem_safe_block_def, Once exec_block_def]
QED

Theorem compile_external_return_raw_mem_parts[local]:
  !op prim ei msz nr nkey ut iv st x st'.
    compile_external_return (SOME op) prim T ei msz nr nkey ut iv st =
      (x, st') /\ (nr /\ ~iv ==> ut) ==>
    cs_extends st st' /\
    ?len off.
      ~not_fresh_at st len /\ ~not_fresh_at st off /\ len <> off /\
      st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts = st.cs_current_insts ++
        (if nr /\ ~iv then
           [mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []]
         else []) ++
        [mk_inst (st.cs_next_id + (if nr /\ ~iv then 1 else 0)) MLOAD [op] [len];
         mk_inst (st.cs_next_id + (if nr /\ ~iv then 1 else 0) + 1) ADD
           [op; Lit 32w] [off];
         mk_inst (st.cs_next_id + (if nr /\ ~iv then 1 else 0) + 2) RETURN
           [Var off; Var len] []]
Proof
  rpt gen_tac >> Cases_on `nr` >> Cases_on `iv` >>
  simp[compile_external_return_def, compile_nonreentrant_unlock_def,
       emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >>
  (strip_tac >> gvs[emit_void_def, comp_ignore_bind_def, comp_bind_def,
                       fresh_id_def, emit_def] >>
   conj_tac
   >- (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
   qexistsl [`STRING #"%" (toString st.cs_next_var)`,
             `STRING #"%" (toString (st.cs_next_var + 1))`] >>
   simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
   metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD])
QED

Theorem return_raw_mem_safe[local]:
  !fuel ctx fn s bb id len off op p bs.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [op] [len]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) ADD [op; Lit 32w] [off]) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var off; Var len] []) /\
    op <> Var len /\ len <> off /\ eval_operand op s = SOME p /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    LENGTH bs < dimword (:256) /\ w2n p + 32 <= s.vs_alloca_next /\
    (LENGTH bs = 0 \/ w2n (p + 32w) + LENGTH bs <= s.vs_alloca_next) ==>
    mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = update_var len (n2w (LENGTH bs)) s with
                       vs_inst_idx := s.vs_inst_idx + 1` >>
  `step_inst fuel ctx (mk_inst id MLOAD [op] [len]) s =
     OK (update_var len (n2w (LENGTH bs)) s)` by
    (simp[step_inst_non_invoke] >> metis_tac[step_MLOAD]) >>
  `mem_safe_run fuel ctx fn s <=>
     mem_safe_run fuel ctx fn s1` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) mem_safe_run_step >>
     disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
     simp[is_terminator_def, mem_safe_step_non_invoke,
          below_frontier_MLOAD, Abbr `s1`, arithmeticTheory.ADD1,
          Once mk_inst_def] >> simp[mk_inst_def]) >>
  `eval_operand op s1 = SOME p` by
    (Cases_on `op` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_def,
                         update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  qabbrev_tac `s2 = update_var off (p + 32w) s1 with
                       vs_inst_idx := s.vs_inst_idx + 2` >>
  `step_inst fuel ctx (mk_inst (id + 1) ADD [op; Lit 32w] [off]) s1 =
     OK (update_var off (p + 32w) s1)` by
    (simp[step_inst_non_invoke] >> irule step_ADD >> simp[eval_operand_def]) >>
  `inst_mem_below_frontier (mk_inst (id + 1) ADD [op; Lit 32w] [off]) s1` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `mem_safe_run fuel ctx fn s1 <=> mem_safe_run fuel ctx fn s2` by
    (irule EQ_TRANS >> irule_at Any mem_safe_run_step >>
     qexistsl [`update_var off (p + 32w) s1`,
               `mk_inst (id + 1) ADD [op; Lit 32w] [off]`, `bb`] >>
     simp[Abbr `s1`, Abbr `s2`, update_var_def, mk_inst_def,
          is_terminator_def, mem_safe_step_non_invoke,
          arithmeticTheory.ADD1] >>
     gvs[Abbr `s1`, mk_inst_def, update_var_def]) >>
  `mem_safe_run fuel ctx fn s2` suffices_by metis_tac[] >>
  irule return_buffer_mem_safe >>
  qexistsl [`p + 32w`, `bb`, `Var off`, `id + 2`,
            `n2w (LENGTH bs)`, `Var len`] >>
  simp[Abbr `s2`, Abbr `s1`, update_var_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem compile_external_return_raw_unlock_mem_safe[local]:
  !fuel ctx op prim ei msz nr nkey ut iv st x st' p bs fn s.
    compile_external_return (SOME op) prim T ei msz nr nkey ut iv st = (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    LENGTH bs < dimword (:256) /\ fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME p /\ mload (w2n p) s = n2w (LENGTH bs) /\
    w2n p + 32 <= s.vs_alloca_next /\
    (LENGTH bs = 0 \/ w2n (p + 32w) + LENGTH bs <= s.vs_alloca_next) ==>
    mem_safe_run fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >>
  (drule_all compile_external_return_raw_mem_parts >> strip_tac >>
  `op <> Var len` by metis_tac[] >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  Cases_on `nr /\ ~iv`
  >- (qpat_x_assum `!i. _` (fn th =>
        map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`, `3`]) >>
      simp[] >> rpt strip_tac >>
      (* in a static frame the unlock's TSTORE aborts at once *)
      Cases_on `s.vs_call_ctx.cc_static`
      >- (`step_inst fuel ctx (mk_inst st.cs_next_id TSTORE
             [Lit (n2w nkey); Lit 0w] []) s =
           Abort ExHalt_abort (halt_state (set_returndata [] s))` by
            (simp[step_inst_non_invoke] >>
             qspecl_then [`Lit (n2w nkey)`, `Lit 0w`, `n2w nkey`, `0w`,
                          `st.cs_next_id`, `s`] mp_tac step_TSTORE >>
             gvs[eval_operand_def]) >>
          irule (Q.SPECL [`fuel`, `ctx`, `fn`, `s`, `bb`,
            `mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []`,
            `ExHalt_abort`, `halt_state (set_returndata [] s)`]
            mem_safe_run_abort_step) >>
          gvs[mem_safe_step_non_invoke, mk_inst_def] >>
          qexistsl [`nkey`, `st`] >> gvs[] >>
          irule below_frontier_no_ranges >> simp[]) >>
      qabbrev_tac `u = tstore (n2w nkey) 0w s with
                         vs_inst_idx := s.vs_inst_idx + 1` >>
      `step_inst fuel ctx (mk_inst st.cs_next_id TSTORE
          [Lit (n2w nkey); Lit 0w] []) s = OK (tstore (n2w nkey) 0w s)` by
        (simp[step_inst_non_invoke] >>
         qspecl_then [`Lit (n2w nkey)`, `Lit 0w`, `n2w nkey`, `0w`,
                      `st.cs_next_id`, `s`] mp_tac step_TSTORE >>
         gvs[eval_operand_def]) >>
      `inst_mem_below_frontier (mk_inst st.cs_next_id TSTORE
          [Lit (n2w nkey); Lit 0w] []) s` by
        (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
      `mem_safe_run fuel ctx fn s <=> mem_safe_run fuel ctx fn u` by
        (drule_at (Pat `step_inst _ _ _ _ = _`) mem_safe_run_step >>
         disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
         simp[Abbr `u`, mem_safe_step_non_invoke, Once mk_inst_def,
              is_terminator_def, arithmeticTheory.ADD1] >> simp[mk_inst_def]) >>
      `mem_safe_run fuel ctx fn u` suffices_by metis_tac[] >>
      irule return_raw_mem_safe >>
      qexistsl [`bb`, `bs`, `st.cs_next_id + 1`, `len`, `off`, `op`, `p`] >>
      simp[Abbr `u`, tstore_def, mload_def, arithmeticTheory.ADD_ASSOC] >>
      gvs[mload_def] >> Cases_on `op` >>
      gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `!i. _` (fn th =>
    map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
  simp[] >> rpt strip_tac >>
  irule return_raw_mem_safe >>
  qexistsl [`bb`, `bs`, `st.cs_next_id`, `len`, `off`, `op`, `p`] >> simp[] >> gvs[])
QED

(* A zero-length RETURN reads no payload. *)
Theorem compile_external_return_raw_unlock_frag_mem:
  !ctx op prim ei msz nr nkey ut iv st x st' p bs P Q R.
    compile_external_return (SOME op) prim T ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (nr /\ ~iv ==> !s. P s ==> ~s.vs_call_ctx.cc_static) /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    LENGTH bs < dimword (:256) /\
    (!s. P s ==>
         eval_operand op s = SOME p /\
         mload (w2n p) s = n2w (LENGTH bs) /\
         read_memory (w2n (p + 32w)) (LENGTH bs) s = bs /\
         w2n p + 32 <= s.vs_alloca_next /\
         (LENGTH bs = 0 \/
          w2n (p + 32w) + LENGTH bs <= s.vs_alloca_next)) /\
    (!s ss. P s /\ ss.vs_returndata = bs /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then tstore (n2w nkey) 0w s else s).vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
            R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  `frag_exec ctx st st' P Q R` by
    (irule compile_external_return_raw_unlock_frag >>
     goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`bs`, `p`] >>
     simp[] >> metis_tac[]) >>
  simp[frag_exec_mem_def] >> rpt gen_tac >> strip_tac >>
  `!fuel. mem_safe_run fuel ctx fn s` by
    (gen_tac >> irule (INST_TYPE [alpha |-> ``:word8``]
       compile_external_return_raw_unlock_mem_safe) >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`bs`, `p`] >>
     simp[] >> metis_tac[]) >>
  fs[frag_exec_def] >>
  first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >>
  metis_tac[]
QED
