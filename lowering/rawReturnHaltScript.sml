Theory rawReturnHalt
Ancestors
  loweringHalt fragExec stmtLowering compileEnv venomState emitHelper emitHelperProps venomExecSemantics venomInst

Theorem compile_external_return_raw_parts[local]:
  !op prim ei msz nkey ut iv st x st'.
    compile_external_return (SOME op) prim T ei msz F nkey ut iv st =
      (x, st') ==>
    cs_extends st st' /\
    ?len off.
      ~not_fresh_at st len /\ ~not_fresh_at st off /\ len <> off /\
      st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts = st.cs_current_insts ++
        [mk_inst st.cs_next_id MLOAD [op] [len];
         mk_inst (st.cs_next_id + 1) ADD [op; Lit 32w] [off];
         mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] []]
Proof
  rpt gen_tac >>
  simp[compile_external_return_def, optional_unlock_view,
       emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  qexistsl [`STRING #"%" (toString st.cs_next_var)`,
            `STRING #"%" (toString (st.cs_next_var + 1))`] >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem return_raw_run[local]:
  !fuel ctx fn s bb id len off op p bs.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [op] [len]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) ADD [op; Lit 32w] [off]) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var off; Var len] []) /\
    op <> Var len /\ len <> off /\ eval_operand op s = SOME p /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    read_memory (w2n (p + 32w)) (LENGTH bs) s = bs /\
    LENGTH bs < dimword (:256) ==>
    ?ss. run_from fuel ctx fn s = Halt ss /\ ss.vs_returndata = bs /\
         ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
         ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
         ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = update_var len (n2w (LENGTH bs)) s with
                       vs_inst_idx := s.vs_inst_idx + 1` >>
  `run_from fuel ctx fn s = run_from fuel ctx fn s1` by
    (drule step_MLOAD >> strip_tac >>
     drule run_from_step >> disch_then drule >>
     simp[is_terminator_def, Abbr `s1`, arithmeticTheory.ADD1]) >>
  `eval_operand op s1 = SOME p` by
    (Cases_on `op` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_def,
                         update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  qabbrev_tac `s2 = update_var off (p + 32w) s1 with
                       vs_inst_idx := s.vs_inst_idx + 2` >>
  `step_inst_base (mk_inst (id + 1) ADD [op; Lit 32w] [off]) s1 =
   OK (update_var off (p + 32w) s1)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `run_from fuel ctx fn s1 = run_from fuel ctx fn s2` by
    (irule EQ_TRANS >> irule_at Any run_from_step >>
     qexists_tac `update_var off (p + 32w) s1` >>
     gvs[is_terminator_def, Abbr `s2`, Abbr `s1`, update_var_def,
          arithmeticTheory.ADD1]) >>
  qabbrev_tac `ss = halt_state (set_returndata bs s2)` >>
  `step_inst_base (mk_inst (id + 2) RETURN [Var off; Var len] []) s2 =
   Halt ss` by
    (qspecl_then [`Var off`, `Var len`, `p + 32w`,
                  `n2w (LENGTH bs)`, `id + 2`, `s2`] mp_tac step_RETURN >>
     gvs[Abbr `ss`, Abbr `s2`, Abbr `s1`, eval_operand_def,
          lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          read_memory_def]) >>
  `run_from fuel ctx fn s2 = Halt ss` by
    (irule run_from_halt >>
     qexistsl [`bb`, `mk_inst (id + 2) RETURN [Var off; Var len] []`] >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def, mk_inst_def]) >>
  qexists_tac `ss` >>
  simp[Abbr `ss`, Abbr `s2`, Abbr `s1`, halt_state_def,
       set_returndata_def, update_var_def]
QED

Theorem compile_external_return_raw_frag[local]:
  !ctx op prim ei msz nkey ut iv st x st' p bs P Q R.
    compile_external_return (SOME op) prim T ei msz F nkey ut iv st =
      (x, st') /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    LENGTH bs < dimword (:256) /\
    (!s. P s ==> eval_operand op s = SOME p /\
         mload (w2n p) s = n2w (LENGTH bs) /\
         read_memory (w2n (p + 32w)) (LENGTH bs) s = bs) /\
    (!s ss. P s /\ ss.vs_returndata = bs /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient = s.vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_raw_parts >> strip_tac >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var len` by metis_tac[] >>
  `eval_operand op s = SOME p /\
   mload (w2n p) s = n2w (LENGTH bs) /\
   read_memory (w2n (p + 32w)) (LENGTH bs) s = bs` by metis_tac[] >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`,
               `len`, `off`, `op`, `p`, `bs`] mp_tac return_raw_run >>
  impl_tac
  >- (qpat_x_assum `!i. _` (fn th =>
        map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
      simp[]) >>
  strip_tac >> qexists_tac `0` >> simp[exit_result_def] >>
  qpat_x_assum `!s ss. _ ==> R (Halt ss)` (qspecl_then [`s`, `ss`] mp_tac) >>
  simp[]
QED

(* The length prefix is read as a word; ADD computes the payload address
   modulo 2^256. Source-layout bridges discharge the concrete read bounds. *)
Theorem compile_external_return_raw_unlock_frag:
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
         read_memory (w2n (p + 32w)) (LENGTH bs) s = bs) /\
    (!s ss. P s /\ ss.vs_returndata = bs /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then tstore (n2w nkey) 0w s else s).vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_unlock_seq >> simp[] >> disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  conj_tac
  >- (drule compile_external_return_raw_parts >> simp[]) >>
  irule compile_external_return_raw_frag >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`bs`, `p`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  rpt conj_tac >> rpt strip_tac >>
  drule optional_unlock_state >> strip_tac >>
  gvs[mload_def, read_memory_def] >>
  Cases_on `nr /\ ~iv` >> gvs[] >> metis_tac[]
QED
