Theory bodyFullBuiltinUint2StrControl
Ancestors
  bodyFullBuiltinUint2StrBlocks bodyFullGhostFrame bodyFullUnwrapRun
  exprSimUint2Str bodyPtrDefs ptrDiscipline venomState venomInst
  finite_map words list pred_set fragGasSeqPtr fragGasOriginPtrLoop
  exprLoweringProps emitHelperProps ptrSafeRun codegenRel contextCodegenRel
  venomExecSemantics fragExecMem unitTransformDefs memSafeRun

(* One comparison boundary serves the initial check and every loop header. *)
Theorem u2s_compare_joint_transition:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  ~ctx_has_dalloca ctx /\ 2 <= k /\ x < dimword(:256) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
    op_taint tn (Var (u2s_var a i)) = {}) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [u2s_inst a iid EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k];
     u2s_inst a jid JNZ [Var (u2s_var a k); Label yes; Label no] []] /\
  s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!n X str. u2s_digits a b n X x str s ==> u2s_digits a b n X x str t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G' (u2s_var a i) = NONE /\
      op_taint tn' (Var (u2s_var a i)) = {} /\
      lookup_var (u2s_var a i) t = lookup_var (u2s_var a i) s) /\
    tn'.t_mem = tn.t_mem /\
    t.vs_current_bb = (if x = 0 then yes else no) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `u = update_var (u2s_var a k) (bool_to_word (x = 0)) s` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {u2s_var a k})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (u2s_var a k,{})` >>
  qabbrev_tac `t = jump_to (if x = 0 then yes else no) u` >>
  `allocas_from lo s` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `!r. not_fresh_at a r ==> r <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  `p <> u2s_var a k` by metis_tac[] >>
  `!r. not_fresh_at a r ==>
     lookup_var r t = lookup_var r s /\ FLOOKUP G1 r = FLOOKUP G r /\
     op_taint tn1 (Var r) = op_taint tn (Var r)` by
    simp[Abbr `t`, Abbr `u`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
      update_var_def, jump_to_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  qexistsl_tac [`t`, `G1`, `tn1`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- (simp[Abbr `t`, Abbr `u`, u2s_digits_jump, u2s_digits_update]) >>
  conj_tac >- suspend "invariants" >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
      simp[Abbr `tn1`] >> metis_tac[]) >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `t`, Abbr `u`,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def, update_var_def, jump_to_def,
       lookup_var_def] >>
  rpt strip_tac >> gvs[u2s_var_injective] >> fs[op_taint_def]
QED

Resume u2s_compare_joint_transition[invariants]:
  rpt strip_tac
  >- (simp[Abbr `t`, Abbr `u`] >> irule u2s_safe_jump >>
      irule u2s_safe_update >> metis_tac[]) >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `es`, `s`, `a`, `tn`] >>
  simp[Abbr `t`, Abbr `u`, Abbr `tn1`, update_var_def, jump_to_def] >> metis_tac[]
QED

Resume u2s_compare_joint_transition[path]:
  `FLOOKUP G (u2s_var a 0) = NONE /\ op_taint tn (Var (u2s_var a 0)) = {}` by simp[] >>
  `run_inst_seq [u2s_inst a iid EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]] s = OK u` by
    (simp[Abbr `u`] >> irule u2s_eq_run >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn
    [u2s_inst a iid EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]] s G1 tn1` by
    (gen_tac >> simp[u2s_inst_def, Abbr `G1`, Abbr `tn1`] >>
     irule u2s_clean_scalar_seq_cons >>
     simp[op_prov_def, op_taint_def, inst_seq_ptr_def, DISJ_IMP_THM, FORALL_AND_THM] >>
     fs[op_taint_def] >>
     qexists_tac `bool_to_word (x = 0)` >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def, n2w_11]) >>
  `run_inst_seq_mem_ok [u2s_inst a iid EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]] s` by
    simp[run_inst_seq_mem_ok_last, u2s_inst_def, mk_inst_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := 1),G1,tn1)` by
    (gen_tac >>
     qspecl_then [`[u2s_inst a iid EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]]`,
       `s`, `u`, `G`, `tn`, `G1`, `tn1`, `ctx`, `fn`, `bb`]
       mp_tac run_inst_seq_gas_origin_ptr_path >>
     simp[u2s_inst_def, mk_inst_def, is_terminator_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (u with vs_inst_idx := 1,G1,tn1) [] (OK t,G1,tn1)` by
    (gen_tac >> simp[Abbr `t`] >>
     `jump_to (if x = 0 then yes else no) u =
      jump_to (if x = 0 then yes else no) (u with vs_inst_idx := 1)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >>
     `(if x = 0 then yes else no) =
      (if bool_to_word (x = 0) <> 0w then yes else no)` by
       (Cases_on `x = 0` >> simp[bool_to_word_def]) >>
     pop_assum SUBST1_TAC >> irule jnz_origin_ptr_path >>
     simp[Abbr `u`, Abbr `tn1`, u2s_inst_def, mk_inst_def,
       get_instruction_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       eval_operand_def, op_taint_def, allocas_from_def, bool_to_word_def] >>
     fs[allocas_from_def]) >>
  rpt strip_tac >> metis_tac[gas_origin_ptr_path_trans]
QED

Finalise u2s_compare_joint_transition

Theorem u2s_cond_joint_transition:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  ~ctx_has_dalloca ctx /\ x < dimword(:256) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
    op_taint tn (Var (u2s_var a i)) = {}) /\
  ~s.vs_halted /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!n X str. u2s_digits a b n X x str s ==> u2s_digits a b n X x str t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G' (u2s_var a i) = NONE /\
      op_taint tn' (Var (u2s_var a i)) = {} /\
      lookup_var (u2s_var a i) t = lookup_var (u2s_var a i) s) /\
    tn'.t_mem = tn.t_mem /\
    t.vs_current_bb = (if x = 0 then u2s_label a 4 else u2s_label a 2) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  irule (Q.INST [`k` |-> `4`, `iid` |-> `6`, `jid` |-> `7`]
    (SPEC_ALL u2s_compare_joint_transition)) >>
  simp[] >>
  conj_tac >- simp[u2s_cond_def] >>
  metis_tac[]
QED

Theorem u2s_check_joint_transition:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  ~ctx_has_dalloca ctx /\ x < dimword(:256) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
    op_taint tn (Var (u2s_var a i)) = {}) /\
  ~s.vs_halted /\
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!n X str. u2s_digits a b n X x str s ==> u2s_digits a b n X x str t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G' (u2s_var a i) = NONE /\
      op_taint tn' (Var (u2s_var a i)) = {} /\
      lookup_var (u2s_var a i) t = lookup_var (u2s_var a i) s) /\
    tn'.t_mem = tn.t_mem /\
    t.vs_current_bb = (if x = 0 then u2s_label a 3 else u2s_label a 1) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  irule (Q.INST [`k` |-> `3`, `iid` |-> `4`, `jid` |-> `5`]
    (SPEC_ALL u2s_compare_joint_transition)) >>
  simp[] >>
  conj_tac >- simp[u2s_check_def] >>
  metis_tac[]
QED
