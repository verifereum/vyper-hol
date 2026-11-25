(* Join setup, control, zero and positive numeric routes at one endpoint. *)
Theory bodyUint2StrNumericMods
Ancestors
  bodyUint2StrControlMods bodyFullBuiltinUint2StrLoop
  bodyUint2StrZeroMods bodyUint2StrDigitMods bodyUint2StrFinalMods
  bodyFullBuiltinUint2StrBlocks exprSimUint2Str bodyPtrDefs
  fragGasOriginPtrLoop venomState words list finite_map pred_set
  bodyUint2StrNumericCondMods

Theorem u2s_loop_joint_given_cond_mods:
  (!x str s G tn.
    u2s_digits a b n X x str s /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
      ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
    FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
      op_taint tn (Var (u2s_var a i)) = {}) /\
    allocas_from lo s /\ ~s.vs_halted /\ s.vs_current_bb = u2s_label a 1 /\
    s.vs_inst_idx = 0 ==>
    ?c Gc tnc.
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK c,Gc,tnc)) /\
      u2s_digits a b n X x str c /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr c /\
        ghost_inv_at (DF H) 0 d cenv cx es Gc tnc c) /\
      ghost_kept_at lo cenv es a G0 tn0 s0 Gc tnc /\
      FLOOKUP Gc p = SOME (b,sz) /\ op_taint tnc (Var p) = {} /\
      (!i. i < 2 ==> FLOOKUP Gc (u2s_var a i) = NONE /\
        op_taint tnc (Var (u2s_var a i)) = {}) /\
      tnc.t_mem = tn.t_mem /\ allocas_from lo c /\
      c.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
      c.vs_inst_idx = 0 /\ ~c.vs_halted) ==>
  !x str s G tn.
    valid_horizon cx st0 H0 es.storage_trace /\
    not_fresh_at a p /\ local_ptrs_reserved cenv a /\
    (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
    (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
    fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\ n+32 <= sz /\
    LENGTH (num_to_dec_string X) <= n /\ X < dimword(:256) /\
    b+sz < dimword(:256) /\ lo <= b /\
    u2s_digits a b n X x str s /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
      ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
    FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
      op_taint tn (Var (u2s_var a i)) = {}) /\
    allocas_from lo s /\
    (!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem) /\
    ~s.vs_halted /\
    lookup_block (u2s_label a 2) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
    lookup_block (u2s_label a 4) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
    s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 ==>
    ?t G' tn'.
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
        ghost_inv_at (DF H) 0 d cenv cx es G' tn' t) /\
      ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
      op_taint tn' (Var (u2s_var a 2)) = {} /\
      (!j. b+n-LENGTH (num_to_dec_string X) <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
      (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  disch_then (mk_asm "cond") >>
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  asm "cond" (mp_tac o Drule.HO_MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL u2s_cond_specialize_mods))) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `c` (qx_choose_then `Gc`
    (qx_choose_then `tnc` strip_assume_tac))) >>
  `!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tnc.t_mem` by simp[] >>
  `stmt_state_rel H0 ctx fn cenv cx es c /\ lookup_var p c = SOME (n2w b)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> u2s_safe H _ _ _ _ _ _ _ _ _ _ _ c /\ _`
       (qspec_then `H0` (drule_then
         (strip_assume_tac o REWRITE_RULE [u2s_safe_def, eval_operand_def]))) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp c` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  Cases_on `x = 0`
  >- suspend "final"
  >- suspend "body"
QED

Resume u2s_loop_joint_given_cond_mods[final]:
  `c.vs_current_bb = u2s_label a 4` by fs[] >>
  qpat_x_assum `x = 0` SUBST_ALL_TAC >>
  `str = num_to_dec_string X` by fs[u2s_digits_def] >>
  `FLOOKUP Gc (u2s_var a 1) = NONE /\ op_taint tnc (Var (u2s_var a 1)) = {}` by
    (qpat_assum `!i. i < 2 ==> FLOOKUP Gc (u2s_var a i) = NONE /\ _`
      (qspec_then `1` mp_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `c`] (SPEC_ALL u2s_final_joint_mods)) >>
  disch_then (qspecl_then [`ty`, `explicit`, `PG`]
    (qx_choose_then `sf` (qx_choose_then `Gf`
      (qx_choose_then `tnf` strip_assume_tac)))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gc`, `c`, `tnc`] >> simp[]) >>
  gvs[]
QED

Resume u2s_loop_joint_given_cond_mods[body]:
  `0 < x /\ c.vs_current_bb = u2s_label a 2` by fs[] >>
  `LENGTH str < n` by (drule_all u2s_digits_room >> simp[]) >>
  drule_all (Q.INST [`s` |-> `c`] (SPEC_ALL u2s_digit_joint_mods)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `sb` (qx_choose_then `Gb`
      (qx_choose_then `tnb` strip_assume_tac)))) >>
  `x DIV 10 < x` by simp[arithmeticTheory.DIV_LESS] >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`CHR (48+x MOD 10)::str`, `sb`, `Gb`, `tnb`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gc`, `c`, `tnc`] >> simp[] >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gb`, `sb`, `tnb`] >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `i IN tnb.t_mem` by (first_x_assum irule >> simp[]) >>
  `i IN tnc.t_mem` by
    (qpat_assum `!j. j < lo /\ j IN tnb.t_mem ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_x_assum `tnc.t_mem = tn.t_mem` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Finalise u2s_loop_joint_given_cond_mods

Theorem u2s_setup_exit_joint_mods:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ n+32 <= sz /\ LENGTH (num_to_dec_string X) <= n /\
  X < dimword(:256) /\ b+sz < dimword(:256) /\ lo <= b /\
  eval_operand op s = SOME (n2w X) /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  (!k. op <> Var (u2s_var a k)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  allocas_from lo s /\
  op_taint tn (Var p) = {} /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op (Var p) /\
  s.vs_inst_idx = LENGTH pre /\
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
      ghost_inv_at (DF H) 0 d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory ty (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    (!j. b+n-LENGTH (num_to_dec_string X) <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `0 < n` by (Cases_on `num_to_dec_string X` >> gvs[] >> decide_tac) >>
  drule_all u2s_setup_control_mods >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `ss` (qx_choose_then `Gs`
      (qx_choose_then `tns` strip_assume_tac)))) >>
  drule_all (Q.INST [`s` |-> `ss`, `x` |-> `X`]
    (SPEC_ALL u2s_check_control_mods)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `sc` (qx_choose_then `Gc`
      (qx_choose_then `tnc` strip_assume_tac)))) >>
  Cases_on `X = 0`
  >- (suspend "zero")
  >- (suspend "positive")
QED

Resume u2s_setup_exit_joint_mods[zero]:
  gvs[] >>
  `1 <= n` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sc` by
    (`stmt_state_rel H0 ctx fn cenv cx es sc` by
       (fs[u2s_safe_def] >> metis_tac[]) >>
     first_assum (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  drule_all (Q.INST [`s` |-> `sc`] (SPEC_ALL u2s_zero_joint_mods)) >>
  disch_then (qspecl_then [`ty`, `explicit`, `PG`]
    (qx_choose_then `sf` (qx_choose_then `Gf`
      (qx_choose_then `tnf` strip_assume_tac)))) >>
  `num_to_dec_string 0 = "0"` by EVAL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gc`, `sc`, `tnc`] >> simp[] >>
     irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gs`, `ss`, `tns`] >> simp[]) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[] >> metis_tac[]
QED

Resume u2s_setup_exit_joint_mods[positive]:
  `0 < X /\ sc.vs_current_bb = u2s_label a 1` by simp[] >>
  `u2s_digits a b n X X [] sc` by (irule u2s_digits_initial >> simp[]) >>
  `!j. b+n+32-LENGTH ([]:char list) <= j /\ j < b+n+32 ==> j NOTIN tnc.t_mem` by simp[] >>
  mp_tac (SPEC_ALL u2s_loop_joint_given_cond_mods) >>
  impl_tac >- suspend "cond" >>
  disch_then (qspecl_then [`X`, `[]`, `sc`, `Gc`, `tnc`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[] >> metis_tac[gas_origin_ptr_path_trans]
QED

Resume u2s_setup_exit_joint_mods[cond]:
  qx_genl_tac [`x`, `str`, `u`, `g`, `tt`] >> strip_tac >>
  `x < dimword(:256) /\ lookup_var (u2s_var a 0) u = SOME (n2w x)` by
    fs[u2s_digits_def] >>
  drule_all (Q.INST [`s` |-> `u`] (SPEC_ALL u2s_cond_control_mods)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `uc` (qx_choose_then `gc`
      (qx_choose_then `ttc` strip_assume_tac)))) >>
  qexistsl_tac [`uc`, `gc`, `ttc`] >> simp[] >>
  Cases_on `x = 0` >> simp[] >> metis_tac[]
QED

Finalise u2s_setup_exit_joint_mods
