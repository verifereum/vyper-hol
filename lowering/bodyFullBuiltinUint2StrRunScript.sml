(* The setup, initial branch and digit loop share one execution and ghosts. *)
Theory bodyFullBuiltinUint2StrRun
Ancestors
  bodyFullBuiltinUint2StrControl bodyFullBuiltinUint2StrLoop
  bodyFullBuiltinUint2StrBlocks exprSimUint2Str
  bodyPtrDefs fragGasOriginPtrLoop venomState words list finite_map

Theorem u2s_setup_exit_joint:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ n+32 <= sz /\ 78 <= n /\
  X < dimword(:256) /\ b+sz < dimword(:256) /\ lo <= b /\
  ~ctx_has_dalloca ctx /\
  eval_operand op s = SOME (n2w X) /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  (!k. op <> Var (u2s_var a k)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
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
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory ty (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    (!j. b+n-LENGTH (num_to_dec_string X) <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  drule_all u2s_setup_joint_transition >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `ss` (qx_choose_then `Gs`
      (qx_choose_then `tns` strip_assume_tac)))) >>
  drule_all (Q.INST [`s` |-> `ss`, `x` |-> `X`]
    (SPEC_ALL u2s_check_joint_transition)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `sc` (qx_choose_then `Gc`
      (qx_choose_then `tnc` strip_assume_tac)))) >>
  Cases_on `X = 0`
  >- suspend "zero" >>
  suspend "positive"
QED

Resume u2s_setup_exit_joint[zero]:
  gvs[] >>
  `1 <= n` by decide_tac >>
  drule_all (Q.INST [`s` |-> `sc`] (SPEC_ALL u2s_zero_joint_result)) >>
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

Resume u2s_setup_exit_joint[positive]:
  `0 < X /\ sc.vs_current_bb = u2s_label a 1` by simp[] >>
  `u2s_digits a b n X X [] sc` by (irule u2s_digits_initial >> simp[]) >>
  `!j. b+n+32-LENGTH ([]:char list) <= j /\ j < b+n+32 ==> j NOTIN tnc.t_mem` by simp[] >>
  mp_tac (SPEC_ALL u2s_loop_joint_given_cond) >>
  impl_tac >- suspend "cond" >>
  disch_then (qspecl_then [`X`, `[]`, `sc`, `Gc`, `tnc`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[] >> metis_tac[gas_origin_ptr_path_trans]
QED

Resume u2s_setup_exit_joint[cond]:
  qx_genl_tac [`x`, `str`, `u`, `g`, `tt`] >> strip_tac >>
  `x < dimword(:256) /\ lookup_var (u2s_var a 0) u = SOME (n2w x)` by
    fs[u2s_digits_def] >>
  drule_all (Q.INST [`s` |-> `u`] (SPEC_ALL u2s_cond_joint_transition)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `uc` (qx_choose_then `gc`
      (qx_choose_then `ttc` strip_assume_tac)))) >>
  qexistsl_tac [`uc`, `gc`, `ttc`] >> simp[] >>
  Cases_on `x = 0` >> simp[] >> metis_tac[]
QED

Finalise u2s_setup_exit_joint
