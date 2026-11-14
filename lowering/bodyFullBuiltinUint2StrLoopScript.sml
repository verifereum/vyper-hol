Theory bodyFullBuiltinUint2StrLoop
Ancestors
  bodyFullBuiltinUint2StrBlocks exprSimUint2Str bodyPtrDefs
  fragGasOriginPtrLoop venomState words list pred_set finite_map

Theorem u2s_loop_joint_given_cond:
  (!x str s G tn.
    u2s_digits a b n X x str s /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
    FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
      op_taint tn (Var (u2s_var a i)) = {}) /\
    ~s.vs_halted /\ s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 ==>
    ?t G' tn'.
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
      u2s_digits a b n X x str t /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
        ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
      ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
      FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
      (!i. i < 2 ==> FLOOKUP G' (u2s_var a i) = NONE /\
        op_taint tn' (Var (u2s_var a i)) = {}) /\
      tn'.t_mem = tn.t_mem /\
      t.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted) ==>
  !x str s G tn.
    valid_horizon cx st0 H0 es.storage_trace /\
    not_fresh_at a p /\ local_ptrs_reserved cenv a /\
    (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
    (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
    fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\ n+32 <= sz /\ 78 <= n /\ X < dimword(:256) /\
    b+sz < dimword(:256) /\ lo <= b /\ ~ctx_has_dalloca ctx /\
    u2s_digits a b n X x str s /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
    FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
    (!i. i < 2 ==> FLOOKUP G (u2s_var a i) = NONE /\
      op_taint tn (Var (u2s_var a i)) = {}) /\
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
  disch_then (mk_asm "cond") >>
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  asm "cond" drule >> disch_then drule_all >>
  disch_then (qx_choose_then `c` (qx_choose_then `Gc`
    (qx_choose_then `tnc` strip_assume_tac))) >>
  Cases_on `x = 0`
  >- suspend "final" >>
  suspend "body"
QED

Resume u2s_loop_joint_given_cond[final]:
  gvs[] >>
  `str = num_to_dec_string X` by fs[u2s_digits_def] >>
  `FLOOKUP Gc (u2s_var a 1) = NONE /\ op_taint tnc (Var (u2s_var a 1)) = {}` by simp[] >>
  `!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tnc.t_mem` by simp[] >>
  drule_all (Q.INST [`s` |-> `c`] (SPEC_ALL u2s_final_joint_result)) >>
  disch_then (qspecl_then [`ty`, `explicit`, `PG`]
    (qx_choose_then `sf` (qx_choose_then `Gf`
      (qx_choose_then `tnf` strip_assume_tac)))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[] >> metis_tac[gas_origin_ptr_path_trans]
QED

Resume u2s_loop_joint_given_cond[body]:
  `0 < x /\ c.vs_current_bb = u2s_label a 2` by simp[] >>
  `LENGTH str < n` by metis_tac[u2s_digits_room] >>
  `lookup_var p c = SOME (n2w b)` by
    (fs[u2s_safe_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tnc.t_mem` by simp[] >>
  drule_all (Q.INST [`s` |-> `c`] (SPEC_ALL u2s_body_joint_step)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `sb` (qx_choose_then `Gb`
      (qx_choose_then `tnb` strip_assume_tac)))) >>
  `x DIV 10 < x` by simp[arithmeticTheory.DIV_LESS] >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`CHR (48+x MOD 10)::str`, `sb`, `Gb`, `tnb`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  conj_tac >- (rpt strip_tac >> asm_x "cond" kall_tac >>
    metis_tac[gas_origin_ptr_path_trans]) >> simp[]
QED

Finalise u2s_loop_joint_given_cond
