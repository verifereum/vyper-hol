(* Pointer execution of the bytestring encoder phases. *)
Theory abiEncoderBytesPtr
Ancestors
  abiEncoderBytesCode abiEncoderRounding typedCopyPtr decoderNavigationPtr
  fragExecPtr ghostPcTransportPtr emitHelperProps exprLoweringProps ptrDiscipline venomState
  venomExecSemantics finite_map pred_set words arithmetic venomInst codegenRel context emitHelper compileEnv

Theorem abi_encode_round_frag_ptr:
  !sa sb len out s cnt G tn cx ctx PG R.
    abi_encode_round len sa = (out,sb) /\
    eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
    cnt + 31 < dimword(:256) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\ v = t) R /\
      eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
      op_taint u out = {} /\ op_prov H out = NONE /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\ t.vs_logs = s.vs_logs /\
      t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encode_round _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] sa = (arg,sc)` >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op AND _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `v1 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `v2 = STRING #"%" (toString sc.cs_next_var)` >>
  qabbrev_tac `s1 = update_var v1 (31w + n2w cnt) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst sa.cs_next_id ADD [Lit 31w;len] [v1]) s1` >>
  qabbrev_tac `t1 = step_taint (mk_inst sa.cs_next_id ADD [Lit 31w;len] [v1]) s s1 tn` >>
  qabbrev_tac `s2 = update_var v2 (n2w (contractABI$ceil32 cnt)) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = step_prov PG g1 (mk_inst sc.cs_next_id AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;Var v1] [v2]) s2` >>
  qabbrev_tac `t2 = step_taint (mk_inst sc.cs_next_id AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;Var v1] [v2]) s1 s2 t1` >>
  `sc.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sc.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    (imp_res_tac emit_op_extends >> fs[cs_extends_def, same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `frag_exec_ptr cx ctx PG sa sc
    (\g z v. g=G /\ z=tn /\ v=s) (\g z v. g=g1 /\ z=t1 /\ v=s1) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_add`, `sa.cs_next_id`, `Lit 31w`, `ADD`, `len`, `v1`] >>
     simp[mk_inst_def, eval_operand_def, op_taint_def, Abbr `v1`,
       Abbr `g1`, Abbr `t1`, Abbr `s1`, step_prov_def, step_taint_def,
       update_var_def]) >>
  `op_taint t1 (Var v1) = {}` by
    simp[Abbr `t1`, Abbr `s1`, step_taint_def, mk_inst_def, out_taint_def,
      set_var_taint_def, op_taint_def, eval_operand_def, FLOOKUP_UPDATE] >>
  `frag_exec_ptr cx ctx PG sc sb
    (\g z v. g=g1 /\ z=t1 /\ v=s1) (\g z v. g=g2 /\ z=t2 /\ v=s2) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_and`, `sc.cs_next_id`,
       `Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w`,
       `AND`, `Var v1`, `v2`] >>
     simp[Abbr `v2`, mk_inst_def, eval_operand_def, op_taint_def,
       Abbr `g2`, Abbr `t2`, Abbr `s2`, Abbr `s1`,
       step_prov_def, step_taint_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, abi_encoder_round_ceil32]) >>
  qexistsl_tac [`g2`,`t2`,`s2`] >> conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> v1 /\ x <> v2` by
    (simp[not_fresh_at_def, Abbr `v1`, Abbr `v2`] >> rpt strip_tac >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_SUC_REFL]) >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `v2`, lookup_var_def, eval_operand_def,
    update_var_def, FLOOKUP_UPDATE] >>
  `!q w v k. update_var q w (v with vs_inst_idx := k) =
    (update_var q w v with vs_inst_idx := k)` by simp[update_var_def] >>
  simp[Abbr `t2`, Abbr `g2`, Abbr `t1`, Abbr `g1`,
    copy_len_binop_ghost_frame] >>
  conj_tac >-
    simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
      FLOOKUP_DRESTRICT] >>
  conj_tac >-
    simp[step_taint_def, imm_taint_def, mk_inst_def, update_var_def,
      step_writes_def] >>
  gen_tac >> strip_tac >>
  `x <> v1 /\ x <> STRING #"%" (toString (sa.cs_next_var+1))` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame]
QED
