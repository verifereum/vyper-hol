(* Relative-address reads use provenance only on the src, never on a
   position.  Input windows are independent of ABI validity. *)
Theory abiDecodePtrRead
Ancestors
  abiDecodePtrMemberFrame assignTuplePtrLoadStep typedCopyPtr
  abiEncoder abiDecodeStaticProps bodyPtrDefs emitHelperProps exprLoweringProps ptrDiscipline venomState
  venomExecSemantics venomInst words arithmetic finite_map emitHelper compileEnv fragGasPathPtr
  exprSimAccounts freshWrites fragExec stateFrame fragGasSeqPtr
  abiDecodePtrEmit assignTuplePtrCopyLen

Theorem abi_decode_ptr_relative_window:
  abi_decode_ptr_window G tn s src b h /\
  eval_operand pos s = SOME (n2w p) /\ p <= h /\
  w2n b+h < dimword(:256) ==>
  abi_decode_ptr_window
    (step_prov PG G (mk_inst id ADD [Var src;pos] [out])
      (update_var out (b+n2w p) s))
    (step_taint (mk_inst id ADD [Var src;pos] [out]) s
      (update_var out (b+n2w p) s) tn)
    (update_var out (b+n2w p) s with vs_inst_idx := idx)
    out (b+n2w p) (h-p)
Proof
  strip_tac >>
  `w2n (b+n2w p) = w2n b+p` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  fs[abi_decode_ptr_window_def, ptr_covers_def] >>
  simp[abi_decode_ptr_window_def, ptr_covers_def,
       copy_len_binop_ghost_frame, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`b'`, `sz'`] >> simp[] >> decide_tac
QED

Theorem abi_decode_ptr_address:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p <= h /\ w2n b+h < dimword(:256) ==>
  ?out t G' tn'. addr = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    abi_decode_ptr_window G' tn' t out (b+n2w p) (h-p) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op ADD [Var src;pos] sa = (addr,sb)` by
    fs[compile_abi_dec_addr_def] >>
  `lookup_var src s = SOME b /\ op_taint tn (Var src) = {}` by
    gvs[abi_decode_ptr_window_def, ptr_covers_def] >>
  `!out. ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst sa.cs_next_id ADD [Var src;pos] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >> simp[eval_operand_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id ADD [Var src;pos] [out]) s =
    OK (update_var out (b+n2w p) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `ADD`, `PG` |-> `PG`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t)` >>
  qexistsl_tac [`out`, `t`, `H`, `tm`] >> asm_rewrite_tac[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  conj_tac >- gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  conj_tac >- (gvs[] >> simp[Abbr `H`, Abbr `tm`, inst_seq_ptr_def]) >>
  conj_tac >- suspend "address_raw" >>
  conj_tac >- (simp[Abbr `H`, Abbr `tm`, Abbr `t`] >>
              irule abi_decode_ptr_relative_window >> simp[]) >>
  suspend "address_frame"
QED

Resume abi_decode_ptr_address[address_raw]:
  gvs[] >> simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
    exec_pure2_def, eval_operand_def, Abbr `t`, update_var_def,
    venom_state_component_equality]
QED

Resume abi_decode_ptr_address[address_frame]:
  simp[Abbr `t`, Abbr `H`, Abbr `tm`, copy_len_binop_ghost_frame,
       update_var_def, state_frame_def] >> conj_tac
  >- simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  rpt strip_tac >>
  `x <> out` by (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  pure_rewrite_tac[GSYM update_var_def] >>
  simp[copy_len_binop_ghost_frame]
QED

Finalise abi_decode_ptr_address

Theorem abi_decode_ptr_relative_load:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword(:256) ==>
  ?out t G' tn'. v = Var out /\ not_fresh_at sc out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sc) s G' tn' /\
    run_inst_seq (emitted_insts sa sc) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    lookup_var out t = SOME (mload (w2n b+p) s) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sc t) /\
    (?ap. addr = Var ap /\ not_fresh_at sc ap /\
      abi_decode_ptr_window G' tn' t ap (b+n2w p) (h-p)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op ADD [Var src;pos] sa = (addr,sb)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sb sc /\ sb.cs_next_var <= sc.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  `p <= h` by decide_tac >>
  drule_all (abi_decode_ptr_address |> Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `addr = Var ap` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  `lookup_var ap u = SOME (b+n2w p) /\ ptr_covers H tm ap u 32 /\
   (!i. w2n (b+n2w p) <= i /\ i < w2n (b+n2w p)+32 ==> i NOTIN tm.t_mem)` by
    gvs[abi_decode_ptr_window_def, ptr_covers_def] >>
  qpat_x_assum `addr = Var ap` SUBST_ALL_TAC >>
  `!out. ptr_inst_ok D 0 0 ctx func H tm
    (mk_inst sb.cs_next_id MLOAD [Var ap] [out]) u` by
    (gen_tac >> irule ptr_inst_ok_mload >> simp[]) >>
  `!out. step_inst_base (mk_inst sb.cs_next_id MLOAD [Var ap] [out]) u =
    OK (update_var out (mload (w2n (b+n2w p)) u) u)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `MLOAD`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG H tm u 0 Hf tmf (OK tf)` >>
  suspend "load_finish"
QED

Resume abi_decode_ptr_relative_load[load_finish]:
  `gas_path_ptr D 0 ctx func PG G tn s 0 Hf tmf (OK tf)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  drule_all (emit_op_raw_checked_ptr |> Q.INST [`opc` |-> `MLOAD`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts sb sc) u =
    OK (tf with vs_inst_idx := u.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG H tm (emitted_insts sb sc) u Hf tmf` by
    (simp[Abbr `tf`, Abbr `Hf`, Abbr `tmf`] >>
     simp[update_var_def, venom_state_component_equality]) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `tf.vs_inst_idx = LENGTH sc.cs_current_insts` by simp[Abbr `tf`] >>
  suspend "load_compose"
QED

Resume abi_decode_ptr_relative_load[load_compose]:
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc` by simp[] >>
  drule_all emitted_insts_join_normalized_ptr >> strip_tac >>
  qexistsl_tac [`tf`, `Hf`, `tmf`] >> asm_rewrite_tac[] >>
  suspend "load_fields"
QED

Resume abi_decode_ptr_relative_load[load_fields]:
  `w2n (b+n2w p) = w2n b+p` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  `state_frame tf = state_frame (s with vs_inst_idx := tf.vs_inst_idx)` by
    fs[Abbr `tf`, update_var_def, state_frame_def, venom_state_component_equality] >>
  `not_fresh_at sc out` by gvs[not_fresh_at_def] >>
  `op_taint tmf (Var out) = {} /\ tmf.t_mem = tm.t_mem /\
   tmf.t_stor = tm.t_stor /\ tmf.t_trans = tm.t_trans` by
    simp[Abbr `tmf`, mload_ghost_clean, eval_operand_def] >>
  `op_prov Hf (Var out) = NONE /\ tmf.t_imm = tm.t_imm` by
    simp[Abbr `Hf`, Abbr `tmf`, op_prov_def, step_prov_def, set_prov_def,
         out_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, step_taint_def, imm_taint_def] >>
  `not_fresh_at sc ap` by
    (irule not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
  `ap <> out` by gvs[not_fresh_at_def] >>
  `abi_decode_ptr_window Hf tmf tf ap (b+n2w p) (h-p)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`H`, `u`, `tm`] >>
     simp[Abbr `tf`, Abbr `Hf`, Abbr `tmf`, lookup_var_def, update_var_def,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, op_taint_def, mk_inst_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> fs[lookup_var_def, op_taint_def]) >>
  `(fresh_vars_wrt sa s ==> fresh_vars_wrt sc tf)` by suspend "load_fresh" >>
  asm_rewrite_tac[] >>
  qpat_assum `state_frame u = _`
    (strip_assume_tac o SRULE [state_frame_def, venom_state_component_equality]) >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by metis_tac[] >>
  simp[Abbr `tf`, update_var_def, lookup_var_def, FLOOKUP_UPDATE, mload_def] >>
  qx_gen_tac `x` >> disch_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _`
    (qspec_then `x` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `not_fresh_at sb x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `x <> out` by gvs[not_fresh_at_def] >>
  simp[Abbr `Hf`, Abbr `tmf`, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  qpat_x_assum `lookup_var x u = _` mp_tac >>
  qpat_x_assum `op_taint tm (Var x) = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_var_def, op_taint_def]
QED

Resume abi_decode_ptr_relative_load[load_fresh]:
  strip_tac >>
  `lookup_var src s = SOME b` by fs[abi_decode_ptr_window_def] >>
  `ap = STRING #"%" (toString sa.cs_next_var) /\
   out = STRING #"%" (toString sb.cs_next_var)` by gvs[] >>
  `u.vs_vars = (update_var ap (b+n2w p) s).vs_vars` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, update_var_def,
          venom_state_component_equality]) >>
  `fresh_vars_wrt sb u` by
    (fs[fresh_vars_wrt_def, lookup_var_def] >>
     metis_tac[fresh_vars_wrt_advance]) >>
  `fresh_vars_wrt sc (update_var out (mload (w2n (b+n2w p)) u) u)` by
    (irule fresh_vars_wrt_advance >>
     qexistsl_tac [`sb.cs_next_var`, `sb`] >> simp[]) >>
  fs[Abbr `tf`, fresh_vars_wrt_def]
QED

Finalise abi_decode_ptr_relative_load
