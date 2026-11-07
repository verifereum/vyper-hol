(* Relative-address reads use provenance only on the src, never on a
   position.  Input windows are independent of ABI validity. *)
Theory abiDecodePtrRead
Ancestors
  abiDecodePtrMemberFrame assignTuplePtrLoadStep typedCopyPtr
  abiEncoder abiDecodeStaticProps bodyPtrDefs emitHelperProps exprLoweringProps ptrDiscipline venomState
  venomExecSemantics venomInst words arithmetic finite_map emitHelper compileEnv fragGasPathPtr
  exprSimAccounts freshWrites fragExec stateFrame fragGasSeqPtr

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
  drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG H tm u 0 Hf tmf (OK tf)` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Hf tmf (OK tf)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `state_frame tf = state_frame (s with vs_inst_idx := tf.vs_inst_idx)` by
    (fs[state_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`out`, `tf`, `Hf`, `tmf`] >> asm_rewrite_tac[] >>
  `w2n (b+n2w p) = w2n b+p` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  conj_tac >- fs[mload_def] >>
  rpt strip_tac >>
  `not_fresh_at sb x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED
