(* Allocation and modular dynamic calldata address preparation. *)
Theory defaultBytesAddressPrelude
Ancestors moduleLowering compileEnv emitHelper emitHelperProps exprLoweringProps
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployMemoryRunPtrPrefixRegisterAddress
  abiDecoderContract fragExec fragExecMem fragGasSeqPtr fragGasCopyLoop
  venomState venomExecSemantics venomInst words finite_map list arithmetic
  decoderNavigationPtr calldataOverwritePtr bodyPtrDefs ptrDiscipline

Theorem default_bytes_address_shape:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] sa = (head,sb) /\
  emit_op CALLDATALOAD [head] sb = (offset,sc) /\
  emit_op ADD [Lit (n2w 4);offset] sc = (src,sd) ==>
  head = Var ("%" ++ toString sa.cs_next_var) /\
  offset = Var ("%" ++ toString (sa.cs_next_var+1)) /\
  src = Var ("%" ++ toString (sa.cs_next_var+2)) /\
  inst_extends sa sd /\ same_blocks sa sd /\
  sd.cs_next_var = sa.cs_next_var+3 /\ sd.cs_next_id = sa.cs_next_id+3 /\
  emitted_insts sa sd =
    [mk_inst sa.cs_next_id ADD [Lit 4w;Lit (n2w (off-4))]
       ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) CALLDATALOAD [head]
       ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) ADD [Lit 4w;offset]
       ["%" ++ toString (sa.cs_next_var+2)]]
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_inst_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, inst_extends_def, same_blocks_def,
    APPEND_ASSOC, DROP_PREFIX]
QED

Theorem default_bytes_address_exec:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] sa = (head,sb) /\
  emit_op CALLDATALOAD [head] sb = (offset,sc) /\
  emit_op ADD [Lit (n2w 4);offset] sc = (src,sd) ==>
  run_inst_seq (emitted_insts sa sd) s =
    OK (update_var ("%" ++ toString (sa.cs_next_var+2))
      (4w + abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s)
      (update_var ("%" ++ toString (sa.cs_next_var+1))
        (abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s)
        (update_var ("%" ++ toString sa.cs_next_var) (4w+n2w(off-4)) s)))
Proof
  strip_tac >> drule_all default_bytes_address_shape >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `v2 = "%" ++ toString (sa.cs_next_var+2)` >>
  qabbrev_tac `h = (4w+n2w(off-4)):bytes32` >>
  qabbrev_tac `w = abi_decode_load CALLDATALOAD h s` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Lit 4w;Lit (n2w(off-4))] [v0]) s =
    OK (update_var v0 h s)` by
    (simp[Abbr `h`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) CALLDATALOAD [Var v0] [v1])
      (update_var v0 h s) = OK (update_var v1 w (update_var v0 h s))` by
    (qspec_then `Var v0` mp_tac step_CALLDATALOAD >>
     disch_then (qspec_then `h` mp_tac) >>
     simp[eval_operand_def, lookup_var_update_var, Abbr `w`, abi_decode_load_def,
       abi_decode_source_def, update_var_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) ADD [Lit 4w;Var v1] [v2])
      (update_var v1 w (update_var v0 h s)) =
    OK (update_var v2 (4w+w) (update_var v1 w (update_var v0 h s)))` by
    (irule step_ADD >> simp[eval_operand_def, lookup_var_update_var]) >>
  gvs[Abbr `v0`, Abbr `v1`, Abbr `v2`, Abbr `h`, Abbr `w`] >>
  simp[run_inst_seq_def]
QED

(* The two ADDs share this scalar boundary; neither needs runtime freshness. *)
Theorem default_bytes_scalar_add_boundary[local]:
  emit_op ADD [left;right] sa = (out,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  fn_has_code sa sb fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    t = (update_var ("%" ++ toString sa.cs_next_var) (a+b) s)
      with vs_inst_idx := LENGTH sb.cs_current_insts /\
    eval_operand out t = SOME (a+b) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (update_var ("%" ++ toString sa.cs_next_var) (a+b) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `step_inst_base (mk_inst sa.cs_next_id ADD [left;right]
       ["%" ++ toString sa.cs_next_var]) s =
       OK (update_var ("%" ++ toString sa.cs_next_var) (a+b) s)` by
       (irule step_ADD >> simp[]) >> gvs[run_inst_seq_def]) >>
  drule_all (Q.SPEC `ADD` emit_scalar_binop_endpoint_ptr_origin_core
    |> SRULE []) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`] strip_assume_tac) >>
  drule prefix_register_address_emit_shape >> strip_tac >>
  qexistsl [`(update_var ("%" ++ toString sa.cs_next_var) (a+b) s)
      with vs_inst_idx := LENGTH sb.cs_current_insts`, `HG`, `u`] >>
  simp[eval_operand_def, lookup_var_update_var, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE, loweringStateRelDefsTheory.not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL]
QED
