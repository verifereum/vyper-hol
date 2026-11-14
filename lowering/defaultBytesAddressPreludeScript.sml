(* Allocation and modular dynamic calldata address preparation. *)
Theory defaultBytesAddressPrelude
Ancestors moduleLowering compileEnv emitHelper emitHelperProps exprLoweringProps
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployMemoryRunPtrPrefixRegisterAddress
  abiDecoderContract fragExec fragExecMem fragGasSeqPtr fragGasCopyLoop
  venomState venomExecSemantics venomInst words finite_map list arithmetic
  decoderNavigationPtr calldataOverwritePtr bodyPtrDefs ptrDiscipline
  ctorDeployMemoryRunMemEntryRegistration defaultBytesAllocationBoundary
  loweringStateRelDefs localPtrsProps loweringHalt abiDecoderReentry
  ctorDeployLoweringEntryRegisterRun ctorDeployLoweringEntryAllocation

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

Theorem default_bytes_address_joint:
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] sa = (head,sb) /\
  emit_op CALLDATALOAD [head] sb = (offset,sc) /\
  emit_op ADD [Lit 4w;offset] sc = (src,sd) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    (?raw. run_inst_seq (emitted_insts sa sd) s = OK raw /\
      t = raw with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sd.cs_current_insts|> /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    eval_operand src t =
      SOME ((4w+abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s):bytes32) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
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
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[prefix_register_address_emit_shape] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all (Q.INST [`left` |-> `Lit (4w:bytes32)`,
      `right` |-> `Lit ((n2w(off-4)):bytes32)`, `a` |-> `4w:bytes32`,
      `b` |-> `(n2w(off-4)):bytes32`] (SPEC_ALL default_bytes_scalar_add_boundary)
    |> SRULE [eval_operand_def, op_prov_def, op_taint_def]) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`]
    (qx_choose_then `H1` (qx_choose_then `u1` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ _ (OK t1,H1,u1)` >>
  `eval_operand head t1 = SOME ((4w+n2w(off-4)):bytes32) /\
    op_taint u1 head = {}` by
    simp[Abbr `t1`, eval_operand_def, update_var_def, op_taint_def] >>
  `~t1.vs_halted /\ t1.vs_current_bb = sb.cs_current_bb /\
    t1.vs_inst_idx = LENGTH sb.cs_current_insts /\ allocas_from lo t1` by
    (qpat_assum `emit_op ADD _ sa = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     gvs[Abbr `t1`, update_var_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  `!x. head = Var x ==> not_fresh_at sb x` by
    (qpat_assum `emit_op ADD _ sa = _`
      (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_11]) >>
  drule_all calldata_load_overwrite_trace_uniform >>
  disch_then (qspecl_then [`PG`,`H1`]
    (qx_choose_then `t2` (qx_choose_then `H2` (qx_choose_then `u2` strip_assume_tac)))) >>
  `t2 = (update_var ("%" ++ toString sb.cs_next_var)
    (abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) t1) t1)
      with vs_inst_idx := LENGTH sc.cs_current_insts` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `step_inst_base (mk_inst sb.cs_next_id CALLDATALOAD [head]
       ["%" ++ toString sb.cs_next_var]) t1 =
       OK (update_var ("%" ++ toString sb.cs_next_var)
         (abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) t1) t1)` by
       (qpat_assum `eval_operand head t1 = _`
          (mp_then Any mp_tac step_CALLDATALOAD) >>
        simp[abi_decode_load_def, abi_decode_source_def]) >>
     gvs[run_inst_seq_def] >>
     gvs[venom_state_component_equality, update_var_def]) >>
  `allocas_from lo t2` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `eval_operand (Lit (4w:bytes32)) t2 = SOME 4w /\
    op_taint u2 (Lit (4w:bytes32)) = {} /\
    op_prov H2 (Lit (4w:bytes32)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  qpat_assum `emit_op ADD _ sc = _`
    (mp_then Any mp_tac default_bytes_scalar_add_boundary) >>
  disch_then (qspecl_then [`u2`,`t2`,`lo`,`fn`,`ctx`,`abi_decode_load CALLDATALOAD
    ((4w+n2w(off-4)):bytes32) t1`,`4w`,`PG`,`H2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t3` (qx_choose_then `H3`
    (qx_choose_then `u3` strip_assume_tac))) >>
  qexistsl [`t3`,`H3`,`u3`] >>
  `abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) t1 =
    abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s` by
    simp[Abbr `t1`, abi_decode_load_def, abi_decode_source_def, update_var_def] >>
  `t3 = s with <|vs_vars := t3.vs_vars;
    vs_inst_idx := LENGTH sd.cs_current_insts|>` by
    gvs[Abbr `t1`, update_var_def] >>
  `sa.cs_current_bb = sd.cs_current_bb` by
    metis_tac[prefix_register_address_emit_shape] >>
  `~t3.vs_halted /\ t3.vs_current_bb = sd.cs_current_bb /\
    t3.vs_inst_idx = LENGTH sd.cs_current_insts` by
    gvs[update_var_def, Abbr `t1`] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\ not_fresh_at sc x` by
    (qpat_assum `emit_op ADD _ sa = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     qpat_assum `emit_op CALLDATALOAD _ sb = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t2 = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `t2 = _` SUBST1_TAC >>
     qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     `not_fresh_at sb x` by metis_tac[] >>
     `x <> "%" ++ toString sb.cs_next_var` by
       (qpat_x_assum `not_fresh_at sb x` mp_tac >>
        pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
        disch_then (qspec_then `sb.cs_next_var` mp_tac) >> simp[]) >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t1 = _ /\ _` 
       (qspec_then `x` mp_tac) >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t3 = lookup_var x s /\
    FLOOKUP H3 x = FLOOKUP G x /\ op_taint u3 (Var x) = op_taint tn (Var x)` by
    (fs[op_taint_def] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t3,H3,u3)` by
    (rpt gen_tac >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  conj_tac >- (
    drule_all default_bytes_address_exec >>
    disch_then (qspec_then `s` assume_tac) >>
    qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK raw` >>
    qexists `raw` >> simp[] >>
    qpat_assum `emit_op ADD _ sa = _`
      (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
    qpat_assum `emit_op CALLDATALOAD _ sb = _`
      (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
    gvs[Abbr `raw`, Abbr `t1`, update_var_def]) >>
  metis_tac[]
QED

(* Memory/history certificate at the deterministic three-instruction endpoint. *)
Theorem default_bytes_address_memory:
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] sa = (head,sb) /\
  emit_op CALLDATALOAD [head] sb = (offset,sc) /\
  emit_op ADD [Lit 4w;offset] sc = (src,sd) /\
  fn_has_code sa sd fn /\ alloca_history fn s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?raw. run_inst_seq (emitted_insts sa sd) s = OK raw /\
    raw = update_var ("%" ++ toString (sa.cs_next_var+2))
      (4w + abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s)
      (update_var ("%" ++ toString (sa.cs_next_var+1))
        (abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s)
        (update_var ("%" ++ toString sa.cs_next_var) (4w+n2w(off-4)) s)) /\
    gas_path_mem ctx fn s 0
      (OK (raw with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    alloca_history fn (raw with vs_inst_idx := LENGTH sd.cs_current_insts)
Proof
  strip_tac >>
  drule_all default_bytes_address_exec >>
  disch_then (qspec_then `s` assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK raw` >>
  drule_all default_bytes_address_shape >> strip_tac >>
  `sd.cs_blocks = sa.cs_blocks /\ sd.cs_current_bb = sa.cs_current_bb` by
    gvs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sd)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sd) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]) >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `raw`, update_var_def] >>
  drule_all ctor_checked_arg_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `raw` >> simp[Abbr `raw`]
QED

Theorem default_bytes_address_prelude:
  compile_alloc_buffer cap st = (buf,allocated) /\
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] allocated = (head,after_head) /\
  emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
  emit_op ADD [Lit 4w;offset] after_load = (src,after_src) /\
  0 < cap /\ cap < dimword (:256) /\ fn_has_code st after_src fn /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) ready = SOME (n2w s.vs_alloca_next) /\
    eval_operand src ready = SOME ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32) /\
    abi_decoder_operand_live after_src.cs_next_var (Var p) /\
    abi_decoder_operand_live after_src.cs_next_var src /\
    not_fresh_at after_src p /\ (!v. src = Var v ==> not_fresh_at after_src v) /\
    ptr_covers H u p ready cap /\ op_taint u src = {} /\ op_prov H src = NONE /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,cap) /\
    ready.vs_alloca_next = s.vs_alloca_next+cap /\
    s.vs_alloca_next+cap < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv_from k ctx fn site ready /\
    allocas_from lo ready /\ lo <= ready.vs_alloca_next /\ alloca_history fn ready /\
    ~ready.vs_halted /\ ready.vs_current_bb = after_src.cs_current_bb /\
    ready.vs_inst_idx = LENGTH after_src.cs_current_insts /\
    ready = (s with <|vs_vars := ready.vs_vars; vs_allocas := ready.vs_allocas;
      vs_alloca_next := ready.vs_alloca_next;
      vs_inst_idx := LENGTH after_src.cs_current_insts|>) /\
    st.cs_next_id < after_src.cs_next_id /\ st.cs_next_var <= after_src.cs_next_var /\
    (!id. id <> st.cs_next_id ==> FLOOKUP ready.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    u.t_mem = tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    gas_path_mem ctx fn s 0 (OK ready) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK ready,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u ready) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  qpat_assum `emit_op ADD _ allocated = _`
    (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
  qpat_assum `emit_op CALLDATALOAD _ after_head = _`
    (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
  qpat_assum `emit_op ADD _ after_load = _`
    (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
  `cs_extends allocated after_src` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all default_bytes_allocation_boundary >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] (qx_choose_then `a`
    (qx_choose_then `H0` (qx_choose_then `u0` (qx_choose_then `p` strip_assume_tac))))) >>
  drule_all default_bytes_address_joint >>
  disch_then (qspecl_then [`u0`,`PG`,`H0`] (qx_choose_then `ready`
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))) >>
  drule_all default_bytes_address_memory >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx fn a 0 (OK ready) /\ alloca_history fn ready` by gvs[] >>
  qexistsl [`ready`,`H`,`u`,`p`] >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- suspend "pullback" >>
  reverse conj_tac >- suspend "origin" >>
  reverse conj_tac >- suspend "memory" >>
  suspend "fields"
QED
Resume default_bytes_address_prelude[fields]:
  `ready.vs_allocas = a.vs_allocas /\ ready.vs_alloca_next = a.vs_alloca_next /\
    ready.vs_call_ctx = a.vs_call_ctx` by
    (qpat_assum `ready = a with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `a.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `a = s with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) a =
    abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  qpat_x_assum `ready = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `raw' = _` kall_tac >>
  pure_rewrite_tac[GSYM CONJ_ASSOC] >> simp[] >>
  conj_tac >- (fs[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (irule abi_decoder_operand_live_mono >>
    qexists `allocated.cs_next_var` >> simp[]) >>
  conj_tac >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    ASCIInumbersTheory.toString_11] >>
  conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
    qexists `allocated` >> simp[]) >>
  conj_tac >- simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists `a` >> simp[]) >>
  conj_tac >- (irule deploy_ctor_alloca_frontier_fields >>
    qexistsl [`a`,`site`] >> simp[]) >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- gvs[venom_state_component_equality] >>
  conj_tac >- suspend "old_operands" >>
  suspend "old_ghosts"
QED
Resume default_bytes_address_prelude[memory]:
  metis_tac[fragGasPathMemTheory.gas_path_mem_then, ADD]
QED
Resume default_bytes_address_prelude[origin]:
  rpt gen_tac >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]
QED
Resume default_bytes_address_prelude[pullback]:
  metis_tac[]
QED
Resume default_bytes_address_prelude[old_operands]:
  `!v. not_fresh_at st v ==> not_fresh_at allocated v` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `st` >> simp[]) >>
  Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    eval_operand_def]
  >- (strip_tac >>
      `not_fresh_at st s'` by simp[not_fresh_at_def] >>
      qpat_assum `!op. abi_decoder_operand_live _ op ==> _`
        (qspec_then `Var s'` mp_tac) >>
      simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        eval_operand_def] >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED
Resume default_bytes_address_prelude[old_ghosts]:
  `!v. not_fresh_at st v ==> not_fresh_at allocated v` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `st` >> simp[]) >>
  metis_tac[]
QED
Finalise default_bytes_address_prelude
