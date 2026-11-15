(* The offset's arithmetic and optional bounds checks are scalar. *)
Theory abiDecodePtrArrayPositionJoint
Ancestors
  abiDecodePtrRead abiDecodePtrScalarFrame abiDecodePtrScalarAbort
  abiDecodePtrHead abiDecodePtrBytesMember abiDecodePtrNormalized abiDecodePtrContinuation
  abiDecoderVarSequence abiDecoderArrayBound abiDecoderGuard abiDecoderRange abiDecoderReentryPointer
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  abiEncoder abiDecoderContract abiDecodePtrMemberFrame
  fragGasCopyLoop fragGasOriginPtr fragGasOriginPtrDead fragExecMem fragExec
  instSeqComposePtr ghostPcTransportPtr entryDecoderHistoryFrame
  exprSimAccounts emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst
  stateFrame instIdxIndep finite_map pred_set words list rich_list arithmetic

Theorem array_position_suffix_scalar[local]:
  emit_op ADD [data;offset] sa = (v,mid) /\
  (if hi = Lit 0w then sb = mid
   else abi_decode_array_pointer_guard v data hi abi_sz mid = ((),sb)) /\
  data IN A /\ offset IN A /\ hi IN A /\ Lit (n2w abi_sz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ v IN B /\ A SUBSET B
Proof
  strip_tac >> Cases_on `hi = Lit 0w`
  >- (gvs[] >> qexists_tac `v INSERT A` >> simp[SUBSET_DEF] >>
      irule bop_scalar_seq_emit_op >> simp[] >>
      qexistsl_tac [`ADD`, `[data;offset]`] >> simp[]) >>
  `abi_decode_array_pointer_guard v data hi abi_sz mid = ((),sb)` by gvs[] >>
  qpat_x_assum `abi_decode_array_pointer_guard _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_array_pointer_guard_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_ge_guard v data mid = ((),c1)` >>
  rename1 `emit_op ADD [v; Lit (n2w abi_sz)] c1 = (ending,c2)` >>
  `?B1. bop_scalar_seq R A (emitted_insts sa c1) B1 /\ v IN B1` by
    (irule abi_decode_position_suffix_scalar >> simp[] >> metis_tac[]) >>
  `A SUBSET B1` by metis_tac[bop_scalar_seq_available] >>
  `sa.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     simp[abi_decode_ge_guard_def,comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> decide_tac) >>
  `!x. x IN R ==> not_fresh_at c1 x` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `?B2. bop_scalar_seq R B1 (emitted_insts c1 sb) B2 /\
     B1 SUBSET B2 /\ ending IN B2` by
    (irule abi_decode_add_range_scalar >> simp[] >>
     qexistsl_tac [`hi`, `Lit (n2w abi_sz)`, `c2`, `v`] >>
     simp[] >> fs[SUBSET_DEF]) >>
  `inst_extends sa c1 /\ inst_extends c1 sb` by
    (imp_res_tac inst_extends_emit_op >>
     imp_res_tac abi_decode_ge_guard_shape >>
     imp_res_tac compile_abi_decode_range_check_shape >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qexists_tac `B2` >> simp[] >> conj_tac
  >- (irule bop_scalar_seq_append >> qexists_tac `B1` >> simp[]) >>
  fs[SUBSET_DEF]
QED

Theorem array_position_phases[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) ==>
  ?addr c1 offset c2 mid Q.
    compile_abi_dec_addr (Var source) head sa = (addr,c1) /\
    emit_op MLOAD [addr] c1 = (offset,c2) /\
    emit_op ADD [data;offset] c2 = (v,mid) /\
    (if hi = Lit 0w then sb = mid
     else abi_decode_array_pointer_guard v data hi abi_sz mid = ((),sb)) /\
    inst_extends sa c2 /\ inst_extends c2 sb /\
    same_blocks sa c2 /\ same_blocks c2 sb /\
    cs_extends sa c2 /\ cs_extends c2 sb /\
    sa.cs_next_var <= c2.cs_next_var /\
    emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb /\
    bop_scalar_seq {x | not_fresh_at sa x}
      {data;offset;hi;Lit (n2w abi_sz)} (emitted_insts c2 sb) Q /\ v IN Q
Proof
  strip_tac >>
  `?addr c1 offset c2 mid.
     compile_abi_dec_addr (Var source) head sa = (addr,c1) /\
     emit_op MLOAD [addr] c1 = (offset,c2) /\
     emit_op ADD [data;offset] c2 = (v,mid) /\
     (if hi = Lit 0w then sb = mid
      else abi_decode_array_pointer_guard v data hi abi_sz mid = ((),sb))` by
    (qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `hi = Lit 0w` >>
     simp[compile_abi_decode_dyn_elem_ptr_def,abi_decode_array_pointer_guard_def,
       abi_decode_ge_guard_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `emit_op ADD [Var source;head] sa = (addr,c1)` by
    fs[compile_abi_dec_addr_def] >>
  `inst_extends sa c2 /\ same_blocks sa c2 /\
   sa.cs_next_var <= c2.cs_next_var /\ cs_extends sa c2` by
    (imp_res_tac inst_extends_emit_op >>
     imp_res_tac emit_op_extends_next_var >>
     imp_res_tac emit_op_extends >>
     metis_tac[inst_extends_trans,same_blocks_trans,cs_extends_trans,LESS_EQ_TRANS]) >>
  `inst_extends c2 sb /\ same_blocks c2 sb` by
    (Cases_on `hi = Lit 0w` >> gvs[]
     >- metis_tac[inst_extends_emit_op,emit_op_extends] >>
     qpat_x_assum `abi_decode_array_pointer_guard _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_array_pointer_guard_def,abi_decode_ge_guard_def,
       compile_abi_decode_range_check_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     fs[same_blocks_def] >> metis_tac[inst_extends_trans]) >>
  `cs_extends c2 sb` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     fs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `?Q. bop_scalar_seq {x | not_fresh_at sa x}
      {data;offset;hi;Lit (n2w abi_sz)} (emitted_insts c2 sb) Q /\
      v IN Q /\ {data;offset;hi;Lit (n2w abi_sz)} SUBSET Q` by
    (irule array_position_suffix_scalar >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem array_position_prefix_joint[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s source b L /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
    op_prov G op = NONE /\ op_taint tn op = {}) [head;data;hi] /\
  eval_operand head s = SOME (n2w p) /\ p+32 <= L /\
  w2n b+L < dimword (:256) /\ w2n b+L <= s.vs_alloca_next ==>
  ?c2 t Gm tm A Q.
    inst_extends sa c2 /\ inst_extends c2 sb /\
    same_blocks sa c2 /\ same_blocks c2 sb /\
    emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb /\
    run_inst_seq (emitted_insts sa c2) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c2) s Gm tm /\
    t.vs_inst_idx = LENGTH c2.cs_current_insts /\
    bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts c2 sb) Q /\ v IN Q /\
    (!op. op IN A ==> op_prov Gm op = NONE /\ op_taint tm op = {}) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gm x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule array_position_phases >> strip_tac >>
  `fn_has_code sa c2 func` by metis_tac[fn_has_code_split] >>
  `op_taint tn head = {}` by fs[] >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST
    [`D` |-> `D`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!op. MEM op [head;data;hi] ==>
    op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op` by
    (rpt strip_tac >> Cases_on `op` >>
     fs[op_prov_def,op_taint_def,EVERY_MEM] >> metis_tac[]) >>
  `op_prov G' (Lit (n2w abi_sz)) = NONE /\
   op_taint tn' (Lit (n2w abi_sz)) = {}` by simp[op_prov_def,op_taint_def] >>
  `!op. op IN {data;offset;hi;Lit (n2w abi_sz)} ==>
    op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (rw[] >> fs[] >> simp[op_prov_def,op_taint_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa c2) s` by
    (irule abi_decode_relative_load_mem_ok >>
     goal_assum (drule_at (Pat `compile_abi_dec_addr _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     qexistsl_tac [`b`,`p`] >> fs[abi_decode_ptr_window_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
     simp[] >> metis_tac[bop_scalar_seq_mem_ok]) >>
  qexistsl_tac [`c2`,`t`,`G'`,`tn'`,`{data;offset;hi;Lit (n2w abi_sz)}`,`Q`] >>
  asm_rewrite_tac[]
QED

Theorem array_position_code[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule array_position_phases >> strip_tac >>
  `inst_extends sa sb /\ same_blocks sa sb` by
    metis_tac[inst_extends_trans,same_blocks_trans] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (conj_tac >- fs[same_blocks_def] >>
     qpat_assum `inst_extends sa sb`
       (fn th => rewrite_tac [REWRITE_RULE [inst_extends_def] th]) >>
     simp[IS_PREFIX_APPEND]) >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts sa sb)` by
    (irule abi_decoder_array_pointer_code >>
     goal_assum (drule_at (Pat `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _`)) >>
     simp[abi_decode_source_opcode_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     `abi_decoder_reentry_opcode i.inst_opcode /\
      ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode` by
       (qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _ /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     fs[abi_decoder_reentry_opcode_def] >> gvs[is_alloca_op_def]) >>
  qexists_tac `bb` >> simp[IS_PREFIX_APPEND] >>
  qpat_assum `inst_extends sa sb`
    (mp_tac o AP_TERM ``LENGTH:instruction list -> num`` o REWRITE_RULE [inst_extends_def]) >>
  simp[]
QED

Theorem abi_decode_array_position_success_joint:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s source b L /\ not_fresh_at sa source /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
    op_prov G op = NONE /\ op_taint tn op = {}) [head;data;hi] /\
  eval_operand head s = SOME (n2w p) /\ p+32 <= L /\
  w2n b+L < dimword (:256) /\ w2n b+L <= s.vs_alloca_next /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    state_frame u = state_frame s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof

  strip_tac >>
  mp_tac (array_position_prefix_joint |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all array_position_code >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c2) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 sb)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts c2 sb) t = OK (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_continue_normalized >> simp[] >>
     qexistsl_tac [`s`,`emitted_insts sa c2`] >> fs[]) >>
  mp_tac (abi_decode_scalar_success_frame |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`,
     `R` |-> `{x | not_fresh_at sa x}`, `B` |-> `Q`,
     `code` |-> `emitted_insts c2 sb`, `s` |-> `t`,
     `u` |-> `u with vs_inst_idx := t.vs_inst_idx`,
     `G` |-> `Gm`, `tn` |-> `tm`, `fn` |-> `func`, `j` |-> `t.vs_inst_idx`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c2)` by
    fs[inst_extends_def] >>
  `inst_seq_ptr
     <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
     0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (asm_rewrite_tac[] >> irule inst_seq_ptr_append_ok >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Gm`,`t with vs_inst_idx := s.vs_inst_idx`,`tm`] >>
     `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa c2) = t` by
       (simp_tac (srw_ss()) [NoAsms,venom_state_component_equality] >> metis_tac[]) >>
     gvs[]) >>
  `u with vs_inst_idx := s.vs_inst_idx = u` by
    (qspec_then `emitted_insts sa sb` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`,`s.vs_inst_idx`]
       (mp_tac o SIMP_RULE (srw_ss()) [])) >>
     simp[exec_result_map_def,venom_state_component_equality]) >>
  `state_frame u = state_frame s` by
    (qpat_assum `state_frame t = _`
       (strip_assume_tac o SRULE [state_frame_def,venom_state_component_equality]) >>
     qpat_assum `u with vs_inst_idx := _ = t with vs_vars := _`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     qpat_assum `u with vs_inst_idx := s.vs_inst_idx = u`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     fs[state_frame_def,venom_state_component_equality]) >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
      allocas_from lo u` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  fs[lookup_var_def] >> metis_tac[]
QED

Theorem abi_decode_array_position_abort_joint:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s source b L /\ not_fresh_at sa source /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
    op_prov G op = NONE /\ op_taint tn op = {}) [head;data;hi] /\
  eval_operand head s = SOME (n2w p) /\ p+32 <= L /\
  w2n b+L < dimword (:256) /\ w2n b+L <= s.vs_alloca_next /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?j G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort a (u with vs_inst_idx := j),G',tn')) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
      vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof

  strip_tac >>
  mp_tac (array_position_prefix_joint |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all array_position_code >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c2) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 sb)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts c2 sb) t =
     Abort a (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_continue_abort_normalized >> simp[] >>
     qexistsl_tac [`s`,`emitted_insts sa c2`] >> fs[]) >>
  mp_tac (scalar_seq_abort_replay_ptr |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`,
     `R` |-> `{x | not_fresh_at sa x}`, `B` |-> `Q`,
     `code` |-> `emitted_insts c2 sb`, `s` |-> `t`,
     `t` |-> `u with vs_inst_idx := t.vs_inst_idx`,
     `G` |-> `Gm`, `tn` |-> `tm`, `fn` |-> `func`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c2)` by
    fs[inst_extends_def] >>
  `inst_seq_ptr
     <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
     0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (asm_rewrite_tac[] >> irule inst_seq_ptr_append_ok >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Gm`,`t with vs_inst_idx := s.vs_inst_idx`,`tm`] >>
     `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa c2) = t` by
       (simp_tac (srw_ss()) [NoAsms,venom_state_component_equality] >> metis_tac[]) >>
     gvs[]) >>
  `(u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
     vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s` by
    (qpat_assum `state_frame t = _`
       (strip_assume_tac o SRULE [state_frame_def,venom_state_component_equality]) >>
     qpat_assum `((u with vs_inst_idx := _) with <|vs_vars := _;
       vs_halted := _; vs_returndata := _|>) = t`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     fs[venom_state_component_equality]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` (qx_choose_then `abort_idx` assume_tac)) >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (irule (inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
     simp[] >> fs[EVERY_MEM]) >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort a (u with vs_inst_idx := abort_idx),Gf,tnf)` by
    (gen_tac >> qpat_assum `!D lo explicit PG G tn HG th. _`
       (qspecl_then
         [`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
          `lo`,`explicit`,`PG`,`G`,`tn`,`Gf`,`tnf`] irule) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _;
       vs_halted := _; vs_returndata := _|>) = s`
      (mp_tac o AP_TERM ``\z:venom_state. z.vs_allocas``) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. x IN {x | not_fresh_at sa x} ==> FLOOKUP Gf x = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. x IN {x | not_fresh_at sa x} ==> FLOOKUP _ x = _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lookup_var_def,op_taint_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`abort_idx`,`Gf`,`tnf`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  fs[allocas_from_def,venom_state_component_equality] >> metis_tac[]
QED

Theorem abi_decode_array_position_shape:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz sa = (v,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb
Proof
  strip_tac >> drule array_position_phases >> strip_tac >>
  metis_tac[inst_extends_trans,same_blocks_trans]
QED
