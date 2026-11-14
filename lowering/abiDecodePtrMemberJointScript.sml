(* Concrete member navigation preserves its input window and output coverage. *)
Theory abiDecodePtrMemberJoint
Ancestors
  abiDecodePtrSelectionJoint abiDecodePtrBytesTail abiDecodePtrMemberFrame
  abiDecoderMemberSetup abiDecoderMemberCode abiDecodePtrSelectionFrame
  abiMalformedMemberSetup abiMalformedTraversal abiDecoderTypedCompose
  abiDecoderContract abiDecoderReentryPointer abiDecodePtrNormalized
  abiEncoder abiDecoderReentry loweringStateRelDefs decoderGhostFramePtr
  abiEncoderWindowSequence
  bodyPtrBopScalarSeq bodyPtrBopScalarCompile
  fragGasCopyLoop fragGasOriginPtrDead fragGasOriginPtr fragExecMem fragExec
  entryDecoderHistoryFrame emitHelperProps exprLoweringProps freshWrites
  bodyPtrDefs ptrDiscipline compileEnv venomState venomExecSemantics venomInst
  stateFrame finite_map words list rich_list arithmetic pred_set

Theorem abi_decode_member_destination_success_joint[local]:
  emit_op ADD [Var dst;Lit (n2w vo)] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa dst /\ ptr_covers G tn dst s cap /\
  lookup_var dst s = SOME d /\ vo+k <= cap /\ w2n d+cap < dimword(:256) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    ptr_covers G' tn' out u k /\ lookup_var out u = SOME (d+n2w vo) /\
    state_frame u = state_frame s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Lit (n2w vo)) s = SOME (n2w vo) /\
   op_taint tn (Lit (n2w vo)) = {} /\ op_taint tn (Var dst) = {}` by
    fs[eval_operand_def, op_taint_def, ptr_covers_def] >>
  mp_tac (abi_decode_ptr_output_address |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`,
     `pos` |-> `Lit (n2w vo)`, `q` |-> `vo`, `b` |-> `d`,
     `dst` |-> `dst`, `out` |-> `out`, `sa` |-> `sa`, `sb` |-> `sb`,
     `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`, `ctx` |-> `ctx`,
     `cap` |-> `cap`, `k` |-> `k`, `func` |-> `func`, `PG` |-> `PG`]) >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `u = update_var out (d+n2w vo) s` by
    (qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK (_ with vs_inst_idx := _)`
       mp_tac >> fs[venom_state_component_equality, update_var_def]) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr _ 0 ctx func PG G tn
    (emitted_insts sa sb) s HG tm` >>
  `bop_scalar_seq {} UNIV (emitted_insts sa sb) (Var out INSERT UNIV)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[Var dst;Lit (n2w vo)]`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bop_scalar_seq_mem_ok] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_extends, same_blocks_def] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by simp[] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `s.vs_inst_idx+LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `!explicit. gas_origin_ptr_path
    (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
      lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),HG,tm) /\
    allocas_from lo u` by
    (gen_tac >> mp_tac (run_inst_seq_origin_ptr_lift |> Q.INST
       [`code` |-> `emitted_insts sa sb`, `t` |-> `u`, `s` |-> `s`,
        `G'` |-> `HG`, `tn'` |-> `tm`, `G` |-> `G`, `tn` |-> `tn`,
        `ctx` |-> `ctx`, `func` |-> `func`, `PG` |-> `PG`,
        `bb` |-> `bb`, `lo` |-> `lo`, `explicit` |-> `explicit`,
        `D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
          d_imm := K {}; d_ret := K {}|>`]) >>
     (impl_tac >- simp[update_var_def, venom_state_component_equality]) >>
     simp[update_var_def, venom_state_component_equality]) >>
  `state_frame u = state_frame s` by
    (qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     simp[update_var_def, state_frame_def]) >>
  qexistsl_tac [`HG`, `tm`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  asm_rewrite_tac[] >>
  fs[Abbr `HG`, Abbr `tm`, lookup_var_def, update_var_def,
     ghostPcTransportPtrTheory.ptr_covers_inst_idx] >> metis_tac[]
QED

Theorem abi_decode_member_setup_success_joint:
  abi_decode_member_setup (Var dst) pos MLOAD (Var src) hi dyn ao vo sa = (ops,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z+n2w ao) /\
  (dyn ==> p+32 <= h /\ w2n b+h < dimword(:256) /\
    w2n b+h <= s.vs_alloca_next) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME d /\
  vo+k <= cap /\ w2n d+cap < dimword(:256) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?out G' tn'. SND ops = Var out /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    ptr_covers G' tn' out u k /\ lookup_var out u = SOME (d+n2w vo) /\
    state_frame u = state_frame s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u = s with vs_vars := u.vs_vars` by
    (drule abi_malformed_member_setup_instructions >> strip_tac >>
     drule_all abi_malformed_setup_sequence_frame >> simp[]) >>
  `state_frame u = state_frame s` by
    (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  qpat_x_assum `u = s with vs_vars := _` kall_tac >>
  Cases_on `compile_getelemptr_abi pos dyn ao MLOAD (Var src) hi sa` >>
  rename1 `compile_getelemptr_abi pos dyn ao MLOAD (Var src) hi sa = (child,mid)` >>
  `?output_op finish_st. emit_op ADD [Var dst;Lit (n2w vo)] mid =
      (output_op,finish_st)` by
    (Cases_on `emit_op ADD [Var dst;Lit (n2w vo)] mid` >> metis_tac[]) >>
  `ops = (child,output_op) /\ finish_st = sb` by
    fs[abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  qpat_x_assum `finish_st = sb` SUBST_ALL_TAC >>
  qpat_x_assum `ops = (child,output_op)` SUBST_ALL_TAC >>
  `inst_extends sa mid /\ same_blocks sa mid` by
    (Cases_on `dyn` >- metis_tac[abi_decode_selection_shape] >>
     `emit_op ADD [pos;Lit (n2w ao)] sa = (child,mid)` by
       (Cases_on `emit_op ADD [pos;Lit (n2w ao)] sa` >>
        fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
     metis_tac[inst_extends_emit_op, emit_op_extends]) >>
  `inst_extends mid sb /\ same_blocks mid sb` by
    metis_tac[inst_extends_emit_op, emit_op_extends] >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    metis_tac[fn_has_code_split] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa mid)` by
    (Cases_on `dyn`
     >- (drule abi_decode_selection_shape >> strip_tac >>
         rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
         `(fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD)` by
           (qpat_assum `EVERY (\i. (_ \/ _) /\ _) _`
              (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
            disch_then (qspec_then `i` mp_tac) >> simp[]) >>
         Cases_on `fresh_write_op i.inst_opcode`
         >- metis_tac[fresh_write_op_simple] >> fs[is_terminator_def]) >>
     `emit_op ADD [pos;Lit (n2w ao)] sa = (child,mid)` by
       (Cases_on `emit_op ADD [pos;Lit (n2w ao)] sa` >>
        fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
     drule emitted_insts_emit_op >> strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
  `?r. r.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa mid) /\
     run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
     run_inst_seq (emitted_insts mid sb) r = OK (u with vs_inst_idx := r.vs_inst_idx)` by
    (irule abi_decode_run_split_normalized >> simp[] >> metis_tac[]) >>
  `r.vs_inst_idx = LENGTH mid.cs_current_insts` by fs[inst_extends_def] >>
  mp_tac (abi_decode_getelemptr_success_joint |> Q.INST
    [`sb` |-> `mid`, `v` |-> `child`, `off` |-> `ao`,
     `u` |-> `r with vs_inst_idx := s.vs_inst_idx`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `op_prov Gm child = NONE` >>
  rename1 `op_taint tm child = {}` >>
  `(r with vs_inst_idx := s.vs_inst_idx) with
     vs_inst_idx := LENGTH mid.cs_current_insts = r` by
    simp[venom_state_component_equality] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK r,Gm,tm)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `(r with vs_inst_idx := _) with vs_inst_idx := _ = r`
       (fn th => simp_tac (srw_ss()) [th])) >>
  `~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
    r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
    r.vs_alloca_next = s.vs_alloca_next` by
    fs[state_frame_def, venom_state_component_equality, same_blocks_def] >>
  `lookup_var dst r = SOME d /\ ptr_covers Gm tm dst r cap` by
    (conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
     irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `sa.cs_next_var <= mid.cs_next_var /\
    (!x. child = Var x ==> not_fresh_at mid x)` by
    (drule abi_decoder_member_pointer_counters >> strip_tac >>
     conj_tac >- (simp[] >> decide_tac) >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `not_fresh_at mid dst` by (fs[not_fresh_at_def] >> decide_tac) >>
  `?out. output_op = Var out` by metis_tac[emitted_insts_emit_op] >>
  pop_assum strip_assume_tac >> gvs[] >>
  `allocas_from lo r` by (fs[allocas_from_def] >> metis_tac[]) >>
  mp_tac (abi_decode_member_destination_success_joint |> Q.INST
    [`sa` |-> `mid`, `s` |-> `r`, `G` |-> `Gm`, `tn` |-> `tm`,
     `u` |-> `u with vs_inst_idx := r.vs_inst_idx`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `ptr_covers Gf tf out _ k` >>
  `op_prov Gf child = NONE /\ op_taint tf child = {}` by
    (Cases_on `child` >> fs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at mid x` by (fs[not_fresh_at_def] >> decide_tac) >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `(u with vs_inst_idx := r.vs_inst_idx) with
     vs_inst_idx := LENGTH sb.cs_current_insts =
     u with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp[venom_state_component_equality] >>
  qexistsl_tac [`Gf`, `tf`] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ (OK r,Gm,tm)`
        (qspecl_then [`D`, `explicit`] assume_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (r,Gm,tm) _ _`
        (qspecl_then [`D`, `explicit`] assume_tac) >>
      metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  fs[ghostPcTransportPtrTheory.ptr_covers_inst_idx, lookup_var_def] >>
  fs[allocas_from_def] >> metis_tac[]
QED

Theorem abi_decode_member_setup_abort_joint:
  abi_decode_member_setup (Var dst) pos MLOAD (Var src) hi dyn ao vo sa = (ops,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z+n2w ao) /\
  (dyn ==> p+32 <= h /\ w2n b+h < dimword(:256) /\
    w2n b+h <= s.vs_alloca_next) /\
  lookup_var dst s = SOME d /\ allocas_from lo s /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?j G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort a (u with vs_inst_idx := j),G',tn')) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
      vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_malformed_member_setup_instructions >> strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi pos dyn ao MLOAD (Var src) hi sa = (child,mid)` >>
  rename1 `emit_op ADD [Var dst;Lit (n2w vo)] mid = (child_dst,sb)` >>
  `inst_extends sa mid /\ same_blocks sa mid` by
    (Cases_on `dyn` >- metis_tac[abi_decode_selection_shape] >>
     `emit_op ADD [pos;Lit (n2w ao)] sa = (child,mid)` by
       (Cases_on `emit_op ADD [pos;Lit (n2w ao)] sa` >>
        fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
     metis_tac[inst_extends_emit_op, emit_op_extends]) >>
  `inst_extends mid sb /\ same_blocks mid sb` by
    metis_tac[inst_extends_emit_op, emit_op_extends] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts sa mid) s = Abort a u` by
    (Cases_on `?r. run_inst_seq (emitted_insts sa mid) s = OK r`
     >- (pop_assum strip_assume_tac >>
         `r = s with vs_vars := r.vs_vars /\
          !x. not_fresh_at sa x ==> FLOOKUP r.vs_vars x = FLOOKUP s.vs_vars x` by
           (irule abi_malformed_setup_sequence_frame >>
            qexists_tac `emitted_insts sa mid` >> simp[] >> fs[EVERY_APPEND]) >>
         `eval_operand (Var dst) r = SOME d /\
          eval_operand (Lit (n2w vo)) r = SOME (n2w vo)` by
           (fs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
         drule_all window_emit_add_pure >>
         disch_then (qx_choose_then `add_end` strip_assume_tac) >>
         `run_inst_seq (emitted_insts sa sb) s = OK add_end` by
           (qpat_assum `run_inst_seq (emitted_insts sa mid) s = OK r`
              (mp_then Any (qspec_then `emitted_insts mid sb` mp_tac)
                run_inst_seq_append) >>
            fs[window_pure_seq_def, window_seq_def]) >> fs[]) >>
     `!r. run_inst_seq (emitted_insts sa mid) s <> OK r` by metis_tac[] >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> simp[] >> metis_tac[]) >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa mid func` by metis_tac[fn_has_code_split] >>
  Cases_on `dyn` >> gvs[]
  >- (mp_tac (abi_decode_getelemptr_abort_joint |> Q.INST
        [`pos` |-> `pos`, `off` |-> `ao`, `src` |-> `src`, `hi` |-> `hi`,
         `sa` |-> `sa`, `v` |-> `child`, `sb` |-> `mid`, `func` |-> `func`,
         `ctx` |-> `ctx`, `s` |-> `s`, `u` |-> `u`, `a` |-> `a`,
         `G` |-> `G`, `tn` |-> `tn`, `b` |-> `b`, `h` |-> `h`, `z` |-> `z`,
         `p` |-> `w2n (z+n2w ao)`, `lo` |-> `lo`, `PG` |-> `PG`]) >>
      (impl_tac >- simp[ADD_COMM]) >> strip_tac >>
      qexistsl_tac [`j`, `G'`, `tn'`] >> simp[] >>
      qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _;
        vs_halted := _; vs_returndata := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  `emit_op ADD [pos;Lit (n2w ao)] sa = (child,mid)` by
    (Cases_on `emit_op ADD [pos;Lit (n2w ao)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >> fs[window_pure_seq_def, window_seq_def]
QED
