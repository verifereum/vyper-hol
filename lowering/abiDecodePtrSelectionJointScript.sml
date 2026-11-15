(* The member's offset read and underflow check share one actual endpoint. *)
Theory abiDecodePtrSelectionJoint
Ancestors
  abiDecodeSelectionMem abiDecodePtrHead abiDecodePtrSelectionFrame
  abiDecodePtrSelectionAbort
  abiDecodePtrScalarFrame abiDecodePtrMemberFrame bodyPtrBopScalarSeq
  bodyPtrBopScalarCompile abiDecodePtrPosition abiEncoder
  entryDecoderHistoryFrame fragGasCopyLoop fragGasOriginPtrDead
  fragGasOriginPtr fragExecMem fragExec freshWrites stateFrame
  emitHelperProps exprLoweringProps bodyPtrDefs ptrDiscipline compileEnv
  venomState venomExecSemantics venomInst words list rich_list arithmetic

Theorem abi_decode_getelemptr_joint_code[local]:
  compile_getelemptr_abi pos dyn off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `dyn`
  >- (drule abi_decode_selection_shape >> strip_tac >>
      `sb.cs_current_bb = sa.cs_current_bb /\
       isPREFIX sa.cs_current_insts sb.cs_current_insts` by
        fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
      drule_all entry_straight_line_code_slice >> strip_tac >>
      qexists_tac `bb` >> simp[IS_PREFIX_APPEND] >> conj_tac
      >- (rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
          `(fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD)` by
            (qpat_assum `EVERY (\i. (fresh_write_op _ \/ _) /\ _) _`
               (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
             disch_then (qspec_then `i` mp_tac) >> simp[]) >>
          fs[fresh_write_op_def] >> simp[is_terminator_def]) >>
      fs[inst_extends_def]) >>
  `emit_op ADD [pos; Lit (n2w off)] sa = (v,sb)` by
    (Cases_on `emit_op ADD [pos; Lit (n2w off)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_extends, same_blocks_def] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by simp[] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  qexists_tac `bb` >> simp[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_decode_getelemptr_abort_joint:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\ p+32 <= h /\
  w2n b+h < dimword(:256) /\ w2n b+h <= s.vs_alloca_next /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?j G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort a (u with vs_inst_idx := j),G',tn')) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
      vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule abi_decode_getelemptr_mem_ok >>
     goal_assum (drule_at (Pat `compile_getelemptr_abi _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`, `p`, `z`] >>
     fs[abi_decode_ptr_window_def] >> strip_tac >> fs[] >> decide_tac) >>
  drule_all (abi_decode_getelemptr_abort_ptr |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all abi_decode_getelemptr_joint_code >> strip_tac >>
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
          `lo`, `explicit`, `PG`, `G`, `tn`, `Gf`, `tnf`] irule) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _;
        vs_halted := _; vs_returndata := _|>) = s`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_allocas``) >> simp[]) >>
  qexistsl_tac [`abort_idx`, `Gf`, `tnf`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  conj_tac
  >- (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _;
        vs_halted := _; vs_returndata := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  fs[allocas_from_def] >> metis_tac[]
QED

Theorem abi_decode_getelemptr_success_joint:
  compile_getelemptr_abi pos dyn off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\
  (dyn ==> p+32 <= h /\ w2n b+h < dimword(:256) /\
    w2n b+h <= s.vs_alloca_next) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    state_frame u = state_frame s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule abi_decode_getelemptr_mem_ok >>
     goal_assum (drule_at (Pat `compile_getelemptr_abi _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`, `p`, `z`] >>
     fs[abi_decode_ptr_window_def] >> strip_tac >> fs[] >> decide_tac) >>
  `?G' tn'. inst_seq_ptr
       <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
       0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      op_prov G' v = NONE /\ op_taint tn' v = {} /\
      state_frame u = state_frame s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (Cases_on `dyn` >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
     >- (mp_tac (abi_decode_getelemptr_success_ptr |> Q.INST
           [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
             d_imm := K {}; d_ret := K {}|>`,
            `ctx` |-> `ctx`, `func` |-> `func`, `PG` |-> `PG`,
            `pos` |-> `pos`, `off` |-> `off`, `src` |-> `src`,
            `hi` |-> `hi`, `sa` |-> `sa`, `v` |-> `v`, `sb` |-> `sb`,
            `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`, `b` |-> `b`,
            `h` |-> `h`, `z` |-> `z`, `p` |-> `p`, `u` |-> `u`]) >>
         (impl_tac >- simp[ADD_COMM]) >> strip_tac >>
         qexistsl_tac [`G'`, `tn'`] >> asm_rewrite_tac[]) >>
     `emit_op ADD [pos; Lit (n2w off)] sa = (v,sb)` by
       (Cases_on `emit_op ADD [pos; Lit (n2w off)] sa` >>
        fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
     `bop_scalar_seq {x | not_fresh_at sa x} {pos; Lit (n2w off)}
        (emitted_insts sa sb) (v INSERT {pos; Lit (n2w off)})` by
       (irule bop_scalar_seq_emit_op >> simp[] >>
        qexistsl_tac [`ADD`, `[pos; Lit (n2w off)]`] >> simp[]) >>
     `!operand. operand IN {pos; Lit (n2w off)} ==>
        op_prov G operand = NONE /\ op_taint tn operand = {}` by
       (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
     mp_tac (abi_decode_scalar_success_frame |> Q.INST
       [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
          d_imm := K {}; d_ret := K {}|>`,
        `R` |-> `{x | not_fresh_at sa x}`, `A` |-> `{pos; Lit (n2w off)}`,
        `B` |-> `v INSERT {pos; Lit (n2w off)}`, `code` |-> `emitted_insts sa sb`,
        `fn` |-> `func`, `j` |-> `s.vs_inst_idx`]) >>
     (impl_tac >- simp[]) >> strip_tac >>
     rename1 `inst_seq_ptr _ 0 ctx func PG G tn _ s G' tn'` >>
     `state_frame u = state_frame s` by
       (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
        simp[state_frame_def]) >>
     qexistsl_tac [`G'`, `tn'`] >> fs[lookup_var_def]) >>
  drule_all abi_decode_getelemptr_joint_code >> strip_tac >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
      allocas_from lo u` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
