(* The optional complex head guard checks the actual scalar run. *)
Theory abiDecodePtrComplexGuardJoint
Ancestors
  abiDecodePtrPrims abiDecodePtrScalarFrame abiDecodePtrScalarAbort
  abiDecoderComplexGuard abiDecoderComplexHead
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome entryDecoderHistoryFrame
  fragGasCopyLoop fragGasOriginPtrDead fragGasOriginPtr fragExecMem fragExec
  emitHelperProps exprLoweringProps bodyPtrDefs ptrDiscipline compileEnv
  venomState venomExecSemantics venomInst finite_map pred_set list rich_list arithmetic

Theorem abi_decode_complex_guard_joint_code:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?B bb.
    bop_scalar_seq {x | not_fresh_at sa x} ({pos;hi} UNION IMAGE Lit UNIV)
      (emitted_insts sa sb) B /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} ({pos;hi} UNION IMAGE Lit UNIV)
      (emitted_insts sa sb) B` by
    (irule abi_decode_complex_guard_scalar >> simp[] >>
     qexistsl_tac [`hi`, `n`, `pos`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >>
     fs[EVERY_MEM] >> metis_tac[cj 1 is_alloca_op_def]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[DROP_LENGTH_APPEND]) >>
  qexistsl_tac [`B`, `bb`] >> simp[IS_PREFIX_APPEND]
QED

Theorem abi_decode_complex_guard_abort_joint:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?j G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort a (u with vs_inst_idx := j),G',tn')) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >> drule_all abi_decode_complex_guard_joint_code >> strip_tac >>
  rename1 `bop_scalar_seq _ _ _ available` >>
  `!operand. operand IN {pos;hi} UNION IMAGE Lit UNIV ==>
      op_prov G operand = NONE /\ op_taint tn operand = {}` by
    (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bop_scalar_seq_mem_ok] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `inst_seq_ptr
    <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
    lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule (inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
     simp[] >> fs[EVERY_MEM]) >>
  `!explicit. gas_origin_ptr_path
    (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
     lo,explicit,ctx,func,PG) (s,G,tn) [] (Abort a (u with vs_inst_idx := j),G',tn')` by
    (gen_tac >> qpat_assum `!D lo explicit PG G tn HG th. _`
       (qspecl_then
         [`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
          `lo`, `explicit`, `PG`, `G`, `tn`, `G'`, `tn'`] irule) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_halted := _; vs_returndata := _|>) = s`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_allocas``) >> simp[]) >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`j`, `G'`, `tn'`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  fs[lookup_var_def, op_taint_def] >> metis_tac[]
QED

Theorem abi_decode_complex_guard_success_joint:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >> drule_all abi_decode_complex_guard_joint_code >> strip_tac >>
  rename1 `bop_scalar_seq _ _ _ available` >>
  `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
      op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  mp_tac (abi_decode_scalar_success_frame |> Q.INST
    [`R` |-> `{x | not_fresh_at sa x}`, `A` |-> `{pos;hi} UNION IMAGE Lit UNIV`,
     `B` |-> `available`, `code` |-> `emitted_insts sa sb`, `fn` |-> `func`,
     `j` |-> `LENGTH sb.cs_current_insts`,
     `D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `inst_seq_ptr _ 0 ctx func PG G tn _ s G' tn'` >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bop_scalar_seq_mem_ok] >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
      allocas_from lo u` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  fs[lookup_var_def] >> metis_tac[]
QED
