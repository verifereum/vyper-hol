Theory externalReturnBytesJoint
Ancestors
  abiEncoderWindowBytesMem abiEncoderWindowBytes abiEncoderWindowSequence
  abiEncoderRounding abiEncoderMemory abiEncoderBytes abiBytestringCode exprLoweringProps
  memoryReadProps valueEncodingProps abiDecoderContract fragExec rich_list loweringStateRelDefs
  fragGasSeqPtr bodyPtrDefs ptrCoverage abiBytesEncoderJointGhost
  ptrSafetyTransport contractABI venomState venomInst words list arithmetic finite_map

(* Bytes encoder core, before any external RETURN or aggregate wrapper. *)
Theorem compile_abi_bytes_window_joint:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) st =
    (out,en) /\
  fn_has_code st en func /\ not_fresh_at st dst /\ not_fresh_at st src /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var src) s = SOME p /\
  eval_operand (Var dst) s = SOME q /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  read_memory (w2n p + 32) (LENGTH bs) s = bs /\
  w2n p + 32 + LENGTH bs <= s.vs_alloca_next /\
  w2n p + 32 + LENGTH bs < dimword (:256) /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= s.vs_alloca_next /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
  venomMemDefs$regions_disjoint (w2n p,32 + LENGTH bs)
    (w2n q,32 + contractABI$ceil32 (LENGTH bs)) /\
  ptr_covers G tn src s (32 + LENGTH bs) /\
  ptr_covers G tn dst s (32 + contractABI$ceil32 (LENGTH bs)) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==>
       i NOTIN tn.t_mem) ==>
  ?t G' tn'.
    read_memory (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) t =
      contractABI$enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
    eval_operand out t = SOME (n2w (32 + contractABI$ceil32 (LENGTH bs))) /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    ptr_covers G' tn' dst t (32 + contractABI$ceil32 (LENGTH bs)) /\
    (!i. w2n q <= i /\
         i < w2n q + 32 + contractABI$ceil32 (LENGTH bs) ==>
         i NOTIN tn'.t_mem) /\
    mem_agree_outside
      {i | w2n q <= i /\ i < w2n q + 32 + contractABI$ceil32 (LENGTH bs)}
      s.vs_memory t.vs_memory /\
    (!i. i < w2n q \/ w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= i ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at st x ==>
         lookup_var x t = lookup_var x s /\
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  rpt strip_tac >>
  `w2n p < dimword (:256) /\ LENGTH bs + 31 < dimword (:256) /\
   w2n q + contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32 + LENGTH bs < dimword (:256)` by decide_tac >>
  `!x. Var dst = Var x \/ Var src = Var x ==> not_fresh_at st x` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `eval_operand (Var src) s = SOME (n2w (w2n p)) /\
   eval_operand (Var dst) s = SOME (n2w (w2n q))` by simp[] >>
  drule_all window_bytes_sequence >> strip_tac >>
  rename1 `window_seq st en s raw` >>
  suspend "ghost_and_finish"
QED

Resume compile_abi_bytes_window_joint[ghost_and_finish]:
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs) /\
   contractABI$ceil32 (LENGTH bs) <= LENGTH bs + 32` by
    (qspec_then `LENGTH bs` mp_tac (GEN_ALL abi_encoder_ceil32_bounds) >>
     decide_tac) >>
  `w2n p + (32 + LENGTH bs) <= w2n q \/
   w2n q + (32 + contractABI$ceil32 (LENGTH bs)) <= w2n p` by
    gvs[venomMemDefsTheory.regions_disjoint_def] >>
  `read_memory (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) raw =
   contractABI$enc (contractABI$Bytes NONE) (contractABI$BytesV bs)` by
    (asm_simp_tac bool_ss [read_memory_eq_mem_bytes_at, abi_encoder_bytes_encoding] >>
     irule abi_encoder_bytes_zero_copy >>
     simp[GSYM read_memory_eq_mem_bytes_at, mem_word_at_eq_mload]) >>
  `mem_agree_outside
     {i | w2n q <= i /\ i < w2n q + 32 + contractABI$ceil32 (LENGTH bs)}
     s.vs_memory raw.vs_memory` by
    (`abi_decode_frame (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) s
        (mcopy (w2n q) (w2n p) (32 + LENGTH bs)
          (mstore (w2n q + contractABI$ceil32 (LENGTH bs)) 0w s))` by
       (irule abi_encoder_bytes_write_frame >> simp[]) >>
     `abi_decode_frame (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) s raw` by
       metis_tac[abi_encoder_frame_memory] >>
     fs[mem_agree_outside_def, abi_decode_frame_def] >>
     rpt strip_tac >> irule EQ_SYM >> first_x_assum irule >> decide_tac) >>
  drule compile_abi_bytestring_code >> strip_tac >>
  `!x. out = Var x ==> not_fresh_at en x` by
    (gvs[compiler_var_names_EL, not_fresh_at_def] >> simp[]) >>
  suspend "ghosts"
QED

Resume compile_abi_bytes_window_joint[ghosts]:
  markerLib.RESUME_TAC >>
  drule_all window_bytes_mem_checks >> strip_tac >>
  `run_inst_seq (emitted_insts st en) s = OK raw` by fs[window_seq_def] >>
  drule_all bytes_encoder_joint_ghosts >> disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`, `G'`, `tn'`] >>
  `(!x. not_fresh_at st x ==> lookup_var x raw = lookup_var x s) /\
   en.cs_current_bb = st.cs_current_bb` by fs[window_seq_def] >>
  `read_memory (w2n q) (32 + contractABI$ceil32 (LENGTH bs))
     (raw with vs_inst_idx := LENGTH en.cs_current_insts) =
   read_memory (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) raw` by
    simp_tac (srw_ss()) [read_memory_def] >>
  `ptr_covers G' tn' dst (raw with vs_inst_idx := LENGTH en.cs_current_insts)
    (32 + contractABI$ceil32 (LENGTH bs))` by
    fs[ptr_covers_def, lookup_var_def] >>
  `eval_operand out (raw with vs_inst_idx := LENGTH en.cs_current_insts) =
    eval_operand out raw` by (Cases_on `out` >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `!x. lookup_var x (raw with vs_inst_idx := LENGTH en.cs_current_insts) =
    lookup_var x raw` by simp[lookup_var_def] >>
  gvs[] >>
  suspend "path_join"
QED

Resume compile_abi_bytes_window_joint[path_join]:
  markerLib.RESUME_TAC >> gvs[window_seq_def] >>
  (conj_tac >- metis_tac[]) >> gen_tac >>
  `FILTER (\i. i.inst_opcode = GAS)
     (bytestring_encoder_insts st.cs_next_id
       (compiler_var_names st.cs_next_var 9) (Var dst) (Var src)) = []` by
    simp_tac (srw_ss()) [bytestring_encoder_insts_def, mk_inst_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> metis_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
    (qspec_then `D` assume_tac) >>
  fs[] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_origin_ptr_path >>
  disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  simp[] >> gvs[]
QED

Finalise compile_abi_bytes_window_joint
