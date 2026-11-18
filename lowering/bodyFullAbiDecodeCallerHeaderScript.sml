(* Joint execution of the finite caller header, before output allocation. *)
Theory bodyFullAbiDecodeCallerHeader
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  abiBuiltinDecodeSetup
  exprSimAbiDecodeBuiltinHeader abiDecoderAbortReentry
  abiDecoderVarSequence exprSimAbiDecodeFreshProbe
  abiDecodePtrRead assignTuplePtrLocalBytesCopy
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome
  bodyFullAbiDecodePath instSeqPtrLo fragGasOriginPtrDead
  stateFrame words finite_map pred_set list rich_list
  bodyFullAbiDecodeCallerPrefixJoint bodyFullAbiDecodeCallerGuardJoint
  abiBuiltinDecodeHeader abiBuiltinLengthGuard compileEnv exprSimAccounts
  fragExec fragGasPath fragGasOriginPtrLoop

Theorem abi_decode_caller_header_joint:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz)) /\
  abi_builtin_decode_header data min_size max_size st = (inputs,header_st) ==>
  ?r Gh tnh.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,Gh,tnh)) /\
    (!obs. fn_has_code st header_st obs ==> gas_path ctx obs s 0 r) /\
    ((?u. r = Abort Revert_abort u) \/
     (?u input. r = OK u /\ ~u.vs_halted /\ u.vs_current_bb = header_st.cs_current_bb /\
       u.vs_inst_idx = LENGTH header_st.cs_current_insts /\
       SND inputs = Var input /\
       abi_decode_ptr_window Gh tnh u input (n2w (b+32)) (LENGTH input_bytes) /\
       eval_operand (FST inputs) u = SOME (n2w (LENGTH input_bytes)) /\
       min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
       op_prov Gh (FST inputs) = NONE /\
       op_taint tnh (FST inputs) = {} /\ op_taint tnh (SND inputs) = {} /\
       abi_decoder_operand_live header_st.cs_next_var (FST inputs) /\
       abi_decoder_operand_live header_st.cs_next_var (SND inputs) /\
       u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next /\
       state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
       tnh.t_mem = tn.t_mem /\ tnh.t_stor = tn.t_stor /\
       tnh.t_trans = tn.t_trans /\ tnh.t_imm = tn.t_imm /\ alloca_history fn u /\
       (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gh x = FLOOKUP G x /\ op_taint tnh (Var x) = op_taint tn (Var x)) /\
       (!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
         ghost_inv_at (DF H) lo delta ce cx es Gh tnh u /\
         ghost_kept_at lo ce es0 origin G0 tn0 s0 Gh tnh)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?len sa src sb. emit_op MLOAD [data] st = (len,sa) /\
    emit_op ADD [data; Lit 32w] sa = (src,sb) /\
    abi_builtin_length_guard len min_size max_size sb = ((),header_st) /\
    inputs = (len,src)` by
    (qpat_assum `abi_builtin_decode_header _ _ _ _ = _` mp_tac >>
     simp[NoAsms, abi_builtin_decode_header_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
     rename1 `emit_op MLOAD [Var data_var] st = (lv,s1)` >>
     rename1 `emit_op ADD [Var data_var; Lit 32w] s1 = (sv,s2)` >>
     qexistsl_tac [`lv`, `s1`, `sv`, `s2`] >> simp[]) >>
  drule_all (BETA_RULE abi_decode_caller_prefix_joint) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `u` (qx_choose_then `Gp` (qx_choose_then `tnp`
      (map_every assume_tac o CONJUNCTS))))) >>
  mp_tac (SPEC_ALL abi_decode_caller_guard_joint) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gh` (qx_choose_then `tnh`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`, `Gh`, `tnh`] >>
  conj_tac >-
   (qx_gen_tac `h` >> strip_tac >>
    irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gp`, `u`, `tnp`] >> simp[]) >>
  conj_tac >-
   (`cs_extends st sb` by metis_tac[emit_op_extends_next_var, cs_extends_trans] >>
    `cs_extends sb header_st` by
      (drule abi_builtin_length_guard_shape >> strip_tac >>
       irule cs_extends_same_block >> simp[]) >>
    qx_gen_tac `obs` >> strip_tac >>
    drule_all fn_has_code_split >> strip_tac >>
    `gas_path ctx obs s 0 (OK u) /\ gas_path ctx obs u 0 r` by simp[] >>
    drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `(?v. r = Abort Revert_abort v) \/ _` strip_assume_tac >-
    (disj1_tac >> rename1 `r = Abort Revert_abort v` >> qexists_tac `v` >> simp[]) >>
  disj2_tac >> rename1 `r = OK v` >> rename1 `src = Var input` >>
  qexistsl_tac [`v`, `input`] >>
  qpat_assum `inputs = (len,src)`
    (fn th => pure_rewrite_tac [th, pairTheory.FST, pairTheory.SND]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
