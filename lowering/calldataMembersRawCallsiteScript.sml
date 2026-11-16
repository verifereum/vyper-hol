(* Descriptor-directed navigation and physical framing for raw members. *)
Theory calldataMembersRawCallsite
Ancestors
  decoderMemberJointModular calldataSourceCorrespondence abiDecoderCoherence
  calldataChildFrame bodyPtrBytestringBuiltinsWindowGhost assignTuplePtrCopyLen
  exprSimProps abiDecoderMemberSetup abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderContract abiDecoderFrame actualAllocExec valueEncodingDefs
  abiDecoderLoop compileEnv exprLowering abiEncoder freshWrites ptrDiscipline
  fragGasOriginPtr ptrSafeRun bodyPtrDefs venomState venomExecSemantics
  venomInst loweringStateRelDefs words finite_map pred_set list arithmetic

Theorem calldata_member_raw_child_callsite:
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\ dyn = dec_info_needs_offset di /\
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\ eval_operand src s = SOME p /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  FLOOKUP s.vs_allocas oid = SOME (d,cap) /\
  vo + type_memory_size tv <= cap /\ d + vo < dimword (:256) /\
  mid.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    abi_decoder_header ce env ty tv /\
    r = s with <| vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx |> /\
    abi_decode_sim ctx fn s r /\ gas_path_mem ctx fn s 0 (OK r) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,H,u)) /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt limit r /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s else p + n2w ao) /\
    (dyn = tv_abi_dynamic tv ==> eval_operand (FST ops) r = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p)
        (w2n (n2w ao : bytes32))))) /\
    ptr_covers H u q r (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    r.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule_all calldata_member_setup_joint_modular >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p)
      (w2n (n2w ao : bytes32))) =
    (if tv_abi_dynamic tv then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
     else p + n2w ao)` by
    rewrite_tac[calldata_member_pointer, n2w_w2n] >>
  qexistsl_tac [`r`,`H`,`u`,`q`] >> simp[]
QED

(* The child may dirty its padded destination and fresh scratch allocations,
   but cannot damage completed members in the enclosing allocation. *)
Theorem calldata_member_raw_prefix_frame:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (!q len. MEM (q,len) scratch ==>
    ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  EVERY (\(tv,x,b). base_addr <= b /\
    b + type_memory_size tv <= base_addr + cap /\
    (b + type_memory_size tv <= d \/ d + sz <= b) /\ val_wf tv x /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv x b m)) prefix /\
  u.t_mem SUBSET tn.t_mem /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) /\
  (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
    FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\ not_fresh_at st root /\
  ptr_covers G tn root s cap /\
  abi_decoder_operand_live st.cs_next_var src /\
  (!name. src = Var name ==> not_fresh_at st name) /\
  op_taint tn src = {} /\ op_prov G src = NONE ==>
  FLOOKUP t.vs_allocas oid = SOME (base_addr,cap) /\
  ptr_covers H u root t cap /\
  eval_operand src t = eval_operand src s /\
  op_taint u src = {} /\ op_prov H src = NONE /\
  t.vs_call_ctx = s.vs_call_ctx /\
  EVERY (\(tv,x,b). !m. mem_agree_outside u.t_mem t.vs_memory m ==>
    val_in_memory tv x b m) prefix
Proof
  strip_tac >>
  `lookup_var root t = lookup_var root s /\
   FLOOKUP H root = FLOOKUP G root /\
   op_taint u (Var root) = op_taint tn (Var root)` by
    (gvs[op_taint_def] >> metis_tac[eval_operand_def]) >>
  `ptr_covers H u root t cap` by metis_tac[ptr_covers_lookup_frame] >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by fs[abi_decode_footprint_frame_def] >>
  simp[EVERY_MEM] >> qx_gen_tac `e` >> disch_tac >> PairCases_on `e` >>
  qpat_x_assum `EVERY _ prefix` mp_tac >> rewrite_tac[EVERY_MEM] >>
  disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  `mem_bytes_at e2 (type_memory_size e0) t.vs_memory =
   mem_bytes_at e2 (type_memory_size e0) s.vs_memory` by
    (irule (cj 2 calldata_child_preserves_allocated_region) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`base_addr`,`cap`,`d`,`last.cs_next_id`,`st.cs_next_id`,
       `oid`,`scratch`,`sz`] >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_window_transport >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tn.t_mem`,`u.t_mem`,`type_memory_size e0`,`s.vs_memory`,`t.vs_memory`] >>
  simp[val_footprint_le] >> fs[SUBSET_DEF] >> metis_tac[]
QED
