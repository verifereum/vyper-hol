(* Conditional complex-member execution and endpoint-owned allocation frames. *)
Theory abiDecodeMemMembers
Ancestors
  abiDecodeMemMemberPointer abiDecoderFrame abiDecoderEffect abiDecoderMemberSetup abiDecoderMemberCode
  abiEncoder fragGasPathMem fragGasMode fragExec allocaHistory
  abiDecodeMemBytesGuards venomExecSemantics venomState
  finite_map pred_set list rich_list arithmetic words compileEnv emitHelper
  emitHelperProps exprLoweringProps loweringStateRelDefs

Theorem abi_decode_mem_owned_footprint_exists[local]:
  !lo hi (m:num |-> (num # num)).
    ?fp. !p n. MEM (p,n) fp <=>
      ?id. lo <= id /\ id < hi /\ FLOOKUP m id = SOME (p,n)
Proof
  rpt gen_tac >>
  qexists_tac `MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
    (fmap_to_alist m))` >>
  simp[MEM_MAP, MEM_FILTER, alistTheory.MEM_fmap_to_alist_FLOOKUP] >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >> qexists_tac `FST y` >> simp[]) >>
  strip_tac >> qexists_tac `(id,(p,n))` >> simp[]
QED

Theorem abi_decode_mem_owned_frame_widen[local]:
  abi_decode_footprint_frame ((d,n)::fp) s t /\
  (!p k. MEM (p,k) fp ==>
    ?id. child_lo <= id /\ id < child_hi /\
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
  (!id. child_lo <= id /\ id < child_hi ==>
    FLOOKUP u.vs_allocas id = FLOOKUP t.vs_allocas id) /\
  (!p k. MEM (p,k) final_fp <=>
    ?id. lo <= id /\ id < hi /\ FLOOKUP u.vs_allocas id = SOME (p,k)) /\
  lo <= child_lo /\ child_hi <= hi /\
  out <= d /\ d+n <= out+sz ==>
  abi_decode_footprint_frame ((out,sz)::final_fp) s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `(d,n)::fp` >> simp[] >>
  rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`out`,`sz`] >> simp[]) >>
  qexistsl_tac [`d'`,`sz'`] >> simp[] >>
  first_x_assum drule >> strip_tac >>
  disj2_tac >> qexists_tac `id` >> simp[] >> decide_tac
QED

Theorem abi_decode_mem_owned_frames_compose:
  abi_decode_footprint_frame ((d1,n1)::fp1) s t /\
  abi_decode_footprint_frame ((d2,n2)::fp2) t u /\
  (!p n. MEM (p,n) fp1 <=> ?id. lo <= id /\ id < mid /\
    FLOOKUP t.vs_allocas id = SOME (p,n)) /\
  (!p n. MEM (p,n) fp2 <=> ?id. mid <= id /\ id < hi /\
    FLOOKUP u.vs_allocas id = SOME (p,n)) /\
  (!id. lo <= id /\ id < mid ==>
    FLOOKUP u.vs_allocas id = FLOOKUP t.vs_allocas id) /\
  lo <= mid /\ mid <= hi /\
  out <= d1 /\ d1+n1 <= out+sz /\ out <= d2 /\ d2+n2 <= out+sz ==>
  ?fp. (!p n. MEM (p,n) fp <=> ?id. lo <= id /\ id < hi /\
      FLOOKUP u.vs_allocas id = SOME (p,n)) /\
    abi_decode_footprint_frame ((out,sz)::fp) s u
Proof
  strip_tac >>
  qspecl_then [`lo`,`hi`,`u.vs_allocas`] strip_assume_tac
    abi_decode_mem_owned_footprint_exists >>
  qexists_tac `fp` >> simp[] >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule abi_decode_mem_owned_frame_widen >>
      goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`mid`,`lo`] >> simp[]) >>
  irule abi_decode_mem_owned_frame_widen >>
  goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
      goal_assum (drule_at Any) >>
  qexistsl_tac [`hi`,`mid`] >> simp[]
QED

Theorem abi_decode_member_setup_path_mem:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\
  fresh_vars_wrt st s /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+ao < dimword (:256) /\ B+sb+ao+32 <= s.vs_alloca_next) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((dyn ==> sb + w2n (mload (B+sb+ao) s) < dimword (:256)) ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME
        (n2w (sb + if dyn then w2n (mload (B+sb+ao) s) else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (dyn /\ dimword (:256) <= sb + w2n (mload (B+sb+ao) s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao MLOAD base_op hi st = (child_src,mid)` >>
  rename1 `emit_op ADD [dst;Lit (n2w vo)] mid = (child_dst,st')` >>
  drule abi_decode_mem_member_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `fn_has_code st mid func /\ fn_has_code mid st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def, same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all (SRULE [AC ADD_ASSOC ADD_COMM] abi_decode_mload_member_path_mem) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "accept" >>
  strip_tac >> first_x_assum irule >> simp[]
QED
Resume abi_decode_member_setup_path_mem[accept]:
  strip_tac >> gvs[] >>
  `eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit (n2w vo)) t = SOME (n2w vo)` by simp[eval_operand_def] >>
  `alloca_inv t` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> metis_tac[]) >>
  `t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by simp[] >>
  drule_all abi_decode_add_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0 (OK t')` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexists_tac `t'` >> gvs[word_add_n2w] >> metis_tac[]
QED
Finalise abi_decode_member_setup_path_mem
