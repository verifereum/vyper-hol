(* Array element setup retains one joint endpoint across all horizons. *)
Theory abiDecodePtrElementSetupJoint
Ancestors
  abiDecoderDynamicLoopSetup abiDecoderReentryPointer abiDecodePtrArrayPositionJoint
  decoderArraySetupPtr decoderNavigationPtr abiDecoderStaticLoopSetup abiDecodePtrMemberFrame
  ghostPcTransportPtr abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderContract abiDecoderReentry
  loweringStateRelDefs abiEncoder compileEnv emitHelperProps exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  fragGasOriginPtr fragExec emitHelper exprSimAccounts stateFrame instIdxIndep bodyPtrBopScalarDynamic
  finite_map words arithmetic list rich_list venomInst

(* Static-element branch only; relative base/hi do not emit instructions here. *)
Theorem abi_decode_static_element_setup_success_joint:
  ~dec_info_needs_offset di /\
  abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
    (Var source) hi di abi_sz mem_sz st = (ops,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\ j < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s cap /\
  32+j*mem_sz+mem_sz <= cap /\ d+cap < dimword (:256) /\
  not_fresh_at st index /\ not_fresh_at st root /\ not_fresh_at st source /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?G' tn' child.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')) /\
    SND (SND ops) = Var child /\ ptr_covers G' tn' child t mem_sz /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    ptr_covers G' tn' index t 32 /\ ptr_covers G' tn' root t cap /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
     (Var source) hi di abi_sz mem_sz =
   abi_decode_array_element_setup (Var index) pos (Var root) CALLDATALOAD
     (Lit 0w) (Lit 0w) di abi_sz mem_sz` by
    simp[abi_decode_array_element_setup_def] >>
  `abi_decode_array_element_setup (Var index) pos (Var root) CALLDATALOAD
     (Lit 0w) (Lit 0w) di abi_sz mem_sz st = (ops,ready)` by metis_tac[] >>
  `d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256)` by decide_tac >>
  mp_tac (calldata_array_element_setup_endpoint_ptr_origin_core |> Q.SPECL
    [`index`, `pos`, `root`, `di`, `abi_sz`, `mem_sz`, `st`, `ops`, `ready`,
     `s`, `slot`, `j`, `p`, `G`, `tn`, `d`, `cap`, `t`, `ARB`, `ctx`, `PG`, `ARB`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),HG,u)` by
    (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  `abi_decode_ptr_window HG u t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `ptr_covers HG u index t 32 /\ ptr_covers HG u root t cap` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`HG`, `u`, `child`] >>
  fs[ptr_covers_inst_idx]
QED


Theorem element_setup_phases[local]:
  abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
    (Var source) hi di abi_sz mem_sz st = (ops,ready) ==>
  ?idx c0 data c1 off c2 head c3 child_src c4 child_dst.
    emit_op MLOAD [Var index] st = (idx,c0) /\
    emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
    emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
    emit_op ADD [data;off] c2 = (head,c3) /\
    (if dec_info_needs_offset di then
      compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz c3 = (child_src,c4)
     else child_src = head /\ c4 = c3) /\
    abi_decode_indexed_address (Var root) idx mem_sz c4 = (child_dst,ready) /\
    ops = (idx,child_src,child_dst)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_element_setup_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `dec_info_needs_offset di` >> gvs[comp_return_def] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem element_setup_head_layout[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) ==>
  inst_extends st c0 /\ inst_extends c0 c3 /\ inst_extends st c3 /\
  same_blocks st c0 /\ same_blocks c0 c3 /\ same_blocks st c3 /\
  c0.cs_next_var = st.cs_next_var+1 /\ c3.cs_next_var = st.cs_next_var+4 /\
  LENGTH (emitted_insts st c0) = 1 /\ LENGTH (emitted_insts c0 c3) = 3 /\
  LENGTH (emitted_insts st c3) = 4 /\
  emitted_insts st c3 = emitted_insts st c0 ++ emitted_insts c0 c3 /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st c3)
Proof
  strip_tac >>
  `inst_extends st c0 /\ same_blocks st c0 /\
   LENGTH (emitted_insts st c0) = 1` by
    metis_tac[inst_extends_emit_op,emit_op_same_blocks,emit_op_length] >>
  drule_all scaled_address_prefix_structure >> strip_tac >>
  `inst_extends st c3 /\ same_blocks st c3` by
    metis_tac[inst_extends_trans,same_blocks_trans] >>
  `emitted_insts st c3 = emitted_insts st c0 ++ emitted_insts c0 c3` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def] >> decide_tac
QED

Theorem element_setup_index_runtime[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  run_inst_seq (emitted_insts st c0) s = OK t ==>
  ?w. lookup_var index s = SOME w /\
    eval_operand idx t = SOME (mload (w2n w) s) /\
    t = s with vs_vars := t.vs_vars
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts st c0) s = OK t` mp_tac >>
  simp[run_inst_seq_def,step_inst_base_def,mk_inst_def,exec_read1_def,eval_operand_def] >>
  Cases_on `lookup_var index s` >> simp[] >> strip_tac >> gvs[] >>
  simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]
QED

Theorem element_setup_head_runtime[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) /\
  run_inst_seq (emitted_insts st c3) s = OK t ==>
  t = s with vs_vars := t.vs_vars
Proof
  strip_tac >> drule_all element_setup_head_layout >> strip_tac >>
  `?r0. run_inst_seq (emitted_insts st c0) s = OK r0 /\
    run_inst_seq (emitted_insts c0 c3) r0 = OK t` by
    (irule run_inst_seq_append_ok >> fs[]) >>
  `r0 = s with vs_vars := r0.vs_vars` by metis_tac[element_setup_index_runtime] >>
  `emitted_insts c0 c3 = emitted_insts c0 c1 ++
    emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (imp_res_tac inst_extends_emit_op >>
     fs[inst_extends_def] >> metis_tac[emitted_insts_append,APPEND_ASSOC]) >>
  `EVERY (\i. MEM i.inst_opcode [ADD;MUL]) (emitted_insts c0 c3)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def]) >>
  mp_tac (run_inst_seq_protected_frame |> Q.SPECL
    [`emitted_insts c0 c3`,`K F`,`r0`,`t`]) >>
  (impl_tac >- (simp[] >>
     map_every qx_gen_tac [`ins`,`before`,`after`] >> strip_tac >>
     `MEM ins.inst_opcode [ADD;MUL]` by (fs[EVERY_MEM] >> metis_tac[]) >>
     gvs[] >> mp_tac (step_pure_opcode_frame |> Q.SPECL [`ins`,`before`,`after`]) >>
     simp[])) >>
  strip_tac >>
  qpat_assum `r0 = s with vs_vars := _` mp_tac >>
  qpat_assum `t = r0 with vs_vars := _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[venom_state_component_equality]
QED

Theorem element_setup_head_joint[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) /\
  fn_has_code st c3 func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var index s = SOME (n2w slot) /\ ptr_covers G tn index s 32 /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\ eval_operand pos s = SOME (n2w p) /\
  not_fresh_at st index /\ (!x. pos = Var x ==> not_fresh_at st x) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\ allocas_from lo s /\
  run_inst_seq (emitted_insts st c3) s = OK t ==>
  ?HG tm.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH c3.cs_current_insts),HG,tm)) /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (p+32)) /\
    eval_operand head t = SOME (n2w (p+32+j*abi_sz)) /\
    EVERY (\op. op_prov HG op = NONE /\ op_taint tm op = {} /\
      (!x. op = Var x ==> not_fresh_at c3 x)) [idx;data;head] /\
    t = s with vs_vars := t.vs_vars /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all element_setup_head_layout >> strip_tac >>
  `t = s with vs_vars := t.vs_vars` by metis_tac[element_setup_head_runtime] >>
  `?r0. run_inst_seq (emitted_insts st c0) s = OK r0 /\
    run_inst_seq (emitted_insts c0 c3) r0 = OK t` by
    (irule run_inst_seq_append_ok >> fs[]) >>
  `r0 = s with vs_vars := r0.vs_vars /\
   eval_operand idx r0 = SOME (mload (w2n (n2w slot:bytes32)) s)` by
    (drule_all element_setup_index_runtime >> strip_tac >> gvs[]) >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac (emit_mload_clean_endpoint_ptr_origin_core |> Q.SPECL
    [`st`,`idx`,`c0`,`index`,`s`,`r0`,`n2w slot`,`G`,`tn`,`ARB`,`ctx`,`PG`,`ARB`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G0` (qx_choose_then `tn0` strip_assume_tac)) >>
  `eval_operand idx r0 = SOME (n2w j)` by fs[] >>
  `(!x. idx = Var x ==> not_fresh_at c0 x) /\
   (!x. pos = Var x ==> not_fresh_at c0 x)` by
    (imp_res_tac emitted_insts_emit_op >>
     simp[not_fresh_at_def] >> rpt strip_tac >> fs[not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `r0.vs_labels = s.vs_labels` by
    (qpat_assum `r0 = s with vs_vars := _`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_labels``) >> simp[]) >>
  qpat_assum `r0 = s with vs_vars := _`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  `eval_operand pos r0 = SOME (n2w p) /\
   op_prov G0 pos = NONE /\ op_taint tn0 pos = {}` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `cs_extends st c0 /\ cs_extends c0 c3` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def] >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >>
     metis_tac[inst_extends_def]) >>
  `fn_has_code st c0 func /\ fn_has_code c0 c3 func` by
    metis_tac[fn_has_code_split] >>
  qabbrev_tac `s0 = r0 with vs_inst_idx := LENGTH c0.cs_current_insts` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c0 c3)` by
    (qpat_assum `EVERY _ (emitted_insts st c3)` mp_tac >>
     qpat_assum `emitted_insts st c3 = _` (fn th => rewrite_tac[th,EVERY_APPEND]) >>
     simp[]) >>
  `run_inst_seq (emitted_insts c0 c3) s0 =
    OK (t with vs_inst_idx := LENGTH c0.cs_current_insts)` by
    (qspec_then `emitted_insts c0 c3` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`r0`,`LENGTH c0.cs_current_insts`] mp_tac) >>
     (impl_tac >- fs[EVERY_APPEND]) >> simp[Abbr `s0`,exec_result_map_def]) >>
  mp_tac (clean_scaled_source_prefix_endpoint_ptr_origin_core |> Q.SPECL
    [`pos`,`c0`,`data`,`c1`,`idx`,`abi_sz`,`off`,`c2`,`head`,`c3`,
     `s0`,`n2w p`,`n2w j`,`tn0`,`G0`,`t with vs_inst_idx := LENGTH c0.cs_current_insts`,
     `ARB`,`ctx`,`PG`,`ARB`]) >>
  (impl_tac >- simp[Abbr `s0`]) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)) >>
  `eval_operand idx t = SOME (n2w j) /\
   op_prov G3 idx = NONE /\ op_taint tn3 idx = {}` by
    (qpat_assum `!x. not_fresh_at c0 x ==> _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (qspec_then `idx` mp_tac) >> simp[Abbr `s0`]) >>
  `!x. not_fresh_at st x ==> not_fresh_at c0 x /\ not_fresh_at c3 x` by
    (simp[not_fresh_at_def] >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH c3.cs_current_insts),G3,tn3)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK s0,G0,tn0)` by
       (simp[Abbr `s0`] >> first_assum irule >> simp[]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) [] (OK (t with vs_inst_idx := LENGTH c3.cs_current_insts),G3,tn3)` by
       (qpat_assum `!D lower explicit ctx' func. fn_has_code c0 c3 func /\ _ ==> _`
          (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
        fs[Abbr `s0`,allocas_from_def,same_blocks_def] >> metis_tac[]) >>
     metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  qexistsl_tac [`G3`,`tn3`] >>
  fs[Abbr `s0`,word_add_n2w,word_mul_n2w] >>
  conj_tac
  >- (imp_res_tac emitted_insts_emit_op >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  fs[lookup_var_def] >> metis_tac[]
QED

Theorem element_setup_dynamic_layout[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) /\
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz c3 = (child_src,c4) /\
  abi_decode_indexed_address (Var root) idx mem_sz c4 = (child_dst,ready) /\
  fn_has_code st ready func ==>
  inst_extends st c3 /\ inst_extends c3 c4 /\ inst_extends c4 ready /\
  same_blocks st c3 /\ same_blocks c3 c4 /\ same_blocks c4 ready /\
  st.cs_next_var <= c3.cs_next_var /\ c3.cs_next_var <= c4.cs_next_var /\
  c4.cs_next_var <= ready.cs_next_var /\
  fn_has_code st c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 ready func /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st c3) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c4 ready) /\
  emitted_insts st ready =
    (emitted_insts st c3 ++ emitted_insts c3 c4) ++ emitted_insts c4 ready
Proof
  strip_tac >> drule_all element_setup_head_layout >> strip_tac >>
  drule abi_decode_array_position_shape >> strip_tac >>
  drule indexed_destination_structure >> strip_tac >>
  drule abi_decoder_array_pointer_counters >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4)` by
    (mp_tac (abi_decoder_array_pointer_code |> Q.INST
       [`opc` |-> `MLOAD`, `base_op` |-> `Var source`, `elem_src` |-> `head`,
        `src_data` |-> `data`, `st` |-> `c3`, `st'` |-> `c4`, `child_op` |-> `child_src`]) >>
     simp[abi_decode_source_opcode_def,EVERY_MEM]) >>
  `cs_extends st c3 /\ cs_extends c3 c4 /\ cs_extends c4 ready` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def] >> simp_tac bool_ss [IS_PREFIX_APPEND] >>
     metis_tac[inst_extends_def]) >>
  `fn_has_code st c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 ready func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `emitted_insts st ready =
    (emitted_insts st c3 ++ emitted_insts c3 c4) ++ emitted_insts c4 ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append,APPEND_ASSOC]) >>
  simp[] >> Cases_on `hi = Lit 0w` >> simp[] >> decide_tac
QED

Theorem abi_decode_element_setup_success_joint:
  abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
    (Var source) hi di abi_sz mem_sz st = (ops,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\ j < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s cap /\
  32+j*mem_sz+mem_sz <= cap /\ d+cap < dimword (:256) /\
  not_fresh_at st index /\ not_fresh_at st root /\ not_fresh_at st source /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  (dec_info_needs_offset di ==>
    p+32+j*abi_sz+32 <= L /\
    B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
    op_prov G hi = NONE /\ op_taint tn hi = {} /\
    (!x. hi = Var x ==> not_fresh_at st x)) /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?G' tn' child.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')) /\
    SND (SND ops) = Var child /\ ptr_covers G' tn' child t mem_sz /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    ptr_covers G' tn' index t 32 /\ ptr_covers G' tn' root t cap /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >| [ALL_TAC,
      mp_tac abi_decode_static_element_setup_success_joint >> simp[]] >>
  drule element_setup_phases >> strip_tac >> gvs[] >>
  drule_all element_setup_dynamic_layout >> strip_tac >>
  `?r3 r4. run_inst_seq (emitted_insts st c3) s = OK r3 /\
    run_inst_seq (emitted_insts c3 c4) r3 = OK r4 /\
    run_inst_seq (emitted_insts c4 ready) r4 = OK t` by
    (qpat_assum `emitted_insts st ready = _` (fn eq =>
       qpat_assum `run_inst_seq (emitted_insts st ready) s = OK t`
         (strip_assume_tac o MATCH_MP run_inst_seq_append_ok o
          REWRITE_RULE [eq,APPEND_ASSOC])) >>
     qpat_assum `run_inst_seq (emitted_insts st c3 ++ emitted_insts c3 c4) s = OK _`
       (strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >> metis_tac[]) >>
  mp_tac (element_setup_head_joint |> Q.INST [`t` |-> `r3`]) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)) >>
  `abi_decode_ptr_window G3 tn3 r3 source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `r3.vs_labels = s.vs_labels /\ r3.vs_alloca_next = s.vs_alloca_next /\
   r3.vs_halted = s.vs_halted /\ r3.vs_current_bb = s.vs_current_bb /\
   r3.vs_allocas = s.vs_allocas /\ r3.vs_memory = s.vs_memory` by
    (qpat_assum `r3 = s with vs_vars := _`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >> simp[]) >>
  `op_prov G3 hi = NONE /\ op_taint tn3 hi = {}` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at c3 x /\ not_fresh_at c4 x` by
    (simp[not_fresh_at_def] >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qabbrev_tac `s3 = r3 with vs_inst_idx := LENGTH c3.cs_current_insts` >>
  `run_inst_seq (emitted_insts c3 c4) s3 =
     OK (r4 with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    simp[Abbr `s3`,run_inst_seq_inst_idx,exec_result_map_def] >>
  `abi_decode_ptr_window G3 tn3 s3 source (n2w B) L` by
    fs[Abbr `s3`,abi_decode_ptr_window_def,ptr_covers_inst_idx,lookup_var_def] >>
  mp_tac (abi_decode_array_position_success_joint |> Q.INST
    [`sa` |-> `c3`,`sb` |-> `c4`,`head` |-> `head`,`data` |-> `data`,
     `v` |-> `child_src`,`s` |-> `s3`,
     `u` |-> `r4 with vs_inst_idx := LENGTH c3.cs_current_insts`,
     `G` |-> `G3`,`tn` |-> `tn3`,`b` |-> `n2w B`,`p` |-> `p+32+j*abi_sz`]) >>
  (impl_tac >- (simp[Abbr `s3`,abi_decode_ptr_window_def,ptr_covers_inst_idx,lookup_var_def] >>
     fs[same_blocks_def,allocas_from_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `G4` (qx_choose_then `tn4` strip_assume_tac)) >>
  fs[venom_state_fupdfupds,combinTheory.K_o_THM] >>
  `r4.vs_labels = r3.vs_labels /\ r4.vs_allocas = r3.vs_allocas /\
   r4.vs_halted = r3.vs_halted /\ r4.vs_current_bb = r3.vs_current_bb /\
   r4.vs_memory = r3.vs_memory` by
    fs[Abbr `s3`] >>
  `eval_operand idx r4 = SOME (n2w j) /\
   op_prov G4 idx = NONE /\ op_taint tn4 idx = {}` by
    (qpat_assum `!x. not_fresh_at c3 x ==> _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (qspec_then `idx` mp_tac) >> fs[EVERY_MEM,Abbr `s3`]) >>
  `lookup_var root r4 = SOME (n2w d) /\ ptr_covers G4 tn4 root r4 cap` by
    (gvs[ptr_covers_def,Abbr `s3`,lookup_var_def] >> metis_tac[]) >>
  `(!x. idx = Var x ==> not_fresh_at c4 x) /\
   (!x. child_src = Var x ==> not_fresh_at c4 x)` by
    (conj_tac
     >- (fs[EVERY_MEM,not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     drule abi_decoder_array_pointer_counters >>
     Cases_on `child_src` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  qabbrev_tac `s4 = r4 with vs_inst_idx := LENGTH c4.cs_current_insts` >>
  `run_inst_seq (emitted_insts c4 ready) s4 =
     OK (t with vs_inst_idx := LENGTH c4.cs_current_insts)` by
    simp[Abbr `s4`,run_inst_seq_inst_idx,exec_result_map_def] >>
  `d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256)` by decide_tac >>
  mp_tac (indexed_destination_endpoint_ptr_origin_core |> Q.SPECL
    [`c4`,`child_dst`,`ready`,`root`,`idx`,`mem_sz`,`s4`,
     `t with vs_inst_idx := LENGTH c4.cs_current_insts`,`d`,`j`,`cap`,`G4`,`tn4`,
     `ARB`,`ctx`,`PG`,`ARB`]) >>
  (impl_tac >- (simp[Abbr `s4`,ptr_covers_inst_idx,lookup_var_def] >>
     fs[EVERY_MEM,lookup_var_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `child` strip_assume_tac))) >>
  fs[venom_state_fupdfupds,combinTheory.K_o_THM] >>
  suspend "finish"
QED
Resume abi_decode_element_setup_success_joint[finish]:
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at c3 x /\ not_fresh_at c4 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at c4 x ==> _` (qspec_then `x` mp_tac) >>
     fs[Abbr `s3`,Abbr `s4`,lookup_var_def] >> metis_tac[]) >>
  `abi_decode_ptr_window Gf tnf t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `ptr_covers Gf tnf index t 32 /\ ptr_covers Gf tnf root t cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `op_prov Gf idx = NONE /\ op_taint tnf idx = {} /\
   op_prov Gf child_src = NONE /\ op_taint tnf child_src = {}` by
    (Cases_on `idx` >> Cases_on `child_src` >>
     fs[op_prov_def,op_taint_def,Abbr `s3`,Abbr `s4`] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),Gf,tnf)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK s3,G3,tn3)` by simp[Abbr `s3`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s3,G3,tn3) [] (OK s4,G4,tn4)` by simp[Abbr `s4`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s4,G4,tn4) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),Gf,tnf)` by
       (qpat_assum `!D lower explicit ctx' func. fn_has_code c4 ready func /\ _ ==> _`
          (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
        fs[Abbr `s3`,Abbr `s4`,allocas_from_def,same_blocks_def] >> metis_tac[]) >>
     metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  qexistsl_tac [`Gf`,`tnf`] >>
  fs[Abbr `s3`,Abbr `s4`,ptr_covers_inst_idx] >> metis_tac[]
QED
Finalise abi_decode_element_setup_success_joint

Theorem element_setup_head_no_abort[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) ==>
  run_inst_seq (emitted_insts st c3) s <> Abort a t
Proof
  strip_tac >> drule_all element_setup_head_layout >> strip_tac >>
  `emitted_insts c0 c3 = emitted_insts c0 c1 ++
    emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (imp_res_tac inst_extends_emit_op >> fs[inst_extends_def] >>
     metis_tac[emitted_insts_append,APPEND_ASSOC]) >>
  imp_res_tac emitted_insts_emit_op >>
  `!id ops tmp u err v.
    step_inst_base (mk_inst id MLOAD ops [tmp]) u <> Abort err v` by
    (rpt gen_tac >>
     simp[step_inst_base_def,mk_inst_def,exec_read1_def,AllCaseEqs()]) >>
  gvs[] >> simp_tac bool_ss [run_inst_seq_def] >>
  rpt (CASE_TAC >> fs[]) >>
  metis_tac [SIMP_RULE (srw_ss()) [] bop_scalar_no_abort]
QED

Theorem element_setup_destination_no_abort[local]:
  abi_decode_indexed_address (Var root) idx mem_sz st = (out,ready) ==>
  run_inst_seq (emitted_insts st ready) s <> Abort a t
Proof
  simp[abi_decode_indexed_address_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op ADD [Var root;Lit 32w] st = (data,c1)` >>
  rename1 `emit_op MUL [idx;Lit (n2w mem_sz)] c1 = (off,c2)` >>
  rename1 `emit_op ADD [data;off] c2 = (out,ready)` >>
  imp_res_tac inst_extends_emit_op >>
  `emitted_insts st ready = emitted_insts st c1 ++
    emitted_insts c1 c2 ++ emitted_insts c2 ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append,APPEND_ASSOC]) >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[] >> simp_tac bool_ss [run_inst_seq_def] >>
  rpt (CASE_TAC >> fs[]) >>
  metis_tac [SIMP_RULE (srw_ss()) [] bop_scalar_no_abort]
QED


Theorem element_setup_abort_phases[local]:
  emit_op MLOAD [Var index] st = (idx,c0) /\
  emit_op ADD [pos;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w abi_sz)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) /\
  abi_decode_indexed_address (Var root) idx mem_sz c4 = (child_dst,ready) /\
  emitted_insts st ready =
    (emitted_insts st c3 ++ emitted_insts c3 c4) ++ emitted_insts c4 ready /\
  run_inst_seq (emitted_insts st ready) s = Abort a t ==>
  ?r3. run_inst_seq (emitted_insts st c3) s = OK r3 /\
    run_inst_seq (emitted_insts c3 c4) r3 = Abort a t
Proof
  strip_tac >>
  `!err u. run_inst_seq (emitted_insts st c3) s <> Abort err u` by
    metis_tac[element_setup_head_no_abort] >>
  `!r err u. run_inst_seq (emitted_insts c4 ready) r <> Abort err u` by
    metis_tac[element_setup_destination_no_abort] >>
  `run_inst_seq (emitted_insts st c3 ++
     (emitted_insts c3 c4 ++ emitted_insts c4 ready)) s = Abort a t` by
    metis_tac[APPEND_ASSOC] >>
  `?r3. run_inst_seq (emitted_insts st c3) s = OK r3` by
    (spose_not_then assume_tac >>
     `run_inst_seq (emitted_insts st c3 ++
        (emitted_insts c3 c4 ++ emitted_insts c4 ready)) s =
      run_inst_seq (emitted_insts st c3) s` by
       (irule run_inst_seq_append_err >> metis_tac[]) >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c3 c4 ++ emitted_insts c4 ready) r3 = Abort a t` by
    metis_tac[run_inst_seq_append] >>
  qexists_tac `r3` >> simp[] >>
  Cases_on `run_inst_seq (emitted_insts c3 c4) r3` >>
  gvs[run_inst_seq_append_err] >> metis_tac[run_inst_seq_append]
QED

Theorem abi_decode_dynamic_element_setup_abort_joint:
  dec_info_needs_offset di /\
  abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
    (Var source) hi di abi_sz mem_sz st = (ops,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\ j < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s cap /\
  32+j*mem_sz+mem_sz <= cap /\ d+cap < dimword (:256) /\
  not_fresh_at st index /\ not_fresh_at st root /\ not_fresh_at st source /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  (dec_info_needs_offset di ==>
    p+32+j*abi_sz+32 <= L /\
    B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
    op_prov G hi = NONE /\ op_taint tn hi = {} /\
    (!x. hi = Var x ==> not_fresh_at st x)) /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts st ready) s = Abort a t ==>
  ?abort_idx G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort a (t with vs_inst_idx := abort_idx),G',tn')) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
      vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo t
Proof
  strip_tac >> drule element_setup_phases >> strip_tac >> gvs[] >>
  drule_all element_setup_dynamic_layout >> strip_tac >>
  drule_all element_setup_abort_phases >> strip_tac >>
  mp_tac (element_setup_head_joint |> Q.INST [`t` |-> `r3`]) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)) >>
  `abi_decode_ptr_window G3 tn3 r3 source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `r3.vs_labels = s.vs_labels /\ r3.vs_alloca_next = s.vs_alloca_next /\
   r3.vs_halted = s.vs_halted /\ r3.vs_current_bb = s.vs_current_bb /\
   r3.vs_allocas = s.vs_allocas /\ r3.vs_memory = s.vs_memory` by
    (qpat_assum `r3 = s with vs_vars := _`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >> simp[]) >>
  `op_prov G3 hi = NONE /\ op_taint tn3 hi = {}` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at c3 x /\ not_fresh_at c4 x` by
    (simp[not_fresh_at_def] >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qabbrev_tac `s3 = r3 with vs_inst_idx := LENGTH c3.cs_current_insts` >>
  `run_inst_seq (emitted_insts c3 c4) s3 =
     Abort a (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    simp[Abbr `s3`,run_inst_seq_inst_idx,exec_result_map_def] >>
  `abi_decode_ptr_window G3 tn3 s3 source (n2w B) L` by
    fs[Abbr `s3`,abi_decode_ptr_window_def,ptr_covers_inst_idx,lookup_var_def] >>
  mp_tac (abi_decode_array_position_abort_joint |> Q.INST
    [`sa` |-> `c3`,`sb` |-> `c4`,`head` |-> `head`,`data` |-> `data`,
     `v` |-> `child_src`,`s` |-> `s3`,
     `u` |-> `t with vs_inst_idx := LENGTH c3.cs_current_insts`,
     `G` |-> `G3`,`tn` |-> `tn3`,`b` |-> `n2w B`,`p` |-> `p+32+j*abi_sz`]) >>
  (impl_tac >- (simp[Abbr `s3`,abi_decode_ptr_window_def,ptr_covers_inst_idx,lookup_var_def] >>
     fs[same_blocks_def,allocas_from_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `abort_idx` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  fs[venom_state_fupdfupds,combinTheory.K_o_THM] >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at c3 x ==> _` (qspec_then `x` mp_tac) >>
     fs[Abbr `s3`,lookup_var_def] >> metis_tac[]) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
     vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s` by
    (qpat_assum `r3 = s with vs_vars := _`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     fs[Abbr `s3`,venom_state_component_equality]) >>
  qexistsl_tac [`abort_idx`,`Gf`,`tnf`] >> conj_tac
  >- (rpt gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK s3,G3,tn3)` by simp[Abbr `s3`] >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s3,G3,tn3) [] (Abort a (t with vs_inst_idx := abort_idx),Gf,tnf)` by simp[] >>
      metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  fs[Abbr `s3`,allocas_from_def,venom_state_component_equality] >> metis_tac[]
QED
