(* Observe offset heads without assuming a canonical or disjoint payload. *)
Theory abiMalformedNavigation
Ancestors
  abiMalformedLeafProbe abiMalformedPrefix abiDecoderNavigationTotal
  abiDecoderArrayBound abiDecoderArrayPtr
  abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderMemberBound
  abiBoundedBytesExecution abiDecoderRange abiDecoderGuard abiDecoderGuards
  abiCanonicalHeadSize abiValidMember abiEncoder emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomState valueEncodingProps
  vyperABI contractABI words list rich_list arithmetic arithmeticProps

Theorem abi_checked_offset_load:
  mem_bytes_at B len (abi_decode_source opc s) = bs /\
  pos + 32 <= len /\ B + len < dimword (:256) ==>
  abi_decode_load opc (n2w (B + pos):bytes32) s =
    n2w (abi_head_word (DROP pos bs)) /\
  abi_head_word (DROP pos bs) < dimword (:256)
Proof
  strip_tac >>
  `B + pos < dimword (:256)` by decide_tac >>
  `mem_bytes_at (B + pos) 32 (abi_decode_source opc s) =
     TAKE 32 (DROP pos bs)` by
    (irule (cj 1 abi_checked_source_word_window) >> metis_tac[]) >>
  simp[abi_decode_load_bytes, abi_head_word_bytes] >>
  simp[abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt]
QED

Theorem abi_checked_dynamic_member_total:
  compile_getelemptr_abi src T off opc base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  sb + H <= len /\ off + 32 <= H /\ B + len < dimword (:256) /\
  mem_bytes_at B len (abi_decode_source opc s) = bs /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (sb + abi_head_word (DROP (sb + off) bs) < dimword (:256) /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     eval_operand member_op t = SOME (n2w (sb + abi_head_word (DROP (sb + off) bs))) /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >>
  `sb + off + 32 <= len /\ sb < dimword (:256)` by decide_tac >>
  `abi_decode_load opc (n2w (B + (sb + off)):bytes32) s =
     n2w (abi_head_word (DROP (sb + off) bs)) /\
   abi_head_word (DROP (sb + off) bs) < dimword (:256)` by
    (irule abi_checked_offset_load >> metis_tac[]) >>
  irule abi_decode_dynamic_member_total >> metis_tac[]
QED

Theorem abi_array_pointer_guard_shape[local]:
  abi_decode_array_pointer_guard child src_data hi sz st = ((),st') ==>
  inst_extends st st'
Proof
  simp[abi_decode_array_pointer_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac abi_decode_ge_guard_shape >> imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_array_pointer_guard_total:
  abi_decode_array_pointer_guard child src_data hi sz st = ((),st') /\
  eval_operand child s = SOME p /\ eval_operand src_data s = SOME d /\
  eval_operand hi s = SOME h /\ sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n d <= w2n p /\ w2n p + sz <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section /\ inst_extends st st')
Proof
  simp[abi_decode_array_pointer_guard_def, comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_ge_guard child src_data st = (u,c1)` >>
  Cases_on `u` >> gvs[] >>
  `inst_extends st c1` by metis_tac[abi_decode_ge_guard_shape] >>
  `inst_extends c1 st'` by
    (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac inst_extends_emit_op >>
     imp_res_tac compile_abi_decode_range_check_shape >>
     metis_tac[inst_extends_trans]) >>
  drule_all abi_decode_ge_guard_total >> strip_tac
  >- (disj1_tac >>
      `!u. run_inst_seq (emitted_insts st c1) s <> OK u` by simp[] >>
      drule_all run_inst_seq_emit_extend_err >> metis_tac[]) >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand child s1 = SOME p /\ eval_operand hi s1 = SOME h /\
   eval_operand (Lit (n2w sz)) s1 = SOME (n2w sz)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all abi_aggregate_head_guard_total >> strip_tac
  >- (disj1_tac >> drule_all run_inst_seq_emit_extend >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  drule_all abi_decode_sequence_chain >> strip_tac >> metis_tac[]
QED

Theorem abi_dynamic_array_pointer_total:
  compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi sz st = (child_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand elem_src s = SOME (n2w pos) /\
  eval_operand src_data s = SOME (n2w data_base) /\ eval_operand hi s = SOME h /\
  abi_decode_load opc (n2w (B + pos):bytes32) s = n2w child_off /\
  child_off < dimword (:256) /\ data_base < dimword (:256) /\
  sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (data_base + child_off + sz <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_array_pointer_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data (Lit 0w) sz st =
    (child_op,c1)` >>
  rename1 `abi_decode_array_pointer_guard child_op src_data hi sz c1 = (u,st')` >>
  Cases_on `u` >> gvs[] >>
  drule_all abi_decode_array_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src_data s1 = SOME (n2w data_base) /\ eval_operand hi s1 = SOME h` by
    metis_tac[] >>
  drule_all abi_array_pointer_guard_total >> strip_tac
  >- (disj1_tac >> drule abi_array_pointer_guard_shape >> strip_tac >>
      drule_all run_inst_seq_emit_extend >> metis_tac[]) >>
  `data_base + child_off < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w data_base`, `n2w child_off`] w2n_add_overflow) >>
     gvs[word_add_n2w, w2n_n2w]) >>
  disj2_tac >> gvs[w2n_n2w] >>
  drule_all abi_decode_sequence_chain >> strip_tac >> metis_tac[]
QED

Theorem abi_checked_reflected_dynamic_head:
  is_dynamic a /\ mem_bytes_at B len (abi_decode_source opc s) = xs /\
  32 * i + 32 <= len /\ B + len < dimword (:256) ==>
  abi_reflected_head_ok a xs i /\
  abi_decode_load opc (n2w (B + 32 * i):bytes32) s =
    n2w (abi_head_word (DROP (32 * i) xs)) /\
  abi_head_word (DROP (32 * i) xs) < dimword (:256)
Proof
  strip_tac >>
  `LENGTH xs = len` by metis_tac[LENGTH_mem_bytes_at] >>
  conj_tac
  >- (simp[abi_reflected_head_ok_def, LENGTH_DROP, dec_number_def,
           is_num_value_def] >> decide_tac) >>
  irule abi_checked_offset_load >> metis_tac[]
QED

Theorem abi_checked_reflected_dynamic_window:
  is_dynamic a /\ mem_bytes_at (B + data_base) len mem = xs /\
  data_base + abi_head_word (DROP (32 * i) xs) + sz <= hi /\
  hi <= data_base + len ==>
  mem_bytes_at (B + data_base + abi_head_word (DROP (32 * i) xs))
    (len - abi_head_word (DROP (32 * i) xs)) mem = abi_reflected_child a xs i /\
  sz <= LENGTH (abi_reflected_child a xs i)
Proof
  strip_tac >>
  `abi_head_word (DROP (32 * i) xs) <= len` by decide_tac >>
  `LENGTH xs = len` by metis_tac[LENGTH_mem_bytes_at] >>
  simp[abi_reflected_child_def, LENGTH_DROP] >>
  mp_tac (Q.SPECL [`B + data_base`, `abi_head_word (DROP (32 * i) xs)`,
    `len - abi_head_word (DROP (32 * i) xs)`, `len`, `mem`] mem_bytes_at_window) >>
  simp[GSYM ADD_ASSOC] >>
  `len - abi_head_word (DROP (32 * i) xs) =
     LENGTH (DROP (abi_head_word (DROP (32 * i) xs)) xs)` by simp[] >>
  metis_tac[TAKE_LENGTH_ID]
QED
