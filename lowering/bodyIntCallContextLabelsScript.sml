(* Label boundaries for the selected callee's context/memory helpers. *)
Theory bodyIntCallContextLabels
Ancestors
  bodyIntCallLabelFrame bodyIntCallLabelReservations context emitHelperProps
  compileEnv list pred_set

Theorem compile_ptr_load_label_fields:
  compile_ptr_load ctor imm loc src st = (v,out) ==>
  out.cs_blocks = st.cs_blocks /\
  out.cs_current_bb = st.cs_current_bb /\
  out.cs_next_label = st.cs_next_label
Proof
  Cases_on `loc` >> Cases_on `imm` >> Cases_on `ctor` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def,
       emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_ptr_store_label_fields:
  compile_ptr_store ctor imm loc dst v st = (u,out) ==>
  out.cs_blocks = st.cs_blocks /\
  out.cs_current_bb = st.cs_current_bb /\
  out.cs_next_label = st.cs_next_label
Proof
  Cases_on `loc` >> Cases_on `imm` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_state_ok_label_fields:
  out.cs_blocks = st.cs_blocks /\
  out.cs_current_bb = st.cs_current_bb /\
  out.cs_next_label = st.cs_next_label /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  simp[compile_state_ok_def, bound_labels_def, SUBSET_DEF]
QED

Theorem compile_ptr_load_label_bounds:
  compile_ptr_load ctor imm loc src st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> drule compile_ptr_load_label_fields >> strip_tac >>
  irule compile_state_ok_label_fields >> simp[]
QED

Theorem compile_ptr_store_label_bounds:
  compile_ptr_store ctor imm loc dst v st = (u,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> drule compile_ptr_store_label_fields >> strip_tac >>
  irule compile_state_ok_label_fields >> simp[]
QED

Theorem compile_alloc_buffer_label_fields:
  compile_alloc_buffer sz st = (v,out) ==>
  out.cs_blocks = st.cs_blocks /\
  out.cs_current_bb = st.cs_current_bb /\
  out.cs_next_label = st.cs_next_label
Proof
  simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem compile_alloc_buffer_label_bounds:
  compile_alloc_buffer sz st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> drule compile_alloc_buffer_label_fields >> strip_tac >>
  irule compile_state_ok_label_fields >> simp[]
QED

Theorem compiler_block_tail_alloc_buffer:
  compiler_block_tail (compile_alloc_buffer sz)
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compile_alloc_dynamic_label_bounds:
  compile_alloc_dynamic sz st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  simp[compile_alloc_dynamic_def] >> strip_tac >>
  drule_all compile_state_ok_emit_op >> simp[SUBSET_DEF]
QED

Theorem compiler_block_tail_alloc_dynamic:
  compiler_block_tail (compile_alloc_dynamic sz)
Proof
  simp[compile_alloc_dynamic_def, compiler_block_tail_primitives]
QED

Theorem compile_copy_memory_label_bounds:
  compile_copy_memory dst src sz st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Cases_on `sz`
  >- (simp[compile_copy_memory_def, comp_return_def] >> strip_tac >> gvs[]) >>
  simp[compile_copy_memory_def] >> strip_tac >>
  drule_all compile_state_ok_emit_void >> simp[SUBSET_DEF]
QED

Theorem compiler_block_tail_copy_memory:
  compiler_block_tail (compile_copy_memory dst src sz)
Proof
  Cases_on `sz` >>
  simp[compile_copy_memory_def, compiler_block_tail_primitives]
QED

Theorem comp_bind_label_bounds:
  (!st x mid. m st = (x,mid) /\ compile_state_ok st ==>
     compile_state_ok mid /\ st.cs_next_label <= mid.cs_next_label /\
     bound_labels mid SUBSET
       (bound_labels st UNION compiler_labels_future st.cs_next_label)) /\
  (!x mid r out. k x mid = (r,out) /\ compile_state_ok mid ==>
     compile_state_ok out /\ mid.cs_next_label <= out.cs_next_label /\
     bound_labels out SUBSET
       (bound_labels mid UNION compiler_labels_future mid.cs_next_label)) ==>
  !st r out. comp_bind m k st = (r,out) /\ compile_state_ok st ==>
    compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
    bound_labels out SUBSET
      (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m st` >>
  rename1 `m st = (x,mid)` >> simp[comp_bind_def] >> strip_tac >>
  qpat_x_assum `!st x mid. m st = _ /\ _ ==> _` drule >> simp[] >> strip_tac >>
  qpat_x_assum `!x mid r out. k x mid = _ /\ _ ==> _` drule >> simp[] >> strip_tac >>
  metis_tac[compiler_label_bounds_trans]
QED

Theorem compiler_block_tail_copy_memory_dynamic:
  compiler_block_tail (compile_copy_memory_dynamic dst src lenop)
Proof
  simp[compile_copy_memory_dynamic_def, compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_with_byte_offset:
  compiler_block_tail (compile_with_byte_offset baseop off)
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_bytestring_copy_len:
  compiler_block_tail (compile_bytestring_copy_len valop)
Proof
  rewrite_tac[compile_bytestring_copy_len_def, LET_THM] >> BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_store_bytestring:
  compiler_block_tail (compile_store_bytestring valop dstop)
Proof
  rewrite_tac[compile_store_bytestring_def] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_bytestring_copy_len, compiler_block_tail_primitives]
QED

Theorem compile_with_byte_offset_label_bounds:
  compile_with_byte_offset baseop off st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Cases_on `off = 0`
  >- (simp[compile_with_byte_offset_def, comp_return_def] >> strip_tac >> gvs[]) >>
  simp[compile_with_byte_offset_def] >> strip_tac >>
  drule_all compile_state_ok_emit_op >> simp[SUBSET_DEF]
QED

Theorem compile_copy_memory_dynamic_label_bounds:
  compile_copy_memory_dynamic dst src lenop st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule_all compile_state_ok_emit_void >> simp[SUBSET_DEF]
QED

Theorem compile_bytestring_copy_len_label_fields:
  compile_bytestring_copy_len valop st = (v,out) ==>
  out.cs_blocks = st.cs_blocks /\
  out.cs_current_bb = st.cs_current_bb /\
  out.cs_next_label = st.cs_next_label
Proof
  simp[compile_bytestring_copy_len_def, LET_THM, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem compile_bytestring_copy_len_label_bounds:
  compile_bytestring_copy_len valop st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> drule compile_bytestring_copy_len_label_fields >> strip_tac >>
  irule compile_state_ok_label_fields >> simp[]
QED

Theorem compile_store_bytestring_label_bounds:
  compile_store_bytestring valop dstop st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  map_every qid_spec_tac [`out`, `v`, `st`] >>
  rewrite_tac[compile_store_bytestring_def] >>
  ho_match_mp_tac comp_bind_label_bounds >> conj_tac
  >- (rpt strip_tac >> drule_all compile_bytestring_copy_len_label_bounds >> simp[]) >>
  rpt strip_tac >> drule_all compile_state_ok_emit_void >> simp[SUBSET_DEF]
QED

Theorem compiler_block_tail_typed_copy:
  (!cenv dst dst_ty src src_ty.
     compiler_block_tail (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
     compiler_block_tail (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem count.
     compiler_block_tail (compile_copy_sarray_typed cenv dst dst_elem src src_elem count)) /\
  (!cenv dst dst_elem cap src src_elem.
     compiler_block_tail (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
     compiler_block_tail (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  conj_tac >- simp[Once compile_store_memory_typed_def, compiler_block_tail_primitives] >>
  conj_tac >- simp[Once compile_store_memory_typed_def, compiler_block_tail_primitives] >>
  conj_tac >- suspend "fields" >>
  conj_tac >- suspend "sarray" >>
  conj_tac >- suspend "dynarray" >>
  conj_tac >- simp[Once compile_store_memory_typed_def, compiler_block_tail_primitives] >>
  suspend "struct"
QED

Resume compiler_block_tail_typed_copy[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC
  >- (irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  IF_CASES_TAC >- simp[compiler_block_tail_store_bytestring] >>
  IF_CASES_TAC >- simp[compiler_block_tail_primitives] >>
  Cases_on `dst_ty` >> Cases_on `src_ty` >>
  gvs[compiler_block_tail_copy_memory] >>
  rename1 `~is_word_type (ArrayT elem dst_bound)` >>
  qmatch_goalsub_rename_tac `case src_bound of Fixed _ => _ | Dynamic _ => _` >>
  Cases_on `dst_bound` >> Cases_on `src_bound` >>
  gvs[compiler_block_tail_copy_memory]
QED

Resume compiler_block_tail_typed_copy[fields]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  rewrite_tac[Once compile_store_memory_typed_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_with_byte_offset] >> gen_tac >> BETA_TAC) >>
  simp[]
QED
Resume compiler_block_tail_typed_copy[sarray]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >> IF_CASES_TAC >- simp[compiler_block_tail_copy_memory] >> gvs[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED
Resume compiler_block_tail_typed_copy[dynarray]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >>
  Cases_on `type_memory_bytes cenv dst_elem = type_memory_bytes cenv src_elem /\
            dst_elem = src_elem` >> gvs[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_copy_memory_dynamic] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_copy_memory_dynamic]
QED
Resume compiler_block_tail_typed_copy[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  pairarg_tac >> gvs[] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_with_byte_offset] >> gen_tac >> BETA_TAC) >>
  simp[]
QED
Finalise compiler_block_tail_typed_copy

Theorem compiler_label_hoare_context_primitives:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (emit_op opc ops) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (emit_inst opc ops outs) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    fresh_var (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ptr_load ctor imm loc ptrop)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ptr_store ctor imm loc ptrop valop)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rpt conj_tac >> irule compiler_label_hoare_preserves_reservation >>
  rpt gen_tac >> strip_tac
  >- (drule_all compile_state_ok_emit_op >> simp[SUBSET_DEF])
  >- (drule_all compile_state_ok_emit_inst >> simp[SUBSET_DEF])
  >- (drule_all compile_state_ok_fresh_var >> simp[SUBSET_DEF])
  >- (drule_all compile_ptr_load_label_bounds >> simp[])
  >- (drule_all compile_ptr_store_label_bounds >> simp[])
QED

Theorem compiler_label_hoare_scaled_offset:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (if scale = 1 then emit_op ADD [ptrop; Var counter] else
       comp_bind (emit_op MUL [Var counter; Lit (n2w scale)])
         (\scaled. emit_op ADD [ptrop; scaled]))
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `scale = 1` >> simp[compiler_label_hoare_context_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_label_hoare_word_copy_loop:
  compiler_label_hoare (compiler_label_reservation origin {})
    (compile_word_copy_loop src dst nwords load_loc store_loc ctor)
    (\r out. compiler_label_reservation origin {} out)
Proof
  rewrite_tac[compile_word_copy_loop_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >>
  ntac 3 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  BETA_TAC >> gvs[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  BETA_TAC >> gvs[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_scaled_offset] >> gen_tac >> BETA_TAC) >>
  simp[DELETE_INSERT] >>
  rename1 `compiler_label_hoare _ (new_block lastlbl) _` >>
  qspec_then `{lastlbl}` mp_tac
    (Q.GEN `pending` (Q.INST [`lbl` |-> `lastlbl`] compiler_label_hoare_new_block)) >>
  simp[]
QED

Theorem compile_word_copy_loop_label_bounds:
  compile_word_copy_loop src dst nwords load_loc store_loc ctor st = (v,out) /\
  compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  map_every qid_spec_tac [`out`, `v`, `st`] >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >>
  gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  MATCH_ACCEPT_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)
    compiler_label_hoare_word_copy_loop)
QED
