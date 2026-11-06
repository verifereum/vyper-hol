(* Allocation syntax certificate. This concerns generated code, not execution. *)
Theory abiDecoderCode
Ancestors
  abiEncoder abiDecoderContract compileEnv emitHelper context venomInst

Definition abi_decoder_code_member_def:
  abi_decoder_code_member i st <=>
    MEM i st.cs_current_insts \/
    ?bb. MEM bb st.cs_blocks /\ MEM i bb.bb_instructions
End

Definition abi_decoder_alloc_shape_def:
  abi_decoder_alloc_shape i <=>
    (i.inst_opcode = ALLOCA ==>
       i.inst_operands = [Lit 32w] /\ ?out. i.inst_outputs = [out])
End

Definition abi_decoder_code_def:
  abi_decoder_code st st' <=>
    st.cs_next_id <= st'.cs_next_id /\
    !i. abi_decoder_code_member i st' ==>
      abi_decoder_code_member i st \/
      (st.cs_next_id <= i.inst_id /\ i.inst_id < st'.cs_next_id /\
       abi_decoder_alloc_shape i)
End

Theorem abi_decoder_code_refl:
  abi_decoder_code st st
Proof
  simp[abi_decoder_code_def]
QED

Theorem abi_decoder_code_trans:
  abi_decoder_code st st1 /\ abi_decoder_code st1 st2 ==>
  abi_decoder_code st st2
Proof
  rw[abi_decoder_code_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem abi_decoder_code_return:
  abi_decoder_code st (SND (comp_return v st))
Proof
  simp[comp_return_def, abi_decoder_code_refl]
QED

Theorem abi_decoder_code_bind:
  (!st. abi_decoder_code st (SND (f st))) /\
  (!v st. abi_decoder_code st (SND (g v st))) ==>
  abi_decoder_code st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule abi_decoder_code_trans >> metis_tac[pairTheory.SND]
QED

Theorem abi_decoder_code_ignore_bind:
  (!st. abi_decoder_code st (SND (f st))) /\
  (!st. abi_decoder_code st (SND (g st))) ==>
  abi_decoder_code st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_decoder_code_bind >> simp[]
QED

Theorem abi_decoder_code_emit_op:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  abi_decoder_code st (SND (emit_op opc ops st))
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
     fresh_id_def, emit_def, abi_decoder_code_def,
     abi_decoder_code_member_def, abi_decoder_alloc_shape_def, mk_inst_def] >>
  gvs[] >> metis_tac[]
QED

Theorem abi_decoder_code_emit_void:
  opc <> ALLOCA ==>
  abi_decoder_code st (SND (emit_void opc ops st))
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
     emit_def, abi_decoder_code_def, abi_decoder_code_member_def,
     abi_decoder_alloc_shape_def, mk_inst_def] >> gvs[] >> metis_tac[]
QED

Theorem abi_decoder_code_emit_inst:
  opc <> ALLOCA ==>
  abi_decoder_code st (SND (emit_inst opc ops outs st))
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
     emit_def, abi_decoder_code_def, abi_decoder_code_member_def,
     abi_decoder_alloc_shape_def, mk_inst_def] >> gvs[] >> metis_tac[]
QED

Theorem abi_decoder_code_fresh_label:
  abi_decoder_code st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, abi_decoder_code_def, abi_decoder_code_member_def]
QED

Theorem abi_decoder_code_new_block:
  abi_decoder_code st (SND (new_block name st))
Proof
  rw[new_block_def, abi_decoder_code_def, abi_decoder_code_member_def] >>
  gvs[] >> metis_tac[]
QED

Theorem abi_decoder_code_alloc_buffer:
  abi_decoder_code st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >>
  irule abi_decoder_code_bind >>
  simp[abi_decoder_code_emit_op, abi_decoder_code_return]
QED

(* One-level monadic composition, shared by the syntax-only proofs below. *)
val code_simps = [abi_decoder_code_emit_op, abi_decoder_code_emit_void,
  abi_decoder_code_emit_inst, abi_decoder_code_return,
  abi_decoder_code_fresh_label, abi_decoder_code_new_block,
  abi_decoder_code_alloc_buffer];
val code_db = fn t => rpt gen_tac >> ho_match_mp_tac abi_decoder_code_bind >>
  conj_tac >- simp (t::code_simps) >> rpt strip_tac;
val code_dib = fn t => ho_match_mp_tac abi_decoder_code_ignore_bind >>
  conj_tac >- simp (t::code_simps) >> rpt strip_tac;

Theorem abi_decoder_code_addr:
  !st. abi_decoder_code st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >>
  IF_CASES_TAC >> simp[abi_decoder_code_return, abi_decoder_code_emit_op]
QED

Theorem abi_decoder_code_range:
  !st. abi_decoder_code st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (code_db abi_decoder_code_emit_op) >>
  simp[abi_decoder_code_emit_void]
QED

Theorem abi_decoder_code_clamp:
  !c v st. abi_decoder_code st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
      compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
      abi_decoder_code_return] >> rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (code_db abi_decoder_code_emit_op) >>
  simp[abi_decoder_code_emit_void]
QED

Theorem abi_decoder_code_static:
  opc <> ALLOCA /\
  (!v st. abi_decoder_code st (SND (clamp v st))) ==>
  !st. abi_decoder_code st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  code_db abi_decoder_code_emit_op >> code_dib abi_decoder_code_refl >>
  simp[abi_decoder_code_emit_void]
QED

Theorem abi_decoder_code_getelemptr:
  opc <> ALLOCA ==>
  !st. abi_decoder_code st
    (SND (compile_getelemptr_abi src dyn off opc base_op hi st))
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  code_db abi_decoder_code_emit_op >> Cases_on `dyn` >>
  simp[abi_decoder_code_return] >>
  code_db abi_decoder_code_addr >>
  ntac 2 (code_db abi_decoder_code_emit_op) >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      ntac 2 (code_db abi_decoder_code_emit_op) >>
      simp[abi_decoder_code_emit_void]) >>
  simp[abi_decoder_code_return]
QED

Theorem abi_decoder_code_dyn_elem_ptr:
  opc <> ALLOCA ==>
  !st. abi_decoder_code st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  code_db abi_decoder_code_addr >>
  ntac 2 (code_db abi_decoder_code_emit_op) >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      ntac 2 (code_db abi_decoder_code_emit_op) >>
      code_dib abi_decoder_code_emit_void >>
      code_db abi_decoder_code_emit_op >>
      simp[abi_decoder_code_range]) >>
  simp[abi_decoder_code_return]
QED

(* A non-ALLOCA load opcode is essential: the dispatcher deliberately accepts
   an opcode parameter, and an arbitrary ALLOCA would allocate a loaded value.
   In particular all three abi_decode_source_opcode alternatives satisfy this. *)
Theorem abi_decoder_code_mutual:
  (!dst src opc base_op hi info. opc <> ALLOCA ==>
     !st. abi_decoder_code st
       (SND (compile_abi_decode_to_buf dst src opc base_op hi info st))) /\
  (!dst src opc base_op hi elems ao vo. opc <> ALLOCA ==>
     !st. abi_decoder_code st
       (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st))) /\
  (!dst src opc base_op hi ei asz msz ip cnt. opc <> ALLOCA ==>
     !st. abi_decoder_code st
       (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume abi_decoder_code_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  code_db abi_decoder_code_addr >>
  irule abi_decoder_code_static >> simp[abi_decoder_code_clamp]
QED
Resume abi_decoder_code_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_code_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      code_db abi_decoder_code_emit_op >> code_dib abi_decoder_code_range >>
      simp[abi_decoder_code_return]) >>
  rpt strip_tac >> code_db abi_decoder_code_addr >>
  ntac 3 (code_db abi_decoder_code_emit_op) >>
  code_dib abi_decoder_code_emit_void >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      code_db abi_decoder_code_emit_op >> simp[abi_decoder_code_range]) >>
  rpt strip_tac >> IF_CASES_TAC
  >- (Cases_on `opc` >> simp[abi_decoder_code_emit_void]) >>
  ntac 4 (code_db abi_decoder_code_emit_op) >>
  code_dib abi_decoder_code_emit_void >> code_db abi_decoder_code_emit_op >>
  simp[abi_decoder_code_emit_void]
QED
Resume abi_decoder_code_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac abi_decoder_code_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      code_db abi_decoder_code_emit_op >> code_dib abi_decoder_code_range >>
      simp[abi_decoder_code_return]) >>
  rpt strip_tac >> code_db abi_decoder_code_addr >>
  ntac 3 (code_db abi_decoder_code_emit_op) >>
  code_dib abi_decoder_code_emit_void >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_code_return] >>
      ntac 2 (code_db abi_decoder_code_emit_op) >>
      simp[abi_decoder_code_range]) >>
  rpt strip_tac >> code_db abi_decoder_code_emit_op >>
  code_dib abi_decoder_code_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (code_db abi_decoder_code_emit_op) >>
      code_db abi_decoder_code_addr >> code_db abi_decoder_code_emit_op >>
      Cases_on `opc` >> simp[abi_decoder_code_emit_void]) >>
  code_db abi_decoder_code_alloc_buffer >> code_dib abi_decoder_code_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume abi_decoder_code_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  code_db abi_decoder_code_emit_op >> code_dib abi_decoder_code_range >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume abi_decoder_code_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[abi_decoder_code_return]
QED
Resume abi_decoder_code_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  code_db abi_decoder_code_getelemptr >> code_db abi_decoder_code_emit_op >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume abi_decoder_code_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (code_db abi_decoder_code_fresh_label) >>
  code_dib abi_decoder_code_emit_inst >> code_dib abi_decoder_code_new_block >>
  code_db abi_decoder_code_emit_op >> code_db abi_decoder_code_addr >>
  ntac 3 (code_db abi_decoder_code_emit_op) >>
  code_dib abi_decoder_code_emit_inst >> code_dib abi_decoder_code_new_block >>
  ntac 4 (code_db abi_decoder_code_emit_op) >>
  ho_match_mp_tac abi_decoder_code_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_code_dyn_elem_ptr, abi_decoder_code_return]) >>
  rpt strip_tac >> ntac 3 (code_db abi_decoder_code_emit_op) >>
  ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> code_db abi_decoder_code_emit_op >>
  code_dib abi_decoder_code_emit_void >> code_dib abi_decoder_code_emit_inst >>
  code_dib abi_decoder_code_new_block >> simp[abi_decoder_code_return]
QED
Finalise abi_decoder_code_mutual

Definition abi_decoder_code_ids_below_def:
  abi_decoder_code_ids_below st <=>
    !i. abi_decoder_code_member i st ==> i.inst_id < st.cs_next_id
End

Theorem abi_decoder_code_ids_preserved:
  abi_decoder_code st st' /\ abi_decoder_code_ids_below st ==>
  abi_decoder_code_ids_below st'
Proof
  rw[abi_decoder_code_def, abi_decoder_code_ids_below_def] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem abi_decoder_code_new_instruction:
  abi_decoder_code st st' /\ abi_decoder_code_member i st' /\
  ~abi_decoder_code_member i st ==>
  st.cs_next_id <= i.inst_id /\ i.inst_id < st'.cs_next_id /\
  abi_decoder_alloc_shape i
Proof
  simp[abi_decoder_code_def] >> metis_tac[]
QED

(* With the ordinary compiler id invariant, the generation interval itself
   selects new instructions even when old and new blocks share a label. *)
Theorem abi_decoder_code_interval_instruction:
  abi_decoder_code st st' /\ abi_decoder_code_ids_below st /\
  abi_decoder_code_member i st' /\ st.cs_next_id <= i.inst_id ==>
  i.inst_id < st'.cs_next_id /\ abi_decoder_alloc_shape i
Proof
  rw[abi_decoder_code_def, abi_decoder_code_ids_below_def] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem abi_decoder_to_buf_code:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),st') /\
  abi_decode_source_opcode opc ==>
  abi_decoder_code st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 1 abi_decoder_code_mutual, pairTheory.SND]
QED

Theorem abi_decoder_complex_elems_code:
  compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st = ((),st') /\
  abi_decode_source_opcode opc ==>
  abi_decoder_code st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 2 abi_decoder_code_mutual, pairTheory.SND]
QED

Theorem abi_decoder_dyn_loop_code:
  compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st = ((),st') /\
  abi_decode_source_opcode opc ==>
  abi_decoder_code st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 3 abi_decoder_code_mutual, pairTheory.SND]
QED

(* Reusable extraction of the actual ALLOCA syntax from any of the three
   compilation certificates, without a flat-list difference across CFGs. *)
Theorem abi_decoder_code_alloca:
  abi_decoder_code st st' /\ abi_decoder_code_member inst st' /\
  ~abi_decoder_code_member inst st /\ inst.inst_opcode = ALLOCA ==>
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < st'.cs_next_id /\
  inst.inst_operands = [Lit 32w] /\ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >> drule_all abi_decoder_code_new_instruction >>
  simp[abi_decoder_alloc_shape_def]
QED

Theorem abi_decoder_code_child_interval:
  abi_decoder_code parent child /\ abi_decoder_code child child_end /\
  abi_decoder_code child_end parent_end /\
  child.cs_next_id <= id /\ id < child_end.cs_next_id ==>
  parent.cs_next_id <= id /\ id < parent_end.cs_next_id
Proof
  simp[abi_decoder_code_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_decoder_code_sequential_intervals:
  abi_decoder_code first middle /\ abi_decoder_code middle last ==>
  (!id. first.cs_next_id <= id /\ id < middle.cs_next_id ==>
       ~(middle.cs_next_id <= id /\ id < last.cs_next_id)) /\
  first.cs_next_id <= middle.cs_next_id /\
  middle.cs_next_id <= last.cs_next_id
Proof
  simp[abi_decoder_code_def] >> rpt strip_tac >> decide_tac
QED

(* An emitted instruction, unlike a label, advances the scratch-site floor.
   These facts apply to the MSTORE before the array index allocation and the
   destination ADD immediately preceding each recursive child invocation. *)
Theorem abi_decoder_emit_op_entry_floor:
  abi_decoder_code start before /\ emit_op opc ops before = (v,after) /\
  abi_decoder_code after phase /\ abi_decoder_code phase final ==>
  start.cs_next_id + 1 <= phase.cs_next_id /\
  phase.cs_next_id <= final.cs_next_id
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, abi_decoder_code_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem abi_decoder_emit_void_entry_floor:
  abi_decoder_code start before /\ emit_void opc ops before = ((),after) /\
  abi_decoder_code after phase /\ abi_decoder_code phase final ==>
  start.cs_next_id + 1 <= phase.cs_next_id /\
  phase.cs_next_id <= final.cs_next_id
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, abi_decoder_code_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem abi_decoder_member_pointer_entry_floor:
  compile_getelemptr_abi src dyn off opc base_op hi start = (elem_ptr,end_st) ==>
  start.cs_next_id + 1 <= end_st.cs_next_id
Proof
  Cases_on `dyn` >> Cases_on `base_op = Lit 0w` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

(* Last instruction of the dynamic-array header, immediately before ALLOCA.
   The prefix certificate can include either optional bound/address branch. *)
Theorem abi_decoder_array_allocation_entry_floor:
  abi_decoder_code start header_st /\
  emit_void MSTORE [dst; cnt] header_st = ((),alloc_st) /\
  abi_decoder_code alloc_st end_st ==>
  start.cs_next_id + 1 <= alloc_st.cs_next_id /\
  alloc_st.cs_next_id <= end_st.cs_next_id
Proof
  strip_tac >> irule abi_decoder_emit_void_entry_floor >>
  goal_assum (drule_at Any) >> simp[abi_decoder_code_refl] >>
  goal_assum (drule_at Any) >> simp[abi_decoder_code_refl]
QED

(* The destination ADD is unconditional in both complex-member and dynamic
   loop child setup. Earlier prefix instructions need only monotone IDs. *)
Theorem abi_decoder_child_add_entry_floor:
  abi_decoder_code start prefix_st /\
  emit_op ADD [dst_base; dst_offset] prefix_st = (elem_dst,child_st) /\
  abi_decoder_code child_st end_st ==>
  start.cs_next_id + 1 <= child_st.cs_next_id /\
  child_st.cs_next_id <= end_st.cs_next_id
Proof
  strip_tac >> irule abi_decoder_emit_op_entry_floor >>
  goal_assum (drule_at Any) >> simp[abi_decoder_code_refl] >>
  goal_assum (drule_at Any) >> simp[abi_decoder_code_refl]
QED

Theorem abi_decoder_complex_child_entry_floor:
  compile_getelemptr_abi src dyn off opc base_op hi start = (elem_src,pointer_st) /\
  emit_op ADD [dst; Lit (n2w vo)] pointer_st = (elem_dst,child_st) /\
  abi_decoder_code child_st end_st ==>
  start.cs_next_id + 1 <= child_st.cs_next_id /\
  child_st.cs_next_id <= end_st.cs_next_id
Proof
  strip_tac >> drule abi_decoder_member_pointer_entry_floor >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, abi_decoder_code_def] >>
  decide_tac
QED

Theorem abi_decoder_entry_floor_credit:
  first <= start.cs_next_id + 1 /\ start.cs_next_id + 1 <= phase.cs_next_id ==>
  first <= phase.cs_next_id
Proof
  decide_tac
QED
