Theory exprSimAbiDecodeImmutableOutcome
Ancestors
  exprSimAbiDecodeImmutableFrame exprSimAbiDecodeSuccessPrefix
  exprSimAbiDecodeQuantifiedLift exprSimAbiGasBridge
  localPtrsProps venomState

Definition abi_decode_immutable_memory_def:
  abi_decode_immutable_memory ce cx (es:evaluation_state) s t <=>
    !name off tv v.
      ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory
End

Definition abi_decode_immutable_success_def:
  abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t <=>
    abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
    abi_decode_immutable_memory ce cx es s t
End

Theorem abi_decode_success_closed_source:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  ?v. evaluate_abi_decode env ty bs = INL v
Proof
  simp[abi_decode_success_closed_def, abi_decode_success_post_def] >> metis_tac[]
QED

Theorem abi_decode_immutable_memory_updates[simp]:
  abi_decode_immutable_memory ce cx es s
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>) =
  abi_decode_immutable_memory ce cx es s t
Proof
  simp[abi_decode_immutable_memory_def]
QED

Theorem abi_decode_immutable_success_updates:
  abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t ==>
  abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>)
Proof
  simp[abi_decode_immutable_success_def] >>
  metis_tac[abi_decode_success_closed_returndata, abi_decode_success_closed_prev_bb]
QED

Theorem abi_decode_original_entry_immutable_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s ==>
  (?t. abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t /\
    local_prefix ctx fn (frag_observer_cut final) s t) \/
  ((?e. evaluate_abi_decode env ty bs = INR e) /\
    ?fuel u. run_from fuel ctx fn s = Abort Revert_abort u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac abi_decode_original_entry_outcome_prefix >>
  (impl_tac >- simp[]) >> strip_tac
  >- (drule abi_decode_success_closed_source >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      simp[abi_decode_immutable_success_def, abi_decode_immutable_memory_def] >>
      rpt strip_tac >> irule abi_decode_prefix_immutable_frame >>
      asm_rewrite_tac [] >>
      goal_assum (drule_at (Pat `local_prefix _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
      asm_rewrite_tac [] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED
