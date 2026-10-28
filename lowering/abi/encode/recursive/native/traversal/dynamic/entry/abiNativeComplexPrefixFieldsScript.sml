(* TOP-LEVEL: exact counter setup prepares the mixed field invariant.
   Source bytes are transported through its enclosing frame; semantic
   child assertions continue to refer to the independent original memory. *)
Theory abiNativeComplexPrefixFields
Ancestors
  abiNativeComplexPrefixReady abiNativeComplexPrefixState abiNativeComplexPrefixCode
  abiNativeDynamicState abiNativeFields abiNativeCursor abiNativeTraversal abiNativeEncodingDefs
  abiMemoryFieldsState abiMemoryEncodingFrame abiMemoryEncoding abiFieldOperands abiFieldLayoutDefs
  abiComplexCode abiStaticLoopCode compileEnv venomState list words arithmetic

Theorem abi_native_complex_entry_operands:
  !head_size cs ss dst src dst_addr root_addr.
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr ==>
    abi_memory_fields_operands dst src (Var (compiler_var_name cs.cs_next_var 0)) dst_addr root_addr
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_complex_prefix_cut head_size cs)
      (abi_native_complex_entry head_size cs ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`head_size`, `cs`, `ss`, `dst`] mp_tac abi_native_complex_entry_old_operand >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`head_size`, `cs`, `ss`, `src`] mp_tac abi_native_complex_entry_old_operand >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`head_size`, `cs`, `ss`] strip_assume_tac abi_native_complex_entry_context >>
  simp_tac (srw_ss()) [abi_memory_fields_operands_def, abi_complex_prefix_cut_def] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >> conj_tac
  >- (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  irule abi_operand_before_reserved >> simp[]
QED

Theorem abi_native_complex_entry_fields:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr full reference entries dst src ss.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) ss /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full /\
    abi_native_fields entries (w2n root_addr) reference full /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    fn_has_code cs (abi_complex_prefix_cut (abi_field_head_size full) cs) func /\
    cs_extends (abi_complex_prefix_cut (abi_field_head_size full) cs) after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    abi_native_traversal ctx func cs after dst_addr (abi_field_bytes (abi_field_head_size full) full) ss
      (abi_complex_prefix_cut (abi_field_head_size full) cs) (abi_native_complex_entry (abi_field_head_size full) cs ss) /\
    abi_native_cursor func cs after (abi_native_complex_counter_inst cs) (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_complex_prefix_cut (abi_field_head_size full) cs) (abi_native_complex_entry (abi_field_head_size full) cs ss) /\
    abi_native_dynamic_state full dst src (Var (compiler_var_name cs.cs_next_var 0)) dst_addr
      (abi_static_loop_counter_addr cs.cs_next_id ss) root_addr source_capacity reference entries 0 0
      (abi_complex_prefix_cut (abi_field_head_size full) cs) (abi_native_complex_entry (abi_field_head_size full) cs ss) /\
    (abi_native_complex_entry (abi_field_head_size full) cs ss).vs_current_bb =
      (abi_complex_prefix_cut (abi_field_head_size full) cs).cs_current_bb /\
    (abi_native_complex_entry (abi_field_head_size full) cs ss).vs_inst_idx =
      LENGTH (abi_complex_prefix_cut (abi_field_head_size full) cs).cs_current_insts /\
    ~(abi_native_complex_entry (abi_field_head_size full) cs ss).vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_complex_entry_traversal >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_native_traversal_source >> DISCH_TAC >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >>
  disch_then (qspec_then `(abi_native_complex_entry (abi_field_head_size full) cs ss).vs_memory` mp_tac) >>
  impl_tac >- (sym_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule abi_native_memory_bounds >> strip_tac >>
  qspecl_then [`abi_field_head_size full`, `cs`, `ss`, `dst`, `src`, `dst_addr`, `root_addr`]
    mp_tac abi_native_complex_entry_operands >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`abi_field_head_size full`, `cs`, `ss`] strip_assume_tac abi_native_complex_entry_context >>
  drule_all abi_native_dynamic_initial >> DISCH_TAC >>
  gvs[abi_complex_prefix_cut_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed exact complex entry mixed field invariant: " ^ name)
  end) (DB.thms "abiNativeComplexPrefixFields")
