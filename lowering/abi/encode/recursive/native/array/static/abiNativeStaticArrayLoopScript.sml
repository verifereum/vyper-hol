(* TOP-LEVEL: the generated static-array loop executes its runtime count
   and returns the packed raw encoding. The proof uses the actual header,
   body and exit blocks; source/output strides may differ. *)
Theory abiNativeStaticArrayLoop
Ancestors
  abiNativeStaticArrayRun abiNativeStaticArrayState abiNativeStaticArrayBounds abiNativeStaticArrayEffects
  abiNativeStaticArraySnapshotFrame abiAllocationWindows abiMemoryFrame compileAllocaProvenance
  abiNativeArrayResources abiNativeEncodingDefs abiMemoryEncoding abiFieldLayoutDefs abiAllocatorState abiStateFrame
  abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopComplete abiStaticLoopExec abiStaticLoopExit abiStaticLoopRun
  compileEnv fragExec venomState venomInst list words arithmetic

Theorem abi_native_static_array_loop:
  !ctx func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity dst_addr
      info stride fields initial ss dst src len_op cs ret after.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity 0 ss /\ LENGTH fields < dimword (:256) /\
    compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_tail_names cs.cs_next_var info) ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = after.cs_current_bb /\
      out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
      eval_operand ret out = SOME (n2w (LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields))) /\
      read_memory (w2n dst_addr) (LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields)) out =
        word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields /\
      abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss /\
      abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss out /\
      abi_memory_frame ((w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields))::
        abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_tail_names cs.cs_next_var info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`LENGTH fields`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `counter_inst`, `counter_addr`,
    `loop_cs`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`, `initial`, `ss`, `cs.cs_next_label`]
    mp_tac abi_native_static_array_memory_run >> impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  drule_all compile_abi_encode_dyn_static_loop_contains >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) _ = SOME header_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1)) _ = SOME body_bb` >>
  rename1 `isPREFIX (abi_static_loop_exit _ _ _ _ _) exit_bb.bb_instructions` >>
  `mload (w2n counter_addr) ss = 0w` by fs[abi_native_static_array_data_def] >>
  qspecl_then [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `dst`, `src`, `info`,
    `abi_static_encoder_size info`, `stride`, `len_op`, `ss`, `dst_addr`, `root_addr`, `counter_addr`,
    `LENGTH fields`, `header_bb`, `body_bb`, `exit_bb`] mp_tac abi_static_loop_complete_path >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`header_bb`, Abbr`body_bb`] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qabbrev_tac `folded = FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info)
    stride counter_addr cs.cs_next_label) (LENGTH fields) ss` >>
  `out.vs_memory = folded.vs_memory` by
    (qpat_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``\st:venom_state. st.vs_memory``) >> simp[Abbr`folded`, jump_to_def]) >>
  `abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
    source_capacity (LENGTH fields) out` by
    (qspecl_then [`info`, `abi_static_encoder_size info`, `stride`, `fields`, `dst_addr`, `root_addr`, `counter_addr`,
       `source_capacity`, `LENGTH fields`, `folded`, `out`] mp_tac abi_native_static_array_data_memory >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[Abbr`folded`]) >>
  drule_all abi_native_static_array_complete >> strip_tac >>
  qspecl_then [`LENGTH fields`, `info`, `dst_addr`, `root_addr`, `abi_static_encoder_size info`, `stride`,
    `counter_addr`, `cs.cs_next_label`, `ss`] strip_assume_tac abi_native_static_effects_context >>
  `abi_allocator_state out = abi_allocator_state ss` by
    (qpat_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``abi_allocator_state``) >> simp[Abbr`folded`]) >>
  `abi_state_frame ss out` by
    (qpat_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``abi_state_context``) >>
     simp_tac (srw_ss()) [] >> DISCH_TAC >> fs[abi_state_frame_def, Abbr`folded`]) >>
  `mload (w2n root_addr) folded = n2w (LENGTH fields)` by
    fs[Abbr`folded`, abi_native_static_array_data_def] >>
  qpat_assum `abi_native_static_array_data _ _ _ _ _ _ _ _ _ ss`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_array_data_def]) >>
  drule_all abi_native_static_array_extents >> strip_tac >>
  drule compile_abi_encode_dyn_static_loop_cut >> strip_tac >>
  `LENGTH after.cs_current_insts = 3` by fs[abi_static_loop_exit_length] >>
  qspecl_then [`LENGTH fields`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `counter_inst`, `counter_addr`,
    `loop_cs`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`, `initial`, `ss`, `cs.cs_next_label`, `out`]
    mp_tac abi_native_static_array_snapshot_frame >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL, Abbr`folded`] >> strip_tac >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) [word_mul_n2w, word_add_n2w]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed generated static array loop raw execution: " ^ name)
  end) (DB.thms "abiNativeStaticArrayLoop")
