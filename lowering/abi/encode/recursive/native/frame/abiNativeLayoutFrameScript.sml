(* TOP-LEVEL: a recursive native result appended after completed tails
   preserves the completed ABI heads and tails in the same owned arena.
   Computed child scratch is separated by the target allocation identity. *)
Theory abiNativeLayoutFrame
Ancestors
  abiNativeReadFrame abiNativeEncodingDefs abiAllocatedSubwindows abiAllocatedWindows abiFieldMemory
  abiFieldLayoutDefs abiMemoryFrame compileAllocaProvenance compileEnv fragExec venomState list words arithmetic

Theorem abi_native_result_layout:
  !ctx func cs after ret encoded_addr payload before out target_id arena capacity done tail_start.
    abi_native_encoding_result ctx func cs after ret encoded_addr payload before out /\ alloca_inv before /\
    abi_allocated_window before target_id arena capacity /\ ~MEM target_id (compiler_alloca_ids cs after) /\
    abi_fields_layout done arena 0 tail_start before /\
    abi_field_head_size done <= tail_start /\ tail_start + abi_field_tail_size done <= capacity /\
    w2n encoded_addr = arena + tail_start + abi_field_tail_size done ==>
    abi_fields_layout done arena 0 tail_start out
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocated_window before target_id arena (abi_field_head_size done)` by
    (qspecl_then [`before`, `target_id`, `arena`, `capacity`, `arena`, `abi_field_head_size done`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp_tac bool_ss []) >>
  `abi_allocated_window before target_id (arena + tail_start) (abi_field_tail_size done)` by
    (qspecl_then [`before`, `target_id`, `arena`, `capacity`, `arena + tail_start`, `abi_field_tail_size done`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp_tac bool_ss []) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `ret`, `encoded_addr`, `payload`, `before`, `out`, `target_id`,
    `arena`, `abi_field_head_size done`] mp_tac abi_native_result_read >>
  impl_tac >- (asm_simp_tac bool_ss [abi_window_separated_def, regions_disjoint_def] >> decide_tac) >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `ret`, `encoded_addr`, `payload`, `before`, `out`, `target_id`,
    `arena + tail_start`, `abi_field_tail_size done`] mp_tac abi_native_result_read >>
  impl_tac >- (asm_simp_tac bool_ss [abi_window_separated_def, regions_disjoint_def] >> decide_tac) >> DISCH_TAC >>
  qpat_x_assum `abi_fields_layout done _ _ _ before` (mp_tac o PURE_REWRITE_RULE [abi_fields_layout_def]) >>
  asm_simp_tac bool_ss [abi_fields_layout_def, ADD_0]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned completed-layout frame through recursive execution: " ^ name)
  end) (DB.thms "abiNativeLayoutFrame")
