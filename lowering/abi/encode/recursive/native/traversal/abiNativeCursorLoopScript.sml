(* TOP-LEVEL: a runtime backedge can select the same genuine cursor
   instruction again. Two loop cursors cover their own stores alongside
   an output head store in the enclosing allocation frame. *)
Theory abiNativeCursorLoop
Ancestors
  abiNativeCursor abiNativeCursorFrame abiMemoryFrameCover compileAllocaProvenance
  compileEnv venomState venomInst list words

Theorem abi_native_cursor_context:
  !func root_cs root_after counter_inst read_addr cs ss next_cs.
    abi_native_cursor func root_cs root_after counter_inst read_addr cs ss /\
    compiler_instruction_member next_cs counter_inst ==>
    abi_native_cursor func root_cs root_after counter_inst read_addr next_cs ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_cursor_def] >> strip_tac >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_cursor_loop_stores_cover:
  !func root_cs root_after dyn_inst dyn_addr index_inst counter_addr cs ss root_dst root_payload head_base.
    abi_native_cursor func root_cs root_after dyn_inst dyn_addr cs ss /\
    abi_native_cursor func root_cs root_after index_inst counter_addr cs ss /\
    w2n (root_dst:bytes32) <= head_base /\
    head_base + 32 <= w2n root_dst + LENGTH (root_payload:word8 list) ==>
    abi_writes_cover ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss)
      [(head_base,32);(w2n dyn_addr,32);(w2n counter_addr,32)]
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`func`, `root_cs`, `root_after`, `dyn_inst`, `dyn_addr`, `cs`, `ss`, `root_dst`, `root_payload`, `head_base`]
    mp_tac abi_native_cursor_stores_cover >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`func`, `root_cs`, `root_after`, `index_inst`, `counter_addr`, `cs`, `ss`, `root_dst`, `root_payload`, `head_base`]
    mp_tac abi_native_cursor_stores_cover >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  fs[abi_writes_cover_def, MEM] >> metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed repeated loop cursor context and store cover: " ^ name)
  end) (DB.thms "abiNativeCursorLoop")
