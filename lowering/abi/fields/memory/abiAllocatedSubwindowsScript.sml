(* TOP-LEVEL: an allocation-backed arena also backs each contained window. *)
Theory abiAllocatedSubwindows
Ancestors
  abiAllocatedWindows venomState list arithmetic

Theorem abi_allocated_window_subwindow:
  !ss id offset capacity sub_offset byte_count.
    abi_allocated_window ss id offset capacity /\ offset <= sub_offset /\
    sub_offset + byte_count <= offset + capacity ==>
    abi_allocated_window ss id sub_offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`window_base`, `window_size`] >>
  simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-backed arena subwindows: " ^ name)
  end) (DB.thms "abiAllocatedSubwindows")
