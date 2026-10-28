(* TOP-LEVEL: local head/tail interval arithmetic discharges same-owner
   separation, for both static payload copies and dynamic tail/head writes. *)
Theory abiNativeDynamicIntervals
Ancestors abiMemoryFrame compileEnv arithmetic

Theorem abi_native_field_intervals:
  !base full_head done_head done_tail is_dyn payload_len.
    done_head + (if is_dyn then 32 else payload_len) <= full_head ==>
    abi_window_separated base done_head
      (if is_dyn then base + full_head + done_tail else base + done_head) payload_len /\
    abi_window_separated (base + full_head) done_tail
      (if is_dyn then base + full_head + done_tail else base + done_head) payload_len /\
    (is_dyn ==>
      regions_disjoint (base + full_head + done_tail) payload_len (base + done_head) 32 /\
      abi_window_separated base done_head (base + done_head) 32 /\
      abi_window_separated (base + full_head) done_tail (base + done_head) 32)
Proof
  rpt gen_tac >> Cases_on `is_dyn` >>
  simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed mixed native interval separation: " ^ name)
  end) (DB.thms "abiNativeDynamicIntervals")
