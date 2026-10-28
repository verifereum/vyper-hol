(* TOP-LEVEL: any finite list of owned native cursor stores fits the
   enclosing computed allocation windows, including cached loop cells. *)
Theory abiNativeCursorWrites
Ancestors
  abiNativeCursor abiAllocatedWindows abiAllocationWindows abiMemoryFrameCover compileAllocaProvenance
  compileEnv venomState venomInst finite_map list pair words arithmetic

Theorem abi_native_cursor_writes_cover:
  !func root_cs root_after point ss cursors.
    EVERY (\(inst,addr). abi_native_cursor func root_cs root_after inst addr point ss) cursors ==>
    abi_writes_cover (abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss)
      (MAP (\(inst,addr). (w2n addr,32)) cursors)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_writes_cover_def] >>
  MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >>
  simp_tac (srw_ss()) [MEM_MAP, EXISTS_PROD] >>
  disch_then (qx_choose_then `inst` (qx_choose_then `addr` strip_assume_tac)) >>
  `abi_native_cursor func root_cs root_after inst addr point ss` by
    (qpat_assum `EVERY _ cursors` (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(inst,addr)` mp_tac) >> simp[]) >>
  qpat_x_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas inst.inst_id = SOME (cursor_base,cursor_capacity)` >>
  qexistsl_tac [`cursor_base`, `cursor_capacity`] >> conj_tac
  >- (simp_tac bool_ss [abi_allocation_windows_member] >> qexists_tac `inst.inst_id` >> simp[]) >>
  gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native cursor store list allocation cover: " ^ name)
  end) (DB.thms "abiNativeCursorWrites")
