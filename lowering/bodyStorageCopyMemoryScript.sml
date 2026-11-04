(* Actual storage/transient copy prefixes and their linear-memory footprints. *)
Theory bodyStorageCopyMemory
Ancestors
  bodyAllocMemory exprSimStorageCopy storageDecodeMemory fragExecMem instMemFrontier
  context compileEnv emitHelperProps venomExecSemantics venomState venomInst
  words arithmetic list finite_map

Theorem body_storage_singleton_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  (!x. dst = Var x ==> x <> v) /\
  b + 32 < dimword (:256) /\ b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v];
     mk_inst (id+1) MSTORE [dst; Var v] []] s
Proof
  strip_tac >> (rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> gvs[mk_inst_def]) >>
  gvs[step_inst_base_def, exec_read1_def, mk_inst_def] >>
  Cases_on `eval_operand src s` >> simp[] >>
  simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def, below_frontier_MSTORE] >>
  Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[])
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_STORAGE_COPY_MEMORY_AUDIT OK\n"
     else raise Fail "storage copy inherited admission"
  end) [body_storage_singleton_mem_ok];
