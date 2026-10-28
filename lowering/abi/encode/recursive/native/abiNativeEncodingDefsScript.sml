(* TOP-LEVEL: native recursive execution uses the compiler's actual local
   allocation profile for scratch, including cached slots from prior loop
   iterations. The induction assertion permits runtime memories agreeing
   with the original source window after earlier prefix/field execution.
   Helpers expose physical readiness and lift existing allocation-free runs. *)
Theory abiNativeEncodingDefs
Ancestors
  abiMemoryLeafRun abiAllocationWindows abiAllocationTrace abiAllocationBudget
  abiAllocationFrame abiAllocatedWindows abiMemoryFrame abiStateFrame abiAllocatorState
  compileAllocaProvenance compileIdFlow abiEncoder context compileEnv fragExec
  venomWf venomMemDefs venomState valueEncoding list pair words arithmetic

Definition abi_native_encoding_result_def:
  abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after <=>
    abi_encoding_result ctx func cs cs' ret dst_addr payload
      (abi_allocation_windows (compiler_alloca_ids cs cs') after) before after /\
    abi_allocation_trace 32 (compiler_alloca_ids cs cs') before after
End

Definition abi_native_memory_ready_def:
  abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload ss <=>
    fn_inst_ids_distinct func /\ compiler_id_history cs /\ alloca_inv ss /\
    abi_alloca_budget 32 (compiler_alloca_ids cs cs') ss < dimword (:256) /\
    (!id. MEM id (compiler_alloca_ids cs cs') ==> abi_alloca_request_ok id 32 ss) /\
    source_id <> target_id /\
    ~MEM source_id (compiler_alloca_ids cs cs') /\ ~MEM target_id (compiler_alloca_ids cs cs') /\
    abi_allocated_window ss source_id (w2n src_addr) span /\
    abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload)
End

Definition abi_native_encoder_def:
  abi_native_encoder info source span reference payload <=>
    !ctx func dst src cs ret cs' ss src_addr dst_addr source_id target_id.
      compile_abi_encode_to_buf dst src info cs = (ret,cs') /\ fn_has_code cs cs' func /\
      ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
      eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
      abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
      w2n src_addr = source /\
      abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload ss /\
      mem_bytes_at source span reference = mem_bytes_at source span ss.vs_memory ==>
      ?out. abi_native_encoding_result ctx func cs cs' ret dst_addr payload ss out
End

Theorem abi_native_memory_bounds:
  !func cs cs' source_id target_id src_addr span dst_addr payload ss.
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload ss ==>
    span < dimword (:256) /\ w2n src_addr + span < dimword (:256) /\
    w2n dst_addr + LENGTH payload < dimword (:256) /\
    abi_window_separated (w2n src_addr) span (w2n dst_addr) (LENGTH payload)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_memory_ready_def] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `ss.vs_alloca_next < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids cs cs'`, `ss`] mp_tac abi_alloca_budget_frontier >>
     decide_tac) >>
  `alloca_next_valid ss /\ allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `w2n src_addr + span <= ss.vs_alloca_next` by
    (qspecl_then [`ss`, `source_id`, `w2n src_addr`, `span`]
       mp_tac abi_allocated_window_frontier >> impl_tac >- simp[] >> simp[]) >>
  `w2n dst_addr + LENGTH payload <= ss.vs_alloca_next` by
    (qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH payload`]
       mp_tac abi_allocated_window_frontier >> impl_tac >- simp[] >> simp[]) >>
  `regions_disjoint (w2n src_addr) span (w2n dst_addr) (LENGTH payload)` by
    (qspecl_then [`ss`, `(source_id,(w2n src_addr,span))`,
       `(target_id,(w2n dst_addr,LENGTH payload))`] mp_tac abi_allocated_window_disjoint >>
     impl_tac >- simp[] >> simp[]) >>
  asm_simp_tac bool_ss [abi_window_separated_def] >> decide_tac
QED

Theorem abi_native_encoding_allocation_free:
  !ctx func cs cs' ret dst_addr payload before after.
    abi_encoding_result ctx func cs cs' ret dst_addr payload [] before after /\
    abi_allocator_state after = abi_allocator_state before ==>
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs cs') before after` by
    (irule abi_allocation_trace_identity >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `abi_memory_frame ((w2n dst_addr,LENGTH payload)::
      abi_allocation_windows (compiler_alloca_ids cs cs') after) before after` by
    (qspecl_then [`[(w2n dst_addr,LENGTH payload)]`,
       `abi_allocation_windows (compiler_alloca_ids cs cs') after`, `before`, `after`]
       mp_tac abi_memory_frame_append_left >> simp[]) >>
  PURE_REWRITE_TAC [abi_native_encoding_result_def, abi_encoding_result_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_encoding_not_halted:
  !ctx func cs cs' ret dst_addr payload before after.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\ ~before.vs_halted ==>
    ~after.vs_halted
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_encoding_result_def, abi_encoding_result_def] >>
  strip_tac >> drule abi_state_frame_observables >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed local-profile native encoder assertions: " ^ name)
  end) (DB.thms "abiNativeEncodingDefs")
