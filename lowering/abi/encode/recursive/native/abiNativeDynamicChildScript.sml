(* TOP-LEVEL: execute the dynamic child and its actual head/cursor suffix
   from the recursive induction assertion. Scratch is the wrapper's computed
   allocation profile plus the two explicit parent stores. *)
Theory abiNativeDynamicChild
Ancestors
  abiNativeEncodingDefs abiNativeDynamicInner abiNativeResources abiMemoryChildRun abiMemoryChildEntry
  abiMemoryLeafRun abiChildStructure abiChildCode abiAllocationTrace abiAllocationWindows abiAllocatorState
  allocationPathGrowth allocationGrowth compileAllocaProfiles compileAllocaProvenance
  abiMemoryFrame compileEnv venomState valueEncoding list words arithmetic

Theorem abi_native_dynamic_child_cuts:
  !info span reference payload ctx func dst src dyn_ptr head_offset cs ret mid after ss
      dst_addr src_addr dyn_addr source_id target_id.
    abi_native_encoder info (w2n src_addr) span reference payload /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (ret,mid) /\
    after = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr ret mid /\
    fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_native_memory_ready func cs after source_id target_id src_addr span
      (dst_addr + mload (w2n dyn_addr) ss) payload ss /\
    mem_bytes_at (w2n src_addr) span reference = mem_bytes_at (w2n src_addr) span ss.vs_memory /\
    regions_disjoint (w2n (dst_addr + n2w head_offset)) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)
      (w2n (dst_addr + n2w head_offset)) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload) (w2n dyn_addr) 32 ==>
    ?out.
      abi_encoding_result ctx func cs after ret (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs after) out ++
          [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs after) ss out /\
      mload (w2n (dst_addr + n2w head_offset)) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qspecl_then [`dst`, `src`, `info`, `head_offset`, `dyn_ptr`, `cs`, `ret`, `mid`, `func`]
    mp_tac abi_child_dynamic_contains >> impl_tac
  >- (qpat_x_assum `after = _` (fn th => asm_simp_tac bool_ss [GSYM th])) >> strip_tac >>
  `cs_extends mid after` by simp[abi_child_suffix_extends] >>
  drule_all abi_native_dynamic_inner >>
  disch_then (qspec_then `ctx` (qx_choose_then `child_out` strip_assume_tac)) >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss
    (abi_child_entry_state cs head_offset dst_addr dyn_addr ss)` by
    (irule abi_allocation_trace_identity >> simp[abi_child_entry_frame]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss child_out` by
    (qspecl_then [`ctx`, `func`, `abi_child_prefix_cut dst dyn_ptr head_offset cs`, `mid`, `ret`,
       `dst_addr + mload (w2n dyn_addr) ss`, `payload`,
       `abi_child_entry_state cs head_offset dst_addr dyn_addr ss`, `child_out`, `cs`, `after`, `ss`]
       mp_tac abi_native_result_enclosing_trace >> simp[abi_child_prefix_extends]) >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `dyn_ptr`, `head_offset`, `cs`, `ret`, `mid`,
    `ss`, `dst_addr`, `dyn_addr`, `payload`,
    `abi_allocation_windows (compiler_alloca_ids (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid) child_out`,
    `child_out`] mp_tac abi_memory_dynamic_child_run >> impl_tac
  >- (qpat_x_assum `after = _` (fn th => asm_simp_tac bool_ss [GSYM th])) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_encoding_result ctx func cs after ret (dst_addr + mload (w2n dyn_addr) ss) payload
    (abi_allocation_windows (compiler_alloca_ids (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid) child_out ++
      [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]) ss out` by
    (qpat_x_assum `after = _` SUBST1_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `allocation_growth child_out out` by
    (irule allocation_growth_map_eq >> fs[abi_allocator_state_eq]) >>
  `set (compiler_alloca_ids (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid) SUBSET
    set (compiler_alloca_ids cs after)` by
    (irule compiler_alloca_profile_subprofile >> simp[abi_child_prefix_extends]) >>
  qspecl_then [`child_out`, `out`,
    `compiler_alloca_ids (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid`,
    `compiler_alloca_ids cs after`, `[(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]`]
    mp_tac abi_allocation_scratch_subset >> impl_tac >- simp[] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `ret`, `dst_addr + mload (w2n dyn_addr) ss`, `payload`,
    `abi_allocation_windows (compiler_alloca_ids (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid) child_out ++
      [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]`,
    `abi_allocation_windows (compiler_alloca_ids cs after) out ++
      [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]`, `ss`, `out`]
    mp_tac abi_encoding_result_scratch_subset >> impl_tac >- simp[] >> DISCH_TAC >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss out` by
    (qspecl_then [`32`, `compiler_alloca_ids cs after`, `ss`, `child_out`, `ss`, `out`]
       mp_tac abi_allocation_trace_fields >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

Theorem abi_native_dynamic_child:
  !info span reference payload ctx func dst src dyn_ptr head_offset cs ret after ss
      dst_addr src_addr dyn_addr source_id target_id.
    abi_native_encoder info (w2n src_addr) span reference payload /\
    compile_abi_encode_child dst src info T head_offset dyn_ptr cs = (ret,after) /\
    fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_native_memory_ready func cs after source_id target_id src_addr span
      (dst_addr + mload (w2n dyn_addr) ss) payload ss /\
    mem_bytes_at (w2n src_addr) span reference = mem_bytes_at (w2n src_addr) span ss.vs_memory /\
    regions_disjoint (w2n (dst_addr + n2w head_offset)) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)
      (w2n (dst_addr + n2w head_offset)) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload) (w2n dyn_addr) 32 ==>
    ?out.
      abi_encoding_result ctx func cs after ret (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs after) out ++
          [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs after) ss out /\
      mload (w2n (dst_addr + n2w head_offset)) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _`
    (strip_assume_tac o PURE_REWRITE_RULE [compile_abi_child_dynamic_cuts]) >>
  drule_all abi_native_dynamic_child_cuts >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native dynamic recursive child execution: " ^ name)
  end) (DB.thms "abiNativeDynamicChild")
