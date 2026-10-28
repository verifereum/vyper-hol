(* TOP-LEVEL: the parent cursor is backed by its actual allocation
   instruction. Compiler membership and function ID uniqueness keep its
   allocation identity outside every recursive child's local profile. *)
Theory abiNativeCursor
Ancestors
  abiNativeReadFrame abiAllocatedWindows abiWriterFrame allocationGrowth
  compileAllocaProfiles compileAllocaProvenance compileEnv venomState venomInst list words

Definition abi_native_cursor_def:
  abi_native_cursor func root_cs root_after counter_inst (dyn_addr:bytes32) cs ss <=>
    MEM counter_inst.inst_id (compiler_alloca_ids root_cs root_after) /\
    MEM counter_inst (fn_insts func) /\ compiler_instruction_member cs counter_inst /\
    abi_allocated_window ss counter_inst.inst_id (w2n dyn_addr) 32
End

Theorem abi_native_cursor_step:
  !func root_cs root_after counter_inst dyn_addr cs ss mid out.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    cs_extends cs mid /\ allocation_growth ss out ==>
    abi_native_cursor func root_cs root_after counter_inst dyn_addr mid out
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_cursor_def] >> strip_tac >>
  `compiler_instruction_member mid counter_inst` by
    (drule_all compiler_instruction_member_extends >> simp[]) >>
  `abi_allocated_window out counter_inst.inst_id (w2n dyn_addr) 32` by
    (qspecl_then [`ss`, `out`, `counter_inst.inst_id`, `w2n dyn_addr`, `32`]
       mp_tac allocation_growth_window >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_cursor_local_exclusion:
  !func root_cs root_after counter_inst dyn_addr cs ss mid.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    fn_inst_ids_distinct func /\ cs_extends cs mid /\ fn_has_code cs mid func ==>
    ~MEM counter_inst.inst_id (compiler_alloca_ids cs mid)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_cursor_def] >> strip_tac >>
  drule_all abi_native_old_instruction_not_scratch >> simp[]
QED

Theorem abi_native_cursor_root_distinct:
  !func root_cs root_after counter_inst dyn_addr cs ss source_id target_id.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after) ==>
    counter_inst.inst_id <> source_id /\ counter_inst.inst_id <> target_id
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_cursor_def] >> strip_tac >>
  conj_tac >> DISCH_TAC >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native parent cursor ownership: " ^ name)
  end) (DB.thms "abiNativeCursor")
