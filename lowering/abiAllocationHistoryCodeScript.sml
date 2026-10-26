(* Derive declared sizes for existing runtime allocations, including reused
   decoder sites. Allocation history is partial: unexecuted sites are absent. *)
Theory abiAllocationHistoryCode
Ancestors
  abiAllocationHistory abiDecoderCode abiDecoderAllocation localPtrsProps
  loweringMemSafetyDefs venomState venomInst finite_map pred_set list words relation

Theorem abi_alloca_history_function_size:
  abi_alloca_history (fn_insts func) s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_operands = [Lit n] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==> sz = w2n n
Proof
  strip_tac >>
  qhdtm_x_assum `abi_alloca_history`
    (mp_tac o PURE_REWRITE_RULE [abi_alloca_history_def]) >>
  disch_then (qspecl_then [`inst.inst_id`, `off`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `MEM witness (fn_insts func)` >>
  `witness = inst` by (drule_all fn_inst_ids_distinct_inj >> simp[]) >>
  gvs[]
QED

Theorem abi_alloca_history_code_sizes:
  abi_alloca_history code s /\
  (!inst. MEM inst code /\ inst.inst_id IN ids /\ inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w]) ==>
  !id off sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32
Proof
  simp_tac bool_ss [abi_alloca_history_def] >> rpt strip_tac >>
  qpat_x_assum `!id off sz. _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `!inst. _` drule_all >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem abi_alloca_history_decoder_sizes:
  abi_alloca_history code s /\ abi_decoder_code start end_st /\
  (!inst. MEM inst code /\ start.cs_next_id <= inst.inst_id /\
    inst.inst_id < end_st.cs_next_id ==> abi_decoder_code_member inst end_st) /\
  (!inst. abi_decoder_code_member inst start ==> inst.inst_id < start.cs_next_id) ==>
  !id off sz. id IN abi_decoder_ids start.cs_next_id end_st.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`code` |-> `code`,
    `ids` |-> `abi_decoder_ids start.cs_next_id end_st.cs_next_id`]
    abi_alloca_history_code_sizes) >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_code_member inst end_st` by
    (qpat_x_assum `!inst. MEM inst code /\ _ ==> _` irule >>
     fs[abi_decoder_ids_def]) >>
  `~abi_decoder_code_member inst start` by
    (strip_tac >> qpat_x_assum `!inst. abi_decoder_code_member inst start ==> _`
      drule >> fs[abi_decoder_ids_def]) >>
  drule_all abi_decoder_code_alloca >> simp[]
QED

Theorem abi_alloca_history_blocks_member:
  !blocks. MEM bb blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem abi_alloca_history_fn_member:
  MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts func)
Proof
  simp[fn_insts_def] >> metis_tac[abi_alloca_history_blocks_member]
QED

Theorem abi_alloca_history_function_reachable:
  reachable_by_execution func s t /\ abi_alloca_history (fn_insts func) s ==>
  abi_alloca_history (fn_insts func) t
Proof
  simp_tac bool_ss [reachable_by_execution_def] >> strip_tac >>
  irule abi_alloca_history_reachable >> qexists_tac `s` >> simp[] >>
  qpat_x_assum `RTC _ s t` mp_tac >>
  match_mp_tac RTC_MONOTONE >> simp_tac bool_ss [] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  drule_all abi_alloca_history_fn_member >> simp[]
QED

Theorem abi_alloca_history_function_initial:
  reachable_by_execution func s t /\ s.vs_allocas = FEMPTY ==>
  abi_alloca_history (fn_insts func) t
Proof
  strip_tac >> irule abi_alloca_history_function_reachable >>
  qexists_tac `s` >> simp[abi_alloca_history_empty]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ALLOCATION_HISTORY_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI allocation history code not kernel closed: " ^ n)
  end) (DB.thms "abiAllocationHistoryCode");

