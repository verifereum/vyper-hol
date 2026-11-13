(* Package the actual decoder's normal result in the existing caller post. *)
Theory abiDecodeMemBuiltinSuccess
Ancestors
  abiDecodeMemBuiltinFrame abiDecodeMemSiteEffect
  exprSimAbiDecodeBuiltinSetup exprSimAbiDecodeImmutableOutcome
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeResources exprSimAbiDecodeOblivious
  exprSimAbiDecodeCoverageBoundary exprSimAbiDecodeSetupExec
  abiBuiltinDecodeSetup abiBuiltinAllocation abiDecoderAppend abiDecoderFrame
  abiDecoderSiteEffect abiDecoderReentry actualDecoderSites allocaSiteResource
  allocationGrowth exprLoweringProps loweringStateRelDefs fragGasPathMem
  compileEnv venomState venomInst finite_map pred_set list arithmetic

Theorem abi_decode_mem_setup_growth[local]:
  abi_builtin_allocation_frame next site sz s u ==> allocation_growth s u
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, allocation_growth_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> Cases_on `site = id` >> gvs[]
QED

Theorem abi_decode_mem_success_allocation_rows[local]:
  lower_abi_decode data info lo hi sz st = (out,fin) /\
  fn_has_code st fin func /\
  FLOOKUP t.vs_allocas (abi_builtin_decode_output_site st lo hi) = SOME(d,sz) /\
  st.cs_next_id <= ready.cs_next_id /\
  (!b n. MEM (b,n) afp ==> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    ready.cs_next_id <= inst.inst_id /\ inst.inst_id < fin.cs_next_id /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,n)) ==>
  !b n. MEM (b,n) ((d,sz)::afp) ==> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    st.cs_next_id <= inst.inst_id /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,n)
Proof
  strip_tac >>
  `cs_extends st fin` by metis_tac[lower_abi_decode_frag_facts] >>
  drule abi_decode_lower_output_allocation >> strip_tac >>
  drule_all abi_decode_resources_code_member >> strip_tac >>
  `st.cs_next_id <= abi_builtin_decode_output_site st lo hi` by
    simp[abi_builtin_decode_output_site_def] >>
  rpt gen_tac >> simp_tac bool_ss [MEM, pairTheory.PAIR_EQ] >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  qpat_x_assum `!b n. MEM (b,n) afp ==> _` drule >> strip_tac >>
  rename1 `ready.cs_next_id <= child.inst_id` >>
  qexists_tac `child` >> simp[] >> decide_tac
QED

Theorem abi_decode_mem_builtin_success:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (out,fin) /\
  abi_builtin_decode_setup data (abi_static_size ce.ce_struct_fields ty)
    (abi_size_bound ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  fn_has_code st fin func /\ immutable_alloca_sep func ce cx es s /\
  abi_builtin_allocation_frame st.cs_next_var
    (abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty)) (type_memory_bytes ce ty) s u /\
  decode_static_frame s u /\ decode_site_resources ctx func u /\
  gas_path_mem ctx func s 0 (OK u) /\ gas_path_mem ctx func u 0 (OK t) /\
  decode_site_resources ctx func t /\ allocation_growth u t /\ decode_static_frame u t /\
  (!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op t = eval_operand op u) /\
  (!id. id < ready.cs_next_id \/ fin.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP u.vs_allocas id) /\
  abi_decoder_operand_live ready.cs_next_var out /\ eval_operand out u = SOME(n2w d) /\
  FLOOKUP u.vs_allocas
    (abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty)) = SOME(d,type_memory_bytes ce ty) /\
  evaluate_abi_decode env ty bs = INL v /\ val_in_memory tv v d t.vs_memory /\
  abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::afp) u t /\
  (!b n. MEM (b,n) afp ==> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    ready.cs_next_id <= inst.inst_id /\ inst.inst_id < fin.cs_next_id /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,n)) /\ ~t.vs_halted ==>
  abi_decode_immutable_success ce env ty tv bs out d st fin ctx func cx es s t /\
  gas_path_mem ctx func s 0 (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `st.cs_next_id <= ready.cs_next_id /\ st.cs_next_var <= ready.cs_next_var` by
    (fs[abi_builtin_decode_output_site_def] >> decide_tac) >>
  `allocation_growth s t` by
    metis_tac[abi_decode_mem_setup_growth, allocation_growth_trans] >>
  `FLOOKUP t.vs_allocas
    (abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty)) = SOME(d,type_memory_bytes ce ty)` by
    metis_tac[allocation_growth_old] >>
  `abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::afp) s t` by
    fs[abi_builtin_allocation_frame_def, abi_decode_footprint_frame_def] >>
  `!b n. MEM (b,n) ((d,type_memory_bytes ce ty)::afp) ==> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    st.cs_next_id <= inst.inst_id /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,n)` by
    (mp_tac (Q.INST [
       `info` |-> `type_to_abi_dec_info ce.ce_struct_fields ce ty`,
       `lo` |-> `abi_static_size ce.ce_struct_fields ty`,
       `hi` |-> `abi_size_bound ce.ce_struct_fields ty`,
       `sz` |-> `type_memory_bytes ce ty`] abi_decode_mem_success_allocation_rows) >>
     (impl_tac >- asm_rewrite_tac[]) >> simp[]) >>
  `abi_decode_immutable_memory ce cx es s t /\ abi_decode_window_frame func st s t` by
    metis_tac[abi_decode_mem_immutable_memory, abi_decode_mem_window_frame] >>
  `!b n. MEM (b,n) ((d,type_memory_bytes ce ty)::afp) ==> b+n <= t.vs_alloca_next` by
    (rpt strip_tac >> qpat_x_assum `!b n. MEM (b,n) ((d,_)::afp) ==> ?inst. _`
      drule >> strip_tac >> metis_tac[alloca_site_registered_below, decode_site_resources_def]) >>
  qabbrev_tac `writes = {a | d <= a /\ a < d+type_memory_bytes ce ty} UNION
    {a | s.vs_alloca_next <= a} UNION
    {a | ?id b sz. st.cs_next_id <= id /\ id < fin.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}` >>
  suspend "effect"
QED

Resume abi_decode_mem_builtin_success[effect]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `decode_site_effect ctx func st.cs_next_var writes u t` by
    (irule abi_decode_footprint_site_effect >> simp[] >> conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> _`
         irule >> metis_tac[abi_decoder_operand_live_mono]) >>
     qexists_tac `((d,type_memory_bytes ce ty)::afp)` >> simp[] >>
     rpt gen_tac >> simp_tac bool_ss [MEM, pairTheory.PAIR_EQ] >> strip_tac
     >- simp[Abbr`writes`] >>
     qpat_x_assum `!b n. MEM (b,n) afp ==> _` drule >> strip_tac >>
     simp[Abbr`writes`] >> disj2_tac >>
     qexistsl_tac [`inst.inst_id`,`b`,`n`] >> simp[] >> decide_tac) >>
  `decode_site_effect ctx func st.cs_next_var writes s t` by
    (drule_all abi_decode_builtin_setup_effect >> strip_tac >>
     drule_all decode_site_effect_trans >> simp[]) >>
  `!id. id < st.cs_next_id \/ fin.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (drule abi_decode_output_site_interval >> strip_tac >> rpt strip_tac >>
     `id < ready.cs_next_id \/ fin.cs_next_id <= id` by decide_tac >>
     `id <> abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields ty)
       (abi_size_bound ce.ce_struct_fields ty)` by decide_tac >>
     metis_tac[abi_builtin_allocation_frame_outside]) >>
  `eval_operand out t = SOME(n2w d)` by metis_tac[] >>
  `abi_decode_success_post ce env ty tv bs out d st fin ctx func s t` by
    (rewrite_tac[abi_decode_success_post_def] >> qexists_tac `v` >>
     unabbrev_all_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_success_closed ce env ty tv bs out d st fin ctx func s t` by
    (simp[abi_decode_success_closed_def, abi_decode_allocation_growth_floor] >>
     qexistsl_tac [`t`,`t.vs_returndata`,`t.vs_prev_bb`] >> simp[]) >>
  simp[abi_decode_immutable_success_def] >> metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Finalise abi_decode_mem_builtin_success
