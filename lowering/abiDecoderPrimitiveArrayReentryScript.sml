(* A complete clamped primitive-array child can execute repeatedly in an outer loop. *)
Theory abiDecoderPrimitiveArrayReentry
Ancestors
  abiDecoderPrimitiveArrayReentryInit abiDecoderPrimitiveArrayCode abiDecoderPrimitiveArray
  abiDecoderBulkReentry
  abiDecoderArrayInitReentry abiDecoderArrayInitReach abiDecoderArrayInitMemory abiDecoderArrayInitExec
  abiDecoderPrimitiveLoopEntry abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopContext
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry abiDecoderAllocation
  abiDecoderProtectedScratch abiDecoderLoop abiDecoderContract abiDecoderFrame fragExec
  compileEnv venomState valueEncoding finite_map words list arithmetic

Theorem abi_decoder_clamped_array_reentry:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot site.
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    b <= slot /\ slot + 32 <= b + cap /\ st.cs_next_id <= site /\ site < end_st.cs_next_id /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    (!id. id <> site ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] initial t /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_reentry_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_code >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_primitive_array_reentry_initialize >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_primitive_dyn_loop >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_loop_rel _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_rel_def]) >>
  `abi_decoder_budget first last b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op t = SOME w` by metis_tac[abi_decoder_operand_live_mono] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)]
    initial prepared` by (irule abi_decoder_array_init_frame_widen >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)]
    initial t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial t` by (drule_all abi_decoder_loop_frame_to_arena >> simp[]) >>
  `abi_decode_sim ctx fn initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]) >>
  qexistsl_tac [`t`, `slot`, `loop_st.cs_next_id - 2`] >>
  asm_simp_tac bool_ss [] >> simp[] >> decide_tac
QED

Theorem abi_decoder_clamped_array_reentry_protected:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!other protected. other IN abi_decoder_ids first last /\
      (other < st.cs_next_id \/ end_st.cs_next_id <= other) /\
      FLOOKUP initial.vs_allocas other = SOME (protected,32) ==>
      mload protected t = mload protected initial) /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_clamped_array_reentry >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `t:venom_state`,
    `child_first` |-> `st.cs_next_id`, `child_last` |-> `end_st.cs_next_id`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_decoder_child_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  `!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> `id <> site` by decide_tac >> metis_tac[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_decoder_primitive_array_reentry:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  fn_has_code st end_st fn /\
  (dec_info_needs_clamp (DecPrimWord clamp) ==>
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!other protected. other IN abi_decoder_ids first last /\
      (other < st.cs_next_id \/ end_st.cs_next_id <= other) /\
      FLOOKUP initial.vs_allocas other = SOME (protected,32) ==>
      mload protected t = mload protected initial) /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_pruned_operands >> strip_tac >>
  Cases_on `dec_info_needs_clamp (DecPrimWord clamp)`
  >- (
      `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      drule_all abi_decoder_clamped_array_reentry_protected >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  drule_all abi_decoder_bulk_reentry_protected >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> rpt strip_tac >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_ARRAY_REENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive array repeated execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveArrayReentry");
