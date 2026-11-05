(* Canonical constructor decoding with credit for actual allocation sites.
   TOP-LEVEL: compile_abi_decode_dload_actual_run.
   The constructor registration wrapper supplies the preallocated output. *)
Theory ctorAbiActual
Ancestors
  ctorAbiActualRecursive abiDecoderCounters ctorAbiActualFrame
  emitHelperProps arithmetic ctorAbiActualSites
  actualAllocExec actualDecoderSites abiDecoderCoherence abiDecoderTypedContract
  abiDecoderLoop abiEncoderRegisteredEffect abiDecoderCode
  exprLoweringProps fragExec allocaFrontierBound allocaBudgetProps
  abiEncoder compileEnv valueEncoding vyperABI contractABI
  venomState venomInst venomWf venomExecSemantics venomMemDefs
  words list finite_map pred_set

Theorem compile_abi_decode_dload_actual_run:
  !dst src hi ce env ty tv av v st st' ctx func site initial sb d.
    compile_abi_decode_to_buf dst src DLOAD hi
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),st') /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
      initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
    (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
      sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\
      h < dimword (:256)) /\
    (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
    fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (d,type_memory_bytes ce ty) (b,sz)) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      val_in_memory tv v d actual.vs_memory /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,type_memory_bytes ce ty)] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_var <= st'.cs_next_var` by
    (drule abi_decoder_variable_counter >> simp[]) >>
  `fresh_vars_wrt st' initial` by
    (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
  `ctor_actual_scratch func (frag_ids st st') d (type_memory_bytes ce ty) initial` by
    (simp_tac bool_ss [ctor_actual_scratch_def] >> first_assum ACCEPT_TAC) >>
  drule (BETA_RULE ctor_actual_coherent_run) >>
  disch_then (drule_at Any) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
  disch_then (qspecl_then [`ctx`, `site`, `d`] mp_tac) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  disch_then drule_all >> strip_tac >>
  qexists `actual` >> asm_rewrite_tac[] >>
  irule abi_encoder_registered_effect_enlarge >>
  goal_assum (drule_at Any) >>
  simp[ctor_actual_sites_subset]
QED
