Theory exprSimAbiEncodeConcreteResources
Ancestors
  exprSimAbiEncodeConcreteBuiltinWrappers abiEncodeWindowBuiltin
  abiBuiltinEncodeCorrect abiBuiltinAllocation abiBuiltinEncodeSetup abiEncoderWindowContract
  abiDecoderContract abiEncoderAdmissible venomMemDefs venomState
  compileEnv finite_map words list

(* This is only field transport. The producer must establish the resource
   premises about the pure allocated state before applying this boundary. *)
Theorem abi_encode_setup_window_pre:
  let allocated = abi_builtin_allocate_state site outsz initial in
  abi_builtin_encode_setup_frame next site outsz p write_size initial actual /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap actual.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live next src /\
  eval_operand dst actual = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x) /\
  fn_has_code body_st body_end func /\ fn_inst_ids_distinct func /\
  alloca_inv allocated /\ alloca_room ctx func allocated /\
  sb+cap <= allocated.vs_alloca_next /\
  d+LENGTH (enc at av) <= allocated.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids body_st body_end /\
    FLOOKUP allocated.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~actual.vs_halted /\ actual.vs_current_bb = body_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH body_st.cs_current_insts ==>
  abi_encoder_window_pre ctx func body_st body_end dst src ei at av sb cap d actual
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `actual.vs_allocas = (abi_builtin_allocate_state site outsz initial).vs_allocas /\
   actual.vs_alloca_next = (abi_builtin_allocate_state site outsz initial).vs_alloca_next` by
    metis_tac[abi_window_setup_allocas, abi_window_setup_frontier] >>
  `alloca_inv actual /\ alloca_room ctx func actual` by
    metis_tac[abi_window_setup_alloca_inv, abi_window_setup_room] >>
  `eval_operand src actual = SOME (n2w sb)` by
    (fs[abi_builtin_encode_setup_frame_def] >> metis_tac[]) >>
  pure_rewrite_tac[abi_encoder_window_pre_def] >>
  pure_asm_rewrite_tac[] >> metis_tac[]
QED
