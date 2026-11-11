(* Uniform caller-counted return decoding, hiding compiler fragment shape. *)
Theory extcallReturnUnifiedCounted
Ancestors
  extcallReturnStraightCounted extcallReturnRelabelCounted
  extcallReturnSyntax extcallReturnLabelSyntax abiMalformedRecursiveInterface
  abiValidAllocatedContract abiMalformedSiteFrame abiEncoderObserver
  fragGasMode fragExec compileEnv venomState venomInst list finite_map

(* Operand liveness permits Label. These syntactic premises are supplied by
   caller safe operands, the allocated destination Var and the size-prefix
   result; they must not be inferred from malformed-entry liveness. *)
Theorem return_capped_counted_success:
  cs_extends st en /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (!l. dst <> Label l /\ base_op <> Label l /\ hi <> Label l) /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v /\
  abi_decoder_coherent ce env sf rt tv /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ceiling u. gas_marked_path F ctx func s 0 (OK u) /\
    u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s u /\
    val_in_memory tv rv d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) s u /\
    fresh_vars_wrt ceiling u /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `st.cs_blocks = en.cs_blocks`
  >- (irule return_capped_straight_counted_success >> metis_tac[]) >>
  irule return_capped_relabel_counted_success >>
  `frag_ops_free st en` by metis_tac[return_decoder_ops_free] >>
  `~MEM en.cs_current_bb
     (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st en)))` by
    metis_tac[return_decoder_endpoint_label] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code st en))` by
    metis_tac[return_decoder_fragment_ids] >>
  metis_tac[]
QED
