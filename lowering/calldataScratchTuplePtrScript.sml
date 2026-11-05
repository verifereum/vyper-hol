(* Heterogeneous calldata member traversal with original-state scratch ghosts. *)
Theory calldataScratchTuplePtr
Ancestors calldataScratchBytesPtr decoderNavigationPtr abiScratchDecoderTuple
  abiScratchDecoderMemberCons abiScratchDecoderMembersContract
  abiDecoderMemberInfos abiScratchLeafEffect abiDecoderLoop abiDecoderFrame
  abiScratchEncoderContract abiEncoder abiDecoderContract exprLowering compileEnv valueEncoding
  venomState venomExecSemantics bodyPtrDefs ptrDiscipline list arithmetic

(* The empty suffix executes no instructions, even after an arbitrary prefix.
   Keep the entire root allocation and arbitrary protected memory in the interface. *)
Theorem calldata_scratch_members_nil_ptr:
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) []
    ao vo start = ((),end_st) /\
  abi_decoder_budget first last b cap initial /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial outsz /\ allocas_from lower initial /\
  DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory [] [] (d + vo) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory [] [] (d + vo) mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st (d + vo) 0 b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual outsz /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  simp_tac (srw_ss()) [Once compile_abi_decode_to_buf_def, comp_return_def] >>
  rpt strip_tac >>
  qexistsl_tac [`initial`, `G`, `tn`] >>
  simp[val_in_memory_def, abi_decode_sim_refl] >>
  irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED
