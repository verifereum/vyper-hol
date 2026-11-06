(* The abi_decode builtin's decoder on arbitrary memory input: it either
   decodes the bytes as evaluate_abi_decode does, or reverts exactly when
   evaluate_abi_decode rejects them. *)
Theory exprSimAbiDecodeBuiltin
Ancestors
  abiBuiltinDecodeCorrect abiBuiltinSource abiBuiltinDecodeEffect
  exprSimAbiDecodeTupleSource exprSimAbiDecodeMemberOutcome
  exprSimAbiDecodeCompositePrefix exprSimAbiDecodeMemberReject
  builtinAbi fragExec vyperABI venomState venomExecSemantics
  abiDecoderSiteEffect actualDecoderSites
  exprSimAbiDecodeBuiltinLayout exprSimAbiDecodeRecursiveClosure
  exprSimAbiDecodeBuiltinHeader abiBuiltinDecodeSetup abiBuiltinDecodeHeader
  abiBuiltinAllocation emitHelperProps exprLoweringProps valueEncoding
  abiDecoderFiniteControl words compileEnv valueEncodingProps arithmetic list finite_map

(* Resources for the decode on arbitrary input, per allocation site: the
   source lies below the next allocation and away from the output and from
   the fragment's allocations (IDs st.cs_next_id .. last) that already
   exist (a decode re-run in a loop reuses its sites), and the
   registered function's allocation sites have room (decode_site_resources).
   The size guard is not assumed: on arbitrary input it is what the emitted
   size check tests. *)
Definition abi_builtin_decode_site_resources_def:
  abi_builtin_decode_site_resources ctx func st last min_size max_size outsz cnt p d s <=>
    max_size < dimword (:256) /\ p + 32 + cnt <= s.vs_alloca_next /\
    d + outsz < dimword (:256) /\ abi_footprint_disjoint (p + 32) cnt [(d,outsz)] /\
    (!id b sz. st.cs_next_id <= id /\ id < last /\
       FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
       abi_footprint_disjoint (p + 32) cnt [(b,sz)]) /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,outsz))
End

Theorem abi_decode_builtin_min_le_max[local]:
  abi_static_size sf ty <= abi_size_bound sf ty
Proof
  Cases_on `ty`
  >- (Cases_on `b` >> simp[abi_static_size_def, abi_size_bound_def] >>
      Cases_on `b'` >> simp[abi_static_size_def, abi_size_bound_def]) >>
  simp[abi_static_size_def, abi_size_bound_def, abi_embedded_static_size_def]
  >- (Induct_on `l` >> simp[] >> gen_tac >> decide_tac)
  >- (Cases_on `b` >> simp[abi_static_size_def, abi_size_bound_def,
         abi_embedded_static_size_def, LEFT_ADD_DISTRIB]) >>
  Cases_on `p` >> simp[abi_static_size_def, abi_size_bound_def] >>
  CASE_TAC >> simp[abi_embedded_static_size_def] >>
  pop_assum kall_tac >> Induct_on `x` >> simp[] >> gen_tac >> decide_tac
QED

Theorem abi_decode_builtin_setup_abort:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  fn_has_code st ready fn /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dabort ctx fn s Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st header_st /\ cs_extends header_st ready` by
    (conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st header_st fn` by metis_tac[fn_has_code_split] >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decode_builtin_header_abort >> simp[]
QED

Theorem lower_abi_decode_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  !s0. eval_operand data s0 = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s0.vs_memory /\
    abi_builtin_decode_site_resources ctx func start final.cs_next_id
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (LENGTH bs) p d s0 /\
    fresh_vars_wrt limit_st s0 ==>
  !fn. fn_has_code start final fn /\ fn_inst_ids_distinct fn /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) /\
    (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
     !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = start.cs_current_bb /\
    s0.vs_inst_idx = LENGTH start.cs_current_insts ==>
    (?t v. evaluate_abi_decode env ty bs = INL v /\
       eval_operand out t = SOME (n2w d) /\ val_in_memory tv v d t.vs_memory /\
       fresh_vars_wrt limit_st t /\
       decode_site_effect ctx func start.cs_next_var
         ({a | d <= a /\ a < d + type_memory_bytes ce ty} UNION
          {a | s0.vs_alloca_next <= a} UNION
          {a | ?id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
                 FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz})
         s0 t /\
       (!id. id < start.cs_next_id \/ final.cs_next_id <= id ==>
             FLOOKUP t.vs_allocas id = FLOOKUP s0.vs_allocas id) /\
       ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
       t.vs_inst_idx = LENGTH final.cs_current_insts /\
       !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s0 = r) \/
    (?fuel r e u. run_from fuel ctx fn s0 = r /\ exit_result r /\
       r = Abort Revert_abort u /\ evaluate_abi_decode env ty bs = INR e)
Proof
  ntac 3 (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     PURE_REWRITE_RULE [abi_builtin_decode_site_resources_def]) >>
  `s0.vs_alloca_next < dimword(:256)` by
    (fs[decode_site_resources_def, alloca_room_def] >> decide_tac) >>
  `p < dimword(:256) /\ LENGTH bs < dimword(:256) /\
   abi_static_size ce.ce_struct_fields ty < dimword(:256)` by
    (`abi_static_size ce.ce_struct_fields ty <= abi_size_bound ce.ce_struct_fields ty`
       by simp[abi_decode_builtin_min_le_max] >> decide_tac) >>
  `mload p s0 = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload] >>
  Cases_on `abi_static_size ce.ce_struct_fields ty <= LENGTH bs /\
            LENGTH bs <= abi_size_bound ce.ce_struct_fields ty`
  >- cheat >>
  disj2_tac >>
  `evaluate_abi_decode env ty bs = INR "abi_decode invalid"` by
    metis_tac[abi_decode_builtin_guard_reject] >>
  `mload (w2n (n2w p:bytes32)) s0 = n2w (LENGTH bs)` by simp[w2n_n2w] >>
  drule_all abi_decode_builtin_setup_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  fs[Dabort_def] >> metis_tac[exit_result_def]
QED
