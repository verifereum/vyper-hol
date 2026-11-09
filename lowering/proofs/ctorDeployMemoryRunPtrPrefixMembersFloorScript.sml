(* Allocation-aware member contract, with a single semantic and ghost endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixMembersFloor
Ancestors
  valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixMembers ctorDeployMemoryRunPtrPrefixAllocationFloor
  abiDecoderMembers abiDecoderMemberInfos abiDecoderEmpty abiDecoderEmptyMember
  ctorAbiActualMembers ctorAbiActualEmpty abiEncoderRegisteredEffect
  abiDecoderCoherence abiDecoderContract abiDecoderTypedContract
  abiDecoderLoop fragExec compileEnv valueEncoding abiEncoder contractABI
  allocaFrontierBound allocaBudgetProps abiDecoderReentryPointer
  ctorDeployMemoryRunPtrPrefixCanonical ptrDiscipline ptrSafeRun
  finite_map pred_set words list rich_list arithmetic

val paired_members_floor = ``\tys tvs.
 !dst src st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs G tn b sz Ddead lo PG.
 compile_abi_decode_complex_elems (Var dst) src DLOAD (Lit 0w)
   (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                          op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_paired_members_nil_floor:
  (^paired_members_floor) [] []
Proof
  BETA_TAC >> rpt gen_tac >>
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
       comp_return_def, Excl "enc_def"] >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >> gvs[Excl "enc_def"] >>
  qexistsl_tac [`initial`,`G`,`tn`,`{}`] >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED
