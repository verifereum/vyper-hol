(* Reach a heterogeneous child's real entry point from canonical parent bytes.
   TOP-LEVEL: abi_decoder_member_prepare.
   Helper: canonical inputs for the emitted setup. *)
Theory abiDecoderMemberPrepare
Ancestors
  abiDecoderMemberCode abiDecoderMemberEntry abiDecoderMemberInputs abiDecoderMemberSetup
  abiDecoderMembers abiDecoderMemberSlice abiDecoderCoherence abiDecoderDynamic
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderTypedContract abiDecoderContract
  abiDecodeRanges vyperABI compileEnv valueEncoding contractABI
  venomState words list rich_list arithmetic

Theorem abi_decoder_member_prepare_inputs:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) ==>
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) : bytes32) s =
      n2w (head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
        SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)) /\
    sb + (head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
      SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)) < dimword (:256)) /\
  abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) =
    if abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) then
      head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
        SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)
    else SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `av` |-> `av`, `avs` |-> `avs`]
    abi_decoder_canonical_member_inputs) >>
  impl_tac >- gvs[MAP_APPEND, Excl "enc_def"] >> strip_tac >>
  gvs[MAP_APPEND, Excl "enc_def"]
QED

Theorem abi_decoder_member_prepare:
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  fn_has_code st middle func /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation middle.cs_next_id last b cap initial /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      middle last (FST ops) (SND ops) opc hi
      (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
        (preavs ++ av::avs) (LENGTH pretys))
      (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap
      (abi_decoder_prune_vars middle.cs_next_var prepared) /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_member_prepare_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= middle.cs_next_var` by
    (Cases_on `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` >>
     Cases_on `hi = Lit 0w` >> gvs[Excl "enc_def"]) >>
  mp_tac (Q.INST [`st'` |-> `middle`,
    `dyn` |-> `abi_decoder_dynamic (type_to_abi_dec_info
      (sf:string |-> (string # vyperAST$type # num) list) ce ty)`,
    `ao` |-> `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`,
    `payload_off` |-> `head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
      SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)`]
    abi_decode_member_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys)))`
    by asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`child_st` |-> `middle`, `childsrc` |-> `FST (ops:operand # operand)`,
    `childdst` |-> `SND (ops:operand # operand)`,
    `next` |-> `st.cs_next_var`, `before` |-> `initial:venom_state`, `after` |-> `prepared:venom_state`]
    abi_decoder_member_pre_address) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member preparation not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberPrepare");
