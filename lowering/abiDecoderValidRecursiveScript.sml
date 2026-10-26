(* Structural decoder closure from coherent metadata and actual source validity.
   Empty dynamic fixed-array members use their inline head without a payload read. *)
Theory abiDecoderValidRecursive
Ancestors
  abiDecoderOffsetHead abiDecoderReadableTypes abiDecoderValidContract abiDecoderValidLeaves abiDecoderValidArray
  abiDecoderValidFixed abiDecoderValidTuple abiDecoderValidStruct abiDecoderCoherence
  abiDecoderTypedContract abiDecoderEffect abiDecoderContract abiDecoderReentry abiDecoderLoop
  abiEncoder fragExec compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState venomExecSemantics words list

Theorem abi_decoder_valid_readable_array:
  (abi_decoder_readable_type env ty ==> abi_decoder_valid_correct ce env sf ty tv) /\
  abi_decoder_readable_type env (ArrayT ty bound) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  simp_tac bool_ss [abi_decoder_readable_array_iff] >> strip_tac >>
  `abi_decoder_valid_correct ce env sf ty tv` by metis_tac[] >>
  drule abi_decoder_readable_type_head >> disch_then assume_tac >>
  Cases_on `bound` >>
  FIRST [irule abi_decoder_valid_correct_array, irule abi_decoder_valid_correct_fixed_array] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_readable_members:
  LIST_REL (\ty tv. abi_decoder_readable_type env ty ==> abi_decoder_valid_correct ce env sf ty tv)
    tys tvs /\ EVERY (abi_decoder_readable_type env) tys ==>
  LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs /\
  EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) tys
Proof
  strip_tac >> drule_all abi_decoder_readable_list_relation >> strip_tac >>
  drule abi_decoder_readable_members_head >> simp[]
QED

Theorem abi_decoder_valid_readable_tuple:
  LIST_REL (\ty tv. abi_decoder_readable_type env ty ==> abi_decoder_valid_correct ce env sf ty tv)
    tys tvs /\ abi_decoder_readable_type env (TupleT tys) ==>
  abi_decoder_valid_correct ce env sf (TupleT tys) (TupleTV tvs)
Proof
  simp_tac bool_ss [abi_decoder_readable_tuple_iff] >> strip_tac >>
  drule_all abi_decoder_valid_readable_members >> strip_tac >>
  irule abi_decoder_valid_correct_tuple >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_readable_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (\ty tv. abi_decoder_readable_type (env \\ nsid) ty ==>
    abi_decoder_valid_correct ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv) (MAP SND args) tvs /\
  abi_decoder_readable_type env (StructT nsid) ==>
  abi_decoder_valid_correct ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> drule abi_decoder_readable_struct_iff >> strip_tac >>
  `EVERY (abi_decoder_readable_type (env \\ nsid)) (MAP SND args)` by metis_tac[] >>
  drule_all abi_decoder_valid_readable_members >> strip_tac >>
  irule abi_decoder_valid_correct_struct >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_evaluated_array:
  abi_decoder_valid_correct ce env sf ty tv /\
  evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_evaluated_array_head >> disch_then assume_tac >>
  Cases_on `bound` >>
  FIRST [irule abi_decoder_valid_correct_array, irule abi_decoder_valid_correct_fixed_array] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_coherent_correct:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_decoder_valid_correct ce env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[abi_decoder_valid_correct_base]
  >- simp[abi_decoder_valid_correct_flag]
  >- (rpt strip_tac >>
      rename1 `abi_decoder_header ce env (ArrayT elem bound) (ArrayTV elem_tv bound)` >>
      `evaluate_type env (ArrayT elem bound) = SOME (ArrayTV elem_tv bound)` by
        fs[abi_decoder_header_def] >>
      irule abi_decoder_valid_evaluated_array >> asm_simp_tac bool_ss [])
  >- (rpt strip_tac >> irule abi_decoder_valid_correct_tuple >> asm_simp_tac bool_ss []) >>
  rpt strip_tac >> irule abi_decoder_valid_correct_struct >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_decode:
  compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf ty tv bs v start src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_valid_pre_def] >>
  `abi_decoder_valid_correct ce env sf ty tv` by
    (drule_all abi_decoder_valid_coherent_correct >> simp[]) >>
  mp_tac abi_decoder_valid_correct_run >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_RECURSIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid structural decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidRecursive");
