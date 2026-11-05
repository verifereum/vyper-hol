(* The external-return caller supplies room for the function's actual
   allocations, including reused scratch sites, and an actual read window. *)
Theory abiEncoderWindowRun
Ancestors
  abiEncoderWindowArray abiEncoderWindowComplex abiEncoderWindowBytes
  abiEncoderWindowLeaves abiEncoderWindowContract
  abiEncoderWindow abiEncoderAdmissible abiEncoderRegisteredEffect
  abiEncoderSharedRecursive abiEncoderExtendSim abiDecoderLoop
  abiEncoderProps exprLoweringProps fragExec compileEnv
  venomState venomInst venomExecSemantics venomMemDefs venomWf
  contractABI valueEncoding words list finite_map pred_set

Theorem window_strong_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==> window_strong_contract ei) /\
  (!infos. abi_encoder_members_admissible infos ==>
    EVERY (\(ei,_,_,_). window_strong_contract ei) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rw[abi_encoder_admissible_def, EVERY_DEF, window_word_contract,
     window_copy_contract, window_bytes_contract] >> gvs[]
  >- (irule window_array_strong_contract >> simp[])
  >- (irule window_array_strong_contract >> simp[]) >>
  irule window_complex_strong_contract >>
  fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem compile_abi_encode_to_buf_window_run:
  !dst src ei st out st' ctx func initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    sb + source_cap <= initial.vs_alloca_next /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,source_cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,LENGTH (enc at av))] initial actual /\
      alloca_inv actual /\ alloca_room ctx func actual /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
             lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\
      actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> strip_tac >>
  `window_strong_contract ei` by
    metis_tac[cj 1 window_strong_admissible_mutual] >>
  drule window_strong_contract_public >>
  simp_tac bool_ss [abi_encoder_window_contract_def] >>
  disch_then drule >>
  strip_tac >>
  `abi_encoder_window_pre ctx func st st' dst src ei at av sb source_cap d initial` by
    asm_rewrite_tac[abi_encoder_window_pre_def] >>
  first_x_assum drule >>
  simp_tac bool_ss [abi_encoder_window_result_def]
QED
