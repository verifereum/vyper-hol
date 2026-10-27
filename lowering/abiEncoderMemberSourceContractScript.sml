(* Uniform source core contract for the indexed member generator.  Value
   data are ghost indices; no member-list execution owner is imported. *)
Theory abiEncoderMemberSourceContract
Ancestors
  abiEncoderMemberSpine abiEncoderCorrect abiEncoderInput abiDecoderEffect
  abiDecoderContract abiDecoderLoop abiDecoderProtectedScratch abiDecoderReentry
  fragExec compileEnv valueEncoding venomState finite_map

Definition abi_encoder_member_core_pre_def:
  abi_encoder_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (ei,dst,src,st,en,out) s <=>
    abi_encoder_correct ei /\
    abi_encoder_pre ei at av st src dst sb source_cap d b cap s /\
    abi_decoder_budget first last b cap s /\
    first <= st.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_member_core_post_def:
  abi_encoder_member_core_post (ctx,func) (at,av,sb,source_cap,d)
      (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t
End

Theorem abi_encoder_member_source_core_run:
  abi_encoder_spine_core_code func c /\ abi_encoder_member_core_pre value resources c s ==>
  ?t. abi_decode_sim ctx func s t /\
    abi_encoder_member_core_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_spine_core_code_def, abi_encoder_member_core_pre_def,
    abi_encoder_member_core_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_correct_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_encoder_member_source_child_run:
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_member_core_pre value resources)
    (abi_encoder_member_core_post (ctx,func) value resources) c s ==>
  ?t. abi_encoder_spine_child (\c r u. abi_decode_sim ctx func r u) c s t /\
    abi_encoder_spine_child_output
      (abi_encoder_member_core_post (ctx,func) value resources) c s t
Proof
  strip_tac >> irule abi_encoder_spine_child_generate >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  irule abi_encoder_member_source_core_run >> asm_rewrite_tac []
QED

(* Saved cursor operands are observations transported by the genuine core
   effect, not an additional execution contract. *)
Theorem abi_encoder_member_source_core_saved:
  abi_encoder_member_core_post (ctx,func) (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,start,en,out) initial actual /\
  first <= site /\ site < last /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  (!op w. abi_decoder_operand_live start.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_decoder_budget first last b cap actual
Proof
  simp_tac bool_ss [abi_encoder_member_core_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_effect_protected_slot >>
  disch_then (qspecl_then [`slot`, `site`] mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  `!op w. abi_decoder_operand_live start.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (fs[abi_decoder_effect_def] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> fs[abi_decoder_effect_def] >> metis_tac[]
QED

val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiEncoderStatic", "abiEncoderDynamic", "abiEncoderMemberSourcePhase", "abiEncoderMembersDefs",
        "abiScratchStatic", "abiScratchDynamicChild", "abiScratchMemberStep", "abiScratchComplex",
        "abiEncoderMemberSpineCompat", "abiEncoderMemberPhaseExec", "abiEncoderMember",
        "abiScratchMembers", "abiEncoderMembersCorrect", "abiEncoderComplexStatic"]
  then raise Fail "source core contract imports a member execution owner"
  else ();

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then ()
    else raise Fail "source core contract has an admission or axiom"
  end) [abi_encoder_member_source_core_run, abi_encoder_member_source_child_run,
    abi_encoder_member_source_core_saved];
