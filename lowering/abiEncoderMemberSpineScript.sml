(* Concrete member certificates. Only recursive to-buffer calls are abstract. *)
Theory abiEncoderMemberSpine
Ancestors
  abiEncoderMemberPhaseRaw abiEncoderChildCode abiEncoderMemberCode abiEncoder
  compileEnv emitHelper venomInst venomState words list

Definition abi_encoder_spine_call_def:
  abi_encoder_spine_call core_run (ei,dst,src,st,en,out) s t <=>
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    core_run (ei,dst,src,st,en,out) s t
End

Definition abi_encoder_spine_child_def:
  abi_encoder_spine_child core_run (ei,dyn,dst,src,ho,dp,st,en,out) s t <=>
    if dyn then
      ?ops p len ce r u.
        abi_encode_child_prefix dst ho dp st = (ops,p) /\
        abi_encoder_member_phase_raw st p s r /\
        abi_encoder_spine_call core_run (ei,SND (SND ops),src,p,ce,len) r u /\
        abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len ce = (out,en) /\
        abi_encoder_member_phase_raw ce en u t
    else
      ?head p r.
        emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
        abi_encoder_member_phase_raw st p s r /\
        abi_encoder_spine_call core_run (ei,head,src,p,en,out) r t
End

Definition abi_encoder_member_spine_def:
  (abi_encoder_member_spine core_run (dst,src,dp) [] (st,so,ho) (out,en) s t <=>
    compile_abi_encode_complex_elems dst src [] so ho dp st = (out,en) /\ t=s) /\
  (abi_encoder_member_spine core_run (dst,src,dp) ((ei,az,mz,dyn)::rest)
      (st,so,ho) (out,en) s t <=>
    ?elem_src p len ce r u.
      emit_op ADD [src;Lit (n2w so)] st = (elem_src,p) /\
      abi_encoder_member_phase_raw st p s r /\
      abi_encoder_spine_child core_run (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r u /\
      abi_encoder_member_spine core_run (dst,src,dp) rest
        (ce,so+mz,ho+az) (out,en) u t)
End

Theorem abi_encoder_spine_child_compile:
  abi_encoder_spine_child core_run (ei,dyn,dst,src,ho,dp,st,en,out) s t ==>
  compile_abi_encode_child dst src ei dyn ho dp st = (out,en)
Proof
  Cases_on `dyn` >>
  simp_tac bool_ss [abi_encoder_spine_child_def, abi_encoder_spine_call_def] >>
  rpt strip_tac
  >- asm_simp_tac (srw_ss()) [abi_encode_dynamic_child_phases, comp_bind_def, LET_THM] >>
  asm_simp_tac (srw_ss()) [Once compile_abi_encode_child_def, comp_bind_def, LET_THM]
QED

Theorem abi_encoder_member_spine_compile:
  !infos dst src dp st so ho out en s t.
    abi_encoder_member_spine core_run (dst,src,dp) infos (st,so,ho) (out,en) s t ==>
    compile_abi_encode_complex_elems dst src infos so ho dp st = (out,en)
Proof
  Induct >- simp[abi_encoder_member_spine_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >>
  simp_tac bool_ss [abi_encoder_member_spine_def] >> rpt strip_tac >>
  drule abi_encoder_spine_child_compile >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp_tac (srw_ss()) [Once compile_abi_encode_child_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem abi_encoder_spine_child_mono:
  (!c s t. core_run c s t ==> core_run' c s t) ==>
  !c s t. abi_encoder_spine_child core_run c s t ==> abi_encoder_spine_child core_run' c s t
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `c` >>
  simp_tac bool_ss [abi_encoder_spine_child_def, abi_encoder_spine_call_def] >>
  Cases_on `c1` >> simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_encoder_member_spine_mono:
  (!c s t. core_run c s t ==> core_run' c s t) ==>
  !infos B q result s t.
    abi_encoder_member_spine core_run B infos q result s t ==>
    abi_encoder_member_spine core_run' B infos q result s t
Proof
  strip_tac >> Induct >> rpt gen_tac >>
  PairCases_on `B` >> PairCases_on `q` >> PairCases_on `result`
  >- simp[abi_encoder_member_spine_def] >>
  PairCases_on `h` >>
  simp_tac bool_ss [abi_encoder_member_spine_def] >>
  metis_tac[abi_encoder_spine_child_mono]
QED

val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiScratchMembers", "abiScratchComplex", "abiEncoderMembersPrepare",
        "abiEncoderMembersCorrect", "abiEncoderComplexStatic"]
  then raise Fail "member spine imports a legacy invariant/execution owner"
  else ();

Definition abi_encoder_spine_core_code_def:
  abi_encoder_spine_core_code func (ei,dst,src,st,en,out) <=>
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    fn_has_code st en func /\
    (st.cs_blocks = en.cs_blocks \/
      !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
End

(* The transport premise is universal at the very endpoint produced by ADD.
   The core runner is independent of that phase and supplies its genuine post. *)
Theorem abi_encoder_spine_static_run:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_encoder_spine_core_code func (ei,head,src,p,en,out) /\
  eval_operand dst initial = SOME d /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!r. abi_encoder_member_phase_raw st p initial r ==>
    child_pre (ei,head,src,p,en,out) r) /\
  (!c r. abi_encoder_spine_core_code func c /\ child_pre c r ==>
    ?t. core_run c r t /\ child_post c r t) ==>
  ?r t. abi_encoder_spine_child core_run (ei,F,dst,src,ho,dp,st,en,out) initial t /\
    abi_encoder_member_phase_raw st p initial r /\
    child_post (ei,head,src,p,en,out) r t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw)) >> strip_tac >>
  `child_pre (ei,head,src,p,en,out) ready` by metis_tac[] >>
  qpat_x_assum `!c r. _` (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`ready`, `t`] >>
  simp_tac bool_ss [abi_encoder_spine_child_def] >>
  conj_tac >- (qexistsl_tac [`head`, `p`, `ready`] >>
    gvs[abi_encoder_spine_call_def, abi_encoder_spine_core_code_def]) >>
  asm_rewrite_tac []
QED

Definition abi_encoder_spine_cursor_input_def:
  abi_encoder_spine_cursor_input (head,dp,offset,len,st,final,limit_st) s <=>
    ?h p off n.
      eval_operand head s = SOME (n2w h) /\ eval_operand dp s = SOME (n2w p) /\
      eval_operand offset s = SOME (n2w off) /\ eval_operand len s = SOME (n2w n) /\
      abi_decoder_operand_live st.cs_next_var dp /\ abi_decoder_operand_live st.cs_next_var len /\
      h < dimword (:256) /\ p < dimword (:256) /\
      final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s
End

Theorem abi_encoder_spine_cursor_run:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  abi_encoder_spine_cursor_input (head,dp,offset,len,st,final,limit_st) s ==>
  ?t. abi_encoder_member_phase_raw st final s t
Proof
  simp_tac bool_ss [abi_encoder_spine_cursor_input_def] >> rpt strip_tac >>
  drule_all abi_encoder_member_cursor_raw >> simp[]
QED

(* All interpretation-specific transport is universal over the returned raw
   endpoints. No property of the core runner is manufactured by this engine. *)
Theorem abi_encoder_spine_dynamic_run:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len ce = (out,en) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!r. abi_encoder_member_phase_raw st p initial r ==>
    child_pre (ei,SND (SND ops),src,p,ce,len) r) /\
  (!c r. abi_encoder_spine_core_code func c /\ child_pre c r ==>
    ?u. core_run c r u /\ child_post c r u) /\
  (!r u. child_post (ei,SND (SND ops),src,p,ce,len) r u ==>
    abi_encoder_spine_cursor_input (FST ops,dp,FST (SND ops),len,ce,en,limit_st) u) ==>
  ?r u t. abi_encoder_spine_child core_run (ei,T,dst,src,ho,dp,st,en,out) initial t /\
    abi_encoder_member_phase_raw st p initial r /\
    child_post (ei,SND (SND ops),src,p,ce,len) r u /\
    abi_encoder_member_phase_raw ce en u t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_prefix_raw >> strip_tac >>
  `child_pre (ei,SND (SND ops),src,p,ce,len) ready` by metis_tac[] >>
  qpat_x_assum `!c r. _` (drule_all_then strip_assume_tac) >>
  `abi_encoder_spine_cursor_input (FST ops,dp,FST (SND ops),len,ce,en,limit_st) u`
    by metis_tac[] >>
  drule_all abi_encoder_spine_cursor_run >> strip_tac >>
  qexistsl_tac [`ready`, `u`, `t`] >>
  simp_tac bool_ss [abi_encoder_spine_child_def] >>
  conj_tac >- (qexistsl_tac [`ops`, `p`, `len`, `ce`, `ready`, `u`] >>
    gvs[abi_encoder_spine_call_def, abi_encoder_spine_core_code_def]) >>
  asm_rewrite_tac []
QED
