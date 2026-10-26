(* Composable recursive decoder effects allow allocations inside the owned code. *)
Theory abiDecoderEffect
Ancestors
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderDynamicLoopSetup
  abiDecoderLoopRegisters abiDecoderExecution
  abiDecoderProtectedScratch
  abiDecoderReentry abiDecoderFrame abiDecoderContract
  compileEnv venomState finite_map words arithmetic pred_set

Definition abi_decoder_scratch_frame_def:
  abi_decoder_scratch_frame first last lo hi s t <=>
    (!id. id < lo \/ hi <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id p. first <= id /\ id < last /\ (id < lo \/ hi <= id) /\
      FLOOKUP s.vs_allocas id = SOME (p,32) ==> mload p t = mload p s)
End

Theorem abi_decoder_scratch_frame_refl:
  abi_decoder_scratch_frame first last lo hi s s
Proof
  simp[abi_decoder_scratch_frame_def]
QED

Theorem abi_decoder_scratch_frame_trans:
  abi_decoder_scratch_frame first last lo hi s t /\
  abi_decoder_scratch_frame first last lo hi t u ==>
  abi_decoder_scratch_frame first last lo hi s u
Proof
  rw[abi_decoder_scratch_frame_def] >> metis_tac[]
QED

Theorem abi_decoder_scratch_frame_widen:
  abi_decoder_scratch_frame first last child_lo child_hi s t /\
  lo <= child_lo /\ child_hi <= hi ==>
  abi_decoder_scratch_frame first last lo hi s t
Proof
  rw[abi_decoder_scratch_frame_def] >>
  `id < child_lo \/ child_hi <= id` by decide_tac >> metis_tac[]
QED

Definition abi_decoder_effect_def:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,sz);(b,cap)] s t /\
    t.vs_halted = s.vs_halted /\ abi_decoder_scratch_frame first last lo hi s t
End

Theorem abi_decoder_effect_refl:
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s s
Proof
  simp[abi_decoder_effect_def, abi_decode_footprint_frame_refl,
    abi_decoder_scratch_frame_refl]
QED

Theorem abi_decoder_effect_trans:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_effect first last lo hi next limit_st d sz b cap t u ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s u
Proof
  simp_tac bool_ss [abi_decoder_effect_def] >> strip_tac >>
  metis_tac[abi_decode_footprint_frame_trans, abi_decoder_scratch_frame_trans]
QED

Theorem abi_decoder_output_footprint_widen:
  abi_decode_footprint_frame [(child_d,child_sz);(b,cap)] s t /\
  d <= child_d /\ child_d + child_sz <= d + sz ==>
  abi_decode_footprint_frame [(d,sz);(b,cap)] s t
Proof
  rw[abi_decode_footprint_frame_def] >> first_x_assum irule >>
  fs[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac
QED

Theorem abi_decoder_effect_widen:
  abi_decoder_effect first last child_lo child_hi child_next limit_st child_d child_sz b cap s t /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  d <= child_d /\ child_d + child_sz <= d + sz ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  simp_tac bool_ss [abi_decoder_effect_def] >> strip_tac >> asm_simp_tac bool_ss [] >>
  rpt conj_tac >|
  [rpt strip_tac >> `abi_decoder_operand_live child_next op` by
     (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >> metis_tac[],
   drule_all abi_decoder_output_footprint_widen >> simp[],
   drule_all abi_decoder_scratch_frame_widen >> simp[]]
QED

Theorem abi_decoder_address_effect:
  abi_decoder_address_frame child_next s t /\ next <= child_next /\
  fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >> qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  drule_all abi_decoder_budget_transport >> strip_tac >>
  asm_simp_tac bool_ss [abi_decoder_effect_def, abi_decode_footprint_frame_def,
    abi_decoder_scratch_frame_def, mload_def] >> rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >> metis_tac[]
QED

Theorem abi_decoder_effect_protected_slot:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  first <= site /\ site < last /\ (site < lo \/ hi <= site) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = mload slot s
Proof
  simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  strip_tac >> metis_tac[]
QED

Theorem abi_decoder_header_effect:
  next <= first_var /\ first_var + 4 <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first_var))
      (STRING #"%" (toString (first_var+1))) (STRING #"%" (toString (first_var+2)))
      (STRING #"%" (toString (first_var+3))) i ncount s))
Proof
  strip_tac >> drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `h = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first_var))
    (STRING #"%" (toString (first_var+1))) (STRING #"%" (toString (first_var+2)))
    (STRING #"%" (toString (first_var+3))) i ncount s)` >>
  `fresh_vars_wrt limit_st h` by simp[Abbr`h`] >>
  `abi_decoder_address_frame first_var s h` by
    (asm_simp_tac bool_ss [abi_decoder_address_frame_def, Abbr`h`, abi_decoder_operand_jump] >>
     simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
  qexists_tac `first_var` >> simp[]
QED

Theorem abi_decoder_arena_footprint:
  abi_decode_footprint_frame [(slot,32)] s t /\ b <= slot /\ slot + 32 <= b + cap ==>
  abi_decode_footprint_frame [(d,sz);(b,cap)] s t
Proof
  rw[abi_decode_footprint_frame_def] >> first_x_assum irule >>
  fs[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac
QED

Theorem abi_decoder_scratch_slot_frame:
  abi_decoder_budget first last b cap s /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  t.vs_allocas = s.vs_allocas /\ abi_decode_footprint_frame [(slot,32)] s t ==>
  abi_decoder_scratch_frame first last lo hi s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [abi_decoder_scratch_frame_def] >>
  MAP_EVERY qx_gen_tac [`id`, `p`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last /\ id IN abi_decoder_ids first last`
    by simp[abi_decoder_ids_def] >>
  `site <> id` by decide_tac >>
  irule abi_decode_footprint_frame_mload >> qexists_tac `[(slot,32)]` >>
  asm_simp_tac bool_ss [] >> simp[abi_footprint_disjoint_def] >>
  mp_tac (Q.INST [`i` |-> `site:num`, `j` |-> `id:num`,
    `p` |-> `slot:num`, `q` |-> `p:num`] abi_decoder_budget_sites_disjoint) >>
  impl_tac >- asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_decoder_index_effect:
  abi_decoder_budget first last b cap s /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  fresh_vars_wrt limit_st t /\ t.vs_halted = s.vs_halted /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_footprint_frame [(slot,32)] s t ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule_all abi_decoder_scratch_slot_frame >> strip_tac >>
  drule_all abi_decoder_budget_transport >> strip_tac >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] s t` by
    (drule_all abi_decoder_arena_footprint >> simp[]) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder effects not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderEffect");
