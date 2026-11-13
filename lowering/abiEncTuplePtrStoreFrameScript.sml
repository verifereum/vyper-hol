Theory abiEncTuplePtrStoreFrame
Ancestors
  abiEncTuplePtrStore bodyPtrBopInMachineMemory bodyPtrDefs valueEncodingProps
  valueEncodingProofs list arithmetic abiTupleEncodeMemory abiTupleProps
  abiEncoderInput abiEncoderInputFrame abiTupleEncodeInput abiBuiltinEncodeWord words
  abiDecoderContract abiDecoderReentry venomState venomExecSemantics

Theorem abi_tuple_store_exterior_witness:
  (!i. ~(d <= i /\ i < d+n) ==>
    mem_bytes_at i 1 newmem = mem_bytes_at i 1 oldmem) /\
  (!i. ~(d <= i /\ i < d+n) ==> (i IN newtaint <=> i IN oldtaint)) /\
  mem_agree_outside newtaint newmem mem ==>
  ?mix. mem_agree_outside oldtaint oldmem mix /\
    (!p k. p+k <= d \/ d+n <= p ==>
      mem_bytes_at p k mix = mem_bytes_at p k mem)
Proof
  strip_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  qabbrev_tac `mix = (write_memory_with_expansion d (mem_bytes_at d n oldmem) s).vs_memory` >>
  `mem_bytes_at d n mix = mem_bytes_at d n oldmem` by
    (simp[Abbr `mix`] >>
     metis_tac[write_memory_mem_bytes_at_same, LENGTH_mem_bytes_at]) >>
  qexists `mix` >> reverse conj_tac
  >- (rpt strip_tac >> simp[Abbr `mix`, Abbr `s`] >>
      irule (SRULE [] (Q.INST [`s` |-> `(ARB:venom_state) with vs_memory := mem`] (SPEC_ALL write_memory_mem_bytes_at_disjoint))) >> simp[]) >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  Cases_on `d <= i /\ i < d+n`
  >- (`i-d < n /\ d+(i-d) = i` by decide_tac >>
      `EL (i-d) (mem_bytes_at d n mix) = EL (i-d) (mem_bytes_at d n oldmem)` by simp[] >>
      gvs[EL_mem_bytes_at] >> irule LIST_EQ >> simp[EL_mem_bytes_at]) >>
  `mem_bytes_at i 1 mix = mem_bytes_at i 1 mem` by
    (simp[Abbr `mix`, Abbr `s`] >> irule (SRULE [] (Q.INST [`s` |-> `(ARB:venom_state) with vs_memory := mem`] (SPEC_ALL write_memory_mem_bytes_at_disjoint))) >>
     simp[] >> decide_tac) >>
  metis_tac[mem_agree_outside_def]
QED

Theorem abi_tuple_encode_memory_window:
  !xs ats avs d mem mem'.
  abi_tuple_encode_memory sf ce xs ats avs d mem /\
  mem_bytes_at d (abi_tuple_bytes ce xs) mem =
    mem_bytes_at d (abi_tuple_bytes ce xs) mem' ==>
  abi_tuple_encode_memory sf ce xs ats avs d mem'
Proof
  Induct >- simp[abi_tuple_encode_memory_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[abi_tuple_encode_memory_def, abi_tuple_bytes_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule abi_encoder_input_mem_agree >> qexists `mem` >> simp[] >>
      irule EQ_SYM >> irule (SRULE [] (Q.INST [`off` |-> `0`] (SPEC_ALL abi_encoder_window_slice))) >>
      qexists `SUM (MAP (type_memory_bytes ce o SND) xs) + type_memory_bytes ce h1` >> simp[]) >>
  first_x_assum irule >> qexists `mem` >> simp[] >>
  irule EQ_SYM >> irule abi_encoder_window_slice >>
  qexists `type_memory_bytes ce h1 + abi_tuple_bytes ce xs` >> simp[abi_tuple_bytes_def]
QED

Theorem abi_tuple_store_robust_exterior:
  (!i. ~(d <= i /\ i < d+n) ==>
    mem_bytes_at i 1 newmem = mem_bytes_at i 1 oldmem) /\
  (!i. ~(d <= i /\ i < d+n) ==> (i IN newtaint <=> i IN oldtaint)) /\
  (p+abi_tuple_bytes ce xs <= d \/ d+n <= p) /\
  (!mem. mem_agree_outside oldtaint oldmem mem ==>
    abi_tuple_encode_memory sf ce xs ats avs p mem) ==>
  !mem. mem_agree_outside newtaint newmem mem ==>
    abi_tuple_encode_memory sf ce xs ats avs p mem
Proof
  rpt strip_tac >> drule_all abi_tuple_store_exterior_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  irule abi_tuple_encode_memory_window >> qexists `mix` >>
  metis_tac[]
QED

Theorem abi_tuple_store_inputs_state_transport:
  !xs ats avs next later lo hi s t.
  abi_tuple_encode_inputs sf ce xs ats avs next lo hi s /\
  next <= later /\ s.vs_memory = t.vs_memory /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  abi_tuple_encode_inputs sf ce xs ats avs later lo hi t
Proof
  Induct >- simp[abi_tuple_encode_inputs_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[abi_tuple_encode_inputs_def] >> strip_tac >> gvs[] >> conj_tac
  >- (gvs[abi_tuple_encode_input_def] >>
      `abi_decoder_operand_live later h0` by
        (irule abi_decoder_operand_live_mono >> qexists `next` >> simp[]) >>
      Cases_on `is_word_type h1` >> gvs[] >> metis_tac[]) >>
  first_x_assum irule >> qexistsl [`next`, `s`] >> simp[]
QED

Theorem abi_tuple_store_robust_tail_inputs:
  (!i. ~(d <= i /\ i < d+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. ~(d <= i /\ i < d+n) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  lo <= d /\ d+n <= hi /\ next <= later /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_tuple_encode_inputs sf ce xs ats avs next lo hi (s with vs_memory := mem)) ==>
  !mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
    abi_tuple_encode_inputs sf ce xs ats avs later lo hi (t with vs_memory := mem)
Proof
  rpt strip_tac >> drule_all abi_tuple_store_exterior_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `abi_tuple_encode_inputs sf ce xs ats avs next lo hi (s with vs_memory := mix)` by metis_tac[] >>
  `abi_tuple_encode_inputs sf ce xs ats avs next lo hi (s with vs_memory := mem)` by
    (irule abi_tuple_encode_inputs_transport >>
     conj_tac >- decide_tac >> qexistsl [`next`, `s with vs_memory := mix`] >>
     simp[abi_decode_frame_def] >> reverse conj_tac
     >- (rpt strip_tac >> sym_tac >> first_x_assum irule >> decide_tac) >>
     (Cases_on `op` >> simp[eval_operand_def, lookup_var_def])) >>
  irule abi_tuple_store_inputs_state_transport >>
  qexistsl [`next`, `s with vs_memory := mem`] >> simp[] >>
  qx_gen_tac `op` >>
  qpat_x_assum `!op w. abi_decoder_operand_live next op /\ _ ==> _`
    (qspec_then `op` mp_tac) >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_tuple_slot_robust_contents:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_tuple_encode_input sf ce ty at av op next lo hi (s with vs_memory := mem)) /\
  (if is_word_type ty then
     (!w. eval_operand op s = SOME w ==>
       mem_bytes_at d 32 t.vs_memory = word_to_bytes w T) /\
     (!i. d <= i /\ i < d+32 ==> i NOTIN tm.t_mem)
   else
     ?sb. eval_operand op s = SOME (n2w sb) /\ sb < dimword (:256) /\
       mem_bytes_at d (type_memory_bytes ce ty) t.vs_memory =
         mem_bytes_at sb (type_memory_bytes ce ty) s.vs_memory /\
       (!i. i < type_memory_bytes ce ty ==>
         (d+i IN tm.t_mem <=> sb+i IN tn.t_mem))) ==>
  !mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
    abi_tuple_encode_memory sf ce [(op,ty)] [at] [av] d mem
Proof
  strip_tac >> simp[abi_tuple_encode_memory_def] >>
  Cases_on `is_word_type ty`
  >- (gvs[] >>
      `abi_tuple_encode_input sf ce ty at av op next lo hi (s with vs_memory := s.vs_memory)` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      gvs[abi_tuple_encode_input_def] >>
      `eval_operand op s = SOME w` by
        (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
      drule abi_builtin_encode_word_info >> strip_tac >> rpt strip_tac >>
      simp[abi_encoder_input_copy_iff] >>
      `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 mem` by
        (irule mem_agree_outside_window >> qexists `tm.t_mem` >> simp[]) >>
      metis_tac[]) >>
  gvs[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb (type_memory_bytes ce ty) mem` by
    (rpt strip_tac >>
     `abi_tuple_encode_input sf ce ty at av op next lo hi (s with vs_memory := mem)` by metis_tac[] >>
     qpat_x_assum `abi_tuple_encode_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [abi_tuple_encode_input_def] >>
     disch_then strip_assume_tac >>
     qpat_x_assum `if is_word_type ty then _ else _` mp_tac >>
     simp[] >> strip_tac >>
     `eval_operand op s = SOME (n2w sb')` by
       (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
     `sb' = sb` by (gvs[wordsTheory.n2w_11]) >> gvs[] >>
     irule abi_encoder_input_capacity >> qexists `source_cap` >> simp[]) >>
  rpt strip_tac >> irule abi_tuple_store_robust_copy >>
  qexistsl [`s.vs_memory`, `t.vs_memory`, `sb`, `tn.t_mem`, `tm.t_mem`] >> simp[]
QED
