Theory bodyFullAbiEncodeRobust
Ancestors
  abiEncoderOpenInput abiDecodeRanges bodyPtrDefs venomState

Theorem abi_encode_robust_array_child:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_open_input (AbiDynArray ei abi_sz mem_sz dyn)
      (Array NONE ct) (ListV avs) a cap mem) /\
  j < LENGTH avs ==>
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_open_input ei ct (EL j avs) (a+32+j*mem_sz) mem_sz mem)
Proof
  rpt strip_tac >> first_x_assum drule >>
  simp[Once abi_encoder_open_input_cases] >> metis_tac[]
QED

Theorem abi_encode_robust_open_members_cons:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_open_input (AbiComplex ((ei,abi_sz,mem_sz,dyn)::infos))
      (Tuple (ty::tys)) (ListV (av::avs)) a cap mem) ==>
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_open_input ei ty av a mem_sz mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (a+mem_sz) (abi_encoder_member_span infos) mem)
Proof
  strip_tac >>
  `abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty` by
    (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def] >>
     metis_tac[abi_encoder_open_complex_cons]) >>
  simp[] >> conj_tac >> rpt strip_tac >> first_x_assum drule >>
  metis_tac[abi_encoder_open_complex_cons]
QED
