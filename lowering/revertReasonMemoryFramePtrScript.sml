(* The reason's length word lives in a local or an older allocation.
   Only this head, not its payload or padding, is framed through the prefix. *)
Theory revertReasonMemoryFramePtr
Ancestors
  revertReasonPrefixFramePtr abiEncoderZeroFrame valueEncoding valueEncodingProps
  exprLoweringProps compileEnv venomState venomMemDefs venomMemProps
  words arithmetic finite_map list pred_set allocaSiteResource

Theorem revert_reason_prefix_head_exterior:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\ alloca_inv t /\
  FLOOKUP t.vs_allocas id = SOME (b,64+ms) /\
  FLOOKUP t.vs_allocas (id+3) = SOME (c,ms) /\
  ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < id /\
      a <= head /\ head+32 <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= head /\ head+32 <= a+sz)) /\
  head <= j /\ j < head+32 ==>
  j NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})
Proof
  strip_tac
  >- (`FLOOKUP t.vs_allocas aid = SOME (a,sz)` by
        (drule revert_reason_prefix_allocation_frame >> disch_then irule >> simp[]) >>
      `aid <> id /\ aid <> id+3` by decide_tac >>
      `venomMemDefs$regions_disjoint (a,sz) (b,64+ms)` by
        (irule alloca_site_registered_disjoint >> metis_tac[]) >>
      `venomMemDefs$regions_disjoint (a,sz) (c,ms)` by
        (irule alloca_site_registered_disjoint >> metis_tac[]) >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `a <= j /\ j < a+sz` by decide_tac >>
  drule_all revert_reason_prefix_local_exterior >> simp[]
QED

Theorem revert_reason_prefix_head_frame:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx fn PG G tn (revert_reason_prefix id v ms) s Gf tnf /\
  ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < id /\
      a <= head /\ head+32 <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= head /\ head+32 <= a+sz)) /\
  (!j. head <= j /\ j < head+32 ==> j NOTIN tn.t_mem) ==>
  mload head t = mload head s /\
  (!j. head <= j /\ j < head+32 ==> j NOTIN tnf.t_mem)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))` by simp[] >>
  drule_all revert_reason_prefix_memory_effects >> strip_tac >>
  `!j. head <= j /\ j < head+32 ==>
     j NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})` by
    (gen_tac >> strip_tac >> drule_all revert_reason_prefix_head_exterior >> simp[]) >>
  conj_tac
  >- (`mem_bytes_at head 32 t.vs_memory = mem_bytes_at head 32 s.vs_memory` by
        (irule abi_encoder_mem_bytes_singletons >> metis_tac[]) >>
      fs[mem_bytes_at_def, mload_def]) >>
  metis_tac[]
QED
