(* The keyword write and ghost frames protect the same owned payload. *)
Theory bodyRawKwargsBytesFrameMods
Ancestors
  exprSimPrecompiles exprSimProps representationCleanPtr abiDecodeStaticProps
  bodyPtrDefs loweringPosts compileEnv valueEncodingDefs valueEncodingProofs

Theorem kwargs_bytes_footprint[local]:
  (!n k k'. local_val_at cenv cx n k (BaseTV(BytesT(Dynamic cap))) (BytesV bs) /\
     val_wf (BaseTV(BytesT(Dynamic cap))) (BytesV bs) /\
     dynarray_len_at cenv n k' ==>
     k + val_footprint (BaseTV(BytesT(Dynamic cap))) (BytesV bs) <= k' \/
     k' + 32 <= k) /\
  expr_val_at cenv cx (BaseT(BytesT(Dynamic cap))) sa sd es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT(BytesT(Dynamic cap))) =
    SOME(BaseTV(BytesT(Dynamic cap))) /\
  eval_operand data s = SOME w /\ sd.cs_next_id <= sk.cs_next_id /\
  wb_frame cenv es es' sk s t ==>
  mem_bytes_at (w2n w) (val_footprint (BaseTV(BytesT(Dynamic cap))) (BytesV bs))
    t.vs_memory =
  mem_bytes_at (w2n w) (val_footprint (BaseTV(BytesT(Dynamic cap))) (BytesV bs))
    s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, is_word_type_def] >> strip_tac >> gvs[]
  >- (fs[wb_frame_def] >>
      `aid < sk.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` drule_all >>
      disch_then (drule o cj 1 o MATCH_MP mem_bytes_at_agree_window) >>
      simp[])
  >- (fs[wb_frame_def, locals_kept_def] >>
      qpat_assum `!n b sz off len. _ ==> _` irule >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> rpt strip_tac >>
      drule dynarray_len_untupled_imp_at >> strip_tac >>
      qpat_assum `!n k k'. _ ==> _` drule_all >> decide_tac) >>
  simp[mem_bytes_at_def]
QED

Theorem raw_kwargs_bytes_frame_from_apart:
  (!n k k'. local_val_at cenv cx n k (BaseTV(BytesT(Dynamic cap))) (BytesV bs) /\
     val_wf (BaseTV(BytesT(Dynamic cap))) (BytesV bs) /\
     dynarray_len_at cenv n k' ==>
     k + val_footprint (BaseTV(BytesT(Dynamic cap))) (BytesV bs) <= k' \/
     k' + 32 <= k) /\
  expr_val_at cenv cx (BaseT(BytesT(Dynamic cap))) sa sd es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT(BytesT(Dynamic cap))) =
    SOME(BaseTV(BytesT(Dynamic cap))) /\
  eval_operand data s = SOME(n2w b) /\ b < dimword(:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
  sd.cs_next_id <= sk.cs_next_id /\
  typed_args_post H ctx func cenv cx es sk s es' kws xs vs t /\
  ghost_kept_at lo cenv es sk G tn s G' tn' ==>
  (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    mem_bytes_at (b+32) (LENGTH bs) mem = bs)
Proof
  strip_tac >>
  `wb_frame cenv es es' sk s t` by fs[typed_args_post_def] >>
  `mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs` by
    (qpat_assum `!mem. mem_agree_outside _ _ _ ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs` by
    (drule_all kwargs_bytes_footprint >>
     simp[val_footprint_def, wordsTheory.w2n_n2w] >> strip_tac >>
     drule (cj 1 mem_bytes_at_agree_window) >>
     disch_then (qspecl_then [`b+32`, `LENGTH bs`] mp_tac) >> simp[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (drule robust_mem_bytes_at_clean >> simp[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn'.t_mem` by
    (gvs[expr_val_at_def, is_word_type_def, val_footprint_def] >>
     rpt strip_tac >> gvs[ghost_kept_at_def] >>
     (`i IN tn.t_mem` suffices_by metis_tac[])
     >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
         `aid < sk.cs_next_id /\ off <= i /\ i < off+sz` by decide_tac >>
         qpat_assum `!aid off sz i. FLOOKUP _ aid = SOME (off,sz) /\ _ ==> _`
           drule_all >> simp[]) >>
     rename1 `local_region cenv es.scopes s name off sz` >>
     `off <= i /\ i < off+sz` by decide_tac >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory =
   mem_bytes_at (b+32) (LENGTH bs) mem` by
    (irule mem_bytes_at_bytewise >> gvs[mem_agree_outside_def]) >>
  metis_tac[]
QED
