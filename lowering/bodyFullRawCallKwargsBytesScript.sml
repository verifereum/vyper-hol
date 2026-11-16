(* The existing payload remains robust across keyword evaluation. *)
Theory bodyFullRawCallKwargsBytes
Ancestors
  exprSimRawCall representationCleanPtr abiDecodeStaticProps
  bodyPtrDefs loweringPosts compileEnv

Theorem raw_call_kwargs_bytes_frame:
  expr_sim_inv cenv cx env es /\
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
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by
    simp[mem_agree_outside_def] >>
  `mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs` by metis_tac[] >>
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs` by
    (drule_all raw_call_kwargs_payload >> simp[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (drule robust_mem_bytes_at_clean >> simp[]) >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn'.t_mem` by
    (gvs[expr_val_at_def, is_word_type_def, val_footprint_def] >>
     rpt strip_tac >> gvs[ghost_kept_at_def] >>
     `i IN tn.t_mem` suffices_by metis_tac[]
     >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
         `aid < sk.cs_next_id /\ off <= i /\ i < off+sz` by decide_tac >>
         metis_tac[]) >>
     rename1 `local_region cenv es.scopes s name off sz` >>
     `off <= i /\ i < off+sz` by decide_tac >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory =
   mem_bytes_at (b+32) (LENGTH bs) mem` by
    (irule mem_bytes_at_bytewise >> gvs[mem_agree_outside_def]) >>
  metis_tac[]
QED
