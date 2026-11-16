Theory bodyFullAbiDecodeAllocLive
Ancestors
  bodyPtrHashBuiltinsAllocFrame allocationPtr loweringHalt
  decoderGhostFramePtr bodyPtrDefs venomState venomInst
  loweringStateRelDefs compileEnv finite_map list pair words

(* The live family excludes only the executed site and output variable.
   In particular the executed site need not be fresh in vs_allocas.
   start/final_st monotonicity is supplied by the compiler descent; separation
   is supplied there by keeping enclosing sites outside the child interval. *)
Theorem abi_decode_alloca_live_frame:
  stmt_state_rel H ctx fn ce cx es s /\
  MEM (mk_inst site ALLOCA [Lit (n2w k)] [out]) (fn_insts fn) /\
  k < dimword (:256) /\
  step_inst_base (mk_inst site ALLOCA [Lit (n2w k)] [out]) s = OK u /\
  start.cs_next_id <= final_st.cs_next_id /\
  EVERY (\(aid,p,b,n,bytes). aid <> site /\ p <> out) live /\
  EVERY (\(aid,p,b,n,bytes).
    aid < start.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s n /\
    op_taint tn (Var p) = {} /\ n = LENGTH bytes /\
    mem_bytes_at b n s.vs_memory = bytes /\ b+n <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  mem_bytes_at input (LENGTH input_bytes) s.vs_memory = input_bytes ==>
  ?G' tn'.
    G' = step_prov PG G (mk_inst site ALLOCA [Lit (n2w k)] [out]) u /\
    tn' = step_taint (mk_inst site ALLOCA [Lit (n2w k)] [out]) s u tn /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\
    (!aid. aid <> site ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    EVERY (\(aid,p,b,n,bytes).
      aid < final_st.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,n) /\
      lookup_var p u = SOME (n2w b) /\ ptr_covers G' tn' p u n /\
      op_taint tn' (Var p) = {} /\ n = LENGTH bytes /\
      mem_bytes_at b n u.vs_memory = bytes /\ b+n <= u.vs_alloca_next) live /\
    EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) u.vs_memory = bytes) protected /\
    mem_bytes_at input (LENGTH input_bytes) u.vs_memory = input_bytes
Proof
  strip_tac >>
  `s.vs_alloca_next <= u.vs_alloca_next /\
   (!aid. aid <> site ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid)`
    by suspend "allocation" >>
  drule_all alloca_step_site >> strip_tac >>
  drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qexistsl_tac [`step_prov PG G (mk_inst site ALLOCA [Lit (n2w k)] [out]) u`,
    `step_taint (mk_inst site ALLOCA [Lit (n2w k)] [out]) s u tn`] >>
  simp[] >>
  gvs[EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> disch_tac >>
  rename1 `MEM (aid,p,lb,n,bytes) live` >>
  `aid <> site /\ p <> out` by metis_tac[] >>
  qpat_x_assum `!a p b n bs. MEM _ live ==> a < _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[] >> irule ptr_covers_frame >> metis_tac[]
QED

Resume abi_decode_alloca_live_frame[allocation]:
  Cases_on `FLOOKUP s.vs_allocas site`
  >- (drule_all step_alloca_fresh >> strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas site = SOME entry` >> PairCases_on `entry` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[update_var_def]
QED

Finalise abi_decode_alloca_live_frame
