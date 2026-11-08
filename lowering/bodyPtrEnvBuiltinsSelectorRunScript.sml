(* Ordinary selector execution, separate from pointer decoration. *)
Theory bodyPtrEnvBuiltinsSelectorRun
Ancestors exprSimLiteralBuffer bodyPtrEnvBuiltinsSelectorBuffer
  exprLoweringProps venomExecSemantics venomState venomInst
  compileEnv context emitHelper fragExec exprSimAlloc localPtrsProps
  loweringSlice exprSimHash exprSimProps list words finite_map

Theorem selector_store_tail_run:
  lookup_var p s = SOME (n2w b) /\ b+64 < dimword (:256) /\
  eval_operand value s = SOME w /\
  (!x. value = Var x ==> x <> q) ==>
  run_inst_seq
    [mk_inst il MSTORE [Var p; Lit 4w] [];
     mk_inst ip ADD [Var p; Lit 32w] [q];
     mk_inst iw MSTORE [Var q; value] []] s =
  OK (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s)))
Proof
  strip_tac >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = mstore b 4w s` >>
  qabbrev_tac `s2 = update_var q (n2w (b+32)) s1` >>
  `step_inst_base (mk_inst il MSTORE [Var p; Lit 4w] []) s = OK s1` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `s1`]) >>
  `lookup_var p s1 = SOME (n2w b) /\ eval_operand value s1 = SOME w` by
    (simp[Abbr `s1`, mstore_def, lookup_var_def, eval_operand_def] >>
     Cases_on `value` >> gvs[eval_operand_def, lookup_var_def]) >>
  `step_inst_base (mk_inst ip ADD [Var p; Lit 32w] [q]) s1 = OK s2` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `s2`,
          word_add_n2w]) >>
  `lookup_var q s2 = SOME (n2w (b+32)) /\ eval_operand value s2 = SOME w` by
    (simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `value` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iw MSTORE [Var q; value] []) s2 =
   OK (mstore (b+32) w s2)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[run_inst_seq_def, Abbr `s2`, Abbr `s1`]
QED

Theorem selector_buffer_run:
  compile_alloc_buffer 64 sa = (buf,sm) /\ buf.buf_operand = Var p /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  eval_operand value s = SOME w /\
  (!x. value = Var x ==> not_fresh_at sa x /\ x <> q) ==>
  ?u b. run_inst_seq (emitted_insts sa sm) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\
    lookup_var p u = SOME (n2w b) /\ b+64 < dimword (:256) /\
    eval_operand value u = SOME w /\
    run_inst_seq (emitted_insts sa sm ++
      [mk_inst il MSTORE [Var p; Lit 4w] [];
       mk_inst ip ADD [Var p; Lit 32w] [q];
       mk_inst iw MSTORE [Var q; value] []]) s =
    OK (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w u)))
Proof
  strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  `eval_operand value t = SOME w` by
    (Cases_on `value` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `w2n w'`] >>
  gvs[eval_operand_def] >>
  `lookup_var p t = SOME (n2w (w2n w'))` by simp[] >>
  drule selector_store_tail_run >> simp[] >>
  disch_then (qspecl_then [`w`, `value`, `q`] mp_tac) >>
  simp[] >> strip_tac >>
  `value <> Var q` by metis_tac[] >>
  drule run_inst_seq_append >> disch_then (qspec_then
    `[mk_inst il MSTORE [Var p; Lit 4w] [];
      mk_inst ip ADD [Var p; Lit 32w] [q];
      mk_inst iw MSTORE [Var q; value] []]` SUBST1_TAC) >>
  simp[]
QED

Theorem selector_store_tail_state_rel:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,64) /\
  not_local_ptr cenv es.scopes q /\
  (!name lb sz. local_region cenv es.scopes s name lb sz ==>
    b+64 <= lb \/ lb+sz <= b) ==>
  stmt_state_rel ctx fn cenv cx es
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s)))
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx es (mstore b 4w s)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`b`, `inst`, `64`] >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx fn cenv cx es
    (update_var q (n2w (b+32)) (mstore b 4w s))` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  irule literal_mstore_state_rel >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`b`, `inst`, `64`] >>
  simp[mstore_def, update_var_def] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s name lb lsz` by
    (gvs[local_region_def, lookup_var_def, not_local_ptr_def,
         FLOOKUP_UPDATE] >> metis_tac[]) >>
  first_x_assum drule >> simp[]
QED

Theorem selector_store_tail_memory_frame:
  regions_disjoint b 64 off len ==>
  mem_bytes_at off len
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))).vs_memory =
  mem_bytes_at off len s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at off len
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))).vs_memory =
   mem_bytes_at off len (update_var q (n2w (b+32)) (mstore b 4w s)).vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`b`, `64`] >> simp[]) >>
  simp[update_var_def] >> irule mstore_region_frame >>
  qexistsl_tac [`b`, `64`] >> simp[]
QED

Theorem selector_store_tail_representation:
  val_in_memory (BaseTV (BytesT (Dynamic 4)))
    (BytesV (TAKE 4 (word_to_bytes w T))) b
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))).vs_memory
Proof
  `LENGTH (TAKE 4 (word_to_bytes w T)) = 4` by
    simp[byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE] >>
  `(mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))).vs_memory =
   (mstore (b+32) w (mstore b 4w s)).vs_memory` by
    (qmatch_goalsub_abbrev_tac `update_var q z s1` >>
     simp[mstore_def, update_var_def]) >>
  asm_rewrite_tac[] >> irule selector_buffer_memory >> simp[]
QED

Theorem selector_store_tail_lookup:
  lookup_var x
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))) =
  if x = q then SOME (n2w (b+32)) else lookup_var x s
Proof
  simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE, EQ_SYM_EQ]
QED

Theorem selector_store_tail_allocas:
  (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))).vs_allocas =
  s.vs_allocas
Proof
  simp[mstore_def, update_var_def]
QED

Theorem selector_store_tail_local_region:
  not_local_ptr cenv scopes q ==>
  (local_region cenv scopes
    (mstore (b+32) w (update_var q (n2w (b+32)) (mstore b 4w s))) name lb sz <=>
   local_region cenv scopes s name lb sz)
Proof
  strip_tac >>
  simp[local_region_def, selector_store_tail_lookup] >>
  gvs[not_local_ptr_def] >> metis_tac[]
QED

Theorem selector_buffer_run_frame:
  compile_alloc_buffer 64 sa = (buf,sm) /\ buf.buf_operand = Var p /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa q /\ p <> q /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  eval_operand value s = SOME w /\
  (!x. value = Var x ==> not_fresh_at sa x) ==>
  ?t b. run_inst_seq (emitted_insts sa sm ++
      [mk_inst il MSTORE [Var p; Lit 4w] [];
       mk_inst ip ADD [Var p; Lit 32w] [q];
       mk_inst iw MSTORE [Var q; value] []]) s = OK t /\
    stmt_state_rel ctx fn cenv cx es t /\
    eval_operand (Var p) t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,64) /\
    sa.cs_next_id < sm.cs_next_id /\ b+64 < dimword (:256) /\
    val_in_memory (BaseTV (BytesT (Dynamic 4)))
      (BytesV (TAKE 4 (word_to_bytes w T))) b t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name off len. local_region cenv es.scopes s name off len ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name off len. local_region cenv es.scopes t name off len ==>
       regions_disjoint b 64 off len)
Proof
  strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `not_local_ptr cenv es.scopes q` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `eval_operand value u = SOME w /\ value <> Var q` by
    (Cases_on `value` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`mstore (w2n w'+32) w
    (update_var q (n2w (w2n w'+32)) (mstore (w2n w') 4w u))`, `w2n w'`] >>
  simp[selector_store_tail_lookup, selector_store_tail_allocas,
       selector_store_tail_representation, eval_operand_def,
       selector_store_tail_local_region] >>
  conj_tac >- suspend "run" >>
  conj_tac >- suspend "state" >>
  conj_tac >- gvs[eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  conj_tac >- suspend "old_alloc" >>
  conj_tac >- suspend "locals" >> metis_tac[]
QED

Resume selector_buffer_run_frame[run]:
  `lookup_var p u = SOME (n2w (w2n w'))` by gvs[eval_operand_def] >>
  drule run_inst_seq_append >> disch_then (qspec_then
    `[mk_inst il MSTORE [Var p; Lit 4w] [];
      mk_inst ip ADD [Var p; Lit 32w] [q];
      mk_inst iw MSTORE [Var q; value] []]` SUBST1_TAC) >>
  irule selector_store_tail_run >> simp[]
QED

Resume selector_buffer_run_frame[state]:
  irule selector_store_tail_state_rel >> simp[] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[mk_inst_def] >> metis_tac[regions_disjoint_def]
QED

Resume selector_buffer_run_frame[old_alloc]:
  rpt strip_tac >>
  `regions_disjoint (w2n w') 64 off len` by metis_tac[] >>
  drule selector_store_tail_memory_frame >>
  disch_then (qspecl_then [`w`, `u`, `q`] mp_tac) >> simp[]
QED

Resume selector_buffer_run_frame[locals]:
  rpt strip_tac >>
  `local_region cenv es.scopes u name off len` by
    (irule local_region_frame_fwd >> goal_assum (drule_at Any) >>
     qexists_tac `sa` >> simp[]) >>
  `regions_disjoint (w2n w') 64 off len` by metis_tac[] >>
  drule selector_store_tail_memory_frame >>
  disch_then (qspecl_then [`w`, `u`, `q`] mp_tac) >> simp[]
QED

Finalise selector_buffer_run_frame
