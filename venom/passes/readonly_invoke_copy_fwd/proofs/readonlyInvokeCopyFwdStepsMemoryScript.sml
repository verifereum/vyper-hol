Theory readonlyInvokeCopyFwdStepsMemory
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdRel taintAgree regularCallEmitSim
  o1LowerDloadRangeTransport venomMemProps venomState venomExecSemantics
  ptrDiscipline internalReturnCopyFwdSim finite_map list pred_set

(* Memory writes leave all local relocation witnesses intact. *)
Theorem ricf_frame_write_memory:
  ricf_frame_agree D X sites PG G tn s t /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (tn.t_mem DIFF {i | a <= i /\ i < a+len}) SUBSET M /\
  (!k. k < len /\ a+k NOTIN M ==> EL k xs = EL k ys) /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(a <= db+k /\ db+k < a+len) /\
    ~(a <= sb+k /\ sb+k < a+len) /\
    (db+k IN M <=> db+k IN tn.t_mem) /\
    (sb+k IN M <=> sb+k IN tn.t_mem)) ==>
  ricf_frame_agree D X sites PG G (tn with t_mem := M)
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a ys t)
Proof
  strip_tac >>
  `ircf_cross (tn with t_mem := M) (ricf_site_triples sites)
     (write_memory_with_expansion a xs s) (write_memory_with_expansion a ys t)` by
    (irule ricf_cross_byte_frame >> qexistsl_tac [`s`, `t`, `tn`] >>
     fs[ricf_frame_agree_def] >> rpt strip_tac >>
     simp[read_byte_write_memory_with_expansion] >> metis_tac[]) >>
  `taint_agree D X (tn with t_mem := M)
     (write_memory_with_expansion a xs s)
     (write_memory_with_expansion a ys
       (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>))` by
    (irule taint_agree_write_memory >> fs[ricf_frame_agree_def] >> metis_tac[]) >>
  fs[ricf_frame_agree_def, write_memory_with_expansion_def, op_taint_def] >> gvs[]
QED

Theorem ricf_write_memory_merge:
  merge_callee_state a (write_memory_with_expansion dst xs s) =
  write_memory_with_expansion dst xs (merge_callee_state a s)
Proof
  simp[merge_callee_state_def, write_memory_with_expansion_def]
QED

Theorem ricf_cert_write_memory:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (tn0.t_mem DIFF {i | a <= i /\ i < a+len}) SUBSET M /\
  (!k. k < len /\ a+k NOTIN M ==> EL k xs = EL k ys) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len) /\
      (db+k IN M <=> db+k IN tn0.t_mem) /\
      (sb+k IN M <=> sb+k IN tn0.t_mem)) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion a xs s) G0)
    (ricf_effective_taint fn (write_memory_with_expansion a xs s)
      (tn0 with t_mem := M)) fn sites maps targets G0
    (tn0 with t_mem := M) cur curs
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a ys t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >>
  conj_tac
  >- (irule ricf_cross_byte_frame >> qexistsl_tac [`s`, `t`, `tn0`] >>
      qpat_assum `!gam. _` (qspec_then `cur` mp_tac) >> simp[] >>
      disch_tac >> simp[] >> rpt strip_tac >>
      `~(a <= db+k /\ db+k < a+len) /\
       ~(a <= sb+k /\ sb+k < a+len) /\
       (db+k IN M <=> db+k IN tn0.t_mem) /\
       (sb+k IN M <=> sb+k IN tn0.t_mem)` by metis_tac[] >>
      simp[read_byte_write_memory_with_expansion] >> gvs[]) >>
  conj_tac
  >- (irule ricf_cert_crosses_refresh >> qexistsl_tac [`s`, `t`, `tn0`] >>
      simp[] >> rpt strip_tac >>
      `~(a <= db+k /\ db+k < a+len) /\
       ~(a <= sb+k /\ sb+k < a+len) /\
       (db+k IN M <=> db+k IN tn0.t_mem) /\
       (sb+k IN M <=> sb+k IN tn0.t_mem)` by metis_tac[] >>
      simp[read_byte_write_memory_with_expansion] >> gvs[]) >>
  conj_tac
  >- (`ircf_dead ids (write_memory_with_expansion a xs s) stk = ircf_dead ids s stk /\
        (write_memory_with_expansion a xs s).vs_params = s.vs_params` by
        simp[ircf_dead_def, write_memory_with_expansion_def] >>
      asm_rewrite_tac[] >> irule ricf_frame_write_memory >> metis_tac[]) >>
  fs[ricf_live_stack_agree_def] >>
  simp[ricf_live_stack_agree_def, ricf_write_memory_merge] >>
  rpt strip_tac >>
  match_mp_tac (ricf_frame_write_memory |> Q.INST
    [`tn` |-> `tn0 with t_var := (EL j stk).cf_tvar`]) >>
  simp[] >> metis_tac[]
QED

Theorem ricf_cert_mstore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME (n2w a) /\ eval_operand addr t = SOME (n2w a) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  a < dimword (:256) /\
  M = (tn0.t_mem DIFF {i | a <= i /\ i < a+32}) UNION {a+k | k IN m} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+32) /\
      ~(a <= sb+k /\ sb+k < a+32)) ==>
  step_inst_base inst s = OK (mstore a x s) /\
  step_inst_base inst t = OK (mstore a y t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (mstore a x s) G0)
    (ricf_effective_taint fn (mstore a x s) (tn0 with t_mem := M)) fn
    sites maps targets G0 (tn0 with t_mem := M) cur curs
    (mstore a x s) (mstore a y t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  `{a+k | k IN m} SUBSET {i | a <= i /\ i < a+32}` by
    (fs[SUBSET_DEF] >> rpt strip_tac >> gvs[] >>
     first_x_assum drule >> decide_tac) >>
  `!i. ~(a <= i /\ i < a+32) ==> (i IN M <=> i IN tn0.t_mem)` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  rewrite_tac[mstore_eq_write_mem] >>
  match_mp_tac (ricf_cert_write_memory |> Q.INST
    [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `32`]) >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `~(a <= db+k /\ db+k < a+32) /\
       ~(a <= sb+k /\ sb+k < a+32)` by metis_tac[] >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
  fs[word_agree_except_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ricf_cert_mstore8:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME (n2w a) /\ eval_operand addr t = SOME (n2w a) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  (w2w x : word8) = w2w y /\ a < dimword (:256) /\
  M = tn0.t_mem DIFF {a} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==> db+k <> a /\ sb+k <> a) ==>
  step_inst_base inst s = OK (mstore8 a x s) /\
  step_inst_base inst t = OK (mstore8 a y t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (mstore8 a x s) G0)
    (ricf_effective_taint fn (mstore8 a x s) (tn0 with t_mem := M)) fn
    sites maps targets G0 (tn0 with t_mem := M) cur curs
    (mstore8 a x s) (mstore8 a y t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  rewrite_tac[mstore8_eq_write_mem] >>
  match_mp_tac (ricf_cert_write_memory |> Q.INST
    [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `1`]) >> simp[] >>
  conj_tac >- (gvs[SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  rpt strip_tac >> `db+k <> a /\ sb+k <> a` by metis_tac[] >>
  gvs[] >> decide_tac
QED

Theorem ricf_cert_mcopy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sizeop] /\
  eval_operand dst s = SOME (n2w a) /\ eval_operand dst t = SOME (n2w a) /\
  eval_operand src s = SOME (n2w b) /\ eval_operand src t = SOME (n2w c) /\
  eval_operand sizeop s = SOME (n2w len) /\ eval_operand sizeop t = SOME (n2w len) /\
  a < dimword (:256) /\ b < dimword (:256) /\ c < dimword (:256) /\
  len < dimword (:256) /\
  (!k. k < len ==> (b+k IN tn0.t_mem <=> c+k IN tn0.t_mem) /\
    (b+k NOTIN tn0.t_mem ==> read_byte (b+k) s.vs_memory = read_byte (c+k) t.vs_memory)) /\
  M = (tn0.t_mem DIFF {i | a <= i /\ i < a+len}) UNION
    {a+k | k < len /\ b+k IN tn0.t_mem} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len)) ==>
  step_inst_base inst s = OK (mcopy a b len s) /\
  step_inst_base inst t = OK (mcopy a c len t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (mcopy a b len s) G0)
    (ricf_effective_taint fn (mcopy a b len s) (tn0 with t_mem := M)) fn
    sites maps targets G0 (tn0 with t_mem := M) cur curs
    (mcopy a b len s) (mcopy a c len t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, IgnAsm `M = _`] >>
  `{a+k | k < len /\ b+k IN tn0.t_mem} SUBSET {i | a <= i /\ i < a+len}` by
    (simp[SUBSET_DEF] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `!i. ~(a <= i /\ i < a+len) ==> (i IN M <=> i IN tn0.t_mem)` by
    (fs[SUBSET_DEF] >> metis_tac[]) >>
  `(tn0.t_mem DIFF {i | a <= i /\ i < a+len}) SUBSET M` by
    (fs[SUBSET_DEF] >> metis_tac[]) >>
  `!k. k < len /\ a+k NOTIN M ==> b+k NOTIN tn0.t_mem` by
    (fs[] >> metis_tac[]) >>
  qpat_x_assum `M = _` kall_tac >>
  pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >> BETA_TAC >>
  match_mp_tac (ricf_cert_write_memory |> Q.INST
    [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `len`]) >>
  simp[ld_read_memory_length] >>
  conj_tac
  >- (rpt strip_tac >> simp[ld_read_memory_element] >>
      `b+k NOTIN tn0.t_mem` by (gvs[] >> metis_tac[]) >> metis_tac[]) >>

  rpt strip_tac >>
  `~(a <= db+k /\ db+k < a+len) /\
   ~(a <= sb+k /\ sb+k < a+len)` by metis_tac[] >>
  fs[] >> metis_tac[]
QED
