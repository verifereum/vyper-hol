Theory stmtSimLogDataFrame
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogData stmtSimLogArgs  exprSimMemoryTransport
  exprSimOps compileEnv loweringStateRelDefs venomState valueEncoding valueEncodingDefs words

Definition log_write_frame_def:
  log_write_frame st b n s t <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!a k. a + k <= b \/ b + n <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
End

Definition log_source_apart_def:
  log_source_apart cx b n (op,ty) v s <=>
    !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
      ~is_word_type ty /\ eval_operand op s = SOME w ==>
      val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= b \/
      b + n <= w2n w
End

Theorem log_write_frame_refl[simp]:
  log_write_frame st b n s s
Proof
  simp[log_write_frame_def]
QED

Theorem log_write_frame_trans:
  log_write_frame st b n s t /\ log_write_frame st b n t u ==>
  log_write_frame st b n s u
Proof
  simp[log_write_frame_def] >> strip_tac >> conj_tac
  >- (qpat_assum `u with <|vs_memory := _; vs_vars := _|> = t`
      (mp_tac o AP_TERM ``\z. z with <|vs_memory := s.vs_memory;
                                      vs_vars := s.vs_vars|>``) >> simp[]) >>
  metis_tac[]
QED

Theorem log_write_frame_widen:
  log_write_frame st b n s t /\ a <= b /\ b + n <= a + k ==>
  log_write_frame st a k s t
Proof
  simp[log_write_frame_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem log_write_frame_operand:
  log_write_frame st b n s t /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  eval_operand op t = eval_operand op s
Proof
  simp[log_write_frame_def] >> strip_tac >> Cases_on `op` >>
  simp[eval_operand_def]
  >- (qpat_assum `t with <|vs_memory := _; vs_vars := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  first_x_assum irule >> first_x_assum irule >> simp[]
QED

Theorem log_source_apart_kept:
  log_source_apart cx b n (op,ty) v s /\ log_write_frame st a k s t /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  log_source_apart cx b n (op,ty) v t
Proof
  strip_tac >> drule_all log_write_frame_operand >> strip_tac >>
  gvs[log_source_apart_def]
QED

Theorem log_source_value_kept:
  log_source_apart cx b n (op,ty) v s /\ log_write_frame st b n s t /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  expr_val_rel cx ty v op s ==>
  expr_val_rel cx ty v op t
Proof
  strip_tac >> drule_all log_write_frame_operand >> strip_tac >>
  Cases_on `is_word_type ty`
  >- gvs[expr_val_rel_def] >>
  `?w. eval_operand op s = SOME w` by gvs[expr_val_rel_def] >>
  irule expr_val_rel_footprint_agree >> simp[] >>
  qexists_tac `s` >> simp[] >>
  `val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= b \/
    b + n <= w2n w` by gvs[log_source_apart_def] >>
  gvs[log_write_frame_def, mem_bytes_at_def] >> metis_tac[]
QED

Theorem log_placement_source_apart:
  expr_val_at cenv cx ty sa sm es v op s /\
  (!aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
      a + k <= b \/ b + n <= a) /\
  (!name a k. local_region cenv es.scopes s name a k ==>
      a + k <= b \/ b + n <= a) ==>
  log_source_apart cx b n (op,ty) v s
Proof
  simp[log_source_apart_def] >> rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (qpat_x_assum `!aid a k. _` drule_all >> decide_tac)
  >- (qpat_x_assum `!name a k. _` drule_all >> decide_tac)
QED

Theorem log_write_frame_local_region:
  log_write_frame st b n s t /\ local_ptrs_reserved cenv st ==>
  (local_region cenv scopes t name a k <=> local_region cenv scopes s name a k)
Proof
  simp[log_write_frame_def, local_ptrs_reserved_def, local_region_def] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem log_placement_kept:
  expr_val_at cenv cx ty sa sm es v op s /\
  log_write_frame st b n s t /\ local_ptrs_reserved cenv st /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  expr_val_at cenv cx ty sa sm es v op t
Proof
  strip_tac >> drule_all log_write_frame_operand >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    (gvs[log_write_frame_def] >>
     qpat_assum `t with <|vs_memory := _; vs_vars := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `!name a k. local_region cenv es.scopes t name a k <=>
              local_region cenv es.scopes s name a k` by
    (rpt gen_tac >> drule_all log_write_frame_local_region >> simp[]) >>
  gvs[expr_val_at_def]
QED

Theorem log_allocated_source_apart:
  expr_val_at cenv cx ty sa sm es v op s /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas dest = SOME (b,n) /\ sm.cs_next_id <= dest /\
  (!name a k. local_region cenv es.scopes s name a k ==>
     a + k <= b \/ b + n <= a) ==>
  log_source_apart cx b n (op,ty) v s
Proof
  strip_tac >> drule log_placement_source_apart >>
  disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> `aid <> dest` by decide_tac >>
  gvs[venomMemDefsTheory.allocas_non_overlapping_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`aid`, `dest`] mp_tac) >> simp[] >> decide_tac
QED
