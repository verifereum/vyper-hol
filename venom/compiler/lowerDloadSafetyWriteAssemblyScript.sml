(* Reachable memory-write consumers. *)
Theory lowerDloadSafetyWriteAssembly
Ancestors
  lowerDloadMemoryWritePointEffect[qualified]
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyRelation lowerDloadSafetyValues
  lowerDloadSafetyAmbient
  codegenRel contextCodegenRel venomWf ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomExecSemantics venomState finite_map list pred_set

Theorem ld_write_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_write_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_write_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_write_access_cases >> metis_tac[]
QED

Theorem ld_read_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_read_access_cases >> metis_tac[]
QED

Theorem ld_sync_memory_write_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = G /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\
    ts.vs_allocas = t.vs_allocas /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ts.vs_current_bb = t.vs_current_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ts.vs_inst_idx = t.vs_inst_idx /\
    (!a. a IN FRANGE f.lf_H ==> a IN FDOM A)
Proof
  strip_tac >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  drule_all ld_sync_dyn_floor >> strip_tac >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs0 /\ c+sz <= dyn_floor C vs0 /\ c+sz < dimword(:256)` by
    metis_tac[] >>
  drule_all lowerDloadMemoryWritePointEffectTheory.ld_sync_memory_write_effect_at >> simp[]
QED
