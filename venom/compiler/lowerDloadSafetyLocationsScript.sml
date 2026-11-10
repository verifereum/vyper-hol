(* Structural transport at singleton expansion boundaries. *)
Theory lowerDloadSafetyLocations
Ancestors
  lowerDloadSafetyRelation lowerDloadConfiguredOrigins lowerDloadDefs
  venomExecSemantics venomExecProofs venomWf venomInst contextCodegenRel o1ContractLowerDload list rich_list arithmetic

Theorem ld_block_label_unique:
  ALL_DISTINCT (MAP (\b. b.bb_label) bs) /\
  MEM x bs /\ MEM y bs /\ x.bb_label = y.bb_label ==> x = y
Proof
  Induct_on `bs` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[MEM_MAP]
QED

Theorem lower_dload_insts_supply_expansion_next:
  j < LENGTH ins /\
  lower_dload_insts_supply u (TAKE j ins) = (pre,u0) /\
  lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
  LENGTH pre + LENGTH X < LENGTH (FST (lower_dload_insts_supply u ins)) ==>
  SUC j < LENGTH ins /\
  LENGTH (FST (lower_dload_insts_supply u (TAKE (SUC j) ins))) =
    LENGTH pre + LENGTH X
Proof
  rpt strip_tac >>
  `lower_dload_insts_supply u (TAKE (SUC j) ins) = (pre ++ X,u1)` by
    (irule lower_dload_insts_supply_next >> simp[] >> metis_tac[]) >>
  gvs[] >>
  Cases_on `SUC j < LENGTH ins` >> simp[] >>
  `TAKE (SUC j) ins = ins` by (irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
  gvs[]
QED

Theorem ld_envelope_expansion_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope u fn s j X p /\
  t.vs_current_bb = s.vs_current_bb /\
  active_inst (FST (lower_dload_function_supply u fn)) ti
    (t with vs_inst_idx := p + LENGTH X) ==>
  ?next Y. active_inst fn next (s with vs_inst_idx := SUC j) /\
    ld_envelope u fn (s with vs_inst_idx := SUC j) (SUC j) Y (p + LENGTH X)
Proof
  simp[ld_envelope_def, active_inst_def] >> rpt strip_tac >>
  qabbrev_tac `g = FST (lower_dload_function_supply u fn)` >>
  `lower_dload_function_supply u fn =
    (g,SND (lower_dload_function_supply u fn))` by simp[Abbr `g`] >>
  drule lower_dload_function_supply_block_at >>
  disch_then (qspec_then `bi` mp_tac) >> simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `MEM (EL bi fn.fn_blocks with bb_instructions := is) g.fn_blocks` by simp[] >>
  `bb = (EL bi fn.fn_blocks with bb_instructions := is)` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `g.fn_blocks` >> asm_rewrite_tac[]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `j < LENGTH src` >>
  qabbrev_tac `X = FST (lower_dload_inst_supply
    (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src))` >>
  `lower_dload_insts_supply u0 (TAKE j src) =
    (FST (lower_dload_insts_supply u0 (TAKE j src)),
     SND (lower_dload_insts_supply u0 (TAKE j src)))` by simp[] >>
  `lower_dload_inst_supply
     (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src) =
     (X, SND (lower_dload_inst_supply
       (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src)))` by
     (Cases_on `lower_dload_inst_supply
       (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src)` >> gvs[Abbr `X`]) >>
  `LENGTH (FST (lower_dload_insts_supply u0 (TAKE j src))) + LENGTH X <
    LENGTH (FST (lower_dload_insts_supply u0 src))` by simp[] >>
  drule_all lower_dload_insts_supply_expansion_next >> strip_tac >>
  qexists_tac `EL (SUC j) src` >>
  qexists_tac `FST (lower_dload_inst_supply
    (SND (lower_dload_insts_supply u0 (TAKE (SUC j) src))) (EL (SUC j) src))` >>
  conj_tac
  >- (qexists_tac `EL (LENGTH pre) fn.fn_blocks` >>
      simp[Abbr `src`, MEM_EL] >> metis_tac[]) >>
  qexists_tac `LENGTH pre` >> simp[Abbr `src`]
QED

Theorem ld_envelope_ordinary:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ld_envelope u fn s s.vs_inst_idx X p /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES ==>
  X = [inst]
Proof
  simp[active_inst_def, ld_envelope_def] >> rpt strip_tac >>
  `bb = EL bi fn.fn_blocks` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `fn.fn_blocks` >> simp[MEM_EL] >> metis_tac[]) >>
  gvs[] >> simp[lower_dload_inst_supply_def]
QED

Theorem ld_sync_ordinary_envelope:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES ==>
  ?p. ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
      t.vs_inst_idx = p
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `?X p. ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
         t.vs_inst_idx = p` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[] >> strip_tac >>
     qpat_x_assum `!j. _ ==> ?X. ld_envelope _ _ _ _ X _`
       (qspec_then `0` mp_tac) >> simp[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_envelope_active_head:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope u fn s j X p /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = p /\
  active_inst (FST (lower_dload_function_supply u fn)) ti t ==>
  0 < LENGTH X /\ ti = EL 0 X
Proof
  simp[ld_envelope_def, active_inst_def] >> strip_tac >>
  qabbrev_tac `g = FST (lower_dload_function_supply u fn)` >>
  `lower_dload_function_supply u fn =
    (g,SND (lower_dload_function_supply u fn))` by simp[Abbr `g`] >>
  drule lower_dload_function_supply_block_at >>
  disch_then (qspec_then `bi` mp_tac) >> simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `bb = (EL bi fn.fn_blocks with bb_instructions := is)` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `g.fn_blocks` >> simp[]) >>
  gvs[] >>
  drule_all lower_dload_insts_supply_at >> strip_tac >>
  `X <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  gvs[] >> Cases_on `X` >> gvs[EL_APPEND]
QED

(* Source activity suffices for forward expansion-boundary transport. *)
Theorem ld_envelope_source_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope u fn s j X p /\
  s'.vs_current_bb = s.vs_current_bb /\
  active_inst fn next (s' with vs_inst_idx := SUC j) ==>
  ?Y. ld_envelope u fn (s' with vs_inst_idx := SUC j)
        (SUC j) Y (p + LENGTH X)
Proof
  simp[ld_envelope_def, active_inst_def] >> rpt strip_tac >>
  `bb = EL bi fn.fn_blocks` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `fn.fn_blocks` >> simp[MEM_EL] >> metis_tac[]) >>
  gvs[] >> qexists_tac `bi` >> simp[] >>
  qmatch_goalsub_abbrev_tac `lower_dload_insts_supply ub (TAKE j ins)` >>
  Cases_on `lower_dload_insts_supply ub (TAKE j ins)` >>
  rename1 `lower_dload_insts_supply ub (TAKE j ins) = (pre,ui)` >>
  Cases_on `lower_dload_inst_supply ui (EL j ins)` >>
  rename1 `lower_dload_inst_supply ui (EL j ins) = (out,un)` >>
  `j < LENGTH ins` by (gvs[Abbr `ins`]) >>
  drule_all lower_dload_insts_supply_next >> simp[]
QED

val _ = if null (hyp ld_envelope_source_next) then ()
        else raise Fail "ld_envelope_source_next has hypotheses";

(* Reverse expansion at a fetched target successor, in post-step coordinates. *)
Theorem ld_envelope_successor_location:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope supply fn s j X p /\
  fn' = FST (lower_dload_function_supply supply fn) /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X /\
  ss.vs_current_bb = s.vs_current_bb /\
  lookup_block q.vs_current_bb fn'.fn_blocks = SOME bb /\
  get_instruction bb q.vs_inst_idx = SOME ti ==>
  ?next Y. active_inst fn next (ss with vs_inst_idx := SUC j) /\
    ld_envelope supply fn (ss with vs_inst_idx := SUC j) (SUC j) Y (p + LENGTH X)
Proof
  strip_tac >>
  `active_inst fn' ti (q with vs_inst_idx := p + LENGTH X)` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM,
               venomExecProofsTheory.lookup_block_label]) >>
  `?next Y. active_inst fn next (s with vs_inst_idx := SUC j) /\
     ld_envelope supply fn (s with vs_inst_idx := SUC j) (SUC j) Y (p + LENGTH X)` by
    (irule ld_envelope_expansion_next >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`q`,`ti`] >> metis_tac[]) >>
  fs[active_inst_def, ld_envelope_def] >> metis_tac[]
QED

val _ = if null (hyp ld_envelope_successor_location) then ()
        else raise Fail "envelope successor location has hypotheses";

Theorem ld_envelope_successor_head:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope supply fn s j X p /\
  fn' = FST (lower_dload_function_supply supply fn) /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X /\
  ss.vs_current_bb = s.vs_current_bb /\ active_inst fn' ti q ==>
  ?next Y. active_inst fn next (ss with vs_inst_idx := SUC j) /\
    ld_envelope supply fn (ss with vs_inst_idx := SUC j) (SUC j) Y (p + LENGTH X) /\
    0 < LENGTH Y /\ ti = EL 0 Y
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (Cases_on `lower_dload_function_supply supply fn` >> gvs[] >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  drule_all lowerDloadSafetyAmbientTheory.ld_active_lookup >> strip_tac >>
  `get_instruction bb q.vs_inst_idx = SOME ti` by simp[get_instruction_def] >>
  drule_all ld_envelope_successor_location >> strip_tac >>
  `0 < LENGTH Y /\ ti = EL 0 Y` by
    (irule ld_envelope_active_head >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `q` >> gvs[]) >>
  qexistsl_tac [`next`,`Y`] >> simp[]
QED
