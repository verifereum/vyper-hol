(* Structural transport at singleton expansion boundaries. *)
Theory lowerDloadSafetyLocations
Ancestors
  lowerDloadSafetyRelation lowerDloadConfiguredOrigins lowerDloadDefs
  venomExecSemantics venomWf venomInst contextCodegenRel o1ContractLowerDload list rich_list arithmetic

Theorem lower_dload_insts_supply_singleton_next:
  j < LENGTH ins /\
  lower_dload_insts_supply u (TAKE j ins) = (pre,u0) /\
  lower_dload_inst_supply u0 (EL j ins) = ([inst],u1) /\
  SUC (LENGTH pre) < LENGTH (FST (lower_dload_insts_supply u ins)) ==>
  SUC j < LENGTH ins /\
  LENGTH (FST (lower_dload_insts_supply u (TAKE (SUC j) ins))) =
    SUC (LENGTH pre)
Proof
  rpt strip_tac >>
  `lower_dload_insts_supply u (TAKE (SUC j) ins) = (pre ++ [inst],u1)` by
    (irule lower_dload_insts_supply_next >> simp[] >> metis_tac[]) >>
  gvs[] >>
  Cases_on `SUC j < LENGTH ins` >> simp[] >>
  `TAKE (SUC j) ins = ins` by (irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
  gvs[]
QED

Theorem ld_envelope_singleton_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope u fn s j [inst] p /\
  t.vs_current_bb = s.vs_current_bb /\
  active_inst (FST (lower_dload_function_supply u fn)) ti
    (t with vs_inst_idx := SUC p) ==>
  ?next Y. active_inst fn next (s with vs_inst_idx := SUC j) /\
    ld_envelope u fn (s with vs_inst_idx := SUC j) (SUC j) Y (SUC p)
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
    (`!bs x y. ALL_DISTINCT (MAP (\b. b.bb_label) bs) /\
        MEM x bs /\ MEM y bs /\ x.bb_label = y.bb_label ==> x = y` by
       (Induct >> simp[] >> rpt strip_tac >> gvs[] >>
        metis_tac[MEM_MAP]) >>
     first_x_assum irule >> conj_tac >- simp[] >>
     qexists_tac `g.fn_blocks` >> asm_rewrite_tac[]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `j < LENGTH src` >>
  `lower_dload_insts_supply u0 (TAKE j src) =
    (FST (lower_dload_insts_supply u0 (TAKE j src)),
     SND (lower_dload_insts_supply u0 (TAKE j src)))` by simp[] >>
  `lower_dload_inst_supply
     (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src) =
     ([inst], SND (lower_dload_inst_supply
       (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src)))` by
     (Cases_on `lower_dload_inst_supply
       (SND (lower_dload_insts_supply u0 (TAKE j src))) (EL j src)` >> gvs[]) >>
  `SUC (LENGTH (FST (lower_dload_insts_supply u0 (TAKE j src)))) <
    LENGTH (FST (lower_dload_insts_supply u0 src))` by simp[] >>
  drule_all lower_dload_insts_supply_singleton_next >> strip_tac >>
  qexists_tac `EL (SUC j) src` >>
  qexists_tac `FST (lower_dload_inst_supply
    (SND (lower_dload_insts_supply u0 (TAKE (SUC j) src))) (EL (SUC j) src))` >>
  conj_tac
  >- (qexists_tac `EL (LENGTH pre) fn.fn_blocks` >>
      simp[Abbr `src`, MEM_EL] >> metis_tac[]) >>
  qexists_tac `LENGTH pre` >> simp[Abbr `src`]
QED
