Theory concretizePtrDallocaEndpointDemands
Ancestors
  concretizePtrDallocaRuntimeSteps concretizePtrDallocaDisciplineTransport
  concretizePtrValueTransport concretizePtrDallocaGhostInterface
  concretizePtrScalarCoreProducer concretizePtrShiftProducer
  concretizePtrReturnTransport lowerDloadPtrDalloca
  concretizePtrPrefixLedger concretizePtrOpaqueRetpc o1FrameLockstep
  basePtrProofs blockPrefixEquiv ptrDiscipline venomExecSemantics venomState venomInst
  concretizeLayoutLocalShifts contextCodegenRel finite_map pred_set words list

(* A tainted MUL operand need not preserve the unit selector.  Its other
   operand can be the clean zero selector, so this violates no discipline. *)
Theorem ptr_dalloca_mul_selector_probe:
  word_agree_except UNIV (1w:bytes32) 2w /\
  taint_ok fn (entry_taint with t_var := FEMPTY |+ ("x",UNIV))
    ((ARB:instruction) with <| inst_opcode := MUL;
      inst_operands := [Var "x"; Lit 0w] |>)
    ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",1w)) /\
  ~(eval_operand (Var "x")
      ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",1w)) = SOME 1w <=>
    eval_operand (Var "x")
      ((ARB:venom_state) with vs_vars := FEMPTY |+ ("x",2w)) = SOME 1w)
Proof
  simp[word_agree_except_def, taint_ok_def, entry_taint_def,
       op_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       source_memory_read_ranges_def, dimword_def] >>
  rpt strip_tac >> gvs[op_taint_def] >>
  simp[eval_operand_def]
QED

Theorem ptr_dalloca_mul_mask_clean[local]:
  inst.inst_opcode = MUL /\ inst.inst_operands = [a;b] /\
  taint_ok fn tn inst s /\
  (!op. MEM op [a;b] ==> op_taint tnt op SUBSET op_taint tn op) /\
  (!op. MEM op [a;b] /\ op_taint tn op = {} ==>
    eval_operand op s = eval_operand op t) ==>
  out_taint tnt inst t SUBSET out_taint tn inst s
Proof
  strip_tac >>
  `op_taint tn a = {} \/ op_taint tn b = {}` by
    (Cases_on `op_taint tn a = {}` >- simp[] >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> strip_tac >>
     first_x_assum (qspec_then `a` mp_tac) >> simp[] >>
     strip_tac >> gvs[]) >>
  `!op. MEM op [a;b] /\ op_taint tn op = {} ==> op_taint tnt op = {}` by
    metis_tac[SUBSET_EMPTY] >>
  `op_taint tn a = {} ==> eval_operand a s = eval_operand a t` by metis_tac[MEM] >>
  `op_taint tn b = {} ==> eval_operand b s = eval_operand b t` by metis_tac[MEM] >>
  gvs[out_taint_def] >>
  rpt IF_CASES_TAC >> gvs[] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_output_mask_clean:
  (!op. MEM op inst.inst_operands ==> op_taint tnt op SUBSET op_taint tn op) /\
  (!a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)) /\
  taint_ok fn tn inst s /\
  (!op. MEM op inst.inst_operands /\ op_taint tn op = {} ==>
    eval_operand op s = eval_operand op t) /\
  (!a b. inst.inst_operands = [a;b] /\
    (inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR) ==>
    eval_operand a s = eval_operand a t) ==>
  out_taint tnt inst t SUBSET out_taint tn inst s
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> gvs[out_taint_def] >>
  rename1 `a::ops` >> Cases_on `ops`
  >- (gvs[] >> Cases_on `eval_operand a t` >> simp[] >>
      rename1 `eval_operand a t = SOME wt` >>
      qpat_x_assum `!wt'. _` (qspec_then `wt` mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      rpt IF_CASES_TAC >> gvs[]) >>
  rename1 `a::b::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `inst.inst_opcode = MUL`
  >- (drule ptr_dalloca_mul_mask_clean >> simp[] >>
      disch_then drule >> simp[] >> disch_then drule >> simp[] >>
      disch_then drule >> simp[] >>
      simp[out_taint_def]) >>
  Cases_on `inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR`
  >- (fs[] >> Cases_on `eval_operand a t` >> gvs[] >>
      irule shift_taint_mono >> simp[]) >>
  Cases_on `eval_operand a t` >> simp[]
QED

(* Direct-mask boundary: the caller supplies mask inclusion through the clean
   operand theorem, not through unit tests on arbitrarily tainted words. *)
Theorem ptr_dalloca_runtime_next_mask:
  ((inst.inst_opcode = ALLOCA /\ instt.inst_opcode = ASSIGN /\
      (?pos. instt.inst_operands = [Lit pos]) /\
      instt.inst_outputs = inst.inst_outputs) \/
   (inst.inst_opcode <> ALLOCA /\ instt = inst)) /\
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     ?a b. inst.inst_operands = [a;b]) /\
  (inst.inst_opcode = ASSIGN ==> ?op. inst.inst_operands = [op]) /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     !op. MEM op inst.inst_operands ==>
       ptr_nonopaque_operand f op /\ op_taint tn op = {}) /\
  LENGTH PT = LENGTH PG /\ LENGTH PG = LENGTH PGt /\
  (!k site. k < LENGTH PG /\ EL k PGt = SOME site ==>
     EL k PG = SOME site /\ EL k PT = NONE) /\
  (!k site. k < LENGTH PG /\ EL k PT = NONE /\ EL k PG = SOME site ==>
     EL k PGt = SOME site) /\
  (!k site. k < LENGTH PGt /\ EL k PGt = SOME site ==>
     EL k s.vs_params = EL k t.vs_params) /\
  s.vs_fmp = t.vs_fmp /\
  (inst.inst_opcode = DALLOCA ==>
     eval_operands inst.inst_operands s = eval_operands inst.inst_operands t) /\
  (inst.inst_opcode <> ALLOCA ==>
     out_taint tnt inst t SUBSET out_taint tn inst s) /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct instt t = OK t' ==>
  ptr_dalloca_ghost_vars (step_prov PG G inst s') (step_taint inst s s' tn).t_var
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
    (step_prov PGt Gt instt t') (step_taint instt t t' tnt).t_var
    (t' with vs_inst_idx := SUC t.vs_inst_idx) /\
  (!v site. FLOOKUP (step_prov PGt Gt instt t') v = SOME site ==>
     FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE) /\
  (!v site. FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE /\
     FLOOKUP (step_prov PG G inst s') v = SOME site ==>
     FLOOKUP (step_prov PGt Gt instt t') v = SOME site)
Proof
  strip_tac
  >- (irule ptr_dalloca_runtime_static_next >> metis_tac[]) >>
  qpat_x_assum `instt = inst` SUBST_ALL_TAC >>
  `!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE` by
    (fs[ptr_dalloca_ghost_vars_def] >> metis_tac[]) >>
  drule_all ptr_dalloca_runtime_next_sites >>
  disch_then (qspec_then `token` strip_assume_tac) >>
  reverse conj_tac >- metis_tac[] >>
  simp[step_prov_def, step_taint_def] >>
  irule ptr_dalloca_runtime_set_vars >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_set_inst_idx] >>
      `MEM v inst.inst_outputs` by simp[] >>
      drule_all ptr_dalloca_runtime_next_values >> simp[]) >>
  simp[lookup_var_set_inst_idx] >> rpt strip_tac >>
  metis_tac[step_inst_preserves_lookup]
QED

Theorem ptr_dalloca_mul_clean_demands:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP (TG:(string,num # num) fmap) v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\
  s.vs_labels = t.vs_labels /\ inst.inst_opcode = MUL ==>
  !op. MEM op inst.inst_operands /\ op_taint tn op = {} ==>
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
     (inst.inst_opcode <> MUL ==> op_taint tn op = {})) inst.inst_operands` by
    (irule ptr_scalar_core_operand_discipline >> simp[] >> metis_tac[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `ptr_nonopaque_operand fn op /\ op_prov TG op = NONE` by metis_tac[] >>
  drule_all ptr_mixed_vars_eval >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

Theorem ptr_dalloca_shift_count_demands:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP (TG:(string,num # num) fmap) v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\
  s.vs_labels = t.vs_labels /\ MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n;a] ==>
  eval_operand n s = eval_operand n t
Proof
  strip_tac >> drule_all ptr_shift_operand_discipline >> simp[] >>
  strip_tac >>
  qpat_x_assum `ptr_nonopaque_operand fn a` kall_tac >>
  drule_all ptr_mixed_vars_eval >>
  Cases_on `eval_operand n s` >> Cases_on `eval_operand n t` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

(* Scalar equality is demanded only where the mask inspects a scalar value.
   Clean ADD/SUB pointers may relocate and need not have equal values. *)
Theorem ptr_dalloca_runtime_mask_demands:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP (TG:(string,num # num) fmap) v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels /\
  (!op. MEM op inst.inst_operands ==> op_taint tnt op SUBSET op_taint tn op) /\
  (!a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)) ==>
  out_taint tnt inst t SUBSET out_taint tn inst s
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = MUL`
  >- (irule ptr_dalloca_output_mask_clean >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      metis_tac[ptr_dalloca_mul_clean_demands]) >>
  `!a b. inst.inst_operands = [a;b] /\
     (inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR) ==>
     eval_operand a s = eval_operand a t` by
    (rpt strip_tac >> irule ptr_dalloca_shift_count_demands >>
     simp[] >> metis_tac[MEM]) >>
  Cases_on `inst.inst_operands` >> gvs[out_taint_def] >>
  rename1 `a::ops` >> Cases_on `ops`
  >- (gvs[] >> Cases_on `eval_operand a t` >> simp[] >>
      rename1 `eval_operand a t = SOME wt` >>
      qpat_x_assum `!wt'. _` (qspec_then `wt` mp_tac) >>
      simp[] >> strip_tac >> simp[] >> rpt IF_CASES_TAC >> gvs[]) >>
  rename1 `a::b::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR`
  >- (fs[] >> Cases_on `eval_operand a t` >> gvs[] >>
      irule shift_taint_mono >> simp[]) >>
  Cases_on `eval_operand a t` >> simp[]
QED

Theorem ptr_dalloca_positive_retention:
  ptr_ledger_erases dyn births TG G /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  (!owner b sz. FLOOKUP births owner = SOME (b,sz) ==> b + sz <= dyn) ==>
  !v b sz. FLOOKUP G v = SOME (b,sz) /\ dyn <= b /\ 0 < sz ==>
    FLOOKUP Gt v = SOME (b,sz)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP TG v` >- metis_tac[] >>
  fs[ptr_ledger_erases_def] >>
  qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >>
  simp[ptr_owner_erases_def] >> strip_tac >>
  `b + sz <= dyn` by metis_tac[] >> fs[]
QED

Theorem ptr_dalloca_runtime_demands:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP (TG:(string,num # num) fmap) v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels /\
  (!op. MEM op inst.inst_operands ==> op_taint tnt op SUBSET op_taint tn op) /\
  (!a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)) ==>
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     !op. MEM op inst.inst_operands ==>
       ptr_nonopaque_operand fn op /\ op_taint tn op = {}) /\
  (inst.inst_opcode = DALLOCA ==>
     eval_operands inst.inst_operands s = eval_operands inst.inst_operands t) /\
  out_taint tnt inst t SUBSET out_taint tn inst s
Proof
  strip_tac >> conj_tac
  >- (strip_tac >>
      `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
        (irule ptr_nonopaque_instruction_operands >> fs[] >> metis_tac[]) >>
      fs[EVERY_MEM] >> rpt strip_tac >> simp[] >>
      qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
      fs[taint_ok_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (irule ptr_dalloca_runtime_mask_demands >> metis_tac[]) >>
  strip_tac >> irule ptr_mixed_scalar_operands_equal >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  `FDOM TG SUBSET fn_pv P fn` by
    (simp[SUBSET_DEF, TO_FLOOKUP] >> gen_tac >>
     Cases_on `FLOOKUP TG x` >> simp[] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[] >> metis_tac[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `op_prov TG op = NONE /\ op_taint tn op = {}` by
    (irule dalloca_operand_clean >> metis_tac[]) >> simp[]
QED

Theorem ptr_dalloca_compare_transport_positive[local]:
  access_ok lo G fn inst s /\
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!v b sz. FLOOKUP Gt v = SOME (b,sz) ==> dyn <= b) /\
  (!v b sz. FLOOKUP G v = SOME (b,sz) /\ dyn <= b /\ 0 < sz ==>
    FLOOKUP Gt v = SOME (b,sz)) ==>
  !u w. (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
         inst.inst_opcode = EQ) /\ inst.inst_operands = [Var u; Var w] /\
    (u IN FDOM Gt \/ w IN FDOM Gt) ==>
    ?b sz x y. FLOOKUP Gt u = SOME (b,sz) /\ FLOOKUP Gt w = SOME (b,sz) /\
      0 < sz /\ eval_operand (Var u) t = SOME x /\
      eval_operand (Var w) t = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\
      b <= w2n y /\ w2n y <= b + sz
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  `FDOM Gt SUBSET FDOM G` by
    (simp[SUBSET_DEF, TO_FLOOKUP] >> gen_tac >>
     Cases_on `FLOOKUP Gt x` >> simp[] >>
     drule_all ptr_dalloca_ghost_prov >> simp[]) >>
  `?b sz x y. FLOOKUP G u = SOME (b,sz) /\ FLOOKUP G w = SOME (b,sz) /\
      0 < sz /\ eval_operand (Var u) s = SOME x /\
      eval_operand (Var w) s = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\
      b <= w2n y /\ w2n y <= b + sz` by
    (fs[access_ok_def, SUBSET_DEF] >> metis_tac[]) >>
  `dyn <= b` by
    (Cases_on `FLOOKUP Gt u`
     >- (fs[TO_FLOOKUP] >> Cases_on `FLOOKUP Gt w` >> fs[] >>
         rename1 `FLOOKUP Gt w = SOME site` >> PairCases_on `site` >>
         drule_all ptr_dalloca_ghost_prov >> strip_tac >> fs[] >> metis_tac[]) >>
     rename1 `FLOOKUP Gt u = SOME site` >> PairCases_on `site` >>
     drule_all ptr_dalloca_ghost_prov >> strip_tac >> fs[] >> metis_tac[]) >>
  `FLOOKUP Gt u = SOME (b,sz) /\ FLOOKUP Gt w = SOME (b,sz)` by metis_tac[] >>
  fs[ptr_dalloca_ghost_vars_def, eval_operand_def] >> metis_tac[]
QED

Theorem ptr_dalloca_access_transport_positive:
  access_ok lo G fn inst s /\ lo <= eom /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (in_revert_forward fn s ==> in_revert_forward ft t) /\
  (!v b sz. FLOOKUP Gt v = SOME (b,sz) ==> dyn <= b) /\
  (!v b sz. FLOOKUP G v = SOME (b,sz) /\ dyn <= b /\ 0 < sz ==>
    FLOOKUP Gt v = SOME (b,sz)) /\
  (!off len. MEM (off,len) (source_memory_read_ranges inst t) /\ len <> 0 ==>
    ?off_s. MEM (off_s,len) (source_memory_read_ranges inst s) /\
    ((off = off_s /\ (!ops. mem_read_ops inst = SOME ops ==>
        op_prov G ops.iao_ofst = op_prov Gt ops.iao_ofst)) \/
     (off + len <= eom /\ (!ops. mem_read_ops inst = SOME ops ==>
        op_prov Gt ops.iao_ofst = NONE)))) /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst t) /\ len <> 0 ==>
    ?off_s. MEM (off_s,len) (source_memory_write_ranges inst s) /\
    ((off = off_s /\ (!ops. mem_write_ops inst = SOME ops ==>
        op_prov G ops.iao_ofst = op_prov Gt ops.iao_ofst)) \/
     (off + len <= eom /\ (!ops. mem_write_ops inst = SOME ops ==>
        op_prov Gt ops.iao_ofst = NONE)))) ==>
  access_ok eom Gt ft inst t
Proof
  strip_tac >> rewrite_tac[access_ok_def] >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> irule ptr_dalloca_compare_transport_positive >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `~in_revert_forward fn s` by metis_tac[] >>
  qpat_x_assum `access_ok _ _ _ _ _`
    (mp_tac o REWRITE_RULE[access_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 (drule_then strip_assume_tac) kall_tac) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> irule ptr_dalloca_range_transport >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`G`, `source_memory_write_ranges inst s`,
                   `source_memory_write_ranges inst t`] >> fs[] >> gvs[]) >>
  rpt gen_tac >> disch_tac >> irule ptr_dalloca_range_transport >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`, `source_memory_read_ranges inst s`,
               `source_memory_read_ranges inst t`] >> fs[] >> gvs[]
QED

Theorem ptr_dalloca_untagged_op_prov[local]:
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\ op_prov TG op = NONE ==>
  op_prov G op = op_prov Gt op
Proof
  strip_tac >> Cases_on `op` >> gvs[op_prov_def] >>
  rename1 `FLOOKUP TG v = NONE` >>
  qpat_x_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[ptr_dalloca_ghost_vars_def]) >>
  qpat_x_assum `!v. op_taint _ _ SUBSET _` kall_tac >>
  qpat_x_assum `!v site. FLOOKUP Gt v = SOME site ==> _`
    (qspec_then `v` assume_tac) >>
  qpat_x_assum `!v site. FLOOKUP TG v = NONE /\ _ ==> _`
    (qspec_then `v` assume_tac) >>
  Cases_on `FLOOKUP G v` >> Cases_on `FLOOKUP Gt v` >> gvs[]
QED
