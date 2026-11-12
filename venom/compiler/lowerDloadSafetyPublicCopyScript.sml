Theory lowerDloadSafetyPublicCopy
Ancestors
  lowerDloadOracleCallAssembly lowerDloadExternalBoundary
  lowerDloadSafetyWriteAssembly lowerDloadSafetyReadCoverage
  lowerDloadSafetyAccountReadEffects lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadSafetyKernel lowerDloadSafetyRelation ptrDiscipline
  lowerDloadSafetyAssemblyPremises contextCodegenRel codegenRel memLocDefs pointerConfinedDefs venomWf venomInst venomExecSemantics venomState
  finite_map pred_set list words arithmetic

(* Non-address operands of a public write cannot carry selected pointers. *)
Theorem ld_public_copy_scalar_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len] /\ MEM op [src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\ MEM op [addr;src;len])) /\
  op = Var v ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_use_ok_def] >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  fs[MEM] >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `dst = Var v` >> gvs[AllCaseEqs()]
QED

Theorem ld_public_copy_scalar_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len] /\ MEM op [src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\ MEM op [addr;src;len])) ==>
  eval_operand op f.lf_src = eval_operand op f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM op inst.inst_operands` by (fs[MEM] >> gvs[]) >>
  `!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    metis_tac[ld_public_copy_scalar_nonpointer] >>
  `op_prov f.lf_H op = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  irule ld_vars_operand_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >> conj_tac
  >- (irule ld_numeric_operand_nonopaque >> simp[] >>
      qexists_tac `inst` >> simp[] >> fs[MEM] >> gvs[]) >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[] >>
     fs[MEM] >> gvs[]) >>
  gvs[op_taint_def]
QED

val _ = if null (hyp ld_public_copy_scalar_nonpointer) andalso
           null (hyp ld_public_copy_scalar_equal) then ()
        else raise Fail "public copy operand lemmas have hypotheses";

(* Operational inversion only; the common byte list is the actual write. *)
Theorem ld_public_copy_steps:
  ld_nonghost tn s t /\
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len] /\
    eval_operand addr s = eval_operand addr t)) /\
  eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
  eval_operand src s = eval_operand src t /\
  eval_operand len s = eval_operand len t /\
  step_inst_base inst t = OK ts ==>
  ?off n xs. eval_operand src s = SOME off /\
    eval_operand len s = SOME n /\ LENGTH xs = w2n n /\
    ts = write_memory_with_expansion (w2n y) xs t /\
    step_inst_base inst s = OK (write_memory_with_expansion (w2n x) xs s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_code = t.vs_code /\
   s.vs_call_ctx = t.vs_call_ctx /\ s.vs_returndata = t.vs_returndata` by
    fs[ld_nonghost_def] >>
  `!a. (lookup_account a s.vs_accounts).code =
       (lookup_account a t.vs_accounts).code` by
    (gen_tac >> drule ld_nonghost_account_code >> simp[]) >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[MEM] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ bytes t` >>
  qexists_tac `bytes` >> simp[Abbr `bytes`, LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem ld_public_copy_dispatch:
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst_base inst t = OK ts ==>
  ?dst src len addr y.
    ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
      inst.inst_operands = [dst;src;len]) \/
     (inst.inst_opcode = EXTCODECOPY /\
      inst.inst_operands = [addr;dst;src;len])) /\
    eval_operand dst t = SOME y
Proof
  strip_tac >> qpat_x_assum `MEM _ _` mp_tac >>
  simp[MEM] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_public_copy_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?dst src len addr x y off n xs.
    ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
      inst.inst_operands = [dst;src;len]) \/
     (inst.inst_opcode = EXTCODECOPY /\
      inst.inst_operands = [addr;dst;src;len])) /\
    eval_operand dst f.lf_src = SOME x /\
    eval_operand dst f.lf_tgt = SOME y /\
    eval_operand src f.lf_src = SOME off /\
    eval_operand len f.lf_src = SOME n /\ LENGTH xs = w2n n /\
    (op_prov f.lf_H dst = NONE ==> x = y) /\
    (!k. op_prov f.lf_H dst = SOME k ==> ld_wordrel A (SOME k) x y) /\
    ts = write_memory_with_expansion (w2n y) xs f.lf_tgt /\
    step_inst_base inst f.lf_src =
      OK (write_memory_with_expansion (w2n x) xs f.lf_src)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_public_copy_dispatch >> strip_tac >>
  `!op. MEM op [src;len] \/ (inst.inst_opcode = EXTCODECOPY /\ op = addr) ==>
    eval_operand op f.lf_src = eval_operand op f.lf_tgt` by
    (rpt strip_tac >> irule ld_public_copy_scalar_equal >>
     simp[Excl "MEM"] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     gvs[MEM]) >>
  `MEM dst inst.inst_operands` by (fs[MEM] >> gvs[]) >>
  `op_taint tn dst = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[] >> fs[MEM] >> gvs[]) >>
  `?x. eval_operand dst f.lf_src = SOME x /\
     (op_prov f.lf_H dst = NONE ==> x = y) /\
     (!k. op_prov f.lf_H dst = SOME k ==> ld_wordrel A (SOME k) x y)` by
    (irule ld_numeric_operand_observation >> simp[] >>
     conj_tac >- (qexists_tac `tn` >> simp[]) >>
     conj_tac >- (qexists_tac `inst` >> simp[] >> fs[MEM] >> gvs[]) >>
     qexists_tac `P` >> simp[]) >>
  `?off n xs. eval_operand src f.lf_src = SOME off /\
    eval_operand len f.lf_src = SOME n /\ LENGTH xs = w2n n /\
    ts = write_memory_with_expansion (w2n y) xs f.lf_tgt /\
    step_inst_base inst f.lf_src =
      OK (write_memory_with_expansion (w2n x) xs f.lf_src)` by
    (irule ld_public_copy_steps >> simp[] >>
     qexists_tac `tn` >> simp[]) >>
  qexistsl_tac [`dst`,`src`,`len`,`addr`,`x`,`y`,`off`,`n`,`xs`] >> simp[]
QED

val _ = if List.all (null o hyp)
  [ld_public_copy_steps, ld_public_copy_dispatch, ld_public_copy_operands]
  then () else raise Fail "public copy step/operand lemmas have hypotheses";

Theorem ld_public_copy_taint:
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  inst.inst_outputs = [] /\ 2 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst s = [(ro,LENGTH xs)] ==>
  step_taint inst s (write_memory_with_expansion ro xs s) tn =
    tn with t_mem := tn.t_mem DIFF {ro+j | j < LENGTH xs}
Proof
  strip_tac >>
  `written_taint tn inst s = {} /\ out_taint tn inst s = {}` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >>
     fs[written_taint_def, out_taint_def, MEM] >>
     Cases_on `t` >> simp[]) >>
  `new_site_bytes s (write_memory_with_expansion ro xs s) = {}` by
    (simp[new_site_bytes_def, write_memory_with_expansion_def,
          write_memory_def, EXTENSION] >> rpt strip_tac >>
     Cases_on `aid IN FDOM s.vs_allocas` >> fs[FLOOKUP_DEF]) >>
  `range_bytes (step_writes inst s (write_memory_with_expansion ro xs s)) =
    {ro+j | j < LENGTH xs}` by
    (fs[MEM] >> gvs[step_writes_def, range_bytes_def, EXTENSION] >>
     gen_tac >> (eq_tac
     >- (strip_tac >> qexists_tac `x-ro` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac)) >>
  Cases_on `tn` >> fs[MEM] >>
  gvs[step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, set_var_taint_def, taint_component_equality,
      DRESTRICT_UNIV]
QED

Theorem ld_public_copy_write_range:
  ((MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY] /\
    inst.inst_operands = [dst;src;len]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;len])) /\
  eval_operand dst s = SOME x /\ eval_operand src s = SOME off /\
  eval_operand len s = SOME n /\ step_inst_base inst s = OK ss ==>
  source_memory_write_ranges inst s = [(w2n x,w2n n)] /\
  ?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = dst
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  simp[source_memory_write_ranges_def, sized_source_write_range_def,
       mem_write_ops_def] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> simp[]
QED

(* Relational boundary for a public byte write; operand transport is separate. *)
Theorem ld_public_copy_effect:
  (xs = [] \/ (ro = rt /\ ro+LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     ro = b+delta /\ rt = c+delta /\ delta+LENGTH xs <= sz)) /\
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  inst.inst_outputs = [] /\ 2 < LENGTH inst.inst_operands /\
  source_memory_write_ranges inst f.lf_src = [(ro,LENGTH xs)] /\
  step_inst_base inst f.lf_src = OK (write_memory_with_expansion ro xs f.lf_src) /\
  ts = write_memory_with_expansion rt xs f.lf_tgt /\
  (!a. a IN FRANGE f.lf_H ==> a IN FDOM A) ==>
  ?ss H'. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qexistsl [`write_memory_with_expansion ro xs f.lf_src`, `f.lf_H`] >>
  qpat_x_assum `ts = _` SUBST_ALL_TAC >>
  drule_all ld_public_copy_taint >>
  disch_then (qspec_then `tn` SUBST1_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- gvs[ld_vars_def, write_memory_with_expansion_def, write_memory_def] >>
  conj_tac
  >- (irule ld_memory_write_classified >> simp[] >>
      conj_tac >- metis_tac[ld_alloc_bounds] >>
      metis_tac[ld_alloc_separate]) >>
  conj_tac >- gvs[ld_nonghost_def, write_memory_with_expansion_def, write_memory_def] >>
  conj_tac >- (fs[MEM] >> simp[step_prov_def, set_prov_def, DRESTRICT_UNIV]) >>
  simp[write_memory_with_expansion_def, write_memory_def]
QED

Theorem ld_sync_public_copy_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ~in_revert_forward fn s /\ t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `inst_wf inst` by
    (drule ld_sync_source >> simp[active_inst_def] >> strip_tac >>
     fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]` by simp[] >>
  drule_all ld_public_copy_operands >> rpt strip_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` kall_tac >>
  `source_memory_write_ranges inst f.lf_src = [(w2n x,LENGTH xs)] /\
   ?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = dst` by
    (simp[] >> irule ld_public_copy_write_range >> simp[] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (fs[inst_wf_def, MEM] >> rpt strip_tac >> gvs[] >>
     Cases_on `inst.inst_outputs` >> gvs[]) >>
  (Q.SUBGOAL_THEN `xs = [] \/ (w2n x = w2n y /\ w2n x+LENGTH xs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n x=b+delta /\ w2n y=c+delta /\ delta+LENGTH xs <= sz)` ASSUME_TAC >-
    (Cases_on `xs = []` >- simp[] >>
     `0 < LENGTH xs` by (Cases_on `xs` >> gvs[]) >>
     `MEM (w2n x,LENGTH xs) (source_memory_write_ranges inst f.lf_src)` by simp[] >>
     `(op_prov f.lf_H ops.iao_ofst = NONE ==> x = y) /\
      (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) x y)` by simp[] >>
     drule_all ld_write_access_classified >> simp[] >> metis_tac[])) >>
  `EVERY (ld_maps A) (f::fs)` by simp[] >>
  `2 < LENGTH inst.inst_operands` by simp[] >>
  qpat_assum `FDOM A = ld_slots A (f::fs)`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  irule ld_public_copy_effect >>
  (conj_tac >- simp[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qexistsl [`w2n x`, `w2n y`, `xs`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (qexists `f::fs` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

