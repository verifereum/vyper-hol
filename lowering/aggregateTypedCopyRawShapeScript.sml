Theory aggregateTypedCopyRawShape
Ancestors
  aggregateCodeTrace exprLoweringProps exprSimAbiGasBridge compileEnv fragExec
  list rich_list pair sum emitHelper emitHelperProps sorting venomInst context

Theorem aggregate_typed_store_extends:
  compile_store_memory_typed ce dst dt src st sa = ((),sb) ==>
  cs_extends sa sb
Proof
  strip_tac >>
  mp_tac (cj 1 ci_mono_typed_memory_family) >>
  disch_then (qspecl_then [`ce`, `dst`, `dt`, `src`, `st`, `sa`] mp_tac) >>
  simp[ci_mono_def]
QED

Definition trace_instructions_def:
  (trace_instructions [] = []) /\
  (trace_instructions (INL i :: tr) = i :: trace_instructions tr) /\
  (trace_instructions (INR l :: tr) = trace_instructions tr)
End

Definition trace_labels_def:
  (trace_labels [] = []) /\
  (trace_labels (INL i :: tr) = trace_labels tr) /\
  (trace_labels (INR l :: tr) = l :: trace_labels tr)
End

Theorem trace_projections_append[simp]:
  (!xs ys. trace_instructions (xs ++ ys) = trace_instructions xs ++ trace_instructions ys) /\
  (!xs ys. trace_labels (xs ++ ys) = trace_labels xs ++ trace_labels ys)
Proof
  conj_tac >> Induct >> simp[trace_instructions_def, trace_labels_def] >>
  Cases_on `h` >> simp[trace_instructions_def, trace_labels_def]
QED

Theorem code_replay_label_history:
  !tr s. if trace_labels tr = [] then
    (code_replay tr s).cs_current_bb = s.cs_current_bb /\
    (code_replay tr s).cs_blocks = s.cs_blocks
  else
    (code_replay tr s).cs_current_bb = LAST (trace_labels tr) /\
    MAP (\bb. bb.bb_label) (code_replay tr s).cs_blocks =
      REVERSE (FRONT (trace_labels tr)) ++ [s.cs_current_bb] ++
      MAP (\bb. bb.bb_label) s.cs_blocks
Proof
  Induct using SNOC_INDUCT
  >- simp[trace_labels_def, code_replay_def] >>
  rpt gen_tac >> Cases_on `x` >>
  Cases_on `trace_labels tr = []` >>
  gvs[SNOC_APPEND, trace_labels_def, code_replay_append, code_replay_def,
      code_event_def, emit_def, new_block_def, FRONT_APPEND, LAST_APPEND] >>
  `trace_labels tr = FRONT (trace_labels tr) ++ [LAST (trace_labels tr)]` by
    simp[APPEND_FRONT_LAST] >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[FRONT_APPEND, LAST_APPEND]
QED

Theorem code_replay_label_shape:
  !tr s. trace_labels tr <> [] ==>
    (code_replay tr s).cs_current_bb = LAST (trace_labels tr) /\
    MAP (\bb. bb.bb_label) (FRONT (emitted_blocks s (code_replay tr s))) =
      REVERSE (FRONT (trace_labels tr))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tr`, `s`] mp_tac code_replay_label_history >> simp[] >> strip_tac >>
  simp[] >>
  `LENGTH (code_replay tr s).cs_blocks =
    LENGTH (FRONT (trace_labels tr)) + 1 + LENGTH s.cs_blocks` by
    (qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH: string list -> num``) >>
     simp[]) >>
  `MAP (\bb. bb.bb_label) (emitted_blocks s (code_replay tr s)) =
    REVERSE (FRONT (trace_labels tr)) ++ [s.cs_current_bb]` by
    (simp[emitted_blocks_def, MAP_TAKE] >>
     rewrite_tac[GSYM APPEND_ASSOC] >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  Cases_on `emitted_blocks s (code_replay tr s)` >> gvs[MAP_FRONT, FRONT_APPEND]
QED

Theorem code_replay_final_label_fresh:
  ALL_DISTINCT (trace_labels tr) ==>
  ~MEM (code_replay tr s).cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks s (code_replay tr s))))
Proof
  strip_tac >> Cases_on `trace_labels tr = []`
  >- (qspecl_then [`tr`, `s`] mp_tac code_replay_label_history >>
      simp[] >> strip_tac >> simp[emitted_blocks_def]) >>
  drule code_replay_label_shape >> disch_then (qspec_then `s` strip_assume_tac) >>
  simp[] >>
  `trace_labels tr = FRONT (trace_labels tr) ++ [LAST (trace_labels tr)]` by
    simp[APPEND_FRONT_LAST] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  simp[ALL_DISTINCT_APPEND, MEM_REVERSE, FRONT_APPEND]
QED

Theorem code_replay_event_instructions:
  PERM
    (frag_code sa (code_replay tr
      (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)) ++
      trace_instructions [ev])
    (frag_code sa (code_event ev (code_replay tr
      (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb))))
Proof
  qspec_then `tr` strip_assume_tac code_replay_shape >> Cases_on `ev` >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def,
    code_event_def, emit_def, new_block_def, code_patch_def,
    trace_instructions_def, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[TAKE_APPEND, DROP_APPEND, FRONT_APPEND, LAST_APPEND,
    TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] >>
  simp[FRONT_DEF, LAST_DEF, FRONT_APPEND, LAST_APPEND] >>
  simp[DROP_LENGTH_APPEND] >>
  rewrite_tac[GSYM APPEND_ASSOC] >> simp[PERM_APPEND_IFF, PERM_APPEND]
QED

Theorem code_replay_instructions:
  !tr sa sb. PERM (trace_instructions tr)
    (frag_code sa (code_replay tr
      (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)))
Proof
  Induct using SNOC_INDUCT
  >- simp[trace_instructions_def, code_replay_def, frag_code_def,
      emitted_blocks_def, emitted_insts_def, code_patch_def] >>
  rpt gen_tac >> simp[SNOC_APPEND, code_replay_append, code_replay_def] >>
  irule PERM_TRANS >>
  qexists_tac `frag_code sa (code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)) ++
      trace_instructions [x]` >>
  conj_tac
  >- simp[PERM_APPEND_IFF] >>
  irule code_replay_event_instructions
QED

Theorem code_replay_ops_free:
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\ i.inst_opcode <> RETURN)
    (trace_instructions tr) ==>
  frag_ops_free sa (code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb))
Proof
  strip_tac >> rewrite_tac[frag_ops_free_def] >>
  qspecl_then [`tr`, `sa`, `sb`] mp_tac code_replay_instructions >>
  metis_tac[PERM_EVERY]
QED

Theorem code_replay_ids_distinct:
  ALL_DISTINCT (MAP (\i. i.inst_id) (trace_instructions tr)) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa (code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb))))
Proof
  strip_tac >>
  qspecl_then [`tr`, `sa`, `sb`] mp_tac code_replay_instructions >>
  metis_tac[PERM_MAP, ALL_DISTINCT_PERM]
QED

Definition trace_certificate_def:
  trace_certificate (sa:compile_state) (sb:compile_state) tr <=>
    sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_label <= sb.cs_next_label /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (trace_instructions tr)) /\
    EVERY (\i. sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
      i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
      i.inst_opcode <> STOP /\ i.inst_opcode <> RETURN) (trace_instructions tr) /\
    ALL_DISTINCT (trace_labels tr) /\
    EVERY (\l. ?suffix k. l = fresh_label_output suffix k /\
      sa.cs_next_label <= k /\ k < sb.cs_next_label) (trace_labels tr)
End

Definition code_trace_certified_def:
  code_trace_certified (m:compile_state -> 'a # compile_state) <=>
    !sa. ?x sb tr. trace_certificate sa sb tr /\
      !B L insts. m (code_patch B L insts sa) =
        (x, code_replay tr (code_patch B L insts sb))
End

Theorem trace_certificate_append:
  trace_certificate sa sm xs /\ trace_certificate sm sb ys ==>
  trace_certificate sa sb (xs ++ ys)
Proof
  simp[trace_certificate_def, EVERY_APPEND, ALL_DISTINCT_APPEND, MAP_APPEND,
    EVERY_MEM] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  metis_tac[fresh_label_output_inj, arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_TRANS,
    arithmeticTheory.NOT_LESS]
QED

Theorem code_trace_certified_bind:
  code_trace_certified m /\ (!x. code_trace_certified (k x)) ==>
  code_trace_certified (comp_bind m k)
Proof
  simp[code_trace_certified_def] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >>
  qpat_x_assum `!x sa. _` (qspecl_then [`x`, `sb`] strip_assume_tac) >>
  rename1 `!B L insts. k x (code_patch B L insts sb) =
    (y, code_replay tr' (code_patch B L insts sc))` >>
  qexistsl_tac [`y`, `sc`, `tr ++ tr'`] >>
  conj_tac >- metis_tac[trace_certificate_append] >>
  simp[comp_bind_def, code_replay_append] >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `k x middle` >>
  `middle = code_patch middle.cs_blocks middle.cs_current_bb middle.cs_current_insts sb` by
    metis_tac[code_patch_self, code_replay_patch, code_patch_overwrite] >>
  pop_assum SUBST1_TAC >> simp[] >>
  simp[code_replay_context, Abbr `middle`] >>
  rewrite_tac[GSYM code_replay_append] >>
  sym_tac >> irule code_replay_patch_context
QED

Theorem code_trace_certified_return:
  code_trace_certified (comp_return x)
Proof
  simp[code_trace_certified_def, comp_return_def] >> gen_tac >>
  qexistsl_tac [`x`, `sa`, `[]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def, code_replay_def]
QED

Theorem code_trace_certified_fresh_id:
  code_trace_certified fresh_id
Proof
  simp[code_trace_certified_def] >> gen_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa with cs_next_id := sa.cs_next_id + 1`, `[]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_patch_def, fresh_id_def]
QED

Theorem code_trace_certified_fresh_var:
  code_trace_certified fresh_var
Proof
  simp[code_trace_certified_def] >> gen_tac >>
  qexistsl_tac [`"%" ++ toString sa.cs_next_var`,
    `sa with cs_next_var := sa.cs_next_var + 1`, `[]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_patch_def, fresh_var_def]
QED

Theorem code_trace_certified_fresh_label:
  code_trace_certified (fresh_label suffix)
Proof
  simp[code_trace_certified_def] >> gen_tac >>
  qexistsl_tac [`fresh_label_output suffix sa.cs_next_label`,
    `sa with cs_next_label := sa.cs_next_label + 1`, `[]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_patch_def, fresh_label_def]
QED

Theorem code_trace_certified_emit_inst:
  ~MEM opc [GAS; INVOKE; PHI; STOP; RETURN] ==>
  code_trace_certified (emit_inst opc ops outs)
Proof
  strip_tac >> simp[code_trace_certified_def] >> gen_tac >>
  qexistsl_tac [`sa with cs_next_id := sa.cs_next_id + 1`,
    `[INL (mk_inst sa.cs_next_id opc ops outs)]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_event_def, code_patch_def, emit_inst_def,
    comp_bind_def, fresh_id_def, emit_def, mk_inst_def] >> gvs[]
QED

Theorem code_trace_certified_ignore_bind:
  code_trace_certified m /\ code_trace_certified n ==>
  code_trace_certified (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule code_trace_certified_bind >> simp[]
QED

Theorem code_trace_certified_emit_void:
  ~MEM opc [GAS; INVOKE; PHI; STOP; RETURN] ==>
  code_trace_certified (emit_void opc ops)
Proof
  simp[emit_void_def, GSYM emit_inst_def, code_trace_certified_emit_inst]
QED

Theorem code_trace_certified_emit_op:
  ~MEM opc [GAS; INVOKE; PHI; STOP; RETURN] ==>
  code_trace_certified (emit_op opc ops)
Proof
  strip_tac >> simp[code_trace_certified_def] >> gen_tac >>
  qexistsl_tac [`Var ("%" ++ toString sa.cs_next_var)`,
    `sa with <|cs_next_id := sa.cs_next_id + 1; cs_next_var := sa.cs_next_var + 1|>`,
    `[INL (mk_inst sa.cs_next_id opc ops ["%" ++ toString sa.cs_next_var])]`] >>
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_event_def, code_patch_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
    fresh_var_def, emit_def, mk_inst_def] >> gvs[]
QED

Theorem trace_certificate_raw_shape:
  trace_certificate sa sb tr ==>
  frag_ops_free sa (code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa (code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)))) /\
  ~MEM (code_replay tr
      (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)).cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa (code_replay tr
      (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb)))))
Proof
  strip_tac >>
  conj_tac
  >- (irule code_replay_ops_free >> gvs[trace_certificate_def, EVERY_MEM]) >>
  conj_tac
  >- (irule code_replay_ids_distinct >> gvs[trace_certificate_def]) >>
  `ALL_DISTINCT (trace_labels tr)` by gvs[trace_certificate_def] >>
  drule code_replay_final_label_fresh >>
  disch_then (qspec_then
    `code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb` mp_tac) >>
  simp[emitted_blocks_def, code_patch_def]
QED

Theorem code_trace_certified_copy_memory:
  code_trace_certified (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def,
    code_trace_certified_return, code_trace_certified_emit_void]
QED

Theorem code_trace_certified_copy_memory_dynamic:
  code_trace_certified (compile_copy_memory_dynamic dst src len)
Proof
  simp[compile_copy_memory_dynamic_def, code_trace_certified_emit_void]
QED

Theorem code_trace_certified_with_byte_offset:
  code_trace_certified (compile_with_byte_offset operand off)
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[code_trace_certified_return, code_trace_certified_emit_op]
QED

Theorem code_trace_certified_store_bytestring:
  code_trace_certified (compile_store_bytestring src dst)
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def, comp_bind_assoc] >>
  irule code_trace_certified_bind >> simp[code_trace_certified_emit_op] >> gen_tac >>
  irule code_trace_certified_bind >> simp[code_trace_certified_emit_op] >> gen_tac >>
  irule code_trace_certified_bind >> simp[code_trace_certified_emit_op] >> gen_tac >>
  irule code_trace_certified_bind >>
  simp[code_trace_certified_emit_op, code_trace_certified_emit_void]
QED

Theorem trace_certificate_weaken:
  trace_certificate sm sn tr /\
  sa.cs_next_id <= sm.cs_next_id /\ sn.cs_next_id <= sb.cs_next_id /\
  sa.cs_next_label <= sm.cs_next_label /\ sn.cs_next_label <= sb.cs_next_label ==>
  trace_certificate sa sb tr
Proof
  simp[trace_certificate_def, EVERY_MEM] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem trace_certificate_join:
  trace_certificate sa sb xs /\ trace_certificate sa sb ys /\
  (!i j. MEM i (trace_instructions xs) /\ MEM j (trace_instructions ys) ==>
    i.inst_id <> j.inst_id) /\
  (!l. MEM l (trace_labels xs) ==> ~MEM l (trace_labels ys)) ==>
  trace_certificate sa sb (xs ++ ys)
Proof
  simp[trace_certificate_def, ALL_DISTINCT_APPEND, EVERY_APPEND, MAP_APPEND,
    MEM_MAP] >> metis_tac[]
QED

Theorem trace_certificate_block:
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_label <= k /\
  k < sb.cs_next_label ==>
  trace_certificate sa sb [INR (fresh_label_output suffix k)]
Proof
  simp[trace_certificate_def, trace_instructions_def, trace_labels_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem trace_certificate_reserved_fresh:
  trace_certificate sm sb tr /\ k < sm.cs_next_label ==>
  ~MEM (fresh_label_output suffix k) (trace_labels tr)
Proof
  simp[trace_certificate_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule fresh_label_output_inj >> strip_tac >> gvs[]
QED


Definition trace_certificate_reserved_def:
  trace_certificate_reserved R (sa:compile_state) (sb:compile_state) tr <=>
    sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_label <= sb.cs_next_label /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (trace_instructions tr)) /\
    EVERY (\i. sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
      i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
      i.inst_opcode <> STOP /\ i.inst_opcode <> RETURN) (trace_instructions tr) /\
    ALL_DISTINCT (trace_labels tr) /\
    EVERY (\l. MEM l R \/ ?suffix k. l = fresh_label_output suffix k /\
      sa.cs_next_label <= k /\ k < sb.cs_next_label) (trace_labels tr)
End

Definition reserved_budget_def:
  reserved_budget R (sa:compile_state) <=>
    ALL_DISTINCT R /\ EVERY (\l. ?suffix k.
      l = fresh_label_output suffix k /\ k < sa.cs_next_label) R
End

Definition code_trace_reserved_def:
  code_trace_reserved R (m:compile_state -> 'a # compile_state) <=>
    !sa. reserved_budget R sa ==> ?x sb tr.
      trace_certificate_reserved R sa sb tr /\
      !B L insts. m (code_patch B L insts sa) =
        (x, code_replay tr (code_patch B L insts sb))
End

Theorem code_trace_reserved_empty[simp]:
  code_trace_reserved [] m <=> code_trace_certified m
Proof
  simp[code_trace_reserved_def, code_trace_certified_def,
    reserved_budget_def, trace_certificate_reserved_def, trace_certificate_def]
QED

Theorem reserved_budget_mono:
  reserved_budget R sa /\ sa.cs_next_label <= sb.cs_next_label ==>
  reserved_budget R sb
Proof
  simp[reserved_budget_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem reserved_budget_append:
  reserved_budget (R ++ rs) sa ==>
  reserved_budget R sa /\ reserved_budget rs sa /\
  (!l. MEM l R ==> ~MEM l rs)
Proof
  simp[reserved_budget_def, ALL_DISTINCT_APPEND, EVERY_APPEND]
QED

Theorem trace_certificate_reserved_append:
  reserved_budget (R ++ rs) sa /\
  trace_certificate_reserved R sa sm xs /\
  trace_certificate_reserved rs sm sb ys ==>
  trace_certificate_reserved (R ++ rs) sa sb (xs ++ ys)
Proof
  simp[reserved_budget_def, trace_certificate_reserved_def,
    EVERY_APPEND, ALL_DISTINCT_APPEND, MAP_APPEND, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rpt (first_x_assum drule >> strip_tac) >>
  gvs[]
  >- (drule fresh_label_output_inj >> strip_tac >> gvs[])
  >- (drule fresh_label_output_inj >> strip_tac >> gvs[])
  >- (drule fresh_label_output_inj >> strip_tac >> gvs[]) >>
  disj2_tac >> qexistsl_tac [`suffix`, `k`] >> simp[]
QED

Theorem code_trace_reserved_bind:
  code_trace_reserved R m /\ (!x. code_trace_reserved rs (k x)) ==>
  code_trace_reserved (R ++ rs) (comp_bind m k)
Proof
  simp[code_trace_reserved_def] >> strip_tac >> gen_tac >> strip_tac >>
  drule reserved_budget_append >> strip_tac >>
  qpat_x_assum `!s. reserved_budget R s ==> _`
    (qspec_then `sa` mp_tac) >> simp[] >> strip_tac >>
  `reserved_budget rs sb` by
    (irule reserved_budget_mono >> qexists_tac `sa` >>
     gvs[trace_certificate_reserved_def]) >>
  qpat_x_assum `!x sa. _` (qspecl_then [`x`, `sb`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `!B L insts. k x (code_patch B L insts sb) =
    (y, code_replay tr' (code_patch B L insts sc))` >>
  qexistsl_tac [`y`, `sc`, `tr ++ tr'`] >>
  conj_tac >- metis_tac[trace_certificate_reserved_append] >>
  simp[comp_bind_def, code_replay_append] >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `k x middle` >>
  `middle = code_patch middle.cs_blocks middle.cs_current_bb middle.cs_current_insts sb` by
    metis_tac[code_patch_self, code_replay_patch, code_patch_overwrite] >>
  pop_assum SUBST1_TAC >> simp[] >>
  simp[code_replay_context, Abbr `middle`] >>
  rewrite_tac[GSYM code_replay_append] >>
  sym_tac >> irule code_replay_patch_context
QED

Theorem code_trace_reserved_weaken:
  code_trace_reserved R m /\ ALL_DISTINCT R /\
  (!l. MEM l R ==> MEM l rs) ==>
  code_trace_reserved rs m
Proof
  simp[code_trace_reserved_def] >> strip_tac >> gen_tac >> strip_tac >>
  `reserved_budget R sa` by
    (gvs[reserved_budget_def, EVERY_MEM] >>
     metis_tac[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexistsl_tac [`x`, `sb`, `tr`] >> simp[] >>
  gvs[trace_certificate_reserved_def, EVERY_MEM] >> metis_tac[]
QED

Theorem code_trace_reserved_lift:
  code_trace_certified m ==> code_trace_reserved R m
Proof
  rewrite_tac[GSYM code_trace_reserved_empty] >> strip_tac >>
  irule code_trace_reserved_weaken >> qexists_tac `[]` >> simp[]
QED

Theorem code_trace_reserved_ignore_bind:
  code_trace_reserved R m /\ code_trace_reserved rs n ==>
  code_trace_reserved (R ++ rs) (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule code_trace_reserved_bind >> simp[]
QED

Theorem code_trace_reserved_new_block_ignore:
  code_trace_reserved [l] (comp_ignore_bind (new_block l) (comp_return ()))
Proof
  simp[code_trace_reserved_def] >> gen_tac >> strip_tac >>
  qexistsl_tac [`sa`, `[INR l]`] >>
  simp[trace_certificate_reserved_def, trace_instructions_def, trace_labels_def,
    code_replay_def, code_event_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def, new_block_def]
QED

Theorem reserved_budget_fresh_label:
  reserved_budget R sa ==>
  reserved_budget (R ++ [fresh_label_output suffix sa.cs_next_label])
    (sa with cs_next_label := sa.cs_next_label + 1)
Proof
  simp[reserved_budget_def, ALL_DISTINCT_APPEND, EVERY_APPEND, EVERY_MEM] >>
  rpt strip_tac
  >- (spose_not_then assume_tac >> first_x_assum drule >> strip_tac >>
      drule fresh_label_output_inj >> strip_tac >> gvs[])
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`suffix`, `k`] >> simp[]) >>
  qexistsl_tac [`suffix`, `sa.cs_next_label`] >> simp[]
QED

Theorem trace_certificate_reserved_fresh_label:
  trace_certificate_reserved (R ++ [fresh_label_output suffix sa.cs_next_label])
    (sa with cs_next_label := sa.cs_next_label + 1) sb tr ==>
  trace_certificate_reserved R sa sb tr
Proof
  simp[trace_certificate_reserved_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  disj2_tac
  >- (qexistsl_tac [`suffix`, `sa.cs_next_label`] >> simp[]) >>
  qexistsl_tac [`suffix'`, `k`] >> simp[]
QED

Theorem code_trace_reserved_fresh_label:
  (!l. code_trace_reserved (R ++ [l]) (k l)) ==>
  code_trace_reserved R (comp_bind (fresh_label suffix) k)
Proof
  simp[code_trace_reserved_def] >> strip_tac >> gen_tac >> strip_tac >>
  drule reserved_budget_fresh_label >>
  disch_then (qspec_then `suffix` assume_tac) >>
  first_x_assum (qspecl_then
    [`fresh_label_output suffix sa.cs_next_label`,
     `sa with cs_next_label := sa.cs_next_label + 1`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`x`, `sb`, `tr`] >>
  conj_tac >- (irule trace_certificate_reserved_fresh_label >>
    qexists_tac `suffix` >> simp[]) >>
  simp[comp_bind_def, fresh_label_def, code_patch_def] >>
  gvs[code_patch_def]
QED

Theorem code_trace_reserved_new_block_bind:
  code_trace_reserved R m ==>
  code_trace_reserved (l :: R) (comp_ignore_bind (new_block l) m)
Proof
  strip_tac >>
  `comp_ignore_bind (new_block l) m =
     comp_ignore_bind (comp_ignore_bind (new_block l) (comp_return ())) m` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def, new_block_def] >>
  pop_assum SUBST1_TAC >>
  `l :: R = [l] ++ R` by simp[] >> pop_assum SUBST1_TAC >>
  irule code_trace_reserved_ignore_bind >>
  simp[code_trace_reserved_new_block_ignore]
QED

Theorem code_trace_certified_fresh_block_probe[local]:
  code_trace_certified
    (comp_bind (fresh_label suffix) (\l.
      comp_ignore_bind (new_block l) (comp_return ())))
Proof
  rewrite_tac[GSYM code_trace_reserved_empty] >>
  irule code_trace_reserved_fresh_label >>
  simp[code_trace_reserved_new_block_ignore]
QED

Theorem code_trace_reserved_bind_left:
  code_trace_certified m /\ (!x. code_trace_reserved R (k x)) ==>
  code_trace_reserved R (comp_bind m k)
Proof
  strip_tac >>
  `R = [] ++ R` by simp[] >> pop_assum SUBST1_TAC >>
  irule code_trace_reserved_bind >> simp[]
QED

Theorem code_trace_reserved_ignore_bind_left:
  code_trace_certified m /\ code_trace_reserved R n ==>
  code_trace_reserved R (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule code_trace_reserved_bind_left >> simp[]
QED

Theorem code_trace_certified_reserve_label:
  (!l. code_trace_reserved [l] (k l)) ==>
  code_trace_certified (comp_bind (fresh_label suffix) k)
Proof
  rewrite_tac[GSYM code_trace_reserved_empty] >> strip_tac >>
  irule code_trace_reserved_fresh_label >> simp[]
QED

val certified_primitives = [code_trace_certified_emit_op,
  code_trace_certified_emit_void, code_trace_certified_emit_inst,
  code_trace_certified_return, code_trace_certified_fresh_var,
  code_trace_certified_fresh_label, code_trace_certified_fresh_id,
  code_trace_certified_copy_memory, code_trace_certified_with_byte_offset];

val reserved_sequence = rpt (FIRST [
  irule code_trace_certified_reserve_label,
  irule code_trace_reserved_fresh_label,
  irule code_trace_reserved_new_block_bind,
  irule (SRULE [comp_ignore_bind_def] code_trace_reserved_new_block_bind),
  irule code_trace_certified_bind >> conj_tac,
  irule code_trace_certified_ignore_bind >> conj_tac,
  irule code_trace_reserved_bind_left >> conj_tac,
  irule code_trace_reserved_ignore_bind_left >> conj_tac,
  gen_tac] >> simp certified_primitives);

Theorem code_trace_certified_sarray:
  (~(type_memory_bytes ce dt = type_memory_bytes ce st /\
      ~is_abi_dynamic ce.ce_struct_fields dt) ==>
    !d s. code_trace_certified (compile_store_memory_typed ce d dt s st)) ==>
  code_trace_certified (compile_copy_sarray_typed ce dst dt src st n)
Proof
  strip_tac >> simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- simp[code_trace_certified_copy_memory] >>
  first_x_assum drule >> strip_tac >>
  rewrite_tac[GSYM code_trace_reserved_empty] >> reserved_sequence
QED

Theorem code_trace_certified_dynarray:
  (~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) ==>
    !d s. code_trace_certified (compile_store_memory_typed ce d dt s st)) ==>
  code_trace_certified (compile_copy_dynarray_typed ce dst dt cap src st)
Proof
  strip_tac >> simp[Once compile_store_memory_typed_def] >>
  rewrite_tac[GSYM code_trace_reserved_empty] >> reserved_sequence >>
  IF_CASES_TAC
  >- (simp[compile_copy_memory_dynamic_def] >> reserved_sequence) >>
  first_x_assum drule >> strip_tac >> reserved_sequence
QED

Theorem code_trace_certified_typed_copy_family:
  (!ce dst dt src st. code_trace_certified (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dts sts doff soff.
     code_trace_certified (compile_typed_copy_fields ce dst src dts sts doff soff)) /\
  (!ce dst dt src st n.
     code_trace_certified (compile_copy_sarray_typed ce dst dt src st n)) /\
  (!ce dst dt cap src st.
     code_trace_certified (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src dfs sfs doff soff.
     code_trace_certified (compile_struct_typed_copy ce dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, code_trace_certified_return]
  >- simp[Once compile_store_memory_typed_def, code_trace_certified_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, code_trace_certified_return]
  >> suspend "struct"
QED

Resume code_trace_certified_typed_copy_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (irule code_trace_certified_bind >> simp certified_primitives) >>
  IF_CASES_TAC >- simp[code_trace_certified_store_bytestring] >>
  IF_CASES_TAC >- simp[code_trace_certified_emit_void] >>
  Cases_on `dt` >> Cases_on `st` >> gvs certified_primitives >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs certified_primitives)
QED

Resume code_trace_certified_typed_copy_family[fields]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_memory_typed_def] >>
  reserved_sequence
QED

Resume code_trace_certified_typed_copy_family[sarray]:
  rpt gen_tac >> strip_tac >> irule code_trace_certified_sarray >>
  strip_tac >> rpt gen_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume code_trace_certified_typed_copy_family[dynarray]:
  rpt gen_tac >> strip_tac >> irule code_trace_certified_dynarray >>
  strip_tac >> rpt gen_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume code_trace_certified_typed_copy_family[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name`
  >- (gvs[] >> reserved_sequence) >>
  rename1 `SOME pair` >> PairCases_on `pair` >> gvs[] >> reserved_sequence
QED

Finalise code_trace_certified_typed_copy_family

Theorem code_trace_certified_raw_shape:
  code_trace_certified m /\ m sa = (x,sb) ==>
  frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  simp[code_trace_certified_def] >> strip_tac >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >>
  qpat_x_assum `!B L insts. _` (qspecl_then
    [`sa.cs_blocks`, `sa.cs_current_bb`, `sa.cs_current_insts`] mp_tac) >>
  simp[code_patch_self] >> strip_tac >> gvs[] >>
  irule trace_certificate_raw_shape >> simp[]
QED

Theorem aggregate_typed_store_raw_shape:
  compile_store_memory_typed ce dst dt src st sa = ((),sb) ==>
  frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  strip_tac >>
  `code_trace_certified (compile_store_memory_typed ce dst dt src st)` by
    simp[code_trace_certified_typed_copy_family] >>
  drule_all code_trace_certified_raw_shape >> simp[]
QED
