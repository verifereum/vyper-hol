(* Proof-only pending-label certificates for emitted decoder suffixes. *)
Theory entryDecoderCfgRules
Ancestors
  emitHelper emitHelperProps fragExec compileEnv venomInst list rich_list arithmetic pred_set

Definition entry_cfg_suffix_def:
  entry_cfg_suffix (start:compile_state) lbl code =
    if lbl = start.cs_current_bb then DROP (LENGTH start.cs_current_insts) code
    else code
End

Definition entry_cfg_branch_def:
  entry_cfg_branch targets inst <=>
    (inst.inst_opcode = JMP /\
     ?lbl. inst.inst_operands = [Label lbl] /\ lbl IN targets) \/
    (inst.inst_opcode = JNZ /\
     ?cond yes no. inst.inst_operands = [cond; Label yes; Label no] /\
                   yes IN targets /\ no IN targets)
End

Definition entry_cfg_open_def:
  entry_cfg_open code <=>
    EVERY (\i. i.inst_opcode <> PHI /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code
End

Definition entry_cfg_closed_def:
  entry_cfg_closed targets code <=>
    ?prefix inst. code = prefix ++ [inst] /\ entry_cfg_open prefix /\
                  entry_cfg_branch targets inst
End

Definition entry_cfg_cert_def:
  entry_cfg_cert start (st:compile_state) B P terminated <=>
    compile_state_ok st /\ cs_extends start st /\
    B = bound_labels st DIFF bound_labels start /\
    DISJOINT P (bound_labels st) /\
    DISJOINT P (compiler_labels_future st.cs_next_label) /\
    P SUBSET compiler_labels_future 0 /\
    EVERY (\bb. entry_cfg_closed (B UNION P)
      (entry_cfg_suffix start bb.bb_label bb.bb_instructions))
      (emitted_blocks start st) /\
    (if terminated then entry_cfg_closed (B UNION P)
       (entry_cfg_suffix start st.cs_current_bb st.cs_current_insts)
     else entry_cfg_open
       (entry_cfg_suffix start st.cs_current_bb st.cs_current_insts))
End

Theorem entry_cfg_cert_initial:
  compile_state_ok st /\ ~block_is_terminated st ==>
  entry_cfg_cert st st {} {} F
Proof
  simp[entry_cfg_cert_def, cs_extends_refl, emitted_blocks_def,
       entry_cfg_suffix_def, entry_cfg_open_def]
QED

Theorem entry_cfg_closed_mono[local]:
  targets SUBSET targets' /\ entry_cfg_closed targets code ==>
  entry_cfg_closed targets' code
Proof
  rw[entry_cfg_closed_def] >> qexistsl_tac [`prefix`, `inst`] >>
  gvs[entry_cfg_branch_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem entry_cfg_cert_fresh_label:
  entry_cfg_cert start st B P phase /\ fresh_label suffix st = (lbl, st') ==>
  entry_cfg_cert start st' B (lbl INSERT P) phase
Proof
  strip_tac >>
  `compile_state_ok st` by fs[entry_cfg_cert_def] >>
  drule_all fresh_label_produces_external >> strip_tac >>
  `st'.cs_current_insts = st.cs_current_insts` by gvs[fresh_label_def] >>
  `cs_extends start st' = cs_extends start st` by simp[cs_extends_def] >>
  `emitted_blocks start st' = emitted_blocks start st` by simp[emitted_blocks_def] >>
  fs[entry_cfg_cert_def] >>
  `DISJOINT P (compiler_labels_future (st.cs_next_label + 1))` by
    (irule DISJOINT_SUBSET >> qexists_tac `compiler_labels_future st.cs_next_label` >>
     simp[compiler_labels_future_antimono]) >>
  fs[label_external_def] >>
  simp[entry_cfg_cert_def, fresh_label_output_in_future] >>
  gvs[] >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> irule entry_cfg_closed_mono >>
      qexists_tac `bound_labels st DIFF bound_labels start UNION P` >>
      simp[] >> SET_TAC[]) >>
  Cases_on `phase` >> fs[] >> irule entry_cfg_closed_mono >>
  qexists_tac `bound_labels st DIFF bound_labels start UNION P` >>
  simp[] >> SET_TAC[]
QED

Theorem entry_cfg_current_prefix[local]:
  cs_extends start st /\ compile_state_ok st /\
  st.cs_current_bb = start.cs_current_bb ==>
  isPREFIX start.cs_current_insts st.cs_current_insts
Proof
  simp[cs_extends_def] >> strip_tac >> Cases_on `new = []` >> gvs[] >>
  `MEM (LAST new) new` by simp[LAST_MEM] >>
  fs[compile_state_ok_def, ALL_DISTINCT, MEM_MAP] >>
  metis_tac[MEM_APPEND]
QED

Theorem entry_cfg_suffix_append[local]:
  cs_extends start st /\ compile_state_ok st ==>
  entry_cfg_suffix start st.cs_current_bb (st.cs_current_insts ++ code) =
  entry_cfg_suffix start st.cs_current_bb st.cs_current_insts ++ code
Proof
  strip_tac >> simp[entry_cfg_suffix_def] >>
  Cases_on `st.cs_current_bb = start.cs_current_bb` >> simp[] >>
  drule_all entry_cfg_current_prefix >> simp[IS_PREFIX_APPEND] >>
  strip_tac >>
  `LENGTH start.cs_current_insts -
    (LENGTH l + LENGTH start.cs_current_insts) = 0` by decide_tac >>
  simp[DROP_APPEND]
QED

Theorem entry_cfg_cert_emit_straight:
  entry_cfg_cert start st B P F /\ emit inst st = ((), st') /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode ==>
  entry_cfg_cert start st' B P F
Proof
  strip_tac >>
  `compile_state_ok st /\ cs_extends start st` by fs[entry_cfg_cert_def] >>
  `cs_extends start st'` by metis_tac[cs_extends_emit, cs_extends_trans] >>
  drule_all entry_cfg_suffix_append >>
  disch_then (qspec_then `[inst]` assume_tac) >>
  gvs[emit_def] >>
  fs[entry_cfg_cert_def] >>
  gvs[entry_cfg_cert_def, compile_state_ok_def, bound_labels_def,
      emitted_blocks_def, entry_cfg_open_def]
QED

Theorem entry_cfg_cert_emit_branch:
  entry_cfg_cert start st B P F /\ emit inst st = ((), st') /\
  entry_cfg_branch (B UNION P) inst ==>
  entry_cfg_cert start st' B P T
Proof
  strip_tac >>
  `compile_state_ok st /\ cs_extends start st` by fs[entry_cfg_cert_def] >>
  `cs_extends start st'` by metis_tac[cs_extends_emit, cs_extends_trans] >>
  drule_all entry_cfg_suffix_append >>
  disch_then (qspec_then `[inst]` assume_tac) >>
  gvs[emit_def] >>
  fs[entry_cfg_cert_def] >>
  simp[entry_cfg_cert_def] >>
  conj_tac
  >- gvs[compile_state_ok_def, bound_labels_def] >>
  conj_tac
  >- gvs[bound_labels_def] >>
  conj_tac
  >- gvs[bound_labels_def] >>
  conj_tac
  >- gvs[emitted_blocks_def, bound_labels_def] >>
  gvs[bound_labels_def, entry_cfg_closed_def] >>
  qexistsl_tac [`entry_cfg_suffix start st.cs_current_bb st.cs_current_insts`, `inst`] >>
  simp[]
QED

Theorem entry_cfg_bound_mono[local]:
  cs_extends start st ==> bound_labels start SUBSET bound_labels st
Proof
  rw[cs_extends_def, bound_labels_def, SUBSET_DEF] >>
  Cases_on `new = []` >> gvs[MEM_MAP] >>
  metis_tac[LAST_MEM, MEM_APPEND]
QED

Theorem entry_cfg_cert_new_block:
  entry_cfg_cert start st B P T /\ lbl IN P /\
  new_block lbl st = (old, st') ==>
  entry_cfg_cert start st' (lbl INSERT B) (P DELETE lbl) F
Proof
  strip_tac >>
  `compile_state_ok st /\ cs_extends start st /\ label_external st lbl` by
    (fs[entry_cfg_cert_def, label_external_def, IN_DISJOINT] >> metis_tac[]) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  `cs_extends start st'` by metis_tac[cs_extends_new_block, cs_extends_trans] >>
  `bound_labels start SUBSET bound_labels st` by
    (irule entry_cfg_bound_mono >> simp[]) >>
  `lbl NOTIN bound_labels start` by
    (fs[label_external_def, SUBSET_DEF] >> metis_tac[]) >>
  `((lbl INSERT B) UNION (P DELETE lbl)) = B UNION P` by ASM_SET_TAC[] >>
  `LENGTH start.cs_blocks <= LENGTH st.cs_blocks` by
    (fs[cs_extends_def] >> simp[]) >>
  `SUC (LENGTH st.cs_blocks) - LENGTH start.cs_blocks =
   SUC (LENGTH st.cs_blocks - LENGTH start.cs_blocks)` by decide_tac >>
  `emitted_blocks start st' =
    <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|> ::
    emitted_blocks start st` by gvs[new_block_def, emitted_blocks_def] >>
  `bound_labels st' DIFF bound_labels start = lbl INSERT B` by
    (fs[entry_cfg_cert_def] >> ASM_SET_TAC[]) >>
  `DISJOINT (P DELETE lbl) (bound_labels st') /\
   DISJOINT (P DELETE lbl) (compiler_labels_future st'.cs_next_label) /\
   P DELETE lbl SUBSET compiler_labels_future 0` by
    (fs[entry_cfg_cert_def] >> ASM_SET_TAC[]) >>
  fs[entry_cfg_cert_def] >> simp[entry_cfg_cert_def] >>
  `st'.cs_current_insts = []` by gvs[new_block_def] >>
  gvs[entry_cfg_suffix_def, entry_cfg_open_def]
QED

Theorem entry_cfg_cert_metadata:
  entry_cfg_cert start st B P phase /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts /\
  st'.cs_next_label = st.cs_next_label ==>
  entry_cfg_cert start st' B P phase
Proof
  strip_tac >>
  gvs[entry_cfg_cert_def, compile_state_ok_def, cs_extends_def,
      bound_labels_def, emitted_blocks_def]
QED

Theorem entry_cfg_cert_fresh_var:
  entry_cfg_cert start st B P phase /\ fresh_var st = (v, st') ==>
  entry_cfg_cert start st' B P phase
Proof
  strip_tac >> irule entry_cfg_cert_metadata >> qexists_tac `st` >>
  gvs[fresh_var_def]
QED

Theorem entry_cfg_cert_fresh_id:
  entry_cfg_cert start st B P phase /\ fresh_id st = (v, st') ==>
  entry_cfg_cert start st' B P phase
Proof
  strip_tac >> irule entry_cfg_cert_metadata >> qexists_tac `st` >>
  gvs[fresh_id_def]
QED

Theorem entry_cfg_cert_bind:
  entry_cfg_cert start st B P phase /\
  (!s v t B0. entry_cfg_cert start s B0 P phase /\ f s = (v,t) ==>
       ?B1. entry_cfg_cert start t B1 P middle) /\
  (!s v t B0. entry_cfg_cert start s B0 P middle /\ g x s = (v,t) ==>
       ?B1. entry_cfg_cert start t B1 P final) /\
  f st = (x,mid) /\ comp_bind f g st = (y,last_st) ==>
  ?B1. entry_cfg_cert start last_st B1 P final
Proof
  simp[comp_bind_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem entry_cfg_cert_ignore_bind:
  entry_cfg_cert start st B P phase /\
  (!s v t B0. entry_cfg_cert start s B0 P phase /\ f s = (v,t) ==>
       ?B1. entry_cfg_cert start t B1 P middle) /\
  (!s v t B0. entry_cfg_cert start s B0 P middle /\ g s = (v,t) ==>
       ?B1. entry_cfg_cert start t B1 P final) /\
  comp_ignore_bind f g st = (y,last_st) ==>
  ?B1. entry_cfg_cert start last_st B1 P final
Proof
  Cases_on `f st` >>
  simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >> metis_tac[]
QED

Theorem entry_cfg_cert_targets_resolved:
  entry_cfg_cert start st B {} phase ==>
  B = bound_labels st DIFF bound_labels start /\
  (!lbl. lbl IN B ==> lbl IN bound_labels st /\ lbl NOTIN bound_labels start) /\
  EVERY (\bb. entry_cfg_closed B
    (entry_cfg_suffix start bb.bb_label bb.bb_instructions))
    (emitted_blocks start st) /\
  (phase ==> entry_cfg_closed B
    (entry_cfg_suffix start st.cs_current_bb st.cs_current_insts))
Proof
  simp[entry_cfg_cert_def] >> strip_tac >> gvs[] >>
  Cases_on `phase` >> gvs[]
QED

Theorem entry_cfg_cert_emit_void_branch:
  entry_cfg_cert start st B P F /\ emit_void opc ops st = ((), st') /\
  entry_cfg_branch (B UNION P) (mk_inst id opc ops []) ==>
  entry_cfg_cert start st' B P T
Proof
  strip_tac >>
  `entry_cfg_cert start (SND (fresh_id st)) B P F` by
    (irule entry_cfg_cert_fresh_id >> qexistsl_tac [`st`, `FST (fresh_id st)`] >> simp[]) >>
  irule entry_cfg_cert_emit_branch >>
  qexistsl_tac [`mk_inst st.cs_next_id opc ops []`, `SND (fresh_id st)`] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, entry_cfg_branch_def, mk_inst_def]
QED

Theorem entry_cfg_cert_emit_void_straight:
  entry_cfg_cert start st B P F /\ emit_void opc ops st = ((), st') /\
  opc <> PHI /\ opc <> INVOKE /\ ~is_terminator opc ==>
  entry_cfg_cert start st' B P F
Proof
  strip_tac >>
  `entry_cfg_cert start (SND (fresh_id st)) B P F` by
    (irule entry_cfg_cert_fresh_id >> qexistsl_tac [`st`, `FST (fresh_id st)`] >> simp[]) >>
  irule entry_cfg_cert_emit_straight >>
  qexistsl_tac [`mk_inst st.cs_next_id opc ops []`, `SND (fresh_id st)`] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, mk_inst_def]
QED

Theorem entry_cfg_cert_fresh_label_new:
  entry_cfg_cert start st B P phase /\ fresh_label suffix st = (lbl, st') ==>
  lbl NOTIN P /\ lbl NOTIN B /\
  entry_cfg_cert start st' B (lbl INSERT P) phase
Proof
  strip_tac >>
  `entry_cfg_cert start st' B (lbl INSERT P) phase` by
    (irule entry_cfg_cert_fresh_label >> metis_tac[]) >>
  `compile_state_ok st` by fs[entry_cfg_cert_def] >>
  drule_all fresh_label_produces_external >> strip_tac >>
  `lbl IN compiler_labels_future st.cs_next_label` by
    gvs[fresh_label_output_in_future] >>
  fs[entry_cfg_cert_def, label_external_def, IN_DISJOINT] >>
  metis_tac[IN_DIFF]
QED

(* A framed compiler fragment may add blocks, but preserves caller targets. *)
Definition entry_cfg_preserves_def:
  entry_cfg_preserves c <=>
    !start st B P v st'.
      entry_cfg_cert start st B P F /\ c st = (v,st') ==>
      ?B'. entry_cfg_cert start st' B' P F /\ B SUBSET B'
End

Theorem entry_cfg_preserves_apply:
  entry_cfg_preserves c /\ entry_cfg_cert start st B P F /\
  c st = (v,st') ==>
  ?B'. entry_cfg_cert start st' B' P F /\ B SUBSET B'
Proof
  metis_tac[entry_cfg_preserves_def]
QED

Theorem entry_cfg_loop_open[local]:
  !start s0 B P hdr body_lbl exit s1 s2 s3 s4 s5 old.
  entry_cfg_cert start s0 B P F /\
  fresh_label hdr_suffix s0 = (hdr,s1) /\
  fresh_label body_suffix s1 = (body_lbl,s2) /\
  fresh_label exit_suffix s2 = (exit,s3) /\
  emit_void JMP [Label hdr] s3 = ((),s4) /\
  new_block hdr s4 = (old,s5) ==>
  hdr NOTIN P /\ body_lbl NOTIN P /\ exit NOTIN P /\
  hdr <> body_lbl /\ hdr <> exit /\ body_lbl <> exit /\
  entry_cfg_cert start s5 (hdr INSERT B) (exit INSERT body_lbl INSERT P) F
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_cfg_cert_fresh_label_new >> strip_tac >>
  drule_all entry_cfg_cert_fresh_label_new >> strip_tac >>
  drule_all entry_cfg_cert_fresh_label_new >> strip_tac >>
  `entry_cfg_cert start s4 B (exit INSERT body_lbl INSERT hdr INSERT P) T` by
    (irule entry_cfg_cert_emit_void_branch >>
     qexistsl_tac [`0`, `JMP`, `[Label hdr]`, `s3`] >>
     simp[entry_cfg_branch_def, mk_inst_def]) >>
  `hdr IN (exit INSERT body_lbl INSERT hdr INSERT P)` by simp[] >>
  drule_all entry_cfg_cert_new_block >> strip_tac >>
  `P DELETE hdr = P` by ASM_SET_TAC[] >>
  gvs[] >> gvs[DELETE_INSERT, INSERT_COMM]
QED

Theorem entry_cfg_cert_jmp:
  entry_cfg_cert start st B P F /\ lbl IN B UNION P /\
  emit_void JMP [Label lbl] st = ((),st') ==>
  entry_cfg_cert start st' B P T
Proof
  strip_tac >> irule entry_cfg_cert_emit_void_branch >>
  qexistsl_tac [`0`, `JMP`, `[Label lbl]`, `st`] >>
  gvs[entry_cfg_branch_def, mk_inst_def]
QED

Theorem entry_cfg_cert_jnz:
  entry_cfg_cert start st B P F /\ yes IN B UNION P /\ no IN B UNION P /\
  emit_void JNZ [cond; Label yes; Label no] st = ((),st') ==>
  entry_cfg_cert start st' B P T
Proof
  strip_tac >> irule entry_cfg_cert_emit_void_branch >>
  qexistsl_tac [`0`, `JNZ`, `[cond; Label yes; Label no]`, `st`] >>
  gvs[entry_cfg_branch_def, mk_inst_def]
QED

Theorem entry_cfg_loop_header[local]:
  !start s0 B P body_lbl exit header v s1 s2 s3 old cond.
  entry_cfg_cert start s0 B (exit INSERT body_lbl INSERT P) F /\
  entry_cfg_preserves header /\ header s0 = (v,s1) /\
  emit_void JNZ [cond; Label exit; Label body_lbl] s1 = ((),s2) /\
  new_block body_lbl s2 = (old,s3) /\ body_lbl <> exit /\ body_lbl NOTIN P ==>
  ?B1. entry_cfg_cert start s3 (body_lbl INSERT B1) (exit INSERT P) F /\
       B SUBSET B1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_cfg_preserves_apply >> strip_tac >>
  `exit IN B' UNION (exit INSERT body_lbl INSERT P) /\
   body_lbl IN B' UNION (exit INSERT body_lbl INSERT P)` by simp[] >>
  drule_all entry_cfg_cert_jnz >> strip_tac >>
  `body_lbl IN (exit INSERT body_lbl INSERT P)` by simp[] >>
  drule_all entry_cfg_cert_new_block >> strip_tac >>
  `P DELETE body_lbl = P` by ASM_SET_TAC[] >>
  qexists_tac `B'` >> gvs[DELETE_INSERT]
QED

Theorem entry_cfg_preserves_ignore_bind:
  entry_cfg_preserves f /\ entry_cfg_preserves g ==>
  entry_cfg_preserves (comp_ignore_bind f g)
Proof
  strip_tac >> rewrite_tac[entry_cfg_preserves_def] >> rpt strip_tac >>
  Cases_on `f st` >> gvs[comp_ignore_bind_def, comp_bind_def] >>
  drule_all entry_cfg_preserves_apply >>
  disch_then (qx_choose_then `BF` strip_assume_tac) >>
  drule_all entry_cfg_preserves_apply >>
  disch_then (qx_choose_then `BG` strip_assume_tac) >>
  qexists_tac `BG` >> simp[] >> metis_tac[SUBSET_TRANS]
QED

Theorem entry_cfg_loop_close[local]:
  entry_cfg_cert start s0 B (exit INSERT P) F /\ hdr IN B /\ exit NOTIN P /\
  emit_void JMP [Label hdr] s0 = ((),s1) /\ new_block exit s1 = (old,s2) ==>
  entry_cfg_cert start s2 (exit INSERT B) P F
Proof
  strip_tac >> `hdr IN B UNION (exit INSERT P)` by simp[] >>
  drule_all entry_cfg_cert_jmp >> strip_tac >>
  `exit IN (exit INSERT P)` by simp[] >>
  drule_all entry_cfg_cert_new_block >> strip_tac >>
  `P DELETE exit = P` by ASM_SET_TAC[] >> gvs[DELETE_INSERT]
QED

Theorem entry_cfg_loop_skeleton:
  !start s0 B P hdr body_lbl exit s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
   header prefix nested update v1 v2 v3 v4 old1 old2 old3 cond.
  entry_cfg_cert start s0 B P F /\
  fresh_label hdr_suffix s0 = (hdr,s1) /\
  fresh_label body_suffix s1 = (body_lbl,s2) /\
  fresh_label exit_suffix s2 = (exit,s3) /\
  emit_void JMP [Label hdr] s3 = ((),s4) /\
  new_block hdr s4 = (old1,s5) /\ header s5 = (v1,s6) /\
  emit_void JNZ [cond; Label exit; Label body_lbl] s6 = ((),s7) /\
  new_block body_lbl s7 = (old2,s8) /\ prefix s8 = (v2,s9) /\
  nested s9 = (v3,s10) /\ update s10 = (v4,s11) /\
  emit_void JMP [Label hdr] s11 = ((),s12) /\
  new_block exit s12 = (old3,s13) /\
  entry_cfg_preserves header /\ entry_cfg_preserves prefix /\
  entry_cfg_preserves nested /\ entry_cfg_preserves update ==>
  ?B'. entry_cfg_cert start s13 B' P F /\ B SUBSET B' /\
       hdr IN B' /\ body_lbl IN B' /\ exit IN B'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_cfg_loop_open >> strip_tac >>
  drule_all entry_cfg_loop_header >> disch_then (qx_choose_then `BH` strip_assume_tac) >>
  drule_all entry_cfg_preserves_apply >> disch_then (qx_choose_then `BP` strip_assume_tac) >>
  drule_all entry_cfg_preserves_apply >> disch_then (qx_choose_then `B_nested` strip_assume_tac) >>
  drule_all entry_cfg_preserves_apply >> disch_then (qx_choose_then `BU` strip_assume_tac) >>
  `hdr IN BU /\ body_lbl IN BU` by ASM_SET_TAC[] >>
  drule_all entry_cfg_loop_close >> strip_tac >>
  qexists_tac `exit INSERT BU` >> simp[] >> ASM_SET_TAC[]
QED

Theorem entry_cfg_terminated_iff[local]:
  block_is_terminated st <=>
  st.cs_current_insts <> [] /\ is_terminator (LAST st.cs_current_insts).inst_opcode
Proof
  Cases_on `st.cs_current_insts` >> simp[block_is_terminated_def]
QED

Theorem entry_cfg_open_last[local]:
  entry_cfg_open code /\ code <> [] ==>
  ~is_terminator (LAST code).inst_opcode
Proof
  simp[entry_cfg_open_def, EVERY_MEM] >>
  metis_tac[LAST_MEM]
QED

Theorem entry_cfg_cert_open_state:
  entry_cfg_cert start st B P F /\ ~block_is_terminated start ==>
  ~block_is_terminated st
Proof
  strip_tac >>
  `compile_state_ok st /\ cs_extends start st /\
   entry_cfg_open (entry_cfg_suffix start st.cs_current_bb st.cs_current_insts)` by
    fs[entry_cfg_cert_def] >>
  Cases_on `st.cs_current_bb = start.cs_current_bb`
  >- (drule_all entry_cfg_current_prefix >> simp[IS_PREFIX_APPEND] >>
      strip_tac >> gvs[entry_cfg_suffix_def, DROP_APPEND] >>
      Cases_on `l = []` >- gvs[entry_cfg_terminated_iff] >>
      drule_all entry_cfg_open_last >>
      gvs[entry_cfg_terminated_iff, LAST_APPEND_NOT_NIL]) >>
  gvs[entry_cfg_suffix_def] >> Cases_on `st.cs_current_insts = []`
  >- gvs[entry_cfg_terminated_iff] >>
  drule_all entry_cfg_open_last >> gvs[entry_cfg_terminated_iff]
QED

Theorem entry_cfg_cert_closed_state:
  entry_cfg_cert start st B P T ==> block_is_terminated st
Proof
  simp[entry_cfg_cert_def] >> strip_tac >>
  qpat_x_assum `entry_cfg_closed _ _` mp_tac >>
  simp[entry_cfg_closed_def, entry_cfg_suffix_def] >>
  strip_tac >> Cases_on `st.cs_current_bb = start.cs_current_bb`
  >- (`st.cs_current_insts = TAKE (LENGTH start.cs_current_insts) st.cs_current_insts ++
                           (prefix ++ [inst])` by metis_tac[TAKE_DROP] >>
      rewrite_tac[entry_cfg_terminated_iff] >>
      qpat_x_assum `st.cs_current_insts = _ ++ _`
        (fn th => once_rewrite_tac[th]) >>
      gvs[entry_cfg_branch_def, is_terminator_def, LAST_APPEND_NOT_NIL]) >>
  gvs[entry_cfg_terminated_iff, entry_cfg_branch_def, is_terminator_def,
      LAST_APPEND_NOT_NIL]
QED
