Theory bodyFullAbiDecodeCutNoncrossing
Ancestors
  bodyFullAbiDecodeCutLayout bodyFullAbiDecodeCutEntryPhase
  bodyFullAbiDecodeCutAfterPath exprSimAbiGasBridge fragExec fragGasPath
  compileEnv venomState venomInst venomInstProps venomExecSemantics list rich_list
Libs
  bodyFullAbiDecodeCutPathLib

val cursor = bodyFullAbiDecodeCutPathLib.shadow_cursor;
val shadow_result = bodyFullAbiDecodeCutPathLib.shadow_result;

val slice_ready = ``\L start a u s.
  ~u.vs_halted /\ (u.vs_current_bb,u.vs_inst_idx) = (^cursor) L start a /\
  frag_relabel_state L start.cs_current_bb u s``;

val slice_outcome = ``\b r.
  (?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
       t.vs_inst_idx = LENGTH b.cs_current_insts) \/
  (?t. r = Abort Revert_abort t)``;

val noncrossing_layout = ``\start a b final L ids fn id.
  cs_extends start a /\ cs_extends a b /\ cs_extends b final /\
  start.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH start.cs_current_insts /\
  fn_has_code start final fn /\
  fn_has_code (start_relabel L ids start) (start_swap start L ids final)
    (frag_relabel_observer start final L ids fn id) /\
  frag_ops_free start final /\ L <> final.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
  (a.cs_blocks = start.cs_blocks ==>
    b.cs_blocks = start.cs_blocks /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
               ~is_terminator i.inst_opcode) (emitted_insts a b))``;

val slice_result = ``\ctx start b final L ids fn id u r.
  (^shadow_result) ctx (frag_relabel_observer start final L ids fn id)
    (frag_observer_cut final) L start.cs_current_bb u ((^cursor) L start b) r``;

(* Histories grow by prepending new blocks. The current label of an
   intermediate compiler state is either final's label or one of those blocks. *)
Theorem cut_slice_label_fresh[local]:
  cs_extends start a /\ cs_extends a final /\ L <> final.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) ==>
  a.cs_current_bb <> L
Proof
  strip_tac >>
  qpat_assum `cs_extends start a` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  qpat_assum `cs_extends a final` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  rename [`a.cs_blocks = xs ++ start.cs_blocks`,
          `final.cs_blocks = ys ++ a.cs_blocks`] >>
  `emitted_blocks start final = ys ++ xs` by
    (irule emitted_blocks_append >> simp[APPEND_ASSOC]) >>
  Cases_on `ys = []` >> gvs[MEM_APPEND, MEM_MAP] >>
  metis_tac[MEM_LAST_NOT_NIL]
QED

Theorem cut_slice_after_history[local]:
  cs_extends start a /\ cs_extends a b /\ a.cs_blocks <> start.cs_blocks ==>
  b.cs_blocks <> start.cs_blocks
Proof
  simp[cs_extends_def] >> rpt strip_tac >> gvs[]
QED

Theorem cut_noncrossing_path[local]:
  (^noncrossing_layout) start a b final L ids fn id /\
  (^slice_ready) L start a u s /\
  (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
  (^slice_outcome) b r ==>
  (^slice_result) ctx start b final L ids fn id u r
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `a.cs_blocks = start.cs_blocks`
  >- suspend "before" >>
  suspend "after"
QED

Resume cut_noncrossing_path[before]:
  `b.cs_blocks = start.cs_blocks` by simp[] >>
  `emitted_blocks start a = []` by simp[emitted_blocks_def] >>
  `a.cs_current_bb = start.cs_current_bb` by
    (qpat_assum `cs_extends start a` (mp_then Any mp_tac frag_extends_emitted_shape) >>
     simp[]) >>
  drule_all abi_decode_cut_entry_slice >> strip_tac >>
  drule frag_relabel_state_fields >> strip_tac >>
  qpat_assum `b.cs_blocks = start.cs_blocks` (fn th => rewrite_tac[th]) >>
  qpat_assum `a.cs_current_bb = start.cs_current_bb`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule (BETA_RULE abi_decode_cut_entry_phase) >>
  fs[frag_observer_cut_def] >> qexists `s` >> simp[] >> metis_tac[]
QED

Resume cut_noncrossing_path[after]:
  `cs_extends start final /\ cs_extends a final` by metis_tac[cs_extends_trans] >>
  `b.cs_blocks <> start.cs_blocks` by metis_tac[cut_slice_after_history] >>
  `a.cs_current_bb <> L` by metis_tac[cut_slice_label_fresh] >>
  `fn_has_code a b (frag_relabel_observer start final L ids fn id)` by
    metis_tac[abi_decode_cut_after_has_code] >>
  drule_all abi_decode_cut_shadow_controls >> simp_tac bool_ss [LET_THM] >>
  disch_then (qspecl_then [`id`,`fn`] strip_assume_tac) >>
  qpat_assum `b.cs_blocks <> start.cs_blocks` (fn th => rewrite_tac[th]) >>
  irule (BETA_RULE abi_decode_cut_after_path) >>
  simp[] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- metis_tac[MEM]
  >- (qexists `id` >> simp[])
  >- fs[]
  >- (qexistsl [`0`,`s`] >> metis_tac[]) >>
  qpat_x_assum `(?t. _ = OK t /\ _) \/ _` strip_assume_tac >>
  gvs[] >> fs[fn_has_code_def]
QED

Finalise cut_noncrossing_path

(* Certify the outcome already chosen by Q, without choosing a second
   physical result or changing either ghost witness. *)
Theorem abi_decode_cut_noncrossing_selected:
  (^noncrossing_layout) start a b final L ids fn id /\
  (^slice_ready) L start a u s /\
  (!r Gf tnf. Q r Gf tnf ==>
    (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
    (^slice_outcome) b r) /\
  (?r Gf tnf. Q r Gf tnf) ==>
  ?r Gf tnf. Q r Gf tnf /\ (^slice_result) ctx start b final L ids fn id u r
Proof
  BETA_TAC >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qexistsl [`r`,`Gf`,`tnf`] >> simp[] >>
  qpat_assum `!r Gf tnf. Q r Gf tnf ==> _`
    (drule_then (CONJUNCTS_THEN assume_tac)) >>
  drule_all (BETA_RULE cut_noncrossing_path) >> simp[]
QED
