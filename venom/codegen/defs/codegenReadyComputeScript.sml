(*
 * Executable counterparts for the relational code-generation readiness guards.
 *
 * TOP-LEVEL:
 *   fn_dominates_cfg_analyze       — computed dominators match path dominance
 *   def_dominates_uses_compute     — finite executable SSA dominance check
 *)

Theory codegenReadyCompute
Ancestors
  stackPlanGen dominatorProofs dominatorDefs cfgAnalysisProps
  simplifyCfgCompute venomExecProps venomWf venomInst cfgTransform cfgDefs
  passSharedDefs fcgDefs relation rich_list

(* ===== Relational / computed CFG bridges ===== *)

Theorem fn_cfg_edge_iff_fn_succ:
  wf_function fn ==>
  (fn_cfg_edge fn src dst <=> fn_succ fn src dst)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  simp[fn_cfg_edge_def, fn_succ_def] >>
  eq_tac >> rpt strip_tac
  >- (qexists_tac `bb` >> simp[] >>
      irule venomExecPropsTheory.MEM_lookup_block >>
      simp[GSYM fn_labels_def])
  >> qexists_tac `bb` >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
            venomExecPropsTheory.lookup_block_label]
QED

Theorem fn_cfg_edge_cfg_analyze:
  wf_function fn ==>
  (fn_cfg_edge fn src dst <=>
   MEM dst (cfg_succs_of (cfg_analyze fn) src))
Proof
  metis_tac[fn_cfg_edge_iff_fn_succ,
            simplifyCfgComputeTheory.fn_succ_cfg_analyze]
QED

Theorem fn_reachable_reachable:
  wf_function fn ==>
  (fn_reachable fn lbl <=> reachable fn lbl)
Proof
  rpt strip_tac >>
  `fn_cfg_edge fn = fn_succ fn` by
    simp[FUN_EQ_THM, fn_cfg_edge_iff_fn_succ] >>
  simp[fn_reachable_def, reachable_def]
QED

Theorem fn_reachable_cfg_analyze:
  wf_function fn ==>
  (fn_reachable fn lbl <=>
   cfg_reachable_of (cfg_analyze fn) lbl)
Proof
  metis_tac[fn_reachable_reachable,
            simplifyCfgComputeTheory.reachable_cfg_analyze]
QED

(* Convert between the list path representation used by venomWf and the LRC
 * representation used by the dominator correctness proof. *)
Theorem is_fn_path_to_lrc:
  !fn path.
    path <> [] /\ is_fn_path fn path ==>
    LRC (fn_cfg_edge fn) (FRONT path) (HD path) (LAST path)
Proof
  gen_tac >> Induct_on `path` >> simp[] >>
  Cases_on `path` >>
  simp[is_fn_path_def, listTheory.LRC_def, listTheory.FRONT_CONS] >>
  rpt strip_tac >> qexists_tac `h` >> simp[] >>
  qpat_x_assum `_ ==> LRC _ _ _ _` mp_tac >> simp[]
QED

Theorem lrc_to_is_fn_path:
  !fn ls x y.
    LRC (fn_cfg_edge fn) ls x y ==>
    is_fn_path fn (ls ++ [y]) /\ HD (ls ++ [y]) = x
Proof
  gen_tac >> Induct_on `ls`
  >- simp[listTheory.LRC_def, is_fn_path_def] >>
  rpt gen_tac >>
  simp[listTheory.LRC_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `ls` >>
  gvs[is_fn_path_def, listTheory.LRC_def]
QED

Theorem is_fn_path_rtc_compute:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    (fn_cfg_edge fn)^* (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[]
QED

Theorem rtc_to_fn_path_compute:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\
           HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem is_fn_path_prefix_compute:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?pre. is_fn_path fn (pre ++ [d]) /\ HD (pre ++ [d]) = HD path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `[]` >> simp[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def]
      >- (qexists_tac `[h]` >> simp[is_fn_path_def])
      >- (first_x_assum (qspecl_then [`fn`, `d`] mp_tac) >> simp[] >>
          strip_tac >> qexists_tac `h::pre` >>
          Cases_on `pre` >> gvs[is_fn_path_def]))
QED

Theorem fn_dominates_dom_reachable_compute:
  !fn d n. fn_dominates fn d n ==> fn_reachable fn d
Proof
  rw[fn_dominates_def, fn_reachable_def] >>
  qexists_tac `entry` >> simp[] >>
  drule rtc_to_fn_path_compute >> strip_tac >>
  `MEM d path` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all is_fn_path_prefix_compute >> strip_tac >>
  drule is_fn_path_rtc_compute >>
  simp[listTheory.APPEND_eq_NIL]
QED

(* The executable dominator analysis is extensionally equal to the original
 * all-paths definition on well-formed functions. *)
Theorem fn_dominates_cfg_analyze:
  !fn d n.
    wf_function fn ==>
    (fn_dominates fn d n <=>
     cfg_reachable_of (cfg_analyze fn) n /\
     dominates (dom_analyze (cfg_analyze fn) fn) d n)
Proof
  rpt strip_tac >>
  `?entry_bb. entry_block fn = SOME entry_bb` by
    (fs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `fn_entry_label fn = SOME entry_bb.bb_label` by
    simp[fn_entry_label_def] >>
  `fn_cfg_edge fn =
   (λa b. MEM b (cfg_succs_of (cfg_analyze fn) a))` by
    simp[FUN_EQ_THM, fn_cfg_edge_cfg_analyze] >>
  eq_tac
  >- (strip_tac >>
      `cfg_reachable_of (cfg_analyze fn) n` by
        metis_tac[fn_reachable_cfg_analyze, fn_dominates_def] >>
      conj_tac >- simp[] >>
      `fn_reachable fn d` by
        metis_tac[fn_dominates_dom_reachable_compute] >>
      `cfg_reachable_of (cfg_analyze fn) d` by
        metis_tac[fn_reachable_cfg_analyze] >>
      `MEM d (fn_labels fn)` by
        metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels] >>
      simp[dominatorDefsTheory.dominates_def] >>
      irule dominatorProofsTheory.on_every_path_dom >>
      simp[] >>
      rpt strip_tac >>
      `LRC (fn_cfg_edge fn) ls entry_bb.bb_label n` by fs[] >>
      drule lrc_to_is_fn_path >> strip_tac >>
      fs[fn_dominates_def] >>
      first_x_assum (qspec_then `ls ++ [n]` mp_tac) >>
      simp[] >> metis_tac[])
  >- (strip_tac >>
      simp[fn_dominates_def] >>
      conj_tac
      >- metis_tac[fn_reachable_cfg_analyze] >>
      rpt strip_tac >>
      mp_tac (Q.SPECL [`fn`, `path`] is_fn_path_to_lrc) >>
      simp[] >> strip_tac >>
      `LRC (λa b. MEM b (cfg_succs_of (cfg_analyze fn) a))
           (FRONT path) entry_bb.bb_label n` by metis_tac[] >>
      `d = n \/ MEM d (FRONT path)` by
        (mp_tac (Q.SPECL [`fn`, `entry_bb`, `FRONT path`, `n`]
                   dominatorProofsTheory.dom_on_every_path) >>
         simp[] >> strip_tac >>
         first_x_assum (qspec_then `d` mp_tac) >>
         fs[dominatorDefsTheory.dominates_def]) >>
      Cases_on `path` >>
      gvs[rich_listTheory.MEM_LAST, rich_listTheory.MEM_FRONT])
QED

(* ===== Finite def-dominates-uses checker ===== *)

(* Helper: well-formed functions have at most one block with a given label. *)
Theorem wf_function_blocks_same_label:
  wf_function fn /\
  MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
  bb1.bb_label = bb2.bb_label ==>
  bb1 = bb2
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `?i. i < LENGTH fn.fn_blocks /\ EL i fn.fn_blocks = bb1` by
    metis_tac[listTheory.MEM_EL] >>
  `?j. j < LENGTH fn.fn_blocks /\ EL j fn.fn_blocks = bb2` by
    metis_tac[listTheory.MEM_EL] >>
  `i = j` by
    (qspecl_then [`MAP (λbb. bb.bb_label) fn.fn_blocks`, `i`, `j`]
       mp_tac listTheory.ALL_DISTINCT_EL_IMP >>
     simp[listTheory.EL_MAP]) >>
  gvs[]
QED

Definition def_available_at_exec_def:
  def_available_at_exec cfg dom fn target_bb use_inst_opt v <=>
    EXISTS
      (λdef_bb.
        EXISTS
          (λdef_inst.
            MEM v def_inst.inst_outputs /\
            cfg_reachable_of cfg target_bb.bb_label /\
            dominates dom def_bb.bb_label target_bb.bb_label /\
            (def_bb.bb_label = target_bb.bb_label ==>
             case use_inst_opt of
               NONE => T
             | SOME use_inst =>
                 EXISTS
                   (λi. EXISTS
                     (λj. i < j /\
                          EL i target_bb.bb_instructions = def_inst /\
                          EL j target_bb.bb_instructions = use_inst)
                     (GENLIST I (LENGTH target_bb.bb_instructions)))
                   (GENLIST I (LENGTH target_bb.bb_instructions))))
          def_bb.bb_instructions)
      fn.fn_blocks
End
(* Computed PHI contract: exact pair shape and predecessor coverage precede
   the edge-availability checks, matching check_venom._handle_var_definition. *)
Definition phi_edge_uses_wf_exec_def:
  phi_edge_uses_wf_exec cfg dom fn bb inst <=>
    let pairs = phi_pairs inst.inst_operands in
      phi_well_formed inst.inst_operands /\
      ALL_DISTINCT (MAP FST pairs) /\
      EVERY (λpred. EXISTS (λp. FST p = pred) pairs)
        (cfg_preds_of cfg bb.bb_label) /\
      EVERY
        (λp.
          MEM (FST p) (cfg_preds_of cfg bb.bb_label) /\
          EXISTS
            (λpred_bb.
              pred_bb.bb_label = FST p /\
              def_available_at_exec cfg dom fn pred_bb NONE (SND p))
            fn.fn_blocks)
        pairs
End
Definition def_dominates_uses_exec_def:
  def_dominates_uses_exec fn <=>
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      EVERY
        (λbb.
          EVERY
            (λinst.
              if inst.inst_opcode = PHI then
                phi_edge_uses_wf_exec cfg dom fn bb inst
              else
                EVERY
                  (λop. case op of
                         Var v => def_available_at_exec cfg dom fn bb
                                    (SOME inst) v
                       | _ => T)
                  inst.inst_operands)
            bb.bb_instructions)
        fn.fn_blocks
End
Theorem def_available_at_exec_correct:
  wf_function fn ==>
  MEM target_bb fn.fn_blocks ==>
  (def_available_at fn target_bb use_inst_opt v <=>
   def_available_at_exec (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) fn target_bb use_inst_opt v)
Proof
  rpt strip_tac >>
  simp[def_available_at_def, def_available_at_exec_def,
       listTheory.EXISTS_MEM, listTheory.EXISTS_GENLIST] >>
  eq_tac >> rpt strip_tac
  >- (qexists_tac `def_bb` >> simp[] >>
      qexists_tac `def_inst` >> simp[] >>
      conj_tac >- metis_tac[fn_dominates_cfg_analyze] >>
      conj_tac >- metis_tac[fn_dominates_cfg_analyze] >>
      strip_tac >>
      `def_bb = target_bb` by
        metis_tac[wf_function_blocks_same_label] >>
      Cases_on `use_inst_opt` >> gvs[] >>
      qexists_tac `i` >> simp[] >> qexists_tac `j` >> simp[])
  >- (qexists_tac `def_bb` >> simp[] >>
      qexists_tac `def_inst` >> simp[] >>
      conj_tac >- metis_tac[fn_dominates_cfg_analyze] >>
      strip_tac >> Cases_on `use_inst_opt` >> gvs[] >>
      qexistsl_tac [`i`, `i'`] >> simp[])
QED
Theorem phi_edge_uses_wf_exec_correct:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  (phi_edge_uses_wf fn bb inst <=>
   phi_edge_uses_wf_exec (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) fn bb inst)
Proof
  rpt strip_tac >>
  simp[phi_edge_uses_wf_def, phi_edge_uses_wf_exec_def,
       listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >>
  simp[fn_cfg_edge_cfg_analyze,
       cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond,
       def_available_at_exec_correct] >>
  eq_tac >> rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >|
    [qpat_x_assum `!pred. _ <=> _` (qspec_then `pred` assume_tac) >>
       gvs[] >> qexists_tac `p` >> simp[],
     PairCases_on `p` >>
       qpat_x_assum `!pred. _ <=> _` (qspec_then `p0` assume_tac) >>
       gvs[] >> qexists_tac `(p0,p1)` >> simp[],
     PairCases_on `p` >>
       qpat_x_assum `!pred v. _` (qspecl_then [`p0`, `p1`] mp_tac) >>
       impl_tac >- simp[] >> simp[] >> strip_tac >> gvs[] >>
       qexists_tac `pred_bb` >> simp[] >>
       metis_tac[def_available_at_exec_correct],
     eq_tac >> strip_tac
       >- (qpat_x_assum `!pred. _ ==> _`
             (qspec_then `pred` mp_tac) >> simp[])
       >- (qpat_x_assum `!p. _` (qspec_then `p` mp_tac) >> simp[]),
     qpat_x_assum `!p. _` (qspec_then `(pred,v)` mp_tac) >> simp[] >>
       strip_tac >> qexists_tac `pred_bb` >> simp[] >>
       metis_tac[def_available_at_exec_correct]]
QED
Theorem def_dominates_uses_exec_correct:
  wf_function fn ==>
  (def_dominates_uses fn <=> def_dominates_uses_exec fn)
Proof
  strip_tac >>
  simp[def_dominates_uses_def, def_dominates_uses_exec_def,
       listTheory.EVERY_MEM] >>
  eq_tac >> rpt strip_tac
  >- (first_x_assum drule_all >>
      Cases_on `inst.inst_opcode = PHI` >> gvs[]
      >- metis_tac[phi_edge_uses_wf_exec_correct]
      >- (strip_tac >> gen_tac >> strip_tac >> Cases_on `op` >> gvs[] >>
          qpat_x_assum `!v. _` (qspec_then `s` mp_tac) >> simp[] >>
          metis_tac[def_available_at_exec_correct]))
  >- (first_x_assum drule_all >>
      Cases_on `inst.inst_opcode = PHI` >> gvs[]
      >- metis_tac[phi_edge_uses_wf_exec_correct]
      >- (rpt strip_tac >>
          first_x_assum (qspec_then `Var v` mp_tac) >> simp[] >>
          metis_tac[def_available_at_exec_correct]))
QED

(* The malformed fallback is deliberately the original specification.  This
 * keeps the theorem unconditional while computeLib takes the finite branch in
 * codegen_ready_fn, where wf_function is checked before this conjunct. *)
Theorem def_dominates_uses_compute[compute]:
  def_dominates_uses fn <=>
    if wf_function fn then
      def_dominates_uses_exec fn
    else
      !bb inst.
        MEM bb fn.fn_blocks /\
        MEM inst bb.bb_instructions ==>
        if inst.inst_opcode = PHI then
          phi_edge_uses_wf fn bb inst
        else
          !v. MEM (Var v) inst.inst_operands ==>
              def_available_at fn bb (SOME inst) v
Proof
  Cases_on `wf_function fn`
  >- simp[def_dominates_uses_exec_correct]
  >- simp[def_dominates_uses_def]
QED
