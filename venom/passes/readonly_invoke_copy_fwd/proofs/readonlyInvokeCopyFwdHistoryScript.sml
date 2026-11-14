(* Chronological rounds retain the DFG at validation time.  All positions
   here are before clear_nops; no source-block acceptance is asserted. *)
Theory readonlyInvokeCopyFwdHistory
Ancestors
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdPlan
  o1PassContract venomInst list

Definition ricf_logged_round_def:
  ricf_logged_round base round logs mid <=>
    mid.fn_name = round.fn_name /\
    mid = round with fn_blocks := mid.fn_blocks /\
    LENGTH logs = LENGTH mid.fn_blocks /\
    LIST_REL (\bb p.
      ricf_block_trace bb (FST p) (SND p) /\
      EVERY (\e. e.rfe_ctx =
        (base with icf_dfg := dfg_build_function round)) (FST p))
      round.fn_blocks (ZIP (logs,mid.fn_blocks))
End

Inductive ricf_logged_function_trace:
[~nil:]
  (!base fn. ricf_logged_function_trace base fn [] fn)
[~cons:]
  (!base round logs mid tail last.
    ricf_logged_round base round logs mid /\
    ricf_logged_function_trace base mid tail last ==>
    ricf_logged_function_trace base round ((round,logs,mid)::tail) last)
End

Theorem ricf_logged_round_erases:
  !base round logs mid. ricf_logged_round base round logs mid ==>
  ricf_round_certificate
    (base with icf_dfg := dfg_build_function round) round mid
Proof
  simp[ricf_logged_round_def, ricf_round_certificate_def,
       LIST_REL_EL_EQN, EL_ZIP] >> rpt strip_tac >>
  qexists_tac `mid.fn_blocks` >> simp[] >> rpt strip_tac >>
  qexists_tac `EL n logs` >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[EL_ZIP]
QED

Theorem ricf_round_logs_exist:
  !bbs cs ctx.
  LIST_REL (\bb bb'. ?es. ricf_block_trace bb es bb' /\
    EVERY (\e. e.rfe_ctx = ctx) es) bbs cs ==>
  ?logs. LENGTH logs = LENGTH cs /\
    LIST_REL (\bb p. ricf_block_trace bb (FST p) (SND p) /\
      EVERY (\e. e.rfe_ctx = ctx) (FST p)) bbs (ZIP (logs,cs))
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `es::logs` >> simp[]
QED

Theorem ricf_logged_round_exists:
  !base round mid. ricf_round_certificate
    (base with icf_dfg := dfg_build_function round) round mid ==>
  ?logs. ricf_logged_round base round logs mid
Proof
  simp[ricf_round_certificate_def] >> rpt strip_tac >> gvs[] >>
  drule ricf_round_logs_exist >> strip_tac >>
  qexists_tac `logs` >> simp[ricf_logged_round_def]
QED

Theorem ricf_logged_function_trace_erases:
  !base fn log last. ricf_logged_function_trace base fn log last ==>
  ricf_function_trace base fn last
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >>
  metis_tac[ricf_function_trace_nil, ricf_function_trace_cons,
            ricf_logged_round_erases]
QED

Theorem ricf_logged_function_trace_exists:
  !base fn last. ricf_function_trace base fn last ==>
  ?log. ricf_logged_function_trace base fn log last
Proof
  ho_match_mp_tac ricf_function_trace_ind >> rpt strip_tac
  >- metis_tac[ricf_logged_function_trace_nil] >>
  drule ricf_logged_round_exists >> strip_tac >>
  metis_tac[ricf_logged_function_trace_cons]
QED

(* Membership retains the round's own analysis context and a trace from
   the original function to its input; no equality of different DFGs is used. *)
Theorem ricf_logged_function_trace_member:
  !base fn log last. ricf_logged_function_trace base fn log last ==>
  !round logs mid. MEM (round,logs,mid) log ==>
    ricf_function_trace base fn round /\
    ricf_logged_round base round logs mid
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >> simp[] >>
  rpt strip_tac >> gvs[]
  >- simp[ricf_function_trace_nil] >>
  metis_tac[ricf_function_trace_cons, ricf_logged_round_erases]
QED

Theorem ricf_block_trace_split:
  !prefix bb suffix last.
    ricf_block_trace bb (prefix ++ suffix) last ==>
    ?current. ricf_block_trace bb prefix current /\
              ricf_block_trace current suffix last
Proof
  Induct >- metis_tac[APPEND, ricf_block_trace_nil] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `ricf_block_trace _ (_::_) _` mp_tac >>
  simp[Once ricf_block_trace_cases] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ricf_block_trace_cons]
QED

(* A location is an occurrence in a chronological execution witness, not
   just membership in an unordered set of accepted events. *)
Definition ricf_located_event_def:
  ricf_located_event base original log round b es prefix e current <=>
    ?last logs mid suffix.
      ricf_logged_function_trace base original log last /\
      MEM (round,logs,mid) log /\
      b < LENGTH round.fn_blocks /\
      es = EL b logs /\ es = prefix ++ e::suffix /\
      ricf_block_trace (EL b round.fn_blocks) prefix current
End

Theorem ricf_logged_round_block:
  !base round logs mid b.
  ricf_logged_round base round logs mid /\ b < LENGTH round.fn_blocks ==>
    b < LENGTH logs /\
    ricf_block_trace (EL b round.fn_blocks) (EL b logs) (EL b mid.fn_blocks) /\
    EVERY (\e. e.rfe_ctx =
      (base with icf_dfg := dfg_build_function round)) (EL b logs)
Proof
  simp[ricf_logged_round_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> gvs[EL_ZIP]
QED

Theorem ricf_block_trace_deterministic:
  !bb es current. ricf_block_trace bb es current ==>
    !other. ricf_block_trace bb es other ==> other = current
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >>
  qpat_x_assum `ricf_block_trace _ _ other` mp_tac >>
  simp[Once ricf_block_trace_cases] >> metis_tac[]
QED

Theorem ricf_located_event_validation:
  !base original log round b es prefix e current.
  ricf_located_event base original log round b es prefix e current ==>
    ricf_event_ok e current /\
    e.rfe_ctx = (base with icf_dfg := dfg_build_function round) /\
    ricf_function_trace base original round /\
    b < LENGTH round.fn_blocks /\
    ricf_block_trace (EL b round.fn_blocks) prefix current /\
    EVERY (\f. f.rfe_ctx =
      (base with icf_dfg := dfg_build_function round)) prefix
Proof
  simp[ricf_located_event_def] >> rpt strip_tac >>
  drule_all ricf_logged_function_trace_member >> strip_tac >>
  drule_all ricf_logged_round_block >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = EL b logs`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  fs[EVERY_APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule ricf_block_trace_split >> strip_tac >>
  `current' = current` by metis_tac[ricf_block_trace_deterministic] >>
  gvs[] >>
  qpat_x_assum `ricf_block_trace _ (e::suffix) _` mp_tac >>
  simp[Once ricf_block_trace_cases]
QED

Theorem ricf_located_event_exists:
  !base original log last round logs mid b e.
  ricf_logged_function_trace base original log last /\
  MEM (round,logs,mid) log /\ b < LENGTH round.fn_blocks /\
  MEM e (EL b logs) ==>
  ?es prefix current.
    ricf_located_event base original log round b es prefix e current
Proof
  rpt strip_tac >>
  drule_all ricf_logged_function_trace_member >> strip_tac >>
  drule_all ricf_logged_round_block >> strip_tac >>
  qpat_x_assum `MEM e _`
    (qx_choose_then `before` (qx_choose_then `after` assume_tac) o
      REWRITE_RULE [MEM_SPLIT]) >>
  `?current. ricf_block_trace (EL b round.fn_blocks) before current /\
     ricf_block_trace current (e::after) (EL b mid.fn_blocks)` by
    (irule ricf_block_trace_split >> metis_tac[]) >>
  simp[ricf_located_event_def] >> metis_tac[APPEND_ASSOC, APPEND]
QED

(* The initial block and the edited validation block occupy the same source
   position.  This is only an edit relation, not acceptance transport. *)
Theorem ricf_located_event_source_block:
  !base original log round b es prefix e current.
  ricf_located_event base original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
    b < LENGTH original.fn_blocks /\
    ricf_block_edit (EL b original.fn_blocks) current
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `ricf_located_event base0 original log round b es prefix e current` >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_function_trace_edit >> strip_tac >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts round))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_block_edit (EL b round.fn_blocks) current` by
    (irule ricf_block_trace_edit >>
     qexistsl_tac [`EL b round.fn_blocks`,`base0 with icf_dfg := dfg_build_function round`,
                  `prefix`] >> simp[EL_MEM] >>
     qexists_tac `round` >> simp[] >> metis_tac[EL_MEM]) >>
  fs[ricf_function_edit_def, LIST_REL_EL_EQN] >>
  metis_tac[ricf_block_edit_trans]
QED

Theorem ricf_located_event_original_copy_member:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  b < LENGTH original.fn_blocks /\
  e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
  MEM (ricf_event_copy e (EL b original.fn_blocks)) (fn_insts original) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   ricf_inst_edit (ricf_event_copy e (EL b original.fn_blocks))
     (ricf_event_copy e current)` by
    (gvs[ricf_block_edit_def, LIST_REL_EL_EQN, ricf_event_copy_def] >>
     metis_tac[]) >>
  simp[fn_insts_def, fn_insts_blocks_MEM, ricf_event_copy_def] >>
  fs[ricf_inst_edit_def, ricf_event_copy_def] >> metis_tac[EL_MEM]
QED

Theorem ricf_located_event_source_descriptor:
  !base original log round b es prefix e current.
  ricf_located_event base original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  ricf_event_copy e current = ricf_event_copy e (EL b original.fn_blocks) /\
  ?dst src sz.
    (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
    ricf_event_roots e current =
      SOME (icf_assign_root (dfg_build_function original) {} dst,
            icf_assign_root_op (dfg_build_function original) src, sz) /\
    icf_collect_aliases (dfg_build_function round)
      (icf_assign_root (dfg_build_function round) {} dst) =
    icf_collect_aliases (dfg_build_function original)
      (icf_assign_root (dfg_build_function original) {} dst)
Proof
  rpt gen_tac >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  irule ricf_later_round_source_descriptor >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem ricf_located_event_operand_history:
  !base original log round b es prefix e current i j.
  ricf_located_event base original log round b es prefix e current /\
  i < LENGTH (EL b round.fn_blocks).bb_instructions ==>
  ricf_operand_at (EL i current.bb_instructions) j =
    FOLDL (ricf_edit_operand i (EL i (EL b round.fn_blocks).bb_instructions).inst_id j)
      (ricf_operand_at (EL i (EL b round.fn_blocks).bb_instructions) j)
      (ricf_event_log (EL b round.fn_blocks) prefix)
Proof
  rpt strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  irule ricf_block_trace_operand_history >> simp[]
QED

Theorem ricf_logged_round_operand_history:
  !base round logs mid b i j.
  ricf_logged_round base round logs mid /\ b < LENGTH round.fn_blocks /\
  i < LENGTH (EL b round.fn_blocks).bb_instructions ==>
  ricf_operand_at (EL i (EL b mid.fn_blocks).bb_instructions) j =
    FOLDL (ricf_edit_operand i (EL i (EL b round.fn_blocks).bb_instructions).inst_id j)
      (ricf_operand_at (EL i (EL b round.fn_blocks).bb_instructions) j)
      (ricf_event_log (EL b round.fn_blocks) (EL b logs))
Proof
  rpt strip_tac >> drule_all ricf_logged_round_block >> strip_tac >>
  irule ricf_block_trace_operand_history >> simp[]
QED
