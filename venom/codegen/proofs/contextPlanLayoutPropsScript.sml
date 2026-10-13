(* Generated context-plan layout producers.
 * TOP-LEVEL: ordered_spill_regions_SNOC, asm_pc_to_offset_zero,
 *   generate_context_plan_layout_wf.
 * Helpers: five-part accumulator invariant, initialization, extension,
 *   region traversal preservation and finishing.
 *)
Theory contextPlanLayoutProps
Ancestors
  stackPlanTypes stackPlanGen allocMono venomLayout codegenRel
  list rich_list arithmetic

(* ===== Structural producers ===== *)

Theorem ordered_spill_regions_SNOC:
  ordered_spill_regions (SNOC r rs) <=>
  ordered_spill_regions rs /\
  EVERY (\r'. r'.sr_spill_end <= r.sr_spill_base) rs /\
  r.sr_spill_base <= r.sr_spill_end
Proof
  Induct_on `rs` >> simp[ordered_spill_regions_def, EVERY_SNOC] >>
  metis_tac[]
QED

Theorem asm_pc_to_offset_zero:
  asm_pc_to_offset prog 0 = 0
Proof
  simp[asm_pc_to_offset_def]
QED

(* ===== Accumulator invariant J (PLAN 8.3 L2) ===== *)

Definition context_plan_acc_layout_def:
  context_plan_acc_layout max_eom acc <=>
    EVERY (\r. max_eom <= r.sr_spill_base /\
                r.sr_spill_base <= r.sr_spill_end) acc.cpa_regions /\
    ordered_spill_regions acc.cpa_regions /\
    EVERY (\r. r.sr_spill_end <= acc.cpa_next_spill_base)
      acc.cpa_regions /\
    max_eom <= acc.cpa_next_spill_base /\
    EVERY (\r. r.sr_spill_base < r.sr_spill_end ==>
                r.sr_spill_end <= acc.cpa_peak_spill_end) acc.cpa_regions
End

Theorem context_plan_acc_layout_init:
  context_plan_acc_layout max_eom
    <| cpa_regions := []; cpa_label_counter := 0;
       cpa_next_spill_base := max_eom; cpa_peak_spill_end := 0 |>
Proof
  simp[context_plan_acc_layout_def, ordered_spill_regions_def]
QED

(* Helper: empty regions do not increase the live spill peak. *)
Theorem context_plan_acc_layout_extend:
  context_plan_acc_layout max_eom acc /\
  region.sr_spill_base = acc.cpa_next_spill_base /\
  region.sr_spill_base <= region.sr_spill_end ==>
  context_plan_acc_layout max_eom
    (<|
      cpa_regions := SNOC region acc.cpa_regions;
      cpa_label_counter := labels;
      cpa_next_spill_base := region.sr_spill_end;
      cpa_peak_spill_end :=
        if region.sr_spill_base < region.sr_spill_end then
          MAX acc.cpa_peak_spill_end region.sr_spill_end
        else acc.cpa_peak_spill_end |> )
Proof
  rw[context_plan_acc_layout_def, EVERY_SNOC,
     ordered_spill_regions_SNOC] >>
  fs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS]
QED

(* Helper: the region traversal is a successful option-valued fold. *)
Theorem generate_context_regions_layout:
  !fns acc acc'.
    (!fn base labels ops ps.
      gen fn base labels = SOME (ops, ps) ==>
      base <= ps.ps_alloc.sa_next_offset) /\
    context_plan_acc_layout max_eom acc /\
    generate_context_regions gen fns acc = SOME acc' ==>
    context_plan_acc_layout max_eom acc'
Proof
  Induct_on `fns` >- simp[generate_context_regions_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_context_regions _ (_::_) _ = _` mp_tac >>
  simp[Once generate_context_regions_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `gen current_fn acc.cpa_next_spill_base acc.cpa_label_counter =
    SOME (ops, final_ps)` >>
  qmatch_asmsub_abbrev_tac `generate_context_regions gen fns next` >>
  first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `next` >> simp[Abbr`next`] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`region` |->
      `<| sr_fn_name := current_fn.fn_name;
          sr_spill_base := acc.cpa_next_spill_base;
          sr_spill_end := final_ps.ps_alloc.sa_next_offset;
          sr_plan := ops |>`] context_plan_acc_layout_extend)) >>
  simp[] >> first_x_assum drule >> simp[]
QED

Theorem finish_context_plan_layout:
  context_plan_acc_layout max_eom acc ==>
  context_plan_layout_wf (finish_context_plan max_eom acc)
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `MAX max_eom acc.cpa_peak_spill_end`]
    ceil32_ge) >>
  fs[context_plan_acc_layout_def, context_plan_layout_wf_def,
     finish_context_plan_def, ceil32_aligned, MAX_DEF] >> decide_tac
QED

(* Helper: successful generation also retains the checked final FMP bound. *)
Theorem generate_context_plan_with_layout:
  (!fn base labels ops ps.
    gen fn base labels = SOME (ops, ps) ==>
    base <= ps.ps_alloc.sa_next_offset) /\
  generate_context_plan_with gen ctx = SOME cp ==>
  context_plan_layout_wf cp /\ cp.cp_initial_fmp < dimword (:256)
Proof
  strip_tac >>
  qpat_x_assum `generate_context_plan_with _ _ = _` mp_tac >>
  simp[generate_context_plan_with_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  irule finish_context_plan_layout >>
  `context_plan_acc_layout max_eom
    <| cpa_regions := []; cpa_label_counter := 0;
       cpa_next_spill_base := max_eom; cpa_peak_spill_end := 0 |>`
    by simp[context_plan_acc_layout_init] >>
  drule_all generate_context_regions_layout >> simp[]
QED

Theorem generate_context_plan_layout_wf:
  generate_context_plan ctx = SOME cp ==> context_plan_layout_wf cp
Proof
  simp[generate_context_plan_def] >> strip_tac >>
  irule (cj 1 generate_context_plan_with_layout) >>
  qexistsl_tac [`ctx`, `generate_fn_plan`] >> simp[] >>
  metis_tac[generate_fn_plan_alloc_mono]
QED
