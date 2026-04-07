(*
 * Venom Pipeline Correctness
 *
 * General composition theorem: sequential application of
 * semantics-preserving context transforms preserves semantics.
 * Instantiated for each optimization level.
 *
 * Relations compose via rel_seq: FOLDL rel_seq (=) [R1; R2; ...; RN].
 * Each pass keeps its own R_ok/R_term pair; no UNION of variable sets.
 *
 * TOP-LEVEL:
 *   pass_correct_trans             -- binary transitivity (relational composition)
 *   apply_ctx_fn_transform_correct -- lift per-block dual-ctx sim to ctx_pass_correct
 *   compose_passes_correct         -- N-ary pipeline composition via list induction
 *   venom_pipeline_correct         -- 5-phase pipeline composition
 *   pass_correct_implies_observable -- pass_correct to observable_result_equiv
 *   rel_seq_preserves_observable   -- rel_seq of obs-preserving rels preserves obs
 *)

Theory venomPipelineCorrect
Ancestors
  venomPipeline venomInst
  passSimulationDefs passSimulationProps crossBlockSimProps
  stateEquiv stateEquivProps
  pointerConfinedDefs
  venomExecSemantics

(* ===== Context-Level Pass Correctness ===== *)

(* A context-level pass: transforms a context, preserves semantics.
   R_ok/R_term are the per-state relations for OK/terminal results. *)
Definition ctx_pass_correct_def:
  ctx_pass_correct (p : venom_context -> venom_context) R_ok R_term ctx s <=>
    pass_correct R_ok R_term R_term
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel (p ctx) s)
End

(* ===== Composition Infrastructure ===== *)

(* pass_correct is transitive when relations compose.
   R12_ok/R12_term must contain the relational composition of the
   individual relations (R1 then R2). *)
Theorem pass_correct_trans:
  !R1_ok R1_term R2_ok R2_term R12_ok R12_term exec1 exec2 exec3.
    (!s1 s2 s3. R1_ok s1 s2 /\ R2_ok s2 s3 ==> R12_ok s1 s3) /\
    (!s1 s2 s3. R1_term s1 s2 /\ R2_term s2 s3 ==> R12_term s1 s3) /\
    pass_correct R1_ok R1_term R1_term exec1 exec2 /\
    pass_correct R2_ok R2_term R2_term exec2 exec3 ==>
    pass_correct R12_ok R12_term R12_term exec1 exec3
Proof
  rw[pass_correct_def] >>
  (* exec2 terminates at some fuel (from either direction) *)
  `?fuel2. terminates (exec2 fuel2)` by metis_tac[] >>
  (* Get lift_results for exec1-exec2 and exec2-exec3 *)
  `lift_result R1_ok R1_term R1_term (exec1 fuel) (exec2 fuel2)` by metis_tac[] >>
  `lift_result R2_ok R2_term R2_term (exec2 fuel2) (exec3 fuel')` by metis_tac[] >>
  (* Compose via case analysis *)
  Cases_on `exec1 fuel` >> Cases_on `exec2 fuel2` >> Cases_on `exec3 fuel'` >>
  gvs[lift_result_def] >> metis_tac[]
QED

(* ===== rel_seq helpers ===== *)

Triviality rel_seq_id_l:
  rel_seq (=) R = R
Proof
  simp[FUN_EQ_THM, rel_seq_def]
QED

Triviality rel_seq_id_r:
  rel_seq R (=) = R
Proof
  simp[FUN_EQ_THM, rel_seq_def]
QED

Triviality rel_seq_assoc:
  rel_seq (rel_seq R1 R2) R3 = rel_seq R1 (rel_seq R2 R3)
Proof
  simp[FUN_EQ_THM, rel_seq_def] >> metis_tac[]
QED

Triviality foldl_rel_seq_acc:
  !Rs (R : 'a -> 'a -> bool).
    FOLDL rel_seq R Rs = rel_seq R (FOLDL rel_seq (=) Rs)
Proof
  Induct >- simp[rel_seq_id_r] >>
  rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [listTheory.FOLDL])) >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [listTheory.FOLDL]))) >>
  PURE_REWRITE_TAC [rel_seq_id_l] >>
  pop_assum (fn ih => PURE_ONCE_REWRITE_TAC [ih]) >>
  simp[rel_seq_assoc]
QED

Triviality foldl_rel_seq_cons:
  FOLDL rel_seq (=) (R::Rs) = rel_seq R (FOLDL rel_seq (=) Rs)
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [listTheory.FOLDL])) >>
  PURE_REWRITE_TAC[rel_seq_id_l] >>
  MATCH_ACCEPT_TAC (SPEC_ALL foldl_rel_seq_acc)
QED

(* ===== Lifting Infrastructure ===== *)

(* Helper: lookup_function in MAP f = OPTION_MAP f of lookup *)
Triviality lookup_fn_map_ctx:
  !name ctx f.
    (!fn. (f fn).fn_name = fn.fn_name) ==>
    lookup_function name (apply_ctx_fn_transform f ctx).ctx_functions =
      OPTION_MAP f (lookup_function name ctx.ctx_functions)
Proof
  rw[apply_ctx_fn_transform_def] >> irule lookup_function_map >> simp[]
QED

(* Helper: run_context fuel_mono from run_function fuel_mono *)
Triviality run_context_fuel_mono:
  !fuel ctx s.
    terminates (run_context fuel ctx s) ==>
    !k. run_context (fuel + k) ctx s = run_context fuel ctx s
Proof
  simp[run_context_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `ctx.ctx_entry` >> gvs[terminates_def] >>
  Cases_on `lookup_function x ctx.ctx_functions` >> gvs[terminates_def] >>
  Cases_on `entry_block x'` >> gvs[terminates_def] >>
  irule run_function_fuel_mono >> gvs[terminates_def]
QED

(* Lift per-block dual-context simulation to context-level pass_correct.
   Uses module_sim_dual_ctx (bidirectional: both-error or lift_result)
   to get termination equivalence.

   Preconditions:
   1. R_ok/R_term properties (reflexive, R_ok => R_term, preserves ctrl fields)
   2. f preserves fn_name
   3. Block label correspondence between fn and f(fn)
   4. Entry block label preservation: HD blocks have same label
   5. Bidirectional per-block simulation with callee IH *)
(* Helper: block label correspondence + fn_blocks=[] ==> other fn_blocks=[] *)
Triviality blocks_empty_from_label_correspondence:
  !fn1_blocks fn2_blocks.
    (!lbl. IS_SOME (lookup_block lbl fn1_blocks) <=>
           IS_SOME (lookup_block lbl fn2_blocks)) /\
    fn1_blocks = [] ==> fn2_blocks = []
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  Cases_on `fn2_blocks` >> gvs[] >>
  first_x_assum (qspec_then `h.bb_label` mp_tac) >>
  simp[lookup_block_def, listTheory.FIND_thm]
QED

(* Helper: bridge between MEM-based per-block sim and lookup-based module_sim *)
Triviality ctx_fn_transform_module_sim:
  !f ctx (R_ok : venom_state -> venom_state -> bool) R_term.
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (!fn. (f fn).fn_name = fn.fn_name) /\
    (!fn. MEM fn ctx.ctx_functions ==>
      !lbl. IS_SOME (lookup_block lbl fn.fn_blocks) <=>
            IS_SOME (lookup_block lbl (f fn).fn_blocks)) /\
    (!fn lbl bb1 bb2 fuel s1 s2.
      MEM fn ctx.ctx_functions /\
      lookup_block lbl fn.fn_blocks = SOME bb1 /\
      lookup_block lbl (f fn).fn_blocks = SOME bb2 /\
      R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
      (!callee_name cfn cs1 cs2.
        lookup_function callee_name ctx.ctx_functions = SOME cfn /\
        R_ok cs1 cs2 /\ cs1.vs_inst_idx = 0 ==>
        ((?e1. run_function fuel ctx cfn cs1 = Error e1) /\
         (?e2. run_function fuel (apply_ctx_fn_transform f ctx)
                 (f cfn) cs2 = Error e2)) \/
        lift_result R_ok R_term R_term
          (run_function fuel ctx cfn cs1)
          (run_function fuel (apply_ctx_fn_transform f ctx)
            (f cfn) cs2))
      ==>
      ((?e1. run_block fuel ctx bb1 s1 = Error e1) /\
       (?e2. run_block fuel (apply_ctx_fn_transform f ctx)
               bb2 s2 = Error e2)) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb1 s1)
        (run_block fuel (apply_ctx_fn_transform f ctx) bb2 s2))
  ==>
    !fn_name fn1 fn2 fuel s1 s2.
      lookup_function fn_name ctx.ctx_functions = SOME fn1 /\
      lookup_function fn_name
        (apply_ctx_fn_transform f ctx).ctx_functions = SOME fn2 /\
      R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
      ((?e1. run_function fuel ctx fn1 s1 = Error e1) /\
       (?e2. run_function fuel (apply_ctx_fn_transform f ctx)
               fn2 s2 = Error e2)) \/
      lift_result R_ok R_term R_term
        (run_function fuel ctx fn1 s1)
        (run_function fuel (apply_ctx_fn_transform f ctx) fn2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `ctx`, `apply_ctx_fn_transform f ctx`]
    mp_tac module_sim_dual_ctx >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    (* Block label correspondence *)
    >- (rpt strip_tac >>
        `fn2 = f fn1` by (
          `lookup_function fn_name
             (apply_ctx_fn_transform f ctx).ctx_functions =
             OPTION_MAP f (lookup_function fn_name ctx.ctx_functions)` by
            (irule lookup_fn_map_ctx >> simp[]) >>
          gvs[]) >>
        gvs[] >>
        first_x_assum irule >>
        metis_tac[lookup_function_MEM])
    (* Per-block sim *)
    >- (rpt strip_tac >>
        `fn2 = f fn1` by (
          `lookup_function fn_name
             (apply_ctx_fn_transform f ctx).ctx_functions =
             OPTION_MAP f (lookup_function fn_name ctx.ctx_functions)` by
            (irule lookup_fn_map_ctx >> simp[]) >>
          gvs[]) >>
        gvs[] >>
        last_x_assum (qspecl_then
          [`fn1`, `lbl`, `bb1`, `bb2`, `fuel`, `s1`, `s2`] mp_tac) >>
        impl_tac
        >- (conj_tac >- metis_tac[lookup_function_MEM] >>
            simp[] >>
            rpt gen_tac >> strip_tac >>
            `lookup_function callee_name
               (apply_ctx_fn_transform f ctx).ctx_functions =
               SOME (f cfn)` by (
              `lookup_function callee_name
                 (apply_ctx_fn_transform f ctx).ctx_functions =
                 OPTION_MAP f (lookup_function callee_name
                   ctx.ctx_functions)` by
                (irule lookup_fn_map_ctx >> simp[]) >>
              gvs[]) >>
            first_x_assum (qspecl_then
              [`callee_name`, `cfn`, `f cfn`, `cs1`, `cs2`] mp_tac) >>
            simp[])
        >- simp[])
  ) >>
  disch_then ACCEPT_TAC
QED

Theorem apply_ctx_fn_transform_correct:
  !f ctx s R_ok R_term.
    (* R_ok properties *)
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (* f preserves fn_name *)
    (!fn. (f fn).fn_name = fn.fn_name) /\
    (* Block label correspondence *)
    (!fn. MEM fn ctx.ctx_functions ==>
      !lbl. IS_SOME (lookup_block lbl fn.fn_blocks) <=>
            IS_SOME (lookup_block lbl (f fn).fn_blocks)) /\
    (* Entry block label preservation *)
    (!fn. MEM fn ctx.ctx_functions /\ fn.fn_blocks <> [] ==>
      (f fn).fn_blocks <> [] /\
      (HD (f fn).fn_blocks).bb_label = (HD fn.fn_blocks).bb_label) /\
    (* Per-block bidirectional simulation *)
    (!fn lbl bb1 bb2 fuel s1 s2.
      MEM fn ctx.ctx_functions /\
      lookup_block lbl fn.fn_blocks = SOME bb1 /\
      lookup_block lbl (f fn).fn_blocks = SOME bb2 /\
      R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
      (* Callee IH *)
      (!callee_name cfn cs1 cs2.
        lookup_function callee_name ctx.ctx_functions = SOME cfn /\
        R_ok cs1 cs2 /\ cs1.vs_inst_idx = 0 ==>
        ((?e1. run_function fuel ctx cfn cs1 = Error e1) /\
         (?e2. run_function fuel (apply_ctx_fn_transform f ctx)
                 (f cfn) cs2 = Error e2)) \/
        lift_result R_ok R_term R_term
          (run_function fuel ctx cfn cs1)
          (run_function fuel (apply_ctx_fn_transform f ctx)
            (f cfn) cs2))
      ==>
      ((?e1. run_block fuel ctx bb1 s1 = Error e1) /\
       (?e2. run_block fuel (apply_ctx_fn_transform f ctx)
               bb2 s2 = Error e2)) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb1 s1)
        (run_block fuel (apply_ctx_fn_transform f ctx) bb2 s2))
  ==>
    ctx_pass_correct (apply_ctx_fn_transform f) R_ok R_term ctx s
Proof
  rpt gen_tac >> strip_tac >>
  (* Get module_sim result BEFORE unfolding definitions *)
  qspecl_then [`f`, `ctx`, `R_ok`, `R_term`]
    mp_tac ctx_fn_transform_module_sim >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  simp[ctx_pass_correct_def, pass_correct_def] >>
  qabbrev_tac `ctx2 = apply_ctx_fn_transform f ctx` >>
  (* Establish ctx2 correspondence facts upfront *)
  `ctx2.ctx_entry = ctx.ctx_entry` by
    simp[Abbr `ctx2`, apply_ctx_fn_transform_def] >>
  `!name. lookup_function name ctx2.ctx_functions =
          OPTION_MAP f (lookup_function name ctx.ctx_functions)` by
    (simp[Abbr `ctx2`, apply_ctx_fn_transform_def] >>
     gen_tac >> irule lookup_function_map >> simp[]) >>
  (* Unfold run_context on both sides, substitute ctx2 facts *)
  simp[run_context_def] >>
  Cases_on `ctx.ctx_entry` >> gvs[terminates_def] >>
  rename1 `ctx.ctx_entry = SOME entry_name` >>
  Cases_on `lookup_function entry_name ctx.ctx_functions` >>
  gvs[terminates_def] >>
  rename1 `_ = SOME entry_fn` >>
  Cases_on `entry_block entry_fn` >> gvs[terminates_def]
  >- (
    (* entry_fn has no blocks => f(entry_fn) has no blocks *)
    `(f entry_fn).fn_blocks = []` by (
      `entry_fn.fn_blocks = []` by gvs[entry_block_def, listTheory.NULL_EQ] >>
      imp_res_tac lookup_function_MEM >>
      irule blocks_empty_from_label_correspondence >>
      qexists_tac `entry_fn.fn_blocks` >> simp[]) >>
    gvs[entry_block_def, listTheory.NULL_EQ, terminates_def]
  ) >>
  rename1 `entry_block entry_fn = SOME entry_bb` >>
  `entry_fn.fn_blocks <> []` by (gvs[entry_block_def, listTheory.NULL_EQ]) >>
  imp_res_tac lookup_function_MEM >>
  `(f entry_fn).fn_blocks <> [] /\
   (HD (f entry_fn).fn_blocks).bb_label = (HD entry_fn.fn_blocks).bb_label` by
    (first_x_assum irule >> simp[]) >>
  `entry_block (f entry_fn) = SOME (HD (f entry_fn).fn_blocks)` by
    simp[entry_block_def, listTheory.NULL_EQ] >>
  gvs[] >>
  `entry_bb = HD entry_fn.fn_blocks` by gvs[entry_block_def, listTheory.NULL_EQ] >>
  gvs[] >>
  (* Both sides call run_function with same initial state (R_ok reflexive) *)
  PURE_REWRITE_TAC [GSYM terminates_def] >>
  qabbrev_tac `s0 = s with <| vs_prev_bb := NONE;
    vs_current_bb := (HD entry_fn.fn_blocks).bb_label;
    vs_inst_idx := 0 |>` >>
  (* Get the bidir simulation result for the entry function *)
  `!fuel.
     ((?e1. run_function fuel ctx entry_fn s0 = Error e1) /\
      (?e2. run_function fuel ctx2 (f entry_fn) s0 = Error e2)) \/
     lift_result R_ok R_term R_term
       (run_function fuel ctx entry_fn s0)
       (run_function fuel ctx2 (f entry_fn) s0)` by (
    gen_tac >>
    first_x_assum (qspecl_then
      [`entry_name`, `entry_fn`, `f entry_fn`, `fuel`, `s0`, `s0`] mp_tac) >>
    simp[Abbr `s0`]) >>
  (* Now derive pass_correct components *)
  conj_tac
  >- (
    (* Termination equivalence *)
    eq_tac >> strip_tac
    >- (
      (* Forward: left terminates => right terminates *)
      rename1 `terminates (run_function fuel0 ctx entry_fn s0)` >>
      first_x_assum (qspec_then `fuel0` mp_tac) >>
      strip_tac >- gvs[terminates_def] >>
      qexists_tac `fuel0` >>
      Cases_on `run_function fuel0 ctx entry_fn s0` >>
      Cases_on `run_function fuel0 ctx2 (f entry_fn) s0` >>
      gvs[terminates_def, lift_result_def]
    )
    >- (
      (* Backward: right terminates => left terminates *)
      rename1 `terminates (run_function fuel0 ctx2 (f entry_fn) s0)` >>
      first_x_assum (qspec_then `fuel0` mp_tac) >>
      strip_tac >- gvs[terminates_def] >>
      qexists_tac `fuel0` >>
      Cases_on `run_function fuel0 ctx entry_fn s0` >>
      Cases_on `run_function fuel0 ctx2 (f entry_fn) s0` >>
      gvs[terminates_def, lift_result_def]
    )
  )
  >- (
    (* lift_result for all fuel/fuel' pairs *)
    rpt strip_tac >>
    rename1 `terminates (run_function fuel1 ctx entry_fn s0)` >>
    rename1 `terminates (run_function fuel2 ctx2 (f entry_fn) s0)` >>
    (* At fuel1: left terminates, so bidir gives lift_result *)
    first_x_assum (qspec_then `fuel1` mp_tac) >>
    strip_tac >- gvs[terminates_def] >>
    (* right also terminates at fuel1 *)
    `terminates (run_function fuel1 ctx2 (f entry_fn) s0)` by (
      Cases_on `run_function fuel1 ctx entry_fn s0` >>
      Cases_on `run_function fuel1 ctx2 (f entry_fn) s0` >>
      gvs[terminates_def, lift_result_def]) >>
    (* By fuel_mono: right@fuel1 = right@fuel2 *)
    `run_function fuel1 ctx2 (f entry_fn) s0 =
     run_function fuel2 ctx2 (f entry_fn) s0` by (
      `fuel1 <= fuel2 \/ fuel2 <= fuel1` by simp[] >> gvs[]
      >- (`fuel2 = fuel1 + (fuel2 - fuel1)` by simp[] >>
          metis_tac[run_function_fuel_mono])
      >- (`fuel1 = fuel2 + (fuel1 - fuel2)` by simp[] >>
          metis_tac[run_function_fuel_mono])) >>
    gvs[]
  )
QED

(* ===== N-ary Pipeline Composition ===== *)

(* Determinism: same exec at two terminating fuels gives same result *)
Triviality run_context_fuel_eq:
  !fuel fuel' ctx s.
    terminates (run_context fuel ctx s) /\
    terminates (run_context fuel' ctx s) ==>
    run_context fuel ctx s = run_context fuel' ctx s
Proof
  rpt strip_tac >>
  `fuel <= fuel' \/ fuel' <= fuel` by simp[] >|
  [all_tac, `fuel' <= fuel` by simp[]] >>
  imp_res_tac arithmeticTheory.LESS_EQUAL_ADD >> gvs[] >>
  metis_tac[run_context_fuel_mono]
QED

(* Compose a list of context-level passes into a single pass_correct.
   Each pass i is correct w.r.t. the context produced by passes 0..i-1.
   Relations compose via FOLDL rel_seq. *)
Theorem compose_passes_correct:
  !passes R_oks R_terms ctx s.
    LENGTH R_oks = LENGTH passes /\ LENGTH R_terms = LENGTH passes /\
    (!i. i < LENGTH passes ==>
      ctx_pass_correct (EL i passes) (EL i R_oks) (EL i R_terms)
        (FOLDL (\c p. p c) ctx (TAKE i passes)) s)
    ==>
    pass_correct (FOLDL rel_seq (=) R_oks) (FOLDL rel_seq (=) R_terms)
      (FOLDL rel_seq (=) R_terms)
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel (FOLDL (\c p. p c) ctx passes) s)
Proof
  Induct
  >- (
    rpt gen_tac >> strip_tac >> gvs[] >>
    simp[pass_correct_def] >> rpt gen_tac >> strip_tac >>
    `run_context fuel ctx s = run_context fuel' ctx s` by
      metis_tac[run_context_fuel_eq] >>
    Cases_on `run_context fuel' ctx s` >> gvs[lift_result_def]
  )
  >- (
    rpt gen_tac >> strip_tac
    >> Cases_on `R_oks` >- gvs[]
    >> Cases_on `R_terms` >- gvs[]
    >> PURE_REWRITE_TAC [foldl_rel_seq_cons]
    >> gvs[]
    >> rename1 `pass_correct
        (rel_seq R_ok_hd (FOLDL _ _ R_oks_tl))
        (rel_seq R_term_hd (FOLDL _ _ R_terms_tl))`
    >> qspecl_then
      [`R_ok_hd`, `R_term_hd`,
       `FOLDL rel_seq (=) R_oks_tl`, `FOLDL rel_seq (=) R_terms_tl`,
       `rel_seq R_ok_hd (FOLDL rel_seq (=) R_oks_tl)`,
       `rel_seq R_term_hd (FOLDL rel_seq (=) R_terms_tl)`,
       `\fuel. run_context fuel ctx s`,
       `\fuel. run_context fuel
         ((h : venom_context -> venom_context) ctx) s`,
       `\fuel. run_context fuel
         (FOLDL (\c p. p c)
           ((h : venom_context -> venom_context) ctx) passes) s`]
      mp_tac pass_correct_trans
    >> impl_tac >- (
      simp[rel_seq_def]
      >> conj_tac >- metis_tac[]
      >> conj_tac >- metis_tac[]
      >> conj_tac >- (
        first_x_assum (qspec_then `0` mp_tac) >> simp[ctx_pass_correct_def]
      )
      >> first_x_assum irule >> simp[]
      >> rpt strip_tac
      >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
    )
    >> simp[]
  )
QED

(* ===== Pipeline Correctness ===== *)

(* The full pipeline preserves semantics, parameterized by the
   per-function pass sequence. Each phase's correctness is a
   precondition; the theorem composes them via rel_seq. *)
Theorem venom_pipeline_correct:
  !ircf_global ricf_global threshold fn_pipeline ctx s
    R_ok_cfg R_term_cfg R_ok_ircf R_term_ircf R_ok_ricf R_term_ricf
    R_ok_inl R_term_inl R_ok_fn R_term_fn.
    (* Pointer confinement: alloca pointers don't escape to
     * observable channels. Precondition on initial context;
     * consumed by passes that change alloca layout
     * (remove_unused, function_inliner). *)
    EVERY alloca_pointer_confined ctx.ctx_functions /\
    ctx_pass_correct (apply_ctx_fn_transform simplify_cfg_fn)
                     R_ok_cfg R_term_cfg ctx s /\
    (let ctx1 = apply_ctx_fn_transform simplify_cfg_fn ctx in
     ctx_pass_correct (apply_ctx_fn_transform ircf_global)
                      R_ok_ircf R_term_ircf ctx1 s) /\
    (let ctx2 = apply_ctx_fn_transform ircf_global
                  (apply_ctx_fn_transform simplify_cfg_fn ctx) in
     ctx_pass_correct (apply_ctx_fn_transform ricf_global)
                      R_ok_ricf R_term_ricf ctx2 s) /\
    (let ctx3 = apply_ctx_fn_transform ricf_global
                  (apply_ctx_fn_transform ircf_global
                    (apply_ctx_fn_transform simplify_cfg_fn ctx)) in
     ctx_pass_correct (function_inliner_ctx threshold)
                      R_ok_inl R_term_inl ctx3 s) /\
    (let ctx4 = function_inliner_ctx threshold
                  (apply_ctx_fn_transform ricf_global
                    (apply_ctx_fn_transform ircf_global
                      (apply_ctx_fn_transform simplify_cfg_fn ctx))) in
     ctx_pass_correct (apply_ctx_fn_transform fn_pipeline)
                      R_ok_fn R_term_fn ctx4 s)
  ==>
    ctx_pass_correct
      (venom_pipeline ircf_global ricf_global threshold fn_pipeline)
      (FOLDL rel_seq (=) [R_ok_cfg; R_ok_ircf; R_ok_ricf; R_ok_inl; R_ok_fn])
      (FOLDL rel_seq (=) [R_term_cfg; R_term_ircf; R_term_ricf;
                          R_term_inl; R_term_fn])
      ctx s
Proof
  simp[ctx_pass_correct_def, venom_pipeline_def] >>
  rpt strip_tac >>
  qspecl_then
    [`[apply_ctx_fn_transform simplify_cfg_fn;
       apply_ctx_fn_transform ircf_global;
       apply_ctx_fn_transform ricf_global;
       function_inliner_ctx threshold;
       apply_ctx_fn_transform fn_pipeline]`,
     `[R_ok_cfg; R_ok_ircf; R_ok_ricf; R_ok_inl; R_ok_fn]`,
     `[R_term_cfg; R_term_ircf; R_term_ricf; R_term_inl; R_term_fn]`,
     `ctx`, `s`] mp_tac compose_passes_correct >>
  simp[] >>
  impl_tac >- (
    rpt strip_tac >>
    `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4` by simp[] >>
    gvs[ctx_pass_correct_def]
  ) >>
  simp[]
QED

(* pass_correct implies observable equivalence when R_ok/R_term
   imply observable equivalence. *)
Theorem pass_correct_implies_observable:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (R_abort : venom_state -> venom_state -> bool) exec1 exec2 fuel fuel'.
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_abort s1 s2 ==> revert_equiv s1 s2) /\
    pass_correct R_ok R_term R_abort exec1 exec2 /\
    terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
    observable_result_equiv (exec1 fuel) (exec2 fuel')
Proof
  rw[pass_correct_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exec1 fuel` >> Cases_on `exec2 fuel'` >>
  gvs[lift_result_def, observable_result_equiv_def, revert_equiv_def,
      terminates_def]
QED

(* rel_seq of observable-equiv-preserving relations preserves observable_equiv.
   Used to discharge pass_correct_implies_observable for composed pipelines. *)
Theorem rel_seq_preserves_observable:
  (!s1 s2. R1 s1 s2 ==> observable_equiv s1 s2) /\
  (!s1 s2. R2 s1 s2 ==> observable_equiv s1 s2) ==>
  (!s1 s2. rel_seq R1 R2 s1 s2 ==> observable_equiv s1 s2)
Proof
  rw[rel_seq_def] >> metis_tac[observable_equiv_trans]
QED

(* FOLDL rel_seq (=) Rs preserves observable_equiv when each Ri does. *)
Theorem foldl_rel_seq_preserves_observable:
  !Rs.
    EVERY (\R. !s1 s2. R s1 s2 ==> observable_equiv s1 s2) Rs ==>
    (!s1 s2. FOLDL rel_seq (=) Rs s1 s2 ==> observable_equiv s1 s2)
Proof
  Induct >- simp[observable_equiv_refl] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FOLDL _ _ _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[foldl_rel_seq_acc] >>
  simp[rel_seq_def] >> rpt strip_tac >>
  irule observable_equiv_trans >>
  metis_tac[]
QED
