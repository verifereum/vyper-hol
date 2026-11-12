(* Forwarding certificates retain the analysis used at each successful step.
   In particular, a block trace does NOT silently rebuild its DFG.  The
   function certificate records round boundaries, where only the DFG changes.
   Safety of these traces is a separate obligation, not a constructor rule. *)
Theory readonlyInvokeCopyFwdPlan
Ancestors
  readonlyInvokeCopyFwdDefs readonlyMemoryArgsProps indexedLists dfgAnalysisProps
  invokeCopyFwdTransport
  list rich_list pair option passSharedDefs allocaRemapSSA

Datatype:
  ricf_forward_event = <|
    rfe_ctx : icf_ctx;
    rfe_index : num;
    rfe_source : string option;
    rfe_sites : (instruction # num) list
  |>
End

(* The selected operand is exactly the one used by ricf_pass_block,
   including the non-variable-source branch. *)
Definition ricf_event_source_def:
  ricf_event_source e bb =
    case e.rfe_source of
      SOME sv => Var sv
    | NONE => EL 1 (EL e.rfe_index bb.bb_instructions).inst_operands
End

Definition ricf_event_ok_def:
  ricf_event_ok e bb <=>
    ricf_try_forward e.rfe_ctx bb e.rfe_index =
      SOME (e.rfe_source, e.rfe_sites)
End

Definition ricf_event_apply_def:
  ricf_event_apply e bb =
    bb with bb_instructions :=
      ricf_apply_forward bb.bb_instructions e.rfe_index
        (ricf_event_source e bb) e.rfe_sites
End

(* Roots and size refer to the pre-step MCOPY, not the NOP left behind.
   Instruction identities are stable throughout a block trace. *)
Definition ricf_event_copy_def:
  ricf_event_copy e bb = EL e.rfe_index bb.bb_instructions
End

Definition ricf_event_roots_def:
  ricf_event_roots e bb =
    case (ricf_event_copy e bb).inst_operands of
      [Var dst; src; sz] =>
        SOME (icf_assign_root e.rfe_ctx.icf_dfg {} dst,
              icf_assign_root_op e.rfe_ctx.icf_dfg src, sz)
    | _ => NONE
End

Inductive ricf_block_trace:
[~nil:]
  (!bb. ricf_block_trace bb [] bb)
[~cons:]
  (!bb e es bb'.
    ricf_event_ok e bb /\
    ricf_block_trace (ricf_event_apply e bb) es bb' ==>
    ricf_block_trace bb (e::es) bb')
End

Theorem ricf_one_forward_certificate:
  ricf_try_forward ctx bb k = SOME (sv, sites) ==>
  ricf_block_trace bb
    [<| rfe_ctx := ctx; rfe_index := k;
        rfe_source := sv; rfe_sites := sites |>]
    (ricf_event_apply
      <| rfe_ctx := ctx; rfe_index := k;
         rfe_source := sv; rfe_sites := sites |> bb)
Proof
  strip_tac >> irule ricf_block_trace_cons >>
  simp[ricf_event_ok_def, ricf_block_trace_nil]
QED

Theorem ricf_block_trace_append:
  !bb es mid. ricf_block_trace bb es mid ==>
    !fs last. ricf_block_trace mid fs last ==>
      ricf_block_trace bb (es ++ fs) last
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >> simp[] >>
  metis_tac[ricf_block_trace_cons]
QED

Theorem ricf_event_copy_shape:
  ricf_event_ok e bb ==>
  e.rfe_index < LENGTH bb.bb_instructions /\
  (ricf_event_copy e bb).inst_opcode = MCOPY /\
  ?dst src sz.
    (ricf_event_copy e bb).inst_operands = [Var dst; src; sz]
Proof
  simp[ricf_event_ok_def, ricf_event_copy_def, ricf_try_forward_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ricf_event_roots_exist:
  ricf_event_ok e bb ==> ?d s sz. ricf_event_roots e bb = SOME (d,s,sz)
Proof
  strip_tac >> drule ricf_event_copy_shape >> strip_tac >>
  simp[ricf_event_roots_def]
QED

Theorem ricf_event_prefix_and_copy:
  ricf_event_ok e bb ==>
    LENGTH (ricf_event_apply e bb).bb_instructions = LENGTH bb.bb_instructions /\
    EL e.rfe_index (ricf_event_apply e bb).bb_instructions =
      mk_nop_inst (ricf_event_copy e bb) /\
    (!i. i < e.rfe_index ==>
      EL i (ricf_event_apply e bb).bb_instructions = EL i bb.bb_instructions)
Proof
  simp[ricf_event_ok_def, ricf_event_apply_def, ricf_event_copy_def] >>
  metis_tac[ricf_try_forward_prefix_and_copy]
QED

(* This equation retains ALL matching positions, including two readonly
   parameters of the same call.  No single-pair-per-call assumption. *)
Theorem ricf_event_operand:
  i < LENGTH bb.bb_instructions /\ i <> e.rfe_index /\
  j < LENGTH (EL i bb.bb_instructions).inst_operands ==>
  EL j (EL i (ricf_event_apply e bb).bb_instructions).inst_operands =
    if MEM ((EL i bb.bb_instructions).inst_id,j)
         (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)
    then ricf_event_source e bb
    else EL j (EL i bb.bb_instructions).inst_operands
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `NULL ps` >>
  Cases_on `NULL ps` >> simp[EL_MAPi] >>
  gvs[Abbr `ps`, MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD,
      NULL_EQ, FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[]
QED

Theorem ricf_event_ids:
  MAP (\inst. inst.inst_id) (ricf_event_apply e bb).bb_instructions =
  MAP (\inst. inst.inst_id) bb.bb_instructions
Proof
  simp[LIST_EQ_REWRITE, ricf_event_apply_def, ricf_apply_forward_def,
       EL_MAPi, EL_MAP] >> rpt strip_tac >>
  rw[mk_nop_inst_def]
QED

Theorem ricf_block_trace_ids:
  !bb es bb'. ricf_block_trace bb es bb' ==>
    bb'.bb_label = bb.bb_label /\
    MAP (\inst. inst.inst_id) bb'.bb_instructions =
      MAP (\inst. inst.inst_id) bb.bb_instructions
Proof
  ho_match_mp_tac ricf_block_trace_ind >>
  simp[ricf_event_ids, ricf_event_apply_def] >>
  rpt strip_tac >>
  qspec_then `e` (qspec_then `bb` mp_tac) ricf_event_ids >>
  simp[ricf_event_apply_def]
QED

(* A round uses one fixed analysis context at all block/fold positions. *)
Definition ricf_round_certificate_def:
  ricf_round_certificate ctx fn fn' <=>
    ?bbs.
      fn' = fn with fn_blocks := bbs /\
      LIST_REL (\bb bb'. ?es.
        ricf_block_trace bb es bb' /\
        EVERY (\e. e.rfe_ctx = ctx) es) fn.fn_blocks bbs
End

(* Only the DFG is rebuilt at round boundaries.  The original BP,
   alias and readonly analyses in base remain fixed, just as in the pass.
   The empty trace also covers the OWHILE nontermination fallback. *)
Inductive ricf_function_trace:
[~nil:]
  (!base fn. ricf_function_trace base fn fn)
[~cons:]
  (!base fn mid last.
    ricf_round_certificate
      (base with icf_dfg := dfg_build_function fn) fn mid /\
    ricf_function_trace base mid last ==>
    ricf_function_trace base fn last)
End

(* These fields are precisely the original syntactic premises; their
   persistence is NOT assumed for intermediate functions.  A preservation
   proof must derive the needed per-event facts from the original fields.
   In particular ricf_src_alloca supplies full source isolation, rather
   than a new hypothesis supplied by the semantic consumer. *)
Definition ricf_function_plan_def:
  ricf_function_plan base fn fn' <=>
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\
    ricf_src_alloca fn /\
    ?mid. ricf_function_trace base fn mid /\
      fn' = if mid.fn_blocks <> fn.fn_blocks
            then clear_nops_function mid else mid
End

Theorem ricf_round_certificate_identity:
  ricf_round_certificate ctx fn fn
Proof
  simp[ricf_round_certificate_def] >>
  qexists_tac `fn.fn_blocks` >> simp[] >>
  irule LIST_REL_refl >> simp[] >>
  rpt strip_tac >> qexists_tac `[]` >> simp[ricf_block_trace_nil]
QED

Theorem ricf_function_trace_trans:
  !base fn mid. ricf_function_trace base fn mid ==>
    !last. ricf_function_trace base mid last ==>
      ricf_function_trace base fn last
Proof
  ho_match_mp_tac ricf_function_trace_ind >> rpt strip_tac >>
  metis_tac[ricf_function_trace_cons]
QED

Theorem ricf_function_plan_identity:
  !base fn.
  ricf_full_alloca_copies fn /\
  ricf_no_derived_mutable_sibling fn /\ ricf_src_alloca fn ==>
  ricf_function_plan base fn fn
Proof
  rpt gen_tac >> simp[ricf_function_plan_def] >> strip_tac >>
  qexists_tac `fn` >> simp[ricf_function_trace_nil]
QED

(* Two eligible copies in one block compose without refreshing the DFG.
   This is deliberately conditional on the second actual try_forward:
   soundness must not pretend that an original success remains a success. *)
Theorem ricf_two_forward_certificate:
  ricf_event_ok e bb /\
  ricf_event_ok f (ricf_event_apply e bb) ==>
  ricf_block_trace bb [e;f]
    (ricf_event_apply f (ricf_event_apply e bb))
Proof
  metis_tac[ricf_block_trace_cons, ricf_block_trace_nil]
QED

(* Regression for repeated readonly arguments: both operand positions,
   not just the first occurrence, must be rewritten. *)
Theorem ricf_apply_forward_repeated_positions:
  ricf_apply_forward
    [mk_inst 1 MCOPY [Var "d"; Var "s"; Lit 32w] [];
     mk_inst 2 INVOKE [Label "callee"; Var "d"; Var "d"] []]
    0 (Var "s")
    [(mk_inst 2 INVOKE [Label "callee"; Var "d"; Var "d"] [],1);
     (mk_inst 2 INVOKE [Label "callee"; Var "d"; Var "d"] [],2)] =
    [mk_nop_inst (mk_inst 1 MCOPY [Var "d"; Var "s"; Lit 32w] []);
     mk_inst 2 INVOKE [Label "callee"; Var "s"; Var "s"] []]
Proof
  EVAL_TAC
QED

(* Moved unchanged from readonlyInvokeCopyFwdProofs for use below Sim. *)
Definition ricf_block_step_def:
  ricf_block_step (ctx : icf_ctx) (changed : bool, cur_bb : basic_block)
                  (i : num) =
    if i >= LENGTH cur_bb.bb_instructions then (changed, cur_bb)
    else
      let inst = EL i cur_bb.bb_instructions in
      if inst.inst_opcode <> MCOPY then (changed, cur_bb)
      else
        case ricf_try_forward ctx cur_bb i of
          NONE => (changed, cur_bb)
        | SOME (src_var_opt, rewrite_sites) =>
            let src_op =
              case src_var_opt of
                SOME sv => Var sv
              | NONE =>
                  EL 1 (EL i cur_bb.bb_instructions).inst_operands in
            let new_insts = ricf_apply_forward
              cur_bb.bb_instructions i src_op rewrite_sites in
            (T, cur_bb with bb_instructions := new_insts)
End

Theorem ricf_pass_block_eq_foldl:
  !ctx bb.
    ricf_pass_block ctx bb =
    FOLDL (ricf_block_step ctx) (F, bb)
      (COUNT_LIST (LENGTH bb.bb_instructions))
Proof
  rw[ricf_pass_block_def, ricf_block_step_def] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ricf_block_step_def]
QED

Theorem ricf_block_step_certificate:
  !ctx c bb i. ?es.
    ricf_block_trace bb es (SND (ricf_block_step ctx (c,bb) i)) /\
    EVERY (\e. e.rfe_ctx = ctx) es
Proof
  rpt gen_tac >> rw[ricf_block_step_def] >>
  TRY (qexists_tac `[]` >> simp[ricf_block_trace_nil] >> NO_TAC) >>
  Cases_on `ricf_try_forward ctx bb i` >> simp[]
  >- (qexists_tac `[]` >> simp[ricf_block_trace_nil]) >>
  PairCases_on `x` >> simp[] >>
  qexists_tac `[<| rfe_ctx := ctx; rfe_index := i;
                  rfe_source := x0; rfe_sites := x1 |>]` >>
  drule ricf_one_forward_certificate >>
  simp[ricf_event_apply_def, ricf_event_source_def]
QED

Theorem ricf_block_fold_certificate:
  !is c bb. ?es.
    ricf_block_trace bb es (SND (FOLDL (ricf_block_step ctx) (c,bb) is)) /\
    EVERY (\e. e.rfe_ctx = ctx) es
Proof
  Induct >> simp[]
  >- (rpt gen_tac >> qexists_tac `[]` >> simp[ricf_block_trace_nil]) >>
  rpt gen_tac >>
  qspecl_then [`ctx`,`c`,`bb`,`h`] strip_assume_tac
    ricf_block_step_certificate >>
  Cases_on `ricf_block_step ctx (c,bb) h` >> gvs[] >>
  first_x_assum (qspecl_then [`q`,`r`] strip_assume_tac) >>
  qexists_tac `es ++ es'` >> simp[] >>
  metis_tac[ricf_block_trace_append]
QED

Theorem ricf_pass_block_certificate:
  !ctx bb. ?es.
    ricf_block_trace bb es (SND (ricf_pass_block ctx bb)) /\
    EVERY (\e. e.rfe_ctx = ctx) es
Proof
  simp[ricf_pass_block_eq_foldl, ricf_block_fold_certificate]
QED

Theorem ricf_function_step_certificate:
  !ctx fn. ricf_round_certificate ctx fn (SND (ricf_function_step ctx fn))
Proof
  rpt gen_tac >>
  simp[ricf_function_step_def, ricf_round_certificate_def] >>
  pairarg_tac >> simp[] >>
  qexists_tac `new_blocks` >> simp[] >>
  `new_blocks = MAP (\bb. SND (ricf_pass_block ctx bb)) fn.fn_blocks` by
    (mp_tac (Q.ISPECL [`ricf_pass_block ctx`, `fn.fn_blocks`, `F`, `[]:basic_block list`]
       invokeCopyFwdCommonDefsTheory.FOLDL_block_pass_SND) >> simp[]) >>
  simp[LIST_REL_MAP2] >> irule LIST_REL_refl >>
  simp[ricf_pass_block_certificate]
QED

Theorem ricf_transform_function_certificate:
  !fn_meta ctx_fns rma fn.
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\ ricf_src_alloca fn ==>
    ricf_function_plan (icf_build_ctx fn_meta ctx_fns rma fn) fn
      (ricf_transform_function fn_meta ctx_fns rma fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[ricf_transform_function_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE G step_fn (T,ctx0,fn)` >>
  Cases_on `OWHILE G step_fn (T,ctx0,fn)`
  >- simp[ricf_function_plan_identity] >>
  PairCases_on `x` >> simp[] >>
  `ricf_function_trace ctx0 fn x2` by
    (mp_tac (WhileTheory.OWHILE_INV_IND
       |> INST_TYPE [alpha |-> ``:bool # icf_ctx # ir_function``]
       |> Q.INST [`P` |-> `\(c,ctx,cur). ctx = (ctx0 with icf_dfg := dfg_build_function cur) /\ ricf_function_trace ctx0 fn cur`]
       |> Q.SPECL [`G`,`step_fn`,`(T,ctx0,fn)`]) >>
     impl_tac
     >- (conj_tac
         >- simp[Abbr `ctx0`, invokeCopyFwdCommonDefsTheory.icf_build_ctx_def,
                 ricf_function_trace_nil] >>
         rpt gen_tac >> PairCases_on `x` >>
         simp[Abbr `G`, Abbr `step_fn`] >> strip_tac >>
         gvs[] >>
         Cases_on `ricf_function_step (ctx0 with icf_dfg := dfg_build_function x2') x2'` >>
         rename1 `ricf_function_step _ _ = (changed,new_fn)` >>
         Cases_on `changed` >> gvs[] >>
         irule ricf_function_trace_trans >> goal_assum drule >>
         irule ricf_function_trace_cons >>
         qexists_tac `new_fn` >> simp[ricf_function_trace_nil] >>
         qspecl_then [`ctx0 with icf_dfg := dfg_build_function x2'`, `x2'`]
           mp_tac ricf_function_step_certificate >> simp[]) >>
     disch_then (qspec_then `(x0,x1,x2)` mp_tac) >> simp[]) >>
  simp[ricf_function_plan_def] >> qexists_tac `x2` >> simp[]
QED

Theorem ricf_sites_fold_readonly[local]:
  !uses acc sites.
    (!xs ri p. acc = SOME xs /\ MEM (ri,p) xs ==>
       ri.inst_opcode = INVOKE /\ icf_is_readonly_op rma ri p) /\
    FOLDL (\acc (v,inst,pos).
      case acc of NONE => NONE | SOME xs =>
        if icf_is_assign_output_use inst pos then SOME xs
        else if inst.inst_opcode = MCOPY /\ pos = 0 then
          if inst.inst_id = copy_id then SOME xs else NONE
        else if inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos
          then SOME ((inst,pos)::xs) else NONE) acc uses = SOME sites ==>
    !ri p. MEM (ri,p) sites ==>
       ri.inst_opcode = INVOKE /\ icf_is_readonly_op rma ri p
Proof
  Induct >> pure_rewrite_tac[FOLDL]
  >- metis_tac[] >>
  rpt gen_tac >> PairCases_on `h` >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f next uses = SOME sites` >>
  qpat_x_assum `!acc sites. _` (qspecl_then [`next`,`sites`] mp_tac) >>
  impl_tac
  >- (conj_tac >- (Cases_on `acc` >>
         gvs[Abbr `next`, Abbr `f`, AllCaseEqs()] >>
         rpt strip_tac >> gvs[] >> metis_tac[]) >>
       gvs[Abbr `f`]) >> simp[]
QED

Theorem ricf_event_sites_readonly:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites ==>
  ri.inst_opcode = INVOKE /\ icf_is_readonly_op e.rfe_ctx.icf_rma ri p
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  irule (INST_TYPE [alpha |-> ``:string``] ricf_sites_fold_readonly) >>
  goal_assum (drule_at Any) >>
  qexists_tac `SOME []` >> simp[] >>
  qexists_tac `(EL e.rfe_index bb.bb_instructions).inst_id` >>
  qexists_tac `icf_alias_use_positions e.rfe_ctx.icf_dfg
    (icf_collect_aliases e.rfe_ctx.icf_dfg
       (icf_assign_root e.rfe_ctx.icf_dfg {} dst))` >> simp[]
QED

Theorem ricf_event_opcode:
  i < LENGTH bb.bb_instructions ==>
  (EL i (ricf_event_apply e bb).bb_instructions).inst_opcode =
    if i = e.rfe_index then NOP
    else (EL i bb.bb_instructions).inst_opcode
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  rpt strip_tac >> rw[mk_nop_inst_def]
QED

Theorem ricf_event_unchanged:
  i < LENGTH bb.bb_instructions /\ i <> e.rfe_index /\
  ~MEM (EL i bb.bb_instructions).inst_id
    (MAP (\(ri,p). ri.inst_id) e.rfe_sites) ==>
  EL i (ricf_event_apply e bb).bb_instructions = EL i bb.bb_instructions
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  rpt strip_tac >>
  `FILTER (\(ri,p). ri.inst_id = (EL i bb.bb_instructions).inst_id)
     e.rfe_sites = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
         pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  simp[]
QED

Theorem ricf_event_surviving_mcopy:
  ricf_event_ok e bb /\ i < LENGTH bb.bb_instructions /\
  (EL i (ricf_event_apply e bb).bb_instructions).inst_opcode = MCOPY /\
  (!ri p. MEM (ri,p) e.rfe_sites /\
     ri.inst_id = (EL i bb.bb_instructions).inst_id ==>
     ri.inst_opcode = (EL i bb.bb_instructions).inst_opcode) ==>
  EL i (ricf_event_apply e bb).bb_instructions = EL i bb.bb_instructions
Proof
  rpt strip_tac >>
  drule ricf_event_opcode >> disch_then (qspec_then `e` mp_tac) >>
  strip_tac >>
  Cases_on `i = e.rfe_index` >> gvs[] >>
  irule ricf_event_unchanged >> simp[] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ricf_event_noninvoke:
  ricf_event_ok e bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> MCOPY /\
  (EL i bb.bb_instructions).inst_opcode <> INVOKE /\
  (!ri p. MEM (ri,p) e.rfe_sites /\
     ri.inst_id = (EL i bb.bb_instructions).inst_id ==>
     ri.inst_opcode = (EL i bb.bb_instructions).inst_opcode) ==>
  EL i (ricf_event_apply e bb).bb_instructions = EL i bb.bb_instructions
Proof
  rpt strip_tac >>
  `i <> e.rfe_index` by
    (drule ricf_event_copy_shape >> simp[ricf_event_copy_def] >> metis_tac[]) >>
  irule ricf_event_unchanged >> simp[] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ricf_event_operand_length:
  i < LENGTH bb.bb_instructions /\ i <> e.rfe_index ==>
  LENGTH (EL i (ricf_event_apply e bb).bb_instructions).inst_operands =
  LENGTH (EL i bb.bb_instructions).inst_operands
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  rpt strip_tac >> rw[]
QED

(* Recorded sites come from the fixed DFG, not from a recomputation on the
   current block.  This is the missing link between event and round histories. *)
Theorem ricf_sites_fold_origin[local]:
  !uses acc sites.
    FOLDL (\acc (v,inst,pos).
      case acc of NONE => NONE | SOME xs =>
        if icf_is_assign_output_use inst pos then SOME xs
        else if inst.inst_opcode = MCOPY /\ pos = 0 then
          if inst.inst_id = copy_id then SOME xs else NONE
        else if inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos
          then SOME ((inst,pos)::xs) else NONE) acc uses = SOME sites ==>
    !ri p. MEM (ri,p) sites ==>
      (?xs. acc = SOME xs /\ MEM (ri,p) xs) \/
      ?v. MEM (v,ri,p) uses
Proof
  Induct >> pure_rewrite_tac[FOLDL]
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f next uses = SOME sites` >>
  qpat_x_assum `!acc sites. _` (qspecl_then [`next`,`sites`] mp_tac) >>
  simp[Abbr `f`] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (Cases_on `acc` >>
      gvs[Abbr `next`, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[MEM]
QED

Theorem ricf_event_sites_origin:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites ==>
  ?v. MEM ri (dfg_get_uses e.rfe_ctx.icf_dfg v)
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `?v. MEM (v,ri,p)
    (icf_alias_use_positions e.rfe_ctx.icf_dfg
      (icf_collect_aliases e.rfe_ctx.icf_dfg
        (icf_assign_root e.rfe_ctx.icf_dfg {} dst)))` by
    (drule (INST_TYPE [alpha |-> ``:string``] ricf_sites_fold_origin) >>
     disch_then drule >> simp[]) >>
  gvs[invokeCopyFwdCommonDefsTheory.icf_alias_use_positions_def,
      invokeCopyFwdCommonDefsTheory.icf_use_positions_mem,
      MEM_FLAT, MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Definition ricf_inst_edit_def:
  ricf_inst_edit old cur <=>
    cur.inst_id = old.inst_id /\
    (cur.inst_opcode = old.inst_opcode \/
      old.inst_opcode = MCOPY /\ cur.inst_opcode = NOP) /\
    (old.inst_opcode <> MCOPY /\ old.inst_opcode <> INVOKE ==> cur = old) /\
    (cur.inst_opcode = MCOPY ==> cur = old)
End

Definition ricf_block_edit_def:
  ricf_block_edit old cur <=>
    old.bb_label = cur.bb_label /\
    LIST_REL ricf_inst_edit old.bb_instructions cur.bb_instructions
End

Theorem ricf_inst_edit_refl[simp]:
  ricf_inst_edit inst inst
Proof
  simp[ricf_inst_edit_def]
QED

Theorem ricf_inst_edit_trans:
  ricf_inst_edit a b /\ ricf_inst_edit b c ==> ricf_inst_edit a c
Proof
  rw[ricf_inst_edit_def] >> metis_tac[]
QED

Theorem ricf_block_edit_refl[simp]:
  ricf_block_edit bb bb
Proof
  simp[ricf_block_edit_def, LIST_REL_refl]
QED

Theorem ricf_block_edit_trans:
  ricf_block_edit a b /\ ricf_block_edit b c ==> ricf_block_edit a c
Proof
  simp[ricf_block_edit_def, LIST_REL_EL_EQN] >>
  metis_tac[ricf_inst_edit_trans]
QED

Theorem ricf_block_edit_EL:
  ricf_block_edit old cur ==> 
  LENGTH old.bb_instructions = LENGTH cur.bb_instructions /\
  !i. i < LENGTH old.bb_instructions ==>
    ricf_inst_edit (EL i old.bb_instructions) (EL i cur.bb_instructions)
Proof
  simp[ricf_block_edit_def, LIST_REL_EL_EQN]
QED

Theorem ricf_event_block_edit:
  ricf_event_ok e bb /\
  (!ri p i. MEM (ri,p) e.rfe_sites /\ i < LENGTH bb.bb_instructions /\
     ri.inst_id = (EL i bb.bb_instructions).inst_id ==>
     (EL i bb.bb_instructions).inst_opcode = INVOKE) ==>
  ricf_block_edit bb (ricf_event_apply e bb)
Proof
  strip_tac >> simp[ricf_block_edit_def, ricf_event_apply_def,
    ricf_apply_forward_def, LIST_REL_EL_EQN, EL_MAPi] >>
  rpt strip_tac >> simp[ricf_inst_edit_def] >>
  Cases_on `n = e.rfe_index`
  >- (drule ricf_event_copy_shape >>
      simp[ricf_event_copy_def] >> strip_tac >> simp[mk_nop_inst_def]) >>
  simp[] >>
  IF_CASES_TAC >> simp[] >>
  `?ri p. MEM (ri,p) e.rfe_sites /\
    ri.inst_id = (EL n bb.bb_instructions).inst_id` by
    (gvs[NULL_EQ, FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[]) >>
  `(EL n bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
  simp[]
QED

Theorem ricf_event_sites_function:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites /\
  e.rfe_ctx.icf_dfg = dfg_build_function fn ==>
  MEM ri (fn_insts fn) /\ ri.inst_opcode = INVOKE
Proof
  strip_tac >> drule_all ricf_event_sites_origin >> strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  gvs[] >> metis_tac[dfg_build_function_uses_sound]
QED

(* Enough of the round-start function is retained to identify each recorded
   INVOKE by ID.  This does not claim equality of its (edited) operands. *)
Theorem ricf_event_current_sites:
  ricf_event_ok e cur /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  ricf_block_edit old cur /\ MEM old fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !ri p i. MEM (ri,p) e.rfe_sites /\ i < LENGTH cur.bb_instructions /\
    ri.inst_id = (EL i cur.bb_instructions).inst_id ==>
    (EL i cur.bb_instructions).inst_opcode = INVOKE
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ricf_event_sites_function >> strip_tac >>
  drule ricf_block_edit_EL >> strip_tac >>
  `ricf_inst_edit (EL i old.bb_instructions) (EL i cur.bb_instructions)`
    by metis_tac[] >>
  `MEM (EL i old.bb_instructions) (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     irule venomInstTheory.fmp_fn_insts_blocks_intro >>
     qexists_tac `old` >> simp[EL_MEM]) >>
  `ri = EL i old.bb_instructions` by
    (gvs[ricf_inst_edit_def] >>
     gvs[MEM_EL] >>
     gvs[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> metis_tac[]) >>
  qpat_x_assum `!i. _ ==> ricf_inst_edit _ _` kall_tac >>
  gvs[ricf_inst_edit_def]
QED

Theorem ricf_block_trace_edit:
  !bb es last. ricf_block_trace bb es last ==>
  !fn old ctx.
    EVERY (\e. e.rfe_ctx = ctx) es /\
    ctx.icf_dfg = dfg_build_function fn /\
    ricf_block_edit old bb /\ MEM old fn.fn_blocks /\
    ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
    ricf_block_edit old last
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule ricf_block_edit_trans >> goal_assum drule >>
  irule ricf_event_block_edit >> simp[] >>
  metis_tac[ricf_event_current_sites]
QED

Definition ricf_function_edit_def:
  ricf_function_edit old cur <=>
    cur = old with fn_blocks := cur.fn_blocks /\
    LIST_REL ricf_block_edit old.fn_blocks cur.fn_blocks
End

Theorem ricf_function_edit_refl[simp]:
  ricf_function_edit fn fn
Proof
  simp[ricf_function_edit_def, LIST_REL_refl]
QED

Theorem ricf_function_edit_trans:
  ricf_function_edit a b /\ ricf_function_edit b c ==>
  ricf_function_edit a c
Proof
  simp[ricf_function_edit_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `c = _` (fn th => once_rewrite_tac[th]) >>
      qpat_x_assum `b = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[ricf_block_edit_trans]
QED

Theorem ricf_round_certificate_edit:
  ricf_round_certificate ctx fn cur /\
  ctx.icf_dfg = dfg_build_function fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_function_edit fn cur
Proof
  simp[ricf_round_certificate_def, ricf_function_edit_def] >>
  strip_tac >> gvs[] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule ricf_block_trace_edit >>
  qexistsl_tac [`EL n fn.fn_blocks`,`ctx`,`es`] >> simp[EL_MEM] >>
  qexists_tac `fn` >> simp[EL_MEM]
QED

Theorem ricf_block_edits_insts:
  !bbs cs. LIST_REL ricf_block_edit bbs cs ==>
  LIST_REL ricf_inst_edit (fn_insts_blocks bbs) (fn_insts_blocks cs)
Proof
  Induct >> Cases_on `cs` >>
  simp[venomInstTheory.fn_insts_blocks_def, ricf_block_edit_def] >>
  rpt strip_tac >> irule EVERY2_APPEND_suff >> simp[]
QED

Theorem ricf_function_edit_insts:
  ricf_function_edit fn cur ==>
  LIST_REL ricf_inst_edit (fn_insts fn) (fn_insts cur)
Proof
  simp[ricf_function_edit_def, venomInstTheory.fn_insts_def] >>
  metis_tac[ricf_block_edits_insts]
QED

Theorem ricf_function_edit_ids:
  ricf_function_edit fn cur ==>
  MAP (\inst. inst.inst_id) (fn_insts cur) =
  MAP (\inst. inst.inst_id) (fn_insts fn)
Proof
  strip_tac >> drule ricf_function_edit_insts >>
  simp[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  metis_tac[ricf_inst_edit_def]
QED

Theorem ricf_function_trace_edit:
  !base fn cur. ricf_function_trace base fn cur ==>
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_function_edit fn cur
Proof
  ho_match_mp_tac ricf_function_trace_ind >> simp[] >> rpt strip_tac >>
  rename1 `ricf_round_certificate (base0 with icf_dfg := _) fn mid` >>
  `ricf_function_edit fn mid` by
    (irule ricf_round_certificate_edit >> simp[] >>
     qexists_tac `base0 with icf_dfg := dfg_build_function fn` >> simp[]) >>
  irule ricf_function_edit_trans >> goal_assum drule >>
  first_x_assum irule >> metis_tac[ricf_function_edit_ids]
QED

(* Record sources at the pre-event block.  Operand histories are folds over
   this chronological log, so a later rewrite wins at a repeated position. *)
Definition ricf_event_log_def:
  ricf_event_log bb [] = [] /\
  ricf_event_log bb (e::es) =
    (e, ricf_event_source e bb) ::
      ricf_event_log (ricf_event_apply e bb) es
End

Definition ricf_edit_operand_def:
  ricf_edit_operand i iid j op (e,src) =
    if i = e.rfe_index then NONE
    else case op of NONE => NONE | SOME v =>
      if MEM (iid,j) (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites)
      then SOME src else SOME v
End

Definition ricf_operand_at_def:
  ricf_operand_at (inst:instruction) j =
    if j < LENGTH inst.inst_operands then SOME (EL j inst.inst_operands)
    else NONE
End

Theorem ricf_event_operand_at:
  i < LENGTH bb.bb_instructions ==>
  ricf_operand_at (EL i (ricf_event_apply e bb).bb_instructions) j =
  ricf_edit_operand i (EL i bb.bb_instructions).inst_id j
    (ricf_operand_at (EL i bb.bb_instructions) j)
    (e,ricf_event_source e bb)
Proof
  strip_tac >> Cases_on `i = e.rfe_index`
  >- simp[ricf_operand_at_def, ricf_edit_operand_def, ricf_event_apply_def,
          ricf_apply_forward_def, EL_MAPi, mk_nop_inst_def] >>
  drule_all ricf_event_operand_length >> strip_tac >>
  simp[ricf_edit_operand_def, ricf_operand_at_def] >>
  Cases_on `j < LENGTH (EL i bb.bb_instructions).inst_operands` >> simp[] >>
  drule_all ricf_event_operand >> simp[] >> metis_tac[]
QED

Theorem ricf_block_trace_operand_history:
  !bb es last. ricf_block_trace bb es last ==>
  !i j. i < LENGTH bb.bb_instructions ==>
    ricf_operand_at (EL i last.bb_instructions) j =
    FOLDL (ricf_edit_operand i (EL i bb.bb_instructions).inst_id j)
      (ricf_operand_at (EL i bb.bb_instructions) j) (ricf_event_log bb es)
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[ricf_event_log_def] >>
  rpt strip_tac >> pure_rewrite_tac[FOLDL] >>
  drule ricf_event_prefix_and_copy >> strip_tac >>
  `i < LENGTH (ricf_event_apply e bb).bb_instructions` by simp[] >>
  first_x_assum (qspecl_then [`i`,`j`] mp_tac) >> simp[] >>
  `((EL i (ricf_event_apply e bb).bb_instructions).inst_id =
     (EL i bb.bb_instructions).inst_id)` by
    (mp_tac ricf_event_ids >>
     simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
  simp[ricf_event_operand_at]
QED

Theorem ricf_function_edit_assigns:
  ricf_function_edit fn cur ==>
  !inst. inst.inst_opcode = ASSIGN ==>
    (MEM inst (fn_insts fn) <=> MEM inst (fn_insts cur))
Proof
  strip_tac >> drule ricf_function_edit_insts >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> rpt strip_tac >>
  simp[MEM_EL] >> eq_tac >> strip_tac >>
  qexists_tac `n` >> simp[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[ricf_inst_edit_def] >> gvs[]
QED

Theorem ricf_function_edit_assign_uses:
  ricf_function_edit fn cur ==>
  !v out.
    ((?inst. MEM inst (dfg_get_uses (dfg_build_function fn) v) /\
       inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]) <=>
     (?inst. MEM inst (dfg_get_uses (dfg_build_function cur) v) /\
       inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]))
Proof
  strip_tac >> drule ricf_function_edit_assigns >> strip_tac >>
  metis_tac[dfg_build_function_uses_sound, dfg_build_function_uses_complete]
QED

Theorem ricf_event_outputs:
  i < LENGTH bb.bb_instructions ==>
  (EL i (ricf_event_apply e bb).bb_instructions).inst_outputs =
    if i = e.rfe_index then [] else (EL i bb.bb_instructions).inst_outputs
Proof
  simp[ricf_event_apply_def, ricf_apply_forward_def, EL_MAPi] >>
  rpt strip_tac >> rw[mk_nop_inst_def]
QED

Theorem ricf_block_trace_outputs:
  !bb es last. ricf_block_trace bb es last ==>
  !i. i < LENGTH bb.bb_instructions ==>
    (EL i last.bb_instructions).inst_outputs = [] \/
    (EL i last.bb_instructions).inst_outputs =
      (EL i bb.bb_instructions).inst_outputs
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[] >> rpt strip_tac >>
  drule ricf_event_prefix_and_copy >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  drule ricf_event_outputs >> disch_then (qspec_then `e` mp_tac) >>
  metis_tac[]
QED

Definition ricf_outputs_edit_def:
  ricf_outputs_edit (a:instruction) b <=>
    b.inst_outputs = [] \/ b.inst_outputs = a.inst_outputs
End

Theorem ricf_outputs_edit_trans:
  ricf_outputs_edit a b /\ ricf_outputs_edit b c ==> ricf_outputs_edit a c
Proof
  simp[ricf_outputs_edit_def] >> metis_tac[]
QED

Theorem ricf_block_trace_outputs_rel:
  ricf_block_trace bb es last ==>
  LIST_REL ricf_outputs_edit bb.bb_instructions last.bb_instructions
Proof
  strip_tac >> drule ricf_block_trace_ids >> strip_tac >>
  `LENGTH last.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  simp[LIST_REL_EL_EQN, ricf_outputs_edit_def] >>
  metis_tac[ricf_block_trace_outputs]
QED

Theorem ricf_outputs_blocks:
  !bbs cs.
  LIST_REL (\b c. LIST_REL ricf_outputs_edit b.bb_instructions c.bb_instructions)
    bbs cs ==>
  LIST_REL ricf_outputs_edit (fn_insts_blocks bbs) (fn_insts_blocks cs)
Proof
  Induct >> Cases_on `cs` >>
  simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> irule EVERY2_APPEND_suff >> simp[]
QED

Theorem ricf_round_certificate_outputs:
  ricf_round_certificate ctx fn cur ==>
  LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts cur)
Proof
  simp[ricf_round_certificate_def, venomInstTheory.fn_insts_def] >>
  rpt strip_tac >> gvs[] >> irule ricf_outputs_blocks >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_block_trace_outputs_rel >> simp[LIST_REL_EL_EQN]
QED

Theorem ricf_function_trace_outputs:
  !base fn cur. ricf_function_trace base fn cur ==>
  LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts cur)
Proof
  ho_match_mp_tac ricf_function_trace_ind >>
  simp[LIST_REL_refl, ricf_outputs_edit_def] >> rpt strip_tac >>
  drule ricf_round_certificate_outputs >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[ricf_outputs_edit_trans]
QED

Theorem ricf_function_output_origin:
  ricf_function_edit fn cur /\
  LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts cur) /\
  MEM inst (fn_insts cur) /\ MEM v inst.inst_outputs ==>
  ?old. MEM old (fn_insts fn) /\ MEM v old.inst_outputs /\ ricf_inst_edit old inst
Proof
  strip_tac >> drule ricf_function_edit_insts >> strip_tac >>
  gvs[MEM_EL, LIST_REL_EL_EQN] >>
  qexists_tac `EL n (fn_insts fn)` >>
  `n < LENGTH (fn_insts fn)` by simp[] >>
  conj_tac >- metis_tac[EL_MEM] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >>
  simp[ricf_outputs_edit_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A defining ASSIGN survives, and output deletion cannot expose a different
   ASSIGN under SSA.  No equality of complete DFG definition maps is claimed. *)
Theorem ricf_function_edit_assign_defs:
  ricf_function_edit fn cur /\
  LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts cur) /\ ssa_form fn ==>
  !inst v. inst.inst_opcode = ASSIGN ==>
    (dfg_get_def (dfg_build_function fn) v = SOME inst <=>
     dfg_get_def (dfg_build_function cur) v = SOME inst)
Proof
  strip_tac >> drule ricf_function_edit_assigns >> strip_tac >>
  rpt gen_tac >> strip_tac >> eq_tac >> strip_tac
  >- (drule dfg_build_function_correct >> strip_tac >>
      `MEM inst (fn_insts cur)` by metis_tac[] >>
      drule_all dfg_build_function_defs_complete >> strip_tac >>
      drule dfg_build_function_correct >> strip_tac >>
      drule_all ricf_function_output_origin >> strip_tac >>
      `old = inst` by (irule ssa_unique_output >> metis_tac[]) >>
      gvs[ricf_inst_edit_def]) >>
  drule dfg_build_function_correct >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst' = inst` by (irule ssa_unique_output >> metis_tac[]) >>
  gvs[]
QED

Theorem ricf_function_trace_assign_defs:
  ricf_function_trace ctx0 fn cur /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !inst v. inst.inst_opcode = ASSIGN ==>
    (dfg_get_def (dfg_build_function fn) v = SOME inst <=>
     dfg_get_def (dfg_build_function cur) v = SOME inst)
Proof
  rpt strip_tac >> irule ricf_function_edit_assign_defs >> simp[] >>
  metis_tac[ricf_function_trace_edit, ricf_function_trace_outputs]
QED

(* ALLOCA definitions are unchanged even when other definitions lose outputs. *)
Theorem ricf_function_edit_alloca_defs:
  ricf_function_edit fn cur /\
  LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts cur) /\ ssa_form fn ==>
  !inst v. inst.inst_opcode = ALLOCA ==>
    (dfg_get_def (dfg_build_function fn) v = SOME inst <=>
     dfg_get_def (dfg_build_function cur) v = SOME inst)
Proof
  strip_tac >>
  `!inst. inst.inst_opcode = ALLOCA ==>
     (MEM inst (fn_insts fn) <=> MEM inst (fn_insts cur))` by
    (drule ricf_function_edit_insts >>
     simp[LIST_REL_EL_EQN] >> strip_tac >> rpt strip_tac >>
     simp[MEM_EL] >> eq_tac >> strip_tac >>
     qexists_tac `n` >> simp[] >>
     first_x_assum (qspec_then `n` mp_tac) >>
     simp[ricf_inst_edit_def] >> gvs[]) >>
  rpt gen_tac >> strip_tac >> eq_tac >> strip_tac
  >- (drule dfg_build_function_correct >> strip_tac >>
      `MEM inst (fn_insts cur)` by metis_tac[] >>
      drule_all dfg_build_function_defs_complete >> strip_tac >>
      drule dfg_build_function_correct >> strip_tac >>
      drule_all ricf_function_output_origin >> strip_tac >>
      `old = inst` by (irule ssa_unique_output >> metis_tac[]) >>
      gvs[ricf_inst_edit_def]) >>
  drule dfg_build_function_correct >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst' = inst` by (irule ssa_unique_output >> metis_tac[]) >>
  gvs[]
QED

Theorem ricf_function_trace_alloca_defs:
  ricf_function_trace ctx0 fn cur /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !inst v. inst.inst_opcode = ALLOCA ==>
    (dfg_get_def (dfg_build_function fn) v = SOME inst <=>
     dfg_get_def (dfg_build_function cur) v = SOME inst)
Proof
  rpt strip_tac >> irule ricf_function_edit_alloca_defs >> simp[] >>
  metis_tac[ricf_function_trace_edit, ricf_function_trace_outputs]
QED

Theorem ricf_function_trace_assign_predecessor:
  ricf_function_trace ctx0 fn cur /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !v.
    (case dfg_get_def (dfg_build_function fn) v of
       NONE => NONE
     | SOME inst => if inst.inst_opcode = ASSIGN then
         (case inst.inst_operands of [Var src] => SOME src | _ => NONE)
         else NONE) =
    (case dfg_get_def (dfg_build_function cur) v of
       NONE => NONE
     | SOME inst => if inst.inst_opcode = ASSIGN then
         (case inst.inst_operands of [Var src] => SOME src | _ => NONE)
         else NONE)
Proof
  strip_tac >> drule ricf_function_trace_assign_defs >> simp[] >> strip_tac >>
  gen_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn) v` >>
  Cases_on `dfg_get_def (dfg_build_function cur) v` >> simp[] >>
  rpt IF_CASES_TAC >> gvs[] >>
  rename1 `ai.inst_opcode = ASSIGN` >>
  qpat_x_assum `!inst v. _` (qspecl_then [`ai`,`v`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ricf_function_trace_assign_uses:
  ricf_function_trace ctx0 fn cur /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !v out.
    ((?inst. MEM inst (dfg_get_uses (dfg_build_function fn) v) /\
       inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]) <=>
     (?inst. MEM inst (dfg_get_uses (dfg_build_function cur) v) /\
       inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]))
Proof
  metis_tac[ricf_function_trace_edit, ricf_function_edit_assign_uses]
QED

(* Rebuilding the DFG observes the same ASSIGN graph, not the same use lists. *)
Theorem ricf_function_trace_assign_root:
  ricf_function_trace ctx0 fn cur /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !visited v. icf_assign_root (dfg_build_function fn) visited v =
              icf_assign_root (dfg_build_function cur) visited v
Proof
  strip_tac >> rpt gen_tac >> irule icf_assign_root_cong >>
  simp[icf_assign_predecessor_def] >>
  metis_tac[ricf_function_trace_assign_predecessor]
QED

Theorem ricf_function_trace_assign_root_op:
  ricf_function_trace ctx0 fn cur /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !op. icf_assign_root_op (dfg_build_function fn) op =
       icf_assign_root_op (dfg_build_function cur) op
Proof
  strip_tac >> irule icf_assign_root_op_cong >>
  simp[icf_assign_predecessor_def] >>
  metis_tac[ricf_function_trace_assign_predecessor]
QED

Theorem ricf_function_trace_collect_aliases:
  ricf_function_trace ctx0 fn cur /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !root. icf_collect_aliases (dfg_build_function fn) root =
         icf_collect_aliases (dfg_build_function cur) root
Proof
  strip_tac >> irule icf_collect_aliases_cong >>
  metis_tac[ricf_function_trace_assign_uses]
QED

Theorem ricf_block_trace_label:
  !bb es cur. ricf_block_trace bb es cur ==> cur.bb_label = bb.bb_label
Proof
  ho_match_mp_tac ricf_block_trace_ind >>
  simp[ricf_event_apply_def] >> rpt strip_tac >> gvs[]
QED

Theorem ricf_round_certificate_structure:
  ricf_round_certificate ctx fn cur ==>
  cur.fn_name = fn.fn_name /\
  MAP (\bb. bb.bb_label) cur.fn_blocks = MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  simp[ricf_round_certificate_def] >> rpt strip_tac >> gvs[] >>
  gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  metis_tac[ricf_block_trace_label]
QED

Theorem ricf_function_trace_structure:
  !base fn cur. ricf_function_trace base fn cur ==>
  cur.fn_name = fn.fn_name /\
  MAP (\bb. bb.bb_label) cur.fn_blocks = MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  ho_match_mp_tac ricf_function_trace_ind >> simp[] >>
  metis_tac[ricf_round_certificate_structure]
QED

Theorem ricf_function_plan_structure:
  ricf_function_plan ctx0 fn cur ==>
  cur.fn_name = fn.fn_name /\
  MAP (\bb. bb.bb_label) cur.fn_blocks = MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  simp[ricf_function_plan_def] >> rpt strip_tac >> gvs[] >>
  drule ricf_function_trace_structure >>
  simp[clear_nops_function_def, MAP_MAP_o, combinTheory.o_DEF,
       clear_nops_block_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, clear_nops_block_def]
QED

(* These structural facts live below Sim; the witness theory reuses them. *)
Theorem ricf_transform_function_fn_name:
  !fn_meta ctx_fns rma fn.
    (ricf_transform_function fn_meta ctx_fns rma fn).fn_name = fn.fn_name
Proof
  rpt gen_tac >> simp[ricf_transform_function_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE G step_fn (T, ctx0, fn)` >>
  Cases_on `OWHILE G step_fn (T, ctx0, fn)` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  mp_tac (WhileTheory.OWHILE_INV_IND
            |> INST_TYPE [alpha |-> ``:bool # icf_ctx # ir_function``]
            |> Q.INST [`P` |-> `\(c, ctx, cur_fn). cur_fn.fn_name = fn.fn_name`]
            |> Q.SPECL [`G`, `step_fn`, `(T, ctx0, fn)`]) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> PairCases_on `x` >>
      fs[Abbr `step_fn`, ricf_function_step_def, pairTheory.UNCURRY] >>
      rw[] >> gvs[] >> rw[]) >>
  disch_then (qspec_then `(x0, x1, x2)` mp_tac) >>
  simp[clear_nops_function_def] >> rw[]
QED

Theorem ricf_transform_ctx_entry[simp]:
  !ctx fn_meta rma.
    (ricf_transform_ctx fn_meta rma ctx).ctx_entry = ctx.ctx_entry
Proof
  simp[ricf_transform_ctx_def]
QED

Theorem ricf_transform_function_labels:
  ricf_full_alloca_copies fn /\
  ricf_no_derived_mutable_sibling fn /\ ricf_src_alloca fn ==>
  MAP (\bb. bb.bb_label)
    (ricf_transform_function fn_meta ctx_fns rma fn).fn_blocks =
  MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  strip_tac >> drule_all ricf_transform_function_certificate >>
  metis_tac[ricf_function_plan_structure]
QED

(* The positional edit interface ends BEFORE NOP clearing.  Final block
   labels survive clearing, whereas final instruction indices need not. *)
Theorem ricf_transform_function_edit_interface:
  ricf_full_alloca_copies fn /\
  ricf_no_derived_mutable_sibling fn /\ ricf_src_alloca fn /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ?mid.
    ricf_function_trace (icf_build_ctx fn_meta ctx_fns rma fn) fn mid /\
    ricf_function_edit fn mid /\
    LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts mid) /\
    (!visited v. icf_assign_root (dfg_build_function fn) visited v =
                 icf_assign_root (dfg_build_function mid) visited v) /\
    (!op. icf_assign_root_op (dfg_build_function fn) op =
          icf_assign_root_op (dfg_build_function mid) op) /\
    (!root. icf_collect_aliases (dfg_build_function fn) root =
            icf_collect_aliases (dfg_build_function mid) root) /\
    ricf_transform_function fn_meta ctx_fns rma fn =
      if mid.fn_blocks <> fn.fn_blocks then clear_nops_function mid else mid
Proof
  strip_tac >> drule_all ricf_transform_function_certificate >>
  disch_then (qspecl_then [`fn_meta`,`ctx_fns`,`rma`] mp_tac) >>
  simp[ricf_function_plan_def] >> strip_tac >> qexists_tac `mid` >>
  metis_tac[ricf_function_trace_edit, ricf_function_trace_outputs,
            ricf_function_trace_assign_root, ricf_function_trace_assign_root_op,
            ricf_function_trace_collect_aliases]
QED
