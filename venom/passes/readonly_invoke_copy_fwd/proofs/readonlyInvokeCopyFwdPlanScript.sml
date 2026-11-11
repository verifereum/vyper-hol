(* Forwarding certificates retain the analysis used at each successful step.
   In particular, a block trace does NOT silently rebuild its DFG.  The
   function certificate records round boundaries, where only the DFG changes.
   Safety of these traces is a separate obligation, not a constructor rule. *)
Theory readonlyInvokeCopyFwdPlan
Ancestors
  readonlyInvokeCopyFwdDefs readonlyMemoryArgsProps indexedLists
  list rich_list pair option passSharedDefs

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
