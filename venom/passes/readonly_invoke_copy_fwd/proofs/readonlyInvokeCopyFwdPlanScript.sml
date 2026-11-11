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
