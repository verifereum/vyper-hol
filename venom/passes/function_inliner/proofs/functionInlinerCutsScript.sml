(* Constructibility consumers for original-indexed administrative cuts.
   Track source-present locals, not all code variables: setup_callee clears
   logical locals but arbitrary physical runtime maps need not be fresh. *)
Theory functionInlinerCuts
Ancestors
  functionInlinerActivation functionInlinerCallBoundary
  functionInlinerPhiTransport functionInlinerOrigin functionInlinerContract
  functionInlinerFrame cfgTransform unitShapeDefs venomExecSemantics
  venomExecProofs venomState venomInst list pred_set

Definition inline_tracked_snapshot_def:
  inline_tracked_snapshot fn a route snap frame <=>
    inline_snapshot_data a route snap frame /\
    snap.ils_defined SUBSET set (cfgTransform$fn_all_vars fn) /\
    (!x. MEM x (cfgTransform$fn_all_vars fn) /\
         IS_SOME (lookup_var x snap.ils_state) ==> x IN snap.ils_defined) /\
    snap.ils_opaque = retpc_var fn /\
    snap.ils_state.vs_labels = FEMPTY /\ frame.ipf_anchor.vs_labels = FEMPTY
End

Theorem inline_call_operand_namespace:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM call (fn_insts fn) /\ call.inst_opcode = INVOKE /\
  decode_invoke call = SOME (nm,ops) ==>
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops
Proof
  strip_tac >>
  `opaque_use_ok fn` by
    (fs[inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `call.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  simp[EVERY_MEM] >> rpt strip_tac >> gvs[]
  >- (simp[cfgTransformTheory.fn_all_vars_def, fn_insts_def,
           MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      `?bb. MEM bb fn.fn_blocks /\ MEM call bb.bb_instructions` by
        metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM] >>
      qexistsl [`bb`, `call`] >> simp[] >> disj2_tac >>
      qexists `Var v` >> simp[]) >>
  `retpc_use_ok call v` by
    (irule opaque_use_ok_retpc_use >> simp[] >> qexists `fn` >> simp[]) >>
  gvs[retpc_use_ok_def]
QED

Theorem inline_tracked_call_eval_two_clones:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM call (fn_insts fn) /\ call.inst_opcode = INVOKE /\
  decode_invoke call = SOME (nm,ops) /\
  inline_tracked_snapshot fn a route snap frame /\
  eval_operands ops snap.ils_state = SOME args /\
  route.ir_rename = (\x. STRCAT outer (STRCAT inner x)) ==>
  eval_operands
    (MAP (clone_operand outer outer_labels)
      (MAP (clone_operand inner inner_labels) ops)) frame.ipf_state = SOME args
Proof
  strip_tac >>
  `EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops` by
    (irule inline_call_operand_namespace >> metis_tac[]) >>
  `EVERY (\op. IS_SOME (eval_operand op snap.ils_state)) ops` by
    (simp[GSYM eval_operands_IS_SOME_EVERY] >> simp[]) >>
  fs[inline_tracked_snapshot_def] >>
  `EVERY (\op. !v. op = Var v ==>
    v IN snap.ils_defined /\ v NOTIN snap.ils_opaque) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >> gvs[] >>
     metis_tac[eval_operand_def, pred_setTheory.IN_APP]) >>
  `frame.ipf_state.vs_labels = FEMPTY` by
    (irule inline_snapshot_anchor_empty_labels >> metis_tac[]) >>
  `eval_operands
    (MAP (clone_operand outer outer_labels)
      (MAP (clone_operand inner inner_labels) ops)) frame.ipf_state =
    eval_operands ops snap.ils_state` by
    (irule inline_snapshot_eval_two_clones >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem inline_tracked_snapshot_identity:
  a.ia_entry.vs_labels = FEMPTY ==>
  inline_tracked_snapshot fn a (inline_route_identity a.ia_id)
    <|ils_state := a.ia_entry; ils_saved := a.ia_entry;
      ils_entry := a.ia_entry;
      ils_defined := {x | MEM x (cfgTransform$fn_all_vars fn) /\
                         IS_SOME (lookup_var x a.ia_entry)};
      ils_opaque := retpc_var fn; ils_protected := {};
      ils_parent_rename := I|>
    <|ipf_state := a.ia_entry; ipf_anchor := a.ia_entry|>
Proof
  simp[inline_tracked_snapshot_def, inline_snapshot_identity,
       SUBSET_DEF]
QED

(* Empty observations at child entry do not constrain the physical locals.
   Bookkeeping/protection are separate obligations of the entry adapter. *)
Theorem inline_tracked_entry_coverage:
  setup_callee fn args s = SOME entry ==>
  !x. ~(MEM x (cfgTransform$fn_all_vars fn) /\
         IS_SOME (lookup_var x entry))
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[lookup_var_def]
QED

Theorem inline_tracked_resume_write:
  inline_tracked_snapshot fn a route snap frame /\
  MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. v IN snap.ils_protected ==>
    snap.ils_parent_rename v <> route.ir_rename x) ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state := update_var x w snap.ils_state;
                 ils_defined := x INSERT snap.ils_defined|>)
    (frame with ipf_state := update_var (route.ir_rename x) w frame.ipf_state)
Proof
  strip_tac >>
  `inline_snapshot_data a route snap frame` by
    fs[inline_tracked_snapshot_def] >>
  `x NOTIN snap.ils_opaque` by
    fs[inline_tracked_snapshot_def, pred_setTheory.IN_APP] >>
  drule_all inline_snapshot_resume_write >>
  disch_then (qspec_then `w` assume_tac) >>
  fs[inline_tracked_snapshot_def] >>
  simp[inline_tracked_snapshot_def, update_var_def] >>
  rpt strip_tac >> Cases_on `x' = x` >>
  gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED
