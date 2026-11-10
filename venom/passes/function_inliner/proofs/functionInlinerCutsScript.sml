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

(* RETPC_PARAM may write a different concrete token in the physical frame;
   the snapshot observes only definedness at this opaque destination. *)
Theorem inline_snapshot_resume_opaque_write:
  inline_snapshot_data a route snap frame /\
  x IN snap.ils_opaque /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. v IN snap.ils_protected ==>
    snap.ils_parent_rename v <> route.ir_rename x) ==>
  inline_snapshot_data a route
    (snap with <|ils_state := update_var x w snap.ils_state;
                 ils_defined := x INSERT snap.ils_defined|>)
    (frame with ipf_state := update_var (route.ir_rename x) u frame.ipf_state)
Proof
  strip_tac >>
  `!v. v IN snap.ils_defined /\ v <> x ==>
       route.ir_rename v <> route.ir_rename x` by
    (qpat_x_assum `INJ _ _ _` mp_tac >>
     pure_rewrite_tac[pred_setTheory.INJ_DEF] >>
     metis_tac[pred_setTheory.IN_INSERT]) >>
  qpat_x_assum `INJ _ _ _` kall_tac >>
  fs[inline_snapshot_data_def] >>
  simp[inline_snapshot_data_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> Cases_on `x = x'` >>
  gvs[lookup_var_def] >> metis_tac[]
QED

Theorem inline_tracked_resume_opaque_write:
  inline_tracked_snapshot fn a route snap frame /\
  MEM x (cfgTransform$fn_all_vars fn) /\ retpc_var fn x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. v IN snap.ils_protected ==>
    snap.ils_parent_rename v <> route.ir_rename x) ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state := update_var x w snap.ils_state;
                 ils_defined := x INSERT snap.ils_defined|>)
    (frame with ipf_state := update_var (route.ir_rename x) u frame.ipf_state)
Proof
  strip_tac >>
  `inline_snapshot_data a route snap frame` by
    fs[inline_tracked_snapshot_def] >>
  `x IN snap.ils_opaque` by
    fs[inline_tracked_snapshot_def, pred_setTheory.IN_APP] >>
  drule_all inline_snapshot_resume_opaque_write >>
  disch_then (qspecl_then [`w`, `u`] assume_tac) >>
  fs[inline_tracked_snapshot_def] >>
  simp[inline_tracked_snapshot_def, update_var_def] >>
  rpt strip_tac >> Cases_on `x' = x` >>
  gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* The parameter-adapter entry cut uses the same physical frame.  It does
   not assert execution of that adapter or inspect uninitialized locals. *)
Theorem inline_tracked_child_entry:
  inline_original_child C fuel parent q call psnap.ils_state r child cr /\
  inline_tracked_snapshot pfn pa proute psnap frame ==>
  inline_tracked_snapshot child.ia_function child route
    <|ils_state := child.ia_entry; ils_saved := psnap.ils_state;
      ils_entry := child.ia_entry; ils_defined := {};
      ils_opaque := retpc_var child.ia_function;
      ils_protected := (psnap.ils_defined DIFF psnap.ils_opaque)
                        DIFF set call.inst_outputs;
      ils_parent_rename := proute.ir_rename|> frame
Proof
  strip_tac >>
  `?args. setup_callee child.ia_function args psnap.ils_state =
          SOME child.ia_entry` by
    (fs[inline_original_child_def] >> metis_tac[]) >>
  `!x. ~IS_SOME (lookup_var x child.ia_entry)` by
    (gvs[setup_callee_def, AllCaseEqs()] >>
     qpat_x_assum `_ = child.ia_entry` (fn th => rewrite_tac[GSYM th]) >>
     simp[lookup_var_def]) >>
  `child.ia_entry.vs_labels = FEMPTY` by
    (irule inline_setup_callee_empty_labels >>
     fs[inline_tracked_snapshot_def] >> metis_tac[]) >>
  fs[inline_tracked_snapshot_def, inline_snapshot_data_def] >>
  simp[inline_tracked_snapshot_def, inline_snapshot_data_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inline_tracked_original_call_two_embeddings:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM call (fn_insts fn) /\
  inline_original_child C fuel parent q call snap.ils_state r child cr /\
  inline_tracked_snapshot fn a route snap frame /\
  route.ir_rename = (\x. STRCAT p2 (STRCAT p1 x)) /\
  inline_fetched_fields fn b j (inline_inst_fields call) /\
  lookup_block lbl1 caller1.fn_blocks = SOME callbb1 /\
  ~MEM (STRCAT p1 b) (fn_labels caller1) /\ STRCAT p1 b <> ret1 /\
  lookup_block lbl2 caller2.fn_blocks = SOME callbb2 /\
  ~MEM (STRCAT p2 (STRCAT p1 b)) (fn_labels caller2) /\
  STRCAT p2 (STRCAT p1 b) <> ret2 ==>
  let mid = renumber_fn_inst_ids (inline_call_site p1 ret1 caller1 fn lbl1 i1);
      final = renumber_fn_inst_ids (inline_call_site p2 ret2 caller2 mid lbl2 i2)
  in ?bb k inst edge nm ops.
    lookup_block (STRCAT p2 (STRCAT p1 b)) final.fn_blocks = SOME bb /\
    get_instruction bb k = SOME inst /\
    inline_inst_fields inst = inline_inst_fields
      (clone_instruction p2 (fn_labels mid)
        (clone_instruction p1 (fn_labels fn) call)) /\
    child.ia_parent = SOME edge /\ decode_invoke call = SOME (nm,ops) /\
    eval_operands
      (MAP (clone_operand p2 (fn_labels mid))
        (MAP (clone_operand p1 (fn_labels fn)) ops)) frame.ipf_state =
      SOME edge.ipe_args /\
    inline_original_child C fuel parent q call snap.ils_state r child cr
Proof
  strip_tac >>
  drule_all inline_original_child_two_embeddings >>
  disch_then (qspecl_then [`i2`, `i1`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  `call.inst_opcode = INVOKE /\
   ?edge nm ops. child.ia_parent = SOME edge /\
     decode_invoke call = SOME (nm,ops) /\
     eval_operands ops snap.ils_state = SOME edge.ipe_args` by
    (fs[inline_original_child_def] >> metis_tac[]) >>
  `eval_operands
      (MAP (clone_operand p2 (fn_labels
        (renumber_fn_inst_ids (inline_call_site p1 ret1 caller1 fn lbl1 i1))))
        (MAP (clone_operand p1 (fn_labels fn)) ops)) frame.ipf_state =
     SOME edge.ipe_args` by
    (irule inline_tracked_call_eval_two_clones >> metis_tac[]) >>
  qexistsl [`bb`, `k`, `inst`, `edge`, `nm`, `ops`] >> simp[]
QED

Theorem inline_tracked_resume_writes:
  !writes snap frame.
  inline_tracked_snapshot fn a route snap frame /\
  INJ route.ir_rename (set (MAP FST writes) UNION snap.ils_defined) UNIV /\
  EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x /\
    (!v. v IN snap.ils_protected ==>
      snap.ils_parent_rename v <> route.ir_rename x)) writes ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state writes;
       ils_defined := set (MAP FST writes) UNION snap.ils_defined|>)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var (route.ir_rename x) w s)
         frame.ipf_state writes)
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `INJ route.ir_rename (h0 INSERT snap.ils_defined) UNIV` by
    (qpat_x_assum `INJ _ _ _` mp_tac >>
     pure_rewrite_tac[pred_setTheory.INJ_DEF] >>
     metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.IN_UNION]) >>
  drule_all inline_tracked_resume_write >>
  disch_then (qspec_then `h1` assume_tac) >>
  first_x_assum drule >>
  simp[] >> impl_tac
  >- (qpat_x_assum `INJ _ (_ UNION _) _` mp_tac >>
      pure_rewrite_tac[pred_setTheory.INJ_DEF] >>
      metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.IN_UNION]) >>
  `set (MAP FST writes) UNION (h0 INSERT snap.ils_defined) =
     (h0 INSERT set (MAP FST writes)) UNION snap.ils_defined` by
    (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[]
QED

Theorem inline_call_output_namespace:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM call (fn_insts fn) /\ call.inst_opcode = INVOKE ==>
  EVERY (\x. MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x)
    call.inst_outputs
Proof
  strip_tac >>
  `retpc_shape_ok fn` by
    (fs[inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac
  >- (simp[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP,
           PULL_EXISTS] >>
      `?bb. MEM bb fn.fn_blocks /\ MEM call bb.bb_instructions` by
        metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM] >>
      qexistsl [`bb`, `call`] >> simp[]) >>
  fs[retpc_shape_ok_def] >>
  qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\ _ ==> _`
    (qspecl_then [`call`, `x`] mp_tac) >> simp[]
QED

Theorem inline_tracked_resume_return:
  inline_tracked_snapshot fn a route snap frame /\
  LENGTH call.inst_outputs = LENGTH vals /\
  INJ route.ir_rename (set call.inst_outputs UNION snap.ils_defined) UNIV /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x /\
    (!v. v IN snap.ils_protected ==>
      snap.ils_parent_rename v <> route.ir_rename x)) call.inst_outputs ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state
         (ZIP (call.inst_outputs, vals));
       ils_defined := set call.inst_outputs UNION snap.ils_defined|>)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var x w s) frame.ipf_state
         (ZIP (MAP route.ir_rename call.inst_outputs, vals)))
Proof
  strip_tac >>
  drule (inline_tracked_resume_writes |> Q.SPEC `ZIP (call.inst_outputs, vals)`) >>
  disch_then (qspecl_then [`vals`, `call`] mp_tac) >>
  simp[MAP_ZIP] >> impl_tac
  >- (gvs[EVERY_MEM] >> gen_tac >> PairCases_on `e` >>
      strip_tac >> simp[] >>
      `MEM e0 call.inst_outputs` by
        (drule MEM_ZIP >> disch_then (qspec_then `(e0,e1)` mp_tac) >>
         simp[] >> metis_tac[MEM_EL]) >>
      metis_tac[]) >>
  simp[ZIP_MAP, rich_listTheory.FOLDL_MAP, combinTheory.o_DEF, pairTheory.UNCURRY_DEF] >>
  `(\s p. update_var (route.ir_rename (FST p)) (SND p) s) =
   (\s (x,w). update_var (route.ir_rename x) w s)` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases >> simp[]) >>
  simp[]
QED

(* Return bindings are ordinary (nonopaque) caller writes, by the frozen
   retpc output-shape clause; SSA is not an input-contract assumption. *)
Theorem inline_tracked_call_return:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM call (fn_insts fn) /\ call.inst_opcode = INVOKE /\
  inline_tracked_snapshot fn a route snap frame /\
  LENGTH call.inst_outputs = LENGTH vals /\
  INJ route.ir_rename (set call.inst_outputs UNION snap.ils_defined) UNIV /\
  (!x v. MEM x call.inst_outputs /\ v IN snap.ils_protected ==>
    snap.ils_parent_rename v <> route.ir_rename x) ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state
         (ZIP (call.inst_outputs, vals));
       ils_defined := set call.inst_outputs UNION snap.ils_defined|>)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var x w s) frame.ipf_state
         (ZIP (MAP route.ir_rename call.inst_outputs, vals)))
Proof
  strip_tac >>
  `EVERY (\x. MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x)
    call.inst_outputs` by
    (irule inline_call_output_namespace >> metis_tac[]) >>
  irule inline_tracked_resume_return >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* Inactive observations for one physical owner.  This is storage only, not
   a reachability certificate or an assertion about saved shared state. *)
Definition inline_suspended_observations_def:
  inline_suspended_observations obs frame <=>
    EVERY (\(a,route,snap).
      inline_tracked_snapshot a.ia_function a route snap frame) obs
End

Definition inline_suspended_avoids_def:
  inline_suspended_avoids obs d <=>
    EVERY (\(a,route,snap).
      (!x. x IN snap.ils_defined ==> d <> route.ir_rename x) /\
      (!x. x IN snap.ils_protected ==> d <> snap.ils_parent_rename x)) obs
End

Theorem inline_suspended_empty[simp]:
  inline_suspended_observations [] frame /\ inline_suspended_avoids [] d
Proof
  simp[inline_suspended_observations_def, inline_suspended_avoids_def]
QED

Theorem inline_tracked_physical_write:
  inline_tracked_snapshot fn a route snap frame /\
  (!x. x IN snap.ils_defined ==> d <> route.ir_rename x) /\
  (!x. x IN snap.ils_protected ==> d <> snap.ils_parent_rename x) ==>
  inline_tracked_snapshot fn a route snap
    (frame with ipf_state := update_var d w frame.ipf_state)
Proof
  strip_tac >>
  `inline_snapshot_data a route snap
     (frame with ipf_state := update_var d w frame.ipf_state)` by
    (irule inline_snapshot_write >> fs[inline_tracked_snapshot_def] >> metis_tac[]) >>
  fs[inline_tracked_snapshot_def]
QED

Theorem inline_suspended_write:
  !obs frame.
    inline_suspended_observations obs frame /\ inline_suspended_avoids obs d ==>
    inline_suspended_observations obs
      (frame with ipf_state := update_var d w frame.ipf_state)
Proof
  Induct >> simp[inline_suspended_observations_def, inline_suspended_avoids_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac
  >- (irule inline_tracked_physical_write >> simp[]) >>
  fs[GSYM inline_suspended_observations_def,
     GSYM inline_suspended_avoids_def]
QED

Theorem inline_suspended_writes:
  !writes frame.
    inline_suspended_observations obs frame /\
    EVERY (\(d,w). inline_suspended_avoids obs d) writes ==>
    inline_suspended_observations obs
      (frame with ipf_state :=
        FOLDL (\s (d,w). update_var d w s) frame.ipf_state writes)
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all inline_suspended_write >>
  disch_then (qspec_then `h1` assume_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem inline_suspended_root:
  a.ia_entry.vs_labels = FEMPTY ==>
  ?snap frame.
    inline_tracked_snapshot a.ia_function a (inline_route_identity a.ia_id) snap frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry /\
    inline_suspended_observations [] frame
Proof
  strip_tac >>
  drule (inline_tracked_snapshot_identity |> Q.INST [`fn` |-> `a.ia_function`]) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inline_suspended_push_child:
  inline_original_child C fuel parent q call psnap.ils_state r child cr /\
  inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
  inline_suspended_observations obs frame ==>
  ?csnap.
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    csnap.ils_protected =
      (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set call.inst_outputs /\
    csnap.ils_parent_rename = proute.ir_rename /\
    inline_tracked_snapshot child.ia_function child route csnap frame /\
    inline_suspended_observations ((pa,proute,psnap)::obs) frame
Proof
  strip_tac >> drule_all inline_tracked_child_entry >>
  disch_then (qspec_then `route` assume_tac) >>
  goal_assum (drule_at Any) >>
  gvs[inline_suspended_observations_def]
QED

Theorem inline_suspended_original_call_push:
  call.inst_opcode = INVOKE /\
  step_inst fuel C call psnap.ils_state = r /\ terminates r /\
  inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
  inline_suspended_observations obs frame ==>
  ?child cr csnap.
    inline_original_child C fuel pa.ia_id q call psnap.ils_state r child cr /\
    inline_original_call_result call psnap.ils_state cr r /\
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    csnap.ils_protected =
      (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set call.inst_outputs /\
    csnap.ils_parent_rename = proute.ir_rename /\
    inline_tracked_snapshot child.ia_function child route csnap frame /\
    inline_suspended_observations ((pa,proute,psnap)::obs) frame
Proof
  strip_tac >> drule_all inline_original_child_exists >>
  disch_then (qspecl_then [`q`, `pa.ia_id`] strip_assume_tac) >>
  drule_all inline_suspended_push_child >>
  disch_then (qspec_then `route` strip_assume_tac) >>
  qexistsl [`child`, `cr`, `csnap`] >> simp[] >>
  fs[inline_original_child_def]
QED

(* The avoidance premise observes ALL suspended ancestors of this owner,
   including routed opaque destinations.  Deriving it from actual edit
   namespaces and reachable source stacks remains the layout frontier's job. *)
Theorem inline_suspended_original_call_push_writes:
  call.inst_opcode = INVOKE /\
  step_inst fuel C call psnap.ils_state = r /\ terminates r /\
  inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
  inline_suspended_observations obs frame /\
  EVERY (\(d,w). inline_suspended_avoids ((pa,proute,psnap)::obs) d) writes ==>
  ?child cr csnap.
    inline_original_child C fuel pa.ia_id q call psnap.ils_state r child cr /\
    inline_original_call_result call psnap.ils_state cr r /\
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    inline_tracked_snapshot child.ia_function child route csnap frame /\
    inline_suspended_observations ((pa,proute,psnap)::obs)
      (frame with ipf_state :=
        FOLDL (\s (d,w). update_var d w s) frame.ipf_state writes)
Proof
  strip_tac >> drule_all inline_suspended_original_call_push >>
  disch_then (qspecl_then [`route`, `q`] strip_assume_tac) >>
  qexistsl [`child`, `cr`, `csnap`] >> simp[] >>
  irule inline_suspended_writes >> simp[]
QED
