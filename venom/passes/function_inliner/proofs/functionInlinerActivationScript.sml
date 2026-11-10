(* Original activation identities and proof-only target storage routing.
   Routes describe storage/layout only: none asserts target execution success. *)
Theory functionInlinerActivation
Ancestors
  functionInlinerSimulation functionInlinerSiteSimulation
  functionInlinerNamespace functionInlinerOrigin
  functionInlinerSiteLayout functionInlinerDefs functionInlinerFrame venomExecSemantics
  venomState venomInst passSimulationProofs passSimulationDefs list rich_list pred_set

Datatype:
  inline_parent_edge = <|
    ipe_parent : num list;
    ipe_call : instruction;
    ipe_saved : venom_state;
    ipe_args : (256 word) list;
    ipe_child : venom_state
  |>
End

Datatype:
  inline_activation = <|
    ia_id : num list;
    ia_function : ir_function;
    ia_entry : venom_state;
    ia_parent : inline_parent_edge option
  |>
End

Datatype:
  inline_source_configuration = <|
    isc_active : inline_activation;
    isc_suspended : inline_activation list;
    isc_state : venom_state
  |>
End

Datatype:
  inline_site_edit = <|
    ise_before : venom_context;
    ise_after : venom_context;
    ise_caller : ir_function;
    ise_callee : ir_function;
    ise_final : ir_function;
    ise_block : string;
    ise_index : num;
    ise_prefix : string;
    ise_return : string;
    ise_state : inline_state;
    ise_next : inline_state
  |>
End

Datatype:
  inline_layout_choice = InlineKeep inline_site_edit
                       | InlineEnter inline_site_edit
End

Datatype:
  inline_location_phase = InlineBeforePhi
                        | InlineAtInstruction num
                        | InlineAtReturn num
End

Datatype:
  inline_route = <|
    ir_owner : num list;
    ir_rename : string -> string;
    ir_path : inline_layout_choice list
  |>
End

(* Owner IDs are dynamic activation IDs, never static function names. *)
Datatype:
  inline_route_edit = <|
    ire_from : num list;
    ire_to : num list;
    ire_choice : inline_layout_choice
  |>
End

Definition inline_choice_rename_def:
  inline_choice_rename (InlineKeep e) x = x /\
  inline_choice_rename (InlineEnter e) x = STRCAT e.ise_prefix x
End

Definition inline_route_identity_def:
  inline_route_identity a = <|ir_owner := a; ir_rename := I; ir_path := []|>
End

Definition inline_route_apply_def:
  inline_route_apply e r =
    if r.ir_owner = e.ire_from then
      r with <| ir_owner := e.ire_to;
                ir_rename := inline_choice_rename e.ire_choice o r.ir_rename;
                ir_path := r.ir_path ++ [e.ire_choice] |>
    else r
End

Definition inline_route_actions_def:
  inline_route_actions es r = FOLDL (\r e. inline_route_apply e r) r es
End

Theorem inline_route_actions_nil[simp]:
  inline_route_actions [] r = r
Proof
  simp[inline_route_actions_def]
QED

Theorem inline_route_actions_append:
  inline_route_actions (es ++ fs) r =
    inline_route_actions fs (inline_route_actions es r)
Proof
  simp[inline_route_actions_def, FOLDL_APPEND]
QED

Theorem inline_route_unrelated:
  r.ir_owner <> e.ire_from ==> inline_route_apply e r = r
Proof
  simp[inline_route_apply_def]
QED

(* Embed B in A, then A in C. The second prefix is outermost. *)
Theorem inline_route_two_embeddings:
  inline_route_actions
    [<|ire_from := b; ire_to := a; ire_choice := InlineEnter eb|>;
     <|ire_from := a; ire_to := c; ire_choice := InlineEnter ea|>]
    (inline_route_identity b) =
  <|ir_owner := c;
    ir_rename := (\x. STRCAT ea.ise_prefix (STRCAT eb.ise_prefix x));
    ir_path := [InlineEnter eb; InlineEnter ea]|>
Proof
  simp[inline_route_actions_def, inline_route_apply_def,
       inline_route_identity_def, inline_choice_rename_def, combinTheory.o_DEF]
QED

Definition inline_site_edit_valid_def:
  inline_site_edit_valid e <=>
    inline_one_site e.ise_caller e.ise_callee e.ise_state =
      SOME (e.ise_final, e.ise_next) /\
    find_invoke_site e.ise_callee.fn_name e.ise_caller.fn_blocks =
      SOME (e.ise_block, e.ise_index) /\
    e.ise_prefix = inline_prefix e.ise_state.is_inline_count /\
    e.ise_return = return_block_label e.ise_prefix e.ise_state.is_label_counter
End

(* None marks a phase requiring its dedicated entry/return adapter. *)
Datatype:
  inline_location = <|
    il_block : string;
    il_phase : inline_location_phase;
    il_counter : num
  |>
End

Definition inline_choice_location_def:
  inline_choice_location choice loc =
    case choice of
      InlineKeep e =>
        (case loc.il_phase of
          InlineBeforePhi => SOME loc
        | InlineAtInstruction j =>
            if loc.il_block = e.ise_block /\ j = e.ise_index then NONE
            else SOME (loc with <|
              il_block := if loc.il_block = e.ise_block /\ e.ise_index < j
                          then e.ise_return else loc.il_block;
              il_phase := InlineAtInstruction
                (if loc.il_block = e.ise_block /\ e.ise_index < j
                 then j - (e.ise_index + 1) else j) |>)
        | InlineAtReturn j => NONE)
    | InlineEnter e =>
        (case loc.il_phase of
          InlineBeforePhi =>
            SOME (loc with il_block := STRCAT e.ise_prefix loc.il_block)
        | InlineAtInstruction j =>
            (case (lookup_block loc.il_block e.ise_callee.fn_blocks,
                   lookup_block e.ise_block e.ise_caller.fn_blocks) of
              (SOME cb, SOME bb) =>
                if j <= LENGTH cb.bb_instructions /\
                   e.ise_index < LENGTH bb.bb_instructions then
                  let pre = rewrite_inline_insts
                    (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)
                    (EL e.ise_index bb.bb_instructions).inst_outputs e.ise_return
                    (MAP (clone_instruction e.ise_prefix (fn_labels e.ise_callee))
                         (TAKE j cb.bb_instructions)) 0
                  in SOME <|il_block := STRCAT e.ise_prefix loc.il_block;
                            il_phase := InlineAtInstruction (LENGTH (FST pre));
                            il_counter := SND pre|>
                else NONE
            | _ => NONE)
        | InlineAtReturn j => NONE)
End

Definition inline_location_step_def:
  inline_location_step loc choice =
    case loc of NONE => NONE | SOME l => inline_choice_location choice l
End

Definition inline_path_location_def:
  inline_path_location path loc = FOLDL inline_location_step loc path
End

Theorem inline_path_location_identity[simp]:
  inline_path_location [] loc = loc
Proof
  simp[inline_path_location_def]
QED

Theorem inline_path_location_append:
  inline_path_location (p ++ q) loc =
    inline_path_location q (inline_path_location p loc)
Proof
  simp[inline_path_location_def, FOLDL_APPEND]
QED

Theorem inline_path_location_absent[simp]:
  !path. inline_path_location path NONE = NONE
Proof
  Induct >> gvs[inline_path_location_def, inline_location_step_def]
QED

Theorem inline_path_location_associative:
  inline_path_location ((p ++ q) ++ r) loc =
    inline_path_location r (inline_path_location q (inline_path_location p loc))
Proof
  simp[inline_path_location_append]
QED

(* A routing edit cannot alter original call identities or saved evidence. *)
Definition inline_activation_route_edit_def:
  inline_activation_route_edit e (a,r) = (a, inline_route_apply e r)
End

Theorem inline_activation_route_edit_original[simp]:
  FST (inline_activation_route_edit e (a,r)) = a
Proof
  simp[inline_activation_route_edit_def]
QED

Datatype:
  inline_physical_frame = <|
    ipf_state : venom_state;
    ipf_anchor : venom_state
  |>
End

Datatype:
  inline_logical_snapshot = <|
    ils_state : venom_state;
    ils_saved : venom_state;
    ils_entry : venom_state;
    ils_defined : string -> bool;
    ils_opaque : string -> bool;
    ils_protected : string -> bool;
    ils_parent_rename : string -> string
  |>
End

(* This relation never identifies the logical child's parameters with those
   of its physical owner. Only the original entry fixes that child's data. *)
Definition inline_snapshot_data_def:
  inline_snapshot_data a route snap frame <=>
    snap.ils_entry = a.ia_entry /\
    snap.ils_state.vs_params = a.ia_entry.vs_params /\
    snap.ils_state.vs_return_pc_token = a.ia_entry.vs_return_pc_token /\
    inline_caller_bookkeeping frame.ipf_anchor frame.ipf_state /\
    (!x. x IN snap.ils_defined DIFF snap.ils_opaque ==>
      lookup_var x snap.ils_state =
      lookup_var (route.ir_rename x) frame.ipf_state) /\
    (!x. x IN snap.ils_defined INTER snap.ils_opaque /\
         IS_SOME (lookup_var x snap.ils_state) ==>
      IS_SOME (lookup_var (route.ir_rename x) frame.ipf_state)) /\
    (!x. x IN snap.ils_protected ==>
      lookup_var x snap.ils_saved =
      lookup_var (snap.ils_parent_rename x) frame.ipf_state)
End

(* Inactive activations have saved logical states, not the current shared
   state or current program counter of an owner now executing their child. *)
Definition inline_activation_storage_def:
  inline_activation_storage active acts routes logical physical <=>
    (!id a. acts id = SOME a ==>
      ?route snap frame.
        routes id = SOME route /\ logical id = SOME snap /\
        physical route.ir_owner = SOME frame /\
        inline_snapshot_data a route snap frame /\
        (id = active ==>
          inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state))
End

Definition inline_active_location_def:
  inline_active_location route phase s t counter <=>
    inline_path_location route.ir_path
      (SOME <|il_block := s.vs_current_bb; il_phase := phase; il_counter := 0|>) =
    SOME <|il_block := t.vs_current_bb;
           il_phase := InlineAtInstruction t.vs_inst_idx; il_counter := counter|>
End

Theorem inline_snapshot_identity:
  inline_snapshot_data a (inline_route_identity a.ia_id)
    <|ils_state := a.ia_entry; ils_saved := a.ia_entry;
      ils_entry := a.ia_entry; ils_defined := V; ils_opaque := opaque;
      ils_protected := {}; ils_parent_rename := I|>
    <|ipf_state := a.ia_entry; ipf_anchor := a.ia_entry|>
Proof
  simp[inline_snapshot_data_def, inline_route_identity_def]
QED

Theorem inline_active_location_identity:
  inline_active_location (inline_route_identity id)
    (InlineAtInstruction s.vs_inst_idx) s s 0
Proof
  simp[inline_active_location_def, inline_route_identity_def]
QED

(* This is the source-entry projection needed by residual parameter steps.
   It has no premise concerning the physical owner's argument vector. *)
Theorem inline_snapshot_original_entry:
  inline_snapshot_data a route snap frame ==>
  snap.ils_state.vs_params = a.ia_entry.vs_params /\
  snap.ils_state.vs_return_pc_token = a.ia_entry.vs_return_pc_token
Proof
  simp[inline_snapshot_data_def]
QED

Theorem inline_snapshot_clone_point:
  inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
    c d V b j counter s t /\
  s.vs_params = a.ia_entry.vs_params /\
  s.vs_return_pc_token = a.ia_entry.vs_return_pc_token ==>
  inline_snapshot_data a
    <|ir_owner := owner; ir_rename := STRCAT p; ir_path := path|>
    <|ils_state := s; ils_saved := c; ils_entry := a.ia_entry;
      ils_defined := V; ils_opaque := opaque;
      ils_protected := N DIFF opaque_caller; ils_parent_rename := I|>
    <|ipf_state := t; ipf_anchor := d|> /\
  inline_shared_frame s = inline_shared_frame t
Proof
  simp[inline_clone_point_def, inline_snapshot_data_def,
       inline_target_anchor_def, inline_opaque_frame_rel_def,
       inline_frame_rel_def, venomStateTheory.lookup_var_def] >>
  metis_tac[]
QED

Theorem inline_snapshot_identity_storage:
  inline_activation_storage a.ia_id
    (\id. if id = a.ia_id then SOME a else NONE)
    (\id. if id = a.ia_id then SOME (inline_route_identity a.ia_id) else NONE)
    (\id. if id = a.ia_id then
      SOME <|ils_state := a.ia_entry; ils_saved := a.ia_entry;
             ils_entry := a.ia_entry; ils_defined := V; ils_opaque := opaque;
             ils_protected := {}; ils_parent_rename := I|> else NONE)
    (\id. if id = a.ia_id then
      SOME <|ipf_state := a.ia_entry; ipf_anchor := a.ia_entry|> else NONE)
Proof
  simp[inline_activation_storage_def, inline_route_identity_def,
       inline_snapshot_data_def]
QED

Definition inline_original_call_result_def:
  inline_original_call_result call caller cr r <=>
    (?ir se u. cr = IntRet ir se /\
      bind_outputs call.inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state caller se)) = SOME u /\ r = OK u) \/
    (?se. cr = Halt se /\ r = Halt se) \/
    (?ab se. cr = Abort ab se /\ r = Abort ab se)
End

(* The exact original child run, not an intermediate target-success premise. *)
Definition inline_original_child_def:
  inline_original_child C fuel parent q call caller r child cr <=>
    call.inst_opcode = INVOKE /\
    step_inst fuel C call caller = r /\ terminates r /\
    child.ia_id = parent ++ [q] /\
    (?edge nm ops.
      child.ia_parent = SOME edge /\
      edge.ipe_parent = parent /\ edge.ipe_call = call /\
      edge.ipe_saved = caller /\ edge.ipe_child = child.ia_entry /\
      decode_invoke call = SOME (nm,ops) /\
      lookup_function nm C.ctx_functions = SOME child.ia_function /\
      eval_operands ops caller = SOME edge.ipe_args /\
      setup_callee child.ia_function edge.ipe_args caller = SOME child.ia_entry) /\
    run_blocks fuel C child.ia_function child.ia_entry = cr /\
    terminates cr /\ inline_original_call_result call caller cr r
End

Theorem inline_original_child_exists:
  call.inst_opcode = INVOKE /\ step_inst fuel C call caller = r /\ terminates r ==>
  ?child cr. inline_original_child C fuel parent q call caller r child cr
Proof
  strip_tac >> drule_all terminating_invoke_inversion >> strip_tac >>
  qexistsl [
    `<|ia_id := parent ++ [q]; ia_function := fn; ia_entry := cs;
       ia_parent := SOME (<|ipe_parent := parent; ipe_call := call;
         ipe_saved := caller; ipe_args := args; ipe_child := cs|>)|>`, `cr`] >>
  simp[inline_original_child_def, inline_original_call_result_def] >>
  metis_tac[]
QED

Theorem inline_original_child_argument:
  inline_original_child C call_fuel parent q call caller r child cr /\
  inline_snapshot_data child route snap frame /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] /\
  step_inst fuel C inst snap.ils_state = pr /\ (!e. pr <> Error e) ==>
  ?ops.
    (?nm. decode_invoke call = SOME (nm,ops)) /\
    w2n idx < LENGTH ops /\
    eval_operand (EL (w2n idx) ops) caller =
      SOME (EL (w2n idx) snap.ils_state.vs_params) /\
    pr = OK (update_var x (EL (w2n idx) snap.ils_state.vs_params) snap.ils_state)
Proof
  strip_tac >> fs[inline_original_child_def] >>
  drule inline_snapshot_original_entry >> strip_tac >>
  `MEM inst.inst_opcode [PARAM; FMP_PARAM]` by simp[] >>
  drule_all inline_original_reached_argument >> simp[]
QED

(* The token belongs to the exact original child, not its storage owner. *)
Theorem inline_original_child_token:
  inline_original_child C call_fuel parent q call caller r child cr /\
  inline_snapshot_data child route snap frame /\
  inst.inst_opcode = RETPC_PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] ==>
  ?edge. child.ia_parent = SOME edge /\
    step_inst fuel C inst snap.ils_state =
      OK (update_var x (if NULL edge.ipe_args then 0w else LAST edge.ipe_args)
            snap.ils_state)
Proof
  strip_tac >> fs[inline_original_child_def] >>
  drule inline_snapshot_original_entry >> strip_tac >>
  drule_all inline_original_reached_token >> simp[]
QED

(* The single-edit point interfaces validate the concrete location actions.
   Their instruction provenance remains available through the point getters. *)
Theorem inline_active_location_keep:
  inline_caller_point e.ise_caller e.ise_final e.ise_block e.ise_index
    e.ise_return N opaque b j s t /\
  ~(b = e.ise_block /\ j = e.ise_index) ==>
  inline_active_location
    <|ir_owner := owner; ir_rename := I; ir_path := [InlineKeep e]|>
    (InlineAtInstruction j) s t 0
Proof
  simp[inline_caller_point_def, inline_active_location_def,
       inline_path_location_def, inline_location_step_def,
       inline_choice_location_def] >>
  rpt strip_tac >> simp[]
QED

Theorem inline_active_location_enter:
  inline_clone_point e.ise_caller e.ise_callee e.ise_final e.ise_block
    e.ise_index e.ise_prefix e.ise_return N opaque_caller opaque
    c d V b j counter s t /\
  (?bb. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
        e.ise_index < LENGTH bb.bb_instructions) ==>
  inline_active_location
    <|ir_owner := owner; ir_rename := STRCAT e.ise_prefix;
      ir_path := [InlineEnter e]|>
    (InlineAtInstruction j) s t counter
Proof
  simp[inline_clone_point_def, inline_active_location_def,
       inline_path_location_def, inline_location_step_def,
       inline_choice_location_def] >>
  rpt strip_tac >> gvs[]
QED

(* Syntax provenance can be transported without re-inverting a target run.
   The indexed layout theorem retains the exact offsets; this projection
   keeps the original child equation alongside a concrete twice-fetched call. *)
Theorem inline_original_child_two_embeddings:
  inline_original_child C fuel parent q call caller r child cr /\
  inline_fetched_fields callee b j (inline_inst_fields call) /\
  lookup_block lbl1 caller1.fn_blocks = SOME callbb1 /\
  ~MEM (STRCAT p1 b) (fn_labels caller1) /\ STRCAT p1 b <> ret1 /\
  lookup_block lbl2 caller2.fn_blocks = SOME callbb2 /\
  ~MEM (STRCAT p2 (STRCAT p1 b)) (fn_labels caller2) /\
  STRCAT p2 (STRCAT p1 b) <> ret2 ==>
  let mid = renumber_fn_inst_ids (inline_call_site p1 ret1 caller1 callee lbl1 i1);
      final = renumber_fn_inst_ids (inline_call_site p2 ret2 caller2 mid lbl2 i2)
  in ?bb k inst.
    lookup_block (STRCAT p2 (STRCAT p1 b)) final.fn_blocks = SOME bb /\
    get_instruction bb k = SOME inst /\
    inline_inst_fields inst = inline_inst_fields
      (clone_instruction p2 (fn_labels mid)
        (clone_instruction p1 (fn_labels callee) call)) /\
    inline_original_child C fuel parent q call caller r child cr
Proof
  strip_tac >>
  `call.inst_opcode = INVOKE` by fs[inline_original_child_def] >>
  drule_all inline_fetched_invoke_two_embeddings >>
  disch_then (qspecl_then [`i2`, `i1`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  qpat_x_assum `inline_fetched_fields callee _ _ _` kall_tac >>
  qpat_x_assum `inline_fetched_fields _ (STRCAT p1 b) _ _` kall_tac >>
  drule inline_fetched_fields_elim >> strip_tac >>
  metis_tac[]
QED

(* All observations, including opaque definedness, are protected here. *)
Theorem inline_snapshot_write:
  inline_snapshot_data a route snap frame /\
  (!v. v IN snap.ils_defined ==> route.ir_rename v <> x) /\
  (!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> x) ==>
  inline_snapshot_data a route snap
    (frame with ipf_state := update_var x w frame.ipf_state)
Proof
  simp[inline_snapshot_data_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[pred_setTheory.IN_DIFF, pred_setTheory.IN_INTER]
QED

Theorem inline_snapshot_writes:
  !writes frame.
  inline_snapshot_data a route snap frame /\
  EVERY (\(x,w).
    (!v. v IN snap.ils_defined ==> route.ir_rename v <> x) /\
    (!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> x)) writes ==>
  inline_snapshot_data a route snap
    (frame with ipf_state :=
      FOLDL (\t (x,w). update_var x w t) frame.ipf_state writes)
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  drule_all inline_snapshot_write >>
  disch_then (qspec_then `h1` assume_tac) >>
  first_x_assum drule_all >> simp[]
QED

Theorem inline_inactive_storage_writes:
  inline_activation_storage active acts routes logical physical /\
  physical owner = SOME frame /\
  (!id a route snap.
    id <> active /\ acts id = SOME a /\ routes id = SOME route /\
    logical id = SOME snap /\ route.ir_owner = owner ==>
    EVERY (\(x,w).
      (!v. v IN snap.ils_defined ==> route.ir_rename v <> x) /\
      (!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> x)) writes) ==>
  !id a. id <> active /\ acts id = SOME a ==>
    ?route snap frame'.
      routes id = SOME route /\ logical id = SOME snap /\
      ((owner =+ SOME (frame with ipf_state :=
        FOLDL (\t (x,w). update_var x w t) frame.ipf_state writes)) physical)
        route.ir_owner = SOME frame' /\
      inline_snapshot_data a route snap frame'
Proof
  pure_rewrite_tac[inline_activation_storage_def] >> rpt strip_tac >>
  qpat_x_assum `!id a. acts id = SOME a ==> _` drule >> strip_tac >>
  qexistsl [`route`, `snap`] >>
  Cases_on `route.ir_owner = owner`
  >- (gvs[] >> simp[combinTheory.APPLY_UPDATE_THM] >>
      irule inline_snapshot_writes >> metis_tac[]) >>
  simp[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem inline_qualified_rewrite_outputs_disjoint:
  qualified_origin ctx n caller /\ qualified_origin ctx n callee /\
  MEM call (fn_insts caller) /\ call.inst_opcode = INVOKE /\
  call.inst_operands = Label callee.fn_name::args /\
  rewrite_inline_blocks (rotate_invoke_ops call.inst_operands)
    call.inst_outputs ret (clone_function (inline_prefix n) callee).fn_blocks param_idx =
    (bbs,param_idx') ==>
  EVERY (\bb. EVERY (\inst. EVERY (\x.
    x NOTIN (set (cfgTransform$fn_all_vars caller) DIFF set call.inst_outputs))
    inst.inst_outputs) bb.bb_instructions) bbs
Proof
  strip_tac >> irule inline_clone_rewrite_outputs_disjoint >>
  goal_assum (drule_at Any) >>
  simp[EVERY_MEM] >>
  metis_tac[qualified_origin_clone_disjoint, qualified_origin_call_return_arity]
QED

Theorem inline_qualified_snapshot_writes:
  qualified_origin ctx n caller /\ qualified_origin ctx n callee /\
  MEM call (fn_insts caller) /\ call.inst_opcode = INVOKE /\
  call.inst_operands = Label callee.fn_name::args /\
  rewrite_inline_blocks (rotate_invoke_ops call.inst_operands)
    call.inst_outputs ret (clone_function (inline_prefix n) callee).fn_blocks param_idx =
    (bbs,param_idx') /\
  inline_snapshot_data a route snap frame /\
  (!v. v IN snap.ils_defined ==>
    route.ir_rename v IN
      (set (cfgTransform$fn_all_vars caller) DIFF set call.inst_outputs)) /\
  (!v. v IN snap.ils_protected ==>
    snap.ils_parent_rename v IN
      (set (cfgTransform$fn_all_vars caller) DIFF set call.inst_outputs)) /\
  EVERY (\(x,w). ?bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs) writes ==>
  inline_snapshot_data a route snap
    (frame with ipf_state :=
      FOLDL (\t (x,w). update_var x w t) frame.ipf_state writes)
Proof
  strip_tac >>
  drule_all inline_qualified_rewrite_outputs_disjoint >>
  simp[EVERY_MEM] >> strip_tac >>
  irule inline_snapshot_writes >> simp[] >>
  simp[EVERY_MEM] >> gen_tac >> PairCases_on `e` >>
  strip_tac >> gvs[EVERY_MEM] >>
  qpat_x_assum `!e. MEM e writes ==> _` drule >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem inline_snapshot_resume_write:
  inline_snapshot_data a route snap frame /\
  x NOTIN snap.ils_opaque /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. v IN snap.ils_protected ==>
    snap.ils_parent_rename v <> route.ir_rename x) ==>
  inline_snapshot_data a route
    (snap with <|ils_state := update_var x w snap.ils_state;
                 ils_defined := x INSERT snap.ils_defined|>)
    (frame with ipf_state := update_var (route.ir_rename x) w frame.ipf_state)
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

Theorem inline_snapshot_resume_writes:
  !writes snap frame.
  inline_snapshot_data a route snap frame /\
  INJ route.ir_rename (set (MAP FST writes) UNION snap.ils_defined) UNIV /\
  EVERY (\(x,w). x NOTIN snap.ils_opaque /\
    (!v. v IN snap.ils_protected ==>
      snap.ils_parent_rename v <> route.ir_rename x)) writes ==>
  inline_snapshot_data a route
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
  drule_all inline_snapshot_resume_write >>
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

Theorem inline_snapshot_resume_return:
  inline_snapshot_data a route snap frame /\
  LENGTH call.inst_outputs = LENGTH vals /\
  INJ route.ir_rename (set call.inst_outputs UNION snap.ils_defined) UNIV /\
  EVERY (\x. x NOTIN snap.ils_opaque /\
    (!v. v IN snap.ils_protected ==>
      snap.ils_parent_rename v <> route.ir_rename x)) call.inst_outputs ==>
  inline_snapshot_data a route
    (snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state
         (ZIP (call.inst_outputs, vals));
       ils_defined := set call.inst_outputs UNION snap.ils_defined|>)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var x w s) frame.ipf_state
         (ZIP (MAP route.ir_rename call.inst_outputs, vals)))
Proof
  strip_tac >>
  drule (inline_snapshot_resume_writes |> Q.SPEC `ZIP (call.inst_outputs, vals)`) >>
  disch_then (qspecl_then [`vals`, `call`] mp_tac) >>
  simp[MAP_ZIP] >> impl_tac
  >- (gvs[EVERY_MEM] >> gen_tac >> PairCases_on `e` >>
      strip_tac >> simp[] >>
      `MEM e0 call.inst_outputs` by
        (drule MEM_ZIP >> disch_then (qspec_then `(e0,e1)` mp_tac) >>
         simp[] >> metis_tac[MEM_EL]) >>
      metis_tac[]) >>
  simp[ZIP_MAP, FOLDL_MAP, combinTheory.o_DEF, pairTheory.UNCURRY_DEF] >>
  `(\s p. update_var (route.ir_rename (FST p)) (SND p) s) =
   (\s (x,w). update_var (route.ir_rename x) w s)` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases >> simp[]) >>
  simp[]
QED
