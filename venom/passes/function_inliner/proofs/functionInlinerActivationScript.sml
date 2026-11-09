(* Original activation identities and proof-only target storage routing.
   Routes describe storage/layout only: none asserts target execution success. *)
Theory functionInlinerActivation
Ancestors
  functionInlinerSimulation functionInlinerSiteSimulation
  functionInlinerSiteLayout functionInlinerDefs venomExecSemantics
  venomState venomInst list rich_list pred_set

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
