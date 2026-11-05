(*
 * The target/place judgment: fields, subscripts, every target (#636,
 * Places)
 *
 * The steps of targetPlaceSim's judgment.  A field adds its offset to the
 * base's pointer with one ADD: struct_field_offset bytes for a local's
 * place, struct_field_offset_slots slots for a storage one, where the
 * source extends the base's place by the field.  An element of an array or
 * a mapping is cheated (target_subscript_case says what it needs).
 *
 * TOP-LEVEL:
 *   target_attr_case       — a field: the base's pointer plus the field's
 *                          byte offset (memory) or slot offset (storage)
 *   target_subscript_case  — an element of an array or a mapping
 *                          (cheated, see there)
 *   target_case_all        — every target, by induction, from the indices'
 *                          judgments
 *   target_indices, target_idx_case_ok — the indices' judgments from
 *                          expr_ok, with no internal calls
 *   target_place_sim       — the judgment for eval_target_place: the place
 *                          of a target typed by a value type
 *   eval_base_place_sim_inv — expr_sim_inv after the target's evaluation
 *   place_ptr_rel_vars_frame, target_post_add — the pointer and the post
 *                          through code that writes only fresh variables
 *
 * Helpers: expr_exit_INR_type,
 *   alookup_fields_args, attribute_type_struct_field,
 *   extend_storage_place_attr, target_field_offset, target_field_type,
 *   compile_get_target_ptr_attr, extend_place_memory_attr,
 *   struct_field_slot_alookup, target_post_inst_idx, target_attr_add_frag,
 *   attr_place_step, base_assignment_target_induct
 *)

Theory targetPlaceSimCases
Ancestors
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc
  venomState venomInst
Libs
  pairLib

(* ===== Facts from the statement simulation =====
   Restated from stmtSim (expr_exit_INR_type), stmtSimAssignAttr
   (struct_field_type, attribute_type_struct_field) and
   stmtSimAssignAttrStorage (extend_storage_place_attr), so the judgment
   does not depend on the statement simulation. *)

Theorem expr_exit_INR_type[local]:
  !ex rr. expr_exit (INR ex : 'a + exception) rr =
          expr_exit (INR ex : 'b + exception) rr
Proof
  cheat
QED

Theorem alookup_fields_args[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty, fsz)
Proof
  cheat
QED

(* A field the typing gives a struct is in the lowering's struct table. *)
Theorem attribute_type_struct_field[local]:
  !cenv cx env es sid fld fty.
    expr_sim_inv cenv cx env es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
    ?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                     (nsid_to_string sid)) fld = SOME (fty, fsz)
Proof
  cheat
QED

(* A field of a storage struct: the slot plus the field's slot offset, at
   the field's type; any other case is a type error. *)
Theorem extend_storage_place_attr[local]:
  !cx tr slot tv fld es r es'.
    extend_storage_place cx tr slot tv (AttrSubscript fld) es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv. tv = StructTV fs /\ struct_field_slot fs fld = SOME (off, ftv) /\
                 r = INL (StoragePlace tr (slot + n2w off) ftv)
Proof
  cheat
QED

(* One-step induction over targets (the pinned HOL mutual AST induction
   bug HOL#2115), as vyperTypeEvalSoundness has it. *)
Theorem base_assignment_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  cheat
QED

(* ===== The source, by step ===== *)

(* No step of the target's evaluation but its indices' changes the state,
   and those keep expr_sim_inv (expr_body_pre_eval_result). *)
Theorem eval_base_place_sim_inv:
  !bt cenv cx env es res es'.
    target_pre cenv cx env bt es /\ eval_base_place cx bt es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  cheat
QED

(* ===== Fields ===== *)

(* The byte or slot offset compile_get_target_ptr adds for a field of a
   base at location loc_opt of place type pt, and the field's place type. *)
Definition target_field_offset_def:
  target_field_offset cenv loc_opt pt fld =
    let fields = get_struct_fields cenv.ce_struct_fields
                   (case pt of SOME (ValPT (StructT sn)) => nsid_to_string sn
                             | _ => "") in
    if (case loc_opt of SOME LocStorage => T | SOME LocTransient => T
                      | _ => F)
    then struct_field_offset_slots fields fld
    else struct_field_offset fields fld
End

Definition target_field_type_def:
  target_field_type cenv pt fld =
    case ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (case pt of SOME (ValPT (StructT sn)) => nsid_to_string sn
                              | _ => "")) fld of
      SOME (fty, _) => SOME (ValPT fty)
    | NONE => NONE
End

Theorem compile_get_target_ptr_attr:
  !cenv bt fld sa r sb.
    compile_get_target_ptr compile_expr cenv (AttributeTarget bt fld) sa =
      (r, sb) ==>
    ?rb sm dst.
      compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
      emit_op ADD [FST rb; Lit (n2w (target_field_offset cenv
                     (FST (SND rb)) (SND (SND rb)) fld))] sm = (dst, sb) /\
      r = (dst, FST (SND rb), target_field_type cenv (SND (SND rb)) fld)
Proof
  cheat
QED

(* A field of a local's place that reads: unless the extension raises a
   type error, the place at the field, which reads too.  popped_keys_indexed
   keeps the popped history off the field itself. *)
Theorem extend_place_memory_attr:
  !cx id path fld es res es'.
    extend_place cx (PlaceR (MemoryPlace id path)) (AttrSubscript fld) es =
      (res, es') /\
    place_readable cx es (PlaceR (MemoryPlace id path)) /\
    popped_keys_indexed es.scopes /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es' = es /\
    res = INL (PlaceR (MemoryPlace id (path ++ [AttrSubscript fld]))) /\
    place_readable cx es (PlaceR (MemoryPlace id (path ++ [AttrSubscript fld])))
Proof
  cheat
QED

Theorem struct_field_slot_alookup[local]:
  !fs id off ftv.
    struct_field_slot fs id = SOME (off, ftv) ==> ALOOKUP fs id = SOME ftv
Proof
  cheat
QED

(* place_ptr_rel reads the state only through the live locals' pointers,
   which code from sa on does not write. *)
Theorem place_ptr_rel_vars_frame:
  !cenv cx s t sa pv w loc vt.
    place_ptr_rel cenv cx s pv w loc vt /\ local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
    place_ptr_rel cenv cx t pv w loc vt
Proof
  cheat
QED

Theorem target_post_inst_idx[simp]:
  !ctx func cenv cx es sa sb s0 es' pv vt r s n.
    target_post ctx func cenv cx es sa sb s0 es' pv vt r
      (s with vs_inst_idx := n) <=>
    target_post ctx func cenv cx es sa sb s0 es' pv vt r s
Proof
  cheat
QED

(* The ADD of an offset to the base's pointer, from the base's post at sm:
   its output is the new place's pointer, and the frame carries over. *)
Theorem target_post_add:
  !ctx func cenv cx es sa sm sb s0 es' pv vt rb s dst w0 off pv' vt'.
    target_post ctx func cenv cx es sa sm s0 es' pv vt rb s /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
    eval_operand (FST rb) s = SOME w0 /\
    place_ptr_rel cenv cx s pv' (w0 + n2w off) (FST (SND rb)) vt' /\
    place_readable cx es' pv' ==>
    ?q. run_inst_seq (emitted_insts sm sb) s = OK q /\
        target_post ctx func cenv cx es sa sb s0 es' pv' vt'
          (dst, FST (SND rb), SOME (value_type_place vt')) q
Proof
  cheat
QED

Theorem target_attr_add_frag[local]:
  !ctx func cenv cx es sa sm sb s0 es1 pv vt rb dst off pv' vt' R t w0.
    target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
    eval_operand (FST rb) t = SOME w0 /\
    place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
    place_readable cx es1 pv' ==>
    frag_exec ctx sm sb (\s. s = t)
      (\s. target_post ctx func cenv cx es sa sb s0 es1 pv' vt'
             (dst, FST (SND rb), SOME (value_type_place vt')) s) R
Proof
  cheat
QED

(* The source's field step on a base place typed by a struct: the field's
   place, at the base's pointer plus the field's offset. *)
Theorem attr_place_step[local]:
  !cenv cx env es1 es' t pv w0 rb sid fld fty res.
    expr_sim_inv cenv cx env es1 /\
    place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
    SND (SND rb) = SOME (ValPT (StructT sid)) /\
    place_readable cx es1 pv /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
    extend_place cx pv (AttrSubscript fld) es1 = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es' = es1 /\
    ?pv'. res = INL pv' /\ place_readable cx es1 pv' /\
          target_field_type cenv (SND (SND rb)) fld =
            SOME (value_type_place (Type fty)) /\
          place_ptr_rel cenv cx t pv'
            (w0 + n2w (target_field_offset cenv (FST (SND rb))
                         (SND (SND rb)) fld))
            (FST (SND rb)) (Type fty)
Proof
  cheat
QED




(* A field: the base's fragment, then the ADD of the field's offset.  The
   source extends the base's place by the field. *)
Theorem target_attr_case:
  !nocalls ctx func cenv cx bt fld.
    target_case nocalls ctx func cenv cx bt ==>
    target_case nocalls ctx func cenv cx (AttributeTarget bt fld)
Proof
  cheat
QED



(* ===== Subscripts ===== *)

(* An element of an array or a mapping: the base's fragment, the index's
   (lower_value), then, by the base's place type, the slot of the key
   (compile_mapping_subscript, with compile_keccak256_key for a bytes or
   string key) or the bounds check and the element's pointer
   (compile_array_subscript).  Cheated, for the later #636 PRs:
   - a nested pop in an index, such as x[0][x[0].pop()], writes an inner
     length word, which the shared locals_kept frame exempts, but the
     index's expr_vv_case for such a pop is exprSimPlaces' cheated
     compile_pop_nested_sim;
   - the index runs after the base, so the base's target_post must survive
     its fragment: place_ptr_rel does (place_ptr_rel_vars_frame: the local
     pointers and the base's operand are not fresh at the index's start),
     but place_readable does not, as the index can pop the base's array;
     the source then reads the base from the popped history
     (read_memory_path), and the element's bytes are still in memory, as
     a root pop writes only its exempt length word, but nothing relates
     the popped history to memory yet;
   - the bounds check: a source RuntimeError for an index out of range
     (evaluate_subscripts array_index for a local's place,
     resolve_array_element's checks for a storage one) against
     compile_array_subscript's ASSERT, which aborts, and an index in range
     against the length the loader reads (an MLOAD at the base's pointer,
     an SLOAD or TLOAD at its slot);
   - the mapping slot: compile_mapping_subscript's SHA3 over the slot and
     key words in a fresh 64-byte buffer against hashmap_slot slot
     (encode_hashmap_key kt kv).
   Given those, the element's place is at the base's pointer plus the
   element's offset (mem_step_offset) for a local, and at the element's
   slot for storage. *)
Theorem target_subscript_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED

(* ===== Every target ===== *)

Theorem target_case_all:
  !bt nocalls ctx func cenv cx.
    target_idx_case nocalls ctx func cenv cx bt ==>
    target_case nocalls ctx func cenv cx bt
Proof
  cheat
QED

(* The indices of a target, in order. *)
Definition target_indices_def:
  target_indices (NameTarget id) = [] /\
  target_indices (TopLevelNameTarget nsid) = [] /\
  target_indices (AttributeTarget t fld) = target_indices t /\
  target_indices (SubscriptTarget t e) = target_indices t ++ [e]
End

(* With no internal calls, the indices' judgments follow from expr_ok, as
   compile_expr_sim's induction hypotheses give it. *)
Theorem target_idx_case_ok:
  !bt nocalls ctx func cenv cx.
    int_calls_target bt = [] /\
    (!e. MEM e (target_indices bt) ==> expr_ok cenv e) ==>
    target_idx_case nocalls ctx func cenv cx bt
Proof
  cheat
QED

(* ===== Places ===== *)

(* The judgment for eval_target_place: a target typed by a value type
   evaluates to a place, at the pointer. *)
Theorem target_place_sim:
  !ctx func cenv cx env bt es ty sa sb r res es' s0.
    target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    eval_target_place cx bt es = (res, es') /\
    ((?p. res = INL p) \/ (?m. res = INR (Error (RuntimeError m))) \/
     (?d. res = INR (Error (RevertData d))) \/
     (?str. res = INR (AssertException str))) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?p. res = INL p /\
               target_post ctx func cenv cx es sa sb s0 es' (PlaceR p)
                 (Type ty) r s)
      (expr_exit res)
Proof
  cheat
QED
