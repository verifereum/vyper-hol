(*
 * The target/place judgment, the steps other than subscripts: the
 * facts the subscript case and target_case_all share, and fields
 * (target_attr_case).  Split from targetPlaceSimCases so that the
 * subscript case (targetSubscriptCase) can use them.
 *)

Theory targetPlaceSimCasesBase
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
  rpt gen_tac >> Cases_on `rr` >> Cases_on `ex` >> simp[expr_exit_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def])
QED

Theorem alookup_fields_args[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty, fsz)
Proof
  Induct >> rpt gen_tac >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> Cases_on `h'` >> rw[] >> gvs[] >> metis_tac[]
QED

(* A field the typing gives a struct is in the lowering's struct table. *)
Theorem attribute_type_struct_field[local]:
  !cenv cx env es sid fld fty.
    expr_sim_inv cenv cx env es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
    ?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                     (nsid_to_string sid)) fld = SOME (fty, fsz)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[attribute_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[get_struct_fields_def] >> metis_tac[alookup_fields_args]
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
  rpt gen_tac >> Cases_on `tv` >>
  simp[extend_storage_place_def, raise_def, bind_def, lift_option_type_def,
       return_def]
  >~ [`struct_field_slot l fld`]
  >- (Cases_on `struct_field_slot l fld` >> simp[raise_def, return_def] >>
      rename1 `SOME q` >> PairCases_on `q` >> simp[return_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

(* One-step induction over targets (the pinned HOL mutual AST induction
   bug HOL#2115), as vyperTypeEvalSoundness has it. *)
Theorem base_assignment_target_induct:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[]
QED

(* ===== The source, by step ===== *)

(* No step of the target's evaluation but its indices' changes the state,
   and those keep expr_sim_inv (expr_body_pre_eval_result). *)
Theorem eval_base_place_sim_inv:
  !bt cenv cx env es res es'.
    target_pre cenv cx env bt es /\ eval_base_place cx bt es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> imp_res_tac eval_base_place_NameTarget_preserves_state >>
      gvs[target_pre_def])
  >- (strip_tac >>
      imp_res_tac eval_base_place_TopLevelNameTarget_preserves_state >>
      gvs[target_pre_def])
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      imp_res_tac (cj 2 target_pre_sub) >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >>
      Cases_on `eval_base_place cx bt es` >> rename1 `(r1, es1)` >>
      `expr_sim_inv cenv cx env es1` by metis_tac[] >>
      reverse (Cases_on `r1`) >> simp[] >- (strip_tac >> gvs[]) >>
      `expr_body_pre cenv cx env e es1` by
        gvs[target_pre_def, target_indices_pre_def] >>
      Cases_on `eval_expr cx e es1` >> rename1 `(r2, es2)` >>
      `expr_sim_inv cenv cx env es2` by
        metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
      reverse (Cases_on `r2`) >> simp[] >- (strip_tac >> gvs[]) >>
      rename1 `eval_expr cx e es1 = (INL tv, es2)` >>
      Cases_on `read_result cx tv es2` >> rename1 `(r3, es3)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `r3` >> simp[] >> strip_tac >> gvs[] >>
      imp_res_tac extend_place_state >> gvs[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 1 target_pre_sub) >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt es` >> rename1 `(r1, es1)` >>
  Cases_on `r1` >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
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
  rpt gen_tac >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def,
       LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, target_field_offset_def, target_field_type_def]
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
  rpt gen_tac >> strip_tac >>
  `~popped_at_field (PlaceR (MemoryPlace id path)) fld es` by
    metis_tac[popped_keys_indexed_not_at_field] >>
  qpat_x_assum `place_readable _ _ _` mp_tac >>
  simp[place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def] >>
  Cases_on `lookup_scopes id es.scopes` >> simp[raise_def, return_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  simp[lift_sum_def] >>
  Cases_on `read_memory_path entry path` >> simp[raise_def, return_def] >>
  rename1 `read_memory_path entry path = INL v` >> strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def, lift_sum_def,
       extend_memory_place_def, ignore_bind_def] >>
  Cases_on `subscripts_type entry.type path` >> simp[raise_def, return_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `v` >> simp[evaluate_subscripts_def, raise_def, return_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  rename1 `ALOOKUP vals fld` >>
  Cases_on `ALOOKUP vals fld` >>
  simp[evaluate_subscripts_def, raise_def, return_def] >>
  strip_tac >> gvs[popped_at_field_def] >>
  drule_all read_memory_path_snoc_attr >> simp[return_def]
QED

Theorem struct_field_slot_alookup[local]:
  !fs id off ftv.
    struct_field_slot fs id = SOME (off, ftv) ==> ALOOKUP fs id = SOME ftv
Proof
  Induct >> simp[struct_field_slot_def] >> PairCases >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[PULL_EXISTS,
  FORALL_PROD] >> metis_tac[]
QED

(* place_ptr_rel reads the state only through the live locals' pointers,
   which code from sa on does not write. *)
Theorem place_ptr_rel_vars_frame:
  !cenv cx s t sa pv w loc vt.
    place_ptr_rel cenv cx s pv w loc vt /\ local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
    place_ptr_rel cenv cx t pv w loc vt
Proof
  rpt gen_tac >> Cases_on `pv` >> simp[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> simp[place_ptr_rel_def] >>
  rpt strip_tac >> gvs[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED

Theorem target_post_inst_idx[simp]:
  !ctx func cenv cx es sa sb s0 es' pv vt r s n.
    target_post ctx func cenv cx es sa sb s0 es' pv vt r
      (s with vs_inst_idx := n) <=>
    target_post ctx func cenv cx es sa sb s0 es' pv vt r s
Proof
  rpt gen_tac >>
  `!q. eval_operand q (s with vs_inst_idx := n) = eval_operand q s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!w loc. place_ptr_rel cenv cx (s with vs_inst_idx := n) pv w loc vt <=>
           place_ptr_rel cenv cx s pv w loc vt` by
    (Cases_on `pv` >> simp[place_ptr_rel_def] >>
     rename1 `PlaceR pl` >> Cases_on `pl` >>
     simp[place_ptr_rel_def, lookup_var_def]) >>
  simp[target_post_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  simp[locals_kept_def]
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
  rpt strip_tac >> drule_all buffer_emit_add_run >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sm.cs_next_var)` >>
  qexists_tac `update_var x (w0 + n2w off) s` >> simp[] >>
  `!z. not_fresh_at sa z ==> z <> x` by
    (rw[Abbr `x`, not_fresh_at_def] >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `!z. not_fresh_at sa z ==>
       lookup_var z (update_var x (w0 + n2w off) s) = lookup_var z s` by
    metis_tac[lookup_var_update_var] >>
  `not_local_ptr cenv es'.scopes x` by
    (rw[not_local_ptr_def] >> strip_tac >>
     metis_tac[local_ptrs_reserved_def]) >>
  fs[target_post_def] >>
  `stmt_state_rel ctx func cenv cx es' (update_var x (w0 + n2w off) s)` by
    metis_tac[stmt_state_rel_update_var] >>
  simp[eval_operand_def, lookup_var_update_var] >> rpt conj_tac
  >~ [`place_ptr_rel _ _ (update_var _ _ _) _ _ _ _`]
  >- (irule place_ptr_rel_vars_frame >> metis_tac[])
  >~ [`not_fresh_at sb _`]
  >- simp[Abbr `x`, not_fresh_at_def, ASCIInumbersTheory.toString_11]
  >~ [`locals_kept _ _ _ (update_var _ _ _)`]
  >- (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[update_var_def]) >>
  simp[update_var_def] >> metis_tac[]
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
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  gvs[same_blocks_def, mk_inst_def, is_terminator_def,
      rich_listTheory.IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> gvs[] >>
  drule_all target_post_add >> strip_tac >> qexists_tac `q` >> gvs[]
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
  rpt gen_tac >> strip_tac >>
  drule_all attribute_type_struct_field >> strip_tac >>
  `target_field_type cenv (SND (SND rb)) fld =
     SOME (value_type_place (Type fty))` by
    simp[target_field_type_def, value_type_place_def] >>
  simp[] >>
  Cases_on `pv` >> gvs[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[place_ptr_rel_def]
  >- suspend "storage" >>
  suspend "memory"
QED

Resume attr_place_step[storage]:
  rename1 `StoragePlace tr slot tv` >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, bind_def] >>
  Cases_on `extend_storage_place cx tr slot (StructTV fs) (AttrSubscript fld)
              es1` >> rename1 `(r1, es2)` >> strip_tac >>
  `!m. r1 <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[]) >>
  drule_all extend_storage_place_attr >> strip_tac >> gvs[return_def] >>
  imp_res_tac struct_field_slot_alookup >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  Cases_on `tr` >>
  simp[target_field_offset_def, slot_loc_def, place_readable_def,
       place_ptr_rel_def]
QED

Resume attr_place_step[memory]:
  rename1 `MemoryPlace id path` >>
  `popped_keys_indexed es1.scopes` by fs[expr_sim_inv_def] >>
  drule_all extend_place_memory_attr >> strip_tac >> gvs[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  drule_all mem_field_offset_layout >> strip_tac >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld, ftv)` by
    simp[mem_step_offset_def] >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  simp[target_field_offset_def, place_ptr_rel_def] >>
  simp[GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC]
QED

Finalise attr_place_step

(* A field: the base's fragment, then the ADD of the field's offset.  The
   source extends the base's place by the field. *)
Theorem target_attr_case:
  !nocalls ctx func cenv cx bt fld.
    target_case nocalls ctx func cenv cx bt ==>
    target_case nocalls ctx func cenv cx (AttributeTarget bt fld)
Proof
  cheat
QED

