(*
 * Expression simulation: struct attributes (#636, Places row 2)
 *
 * compile_attribute lowers the base to its value_vv, a pointer, and adds
 * the field's offset: struct_field_offset bytes in memory,
 * struct_field_offset_slots slots in storage and transient storage.  The
 * source selects the field of the base's result (select_result), whose
 * read is the field of the base's value (exprSimAttributeFields).
 *
 * TOP-LEVEL:
 *   compile_attribute_loc_sim — expr_vv_sim of Attribute, for a base not in
 *                               code
 *
 * Helpers: vv_loc, attr_offset, compile_expr_attribute,
 *   eval_expr_attribute, attr_pre_base, attr_add_post, attr_add_frag,
 *   attr_extends, stmt_state_rel_region_lt, struct_value_shape,
 *   base_vv_holds_struct, base_vv_at_struct, field_ptr_w2n,
 *   attr_vv_at_field, attr_vv_post
 *
 * Where the base is a local's place memory no longer holds (a popped
 * element), the source reads the field from the popped history, which
 * holds no snapshot at the field itself: its keys end in array indices
 * (expr_sim_inv's popped_keys_indexed, exprSimAttributeFields's
 * popped_keys_indexed_not_at_field).
 *
 * Not covered, cheated in exprSimPlaces: a base in code (an immutable,
 * LocCode): immutable_holds asks the pointer to be an immutable's own data
 * offset, which a field's is not.
 *)

Theory exprSimAttribute
Ancestors
  list rich_list finite_map pair
  fragExec exprSim exprSimHyps exprSimUnwrap exprSimLen exprSimLeaves
  exprSimBuffer exprSimAggregateChildren exprSimAttributeFields
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv context
  valueEncoding vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperTyping vyperTypeSystem vyperTypeExprSoundness vyperTypeInvariants
  vyperPlaceResultTyping
  venomState venomInst venomMemDefs
Libs
  pairLib

(* ===== The lowering ===== *)

(* The location compile_attribute reads the base's pointer in. *)
Definition vv_loc_def:
  vv_loc vv = case vv_location vv of SOME l => l | NONE => LocMemory
End

(* The offset compile_attribute adds to the base's pointer: slots in storage
   and transient storage, bytes elsewhere. *)
Definition attr_offset_def:
  attr_offset cenv bty loc fld =
    let fields = get_struct_fields cenv.ce_struct_fields
                   (case bty of StructT sn => nsid_to_string sn | _ => "") in
    if (case loc of LocStorage => T | LocTransient => T | _ => F)
    then struct_field_offset_slots fields fld
    else struct_field_offset fields fld
End

Theorem compile_expr_attribute[local]:
  !cenv ty ann obj fld st vv st'.
    compile_expr cenv ty (Attribute ann obj fld) st = (vv, st') ==>
    ?bvv st1 p.
      compile_expr cenv ty obj st = (bvv, st1) /\
      emit_op ADD [vv_operand bvv;
                   Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv)
                               fld))] st1 = (p, st') /\
      vv = LocatedValue ann (mk_ptr p (vv_loc bvv))
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_attribute_def, comp_bind_def, comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, vv_loc_def, attr_offset_def]
QED

Theorem eval_expr_attribute[local]:
  !cx ann obj fld es.
    eval_expr cx (Attribute ann obj fld) es =
    (do r <- eval_expr cx obj;
        select_result cx (expr_type obj) r (AttrSubscript fld) od) es
Proof
  simp[Once evaluate_def]
QED

Theorem attr_pre_base[local]:
  !cenv cx env ann obj fld es.
    expr_sim_pre cenv cx env (Attribute ann obj fld) es ==>
    expr_sim_pre cenv cx env obj es /\
    ?sid. expr_type obj = StructT sid /\
          attribute_type (get_tenv cx) (StructT sid) fld = SOME ann
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_sim_pre_def, well_typed_expr_def, attribute_type_ok_def,
      vyperTypeCallGraphTheory.int_calls_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def] >>
  Cases_on `expr_type obj` >> gvs[attribute_type_def]
QED

Theorem attr_add_post[local]:
  !cenv ty e sa vv sm off dst sn func cx es s0 es' tv s w.
    compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
    vv_post func cenv cx e es sa sm s0 es' tv vv s /\
    eval_operand (vv_operand vv) s = SOME w ==>
    ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
        vv_post func cenv cx e es sa sn s0 es' tv vv q /\
        eval_operand (vv_operand vv) q = SOME w /\
        eval_operand dst q = SOME (w + n2w off)
Proof
  rpt strip_tac >> drule_all buffer_emit_add_run >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
                 (w + n2w off) s` >>
  simp[] >> rpt conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_11])
  >- (qpat_x_assum `eval_operand (vv_operand vv) s = _` (SUBST1_TAC o SYM) >>
      irule exprSimLiteralBufferTheory.literal_operand_frame >>
      reverse conj_tac >- simp[update_var_def] >>
      qexists_tac `sm` >> simp[] >>
      rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem attr_add_frag[local]:
  !ctx cenv ty e sa vv sm off dst sn func cx es s0 es' tv R.
    compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) ==>
    frag_exec ctx sm sn
      (\s. vv_post func cenv cx e es sa sm s0 es' tv vv s)
      (\s. ?w. vv_post func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) R
Proof
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  gvs[cs_extends_def, same_blocks_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> disj1_tac >>
  `?w. eval_operand (vv_operand vv) s = SOME w` by
    (gvs[vv_post_def] >> Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all attr_add_post >> strip_tac >>
  qexists_tac `q` >> gvs[eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem attr_extends[local]:
  !ops sa p sb. emit_op ADD ops sa = (p, sb) ==> cs_extends sa sb
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ===== The value_vv of the field ===== *)

Theorem stmt_state_rel_region_lt[local]:
  !func cenv cx es s.
    stmt_state_rel func cenv cx es s ==>
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
                b + sz < dimword (:256)) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
              b + sz < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  conj_tac
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  rw[local_region_def] >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  res_tac >> gvs[] >> DECIDE_TAC
QED

Theorem struct_value_shape[local]:
  !fs v. value_has_type (StructTV fs) v ==>
         ?vals. v = StructV vals /\ struct_has_type fs vals
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]
QED

(* What the base's value_vv says of the struct it holds, by location. *)
Theorem base_vv_holds_struct[local]:
  !cenv cx sid tv vv es s stv w.
    vv_holds cenv cx (StructT sid) tv vv es s /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    vv_location vv <> SOME LocCode /\
    eval_operand (vv_operand vv) s = SOME w ==>
    ?v. read_result cx tv es = (INL v, es) /\
        (vv_loc vv = LocMemory ==> val_in_memory stv v (w2n w) s.vs_memory) /\
        (vv_loc vv = LocStorage ==>
           read_storage_slot cx F w stv es = (INL v, es)) /\
        (vv_loc vv = LocTransient ==>
           read_storage_slot cx T w stv es = (INL v, es)) /\
        vv_loc vv <> LocCode /\ vv_loc vv <> LocCalldata
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[storage_holds_def]
QED

Theorem base_vv_at_struct[local]:
  !cenv cx sid sa sb es tv vv s v stv w.
    vv_at cenv cx (StructT sid) sa sb es tv vv s /\
    read_result cx tv es = (INL v, es) /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
    val_wf stv v /\
    ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                 b <= w2n w /\ w2n w + val_footprint stv v <= b + sz) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint stv v <= b + sz) \/
     val_footprint stv v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> gvs[]) >> metis_tac[]
QED

(* A field's pointer does not wrap: the struct's bytes end below 2 ** 256,
   or it has none and the field is at offset 0. *)
Theorem field_ptr_w2n[local]:
  !(w:bytes32) off fsz tsz.
    off + fsz <= tsz /\ (tsz = 0 \/ w2n w + tsz < dimword (:256)) ==>
    w2n (w + n2w off) = w2n w + off
Proof
  rpt strip_tac >- gvs[] >> irule buffer_offset_no_wrap >>
  qexists_tac `tsz` >> DECIDE_TAC
QED

(* The field's placement in memory, from the base's. *)
Theorem attr_vv_at_field[local]:
  !func cenv cx sid sa sn es1 tv bvv q w dst ann fld fs ftv vals fv tv'.
    stmt_state_rel func cenv cx es1 q /\
    vv_at cenv cx (StructT sid) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (StructV vals), es1) /\
    read_result cx tv' es1 = (INL fv, es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP vals fld = SOME fv /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv ==>
    vv_at cenv cx ann sa sn es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_at_def, mk_ptr_def] >> strip_tac >> gvs[attr_offset_def] >>
  qabbrev_tac `fields =
    get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
  `struct_field_offset fields fld + type_memory_size ftv <=
   type_memory_size_fields fs` by
    (irule struct_field_offset_le >> simp[]) >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `sid`, `sa`, `sn`, `es1`, `tv`, `bvv`, `q`,
               `StructV vals`, `StructTV fs`, `w`] mp_tac base_vv_at_struct >>
  impl_tac >- simp[] >> strip_tac >>
  `fields_val_wf vals fs` by gvs[val_wf_def] >>
  `val_wf ftv fv` by (irule fields_val_wf_field >> metis_tac[]) >>
  `val_footprint ftv fv <= type_memory_size ftv` by
    simp[val_footprint_le] >>
  gvs[val_footprint_def, type_memory_size_def] >>
  `w2n (w + n2w (struct_field_offset fields fld)) =
   w2n w + struct_field_offset fields fld` by
    (irule field_ptr_w2n >>
     qexistsl [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
     simp[] >> res_tac >> DECIDE_TAC) >>
  simp[] >>
  TRY (disj1_tac >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  TRY (disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
       NO_TAC) >>
  disj2_tac >> disj2_tac >> DECIDE_TAC
QED

(* The field's value_vv after the ADD, from the base's. *)
Theorem attr_vv_post[local]:
  !func cenv cx obj es sa sn s0 es1 tv bvv q w dst ann fld sid fs ftv tv'.
    vv_post func cenv cx obj es sa sn s0 es1 tv bvv q /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    vv_location bvv <> SOME LocCode /\ expr_type obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    (!v. read_result cx tv es1 = (INL v, es1) ==>
         value_has_type (StructTV fs) v) /\
    (!vals. read_result cx tv es1 = (INL (StructV vals), es1) ==>
       ?fv. ALOOKUP vals fld = SOME fv /\
            read_result cx tv' es1 = (INL fv, es1)) ==>
    vv_post func cenv cx (Attribute ann obj fld) es sa sn s0 es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ obj _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  gvs[] >>
  drule_all base_vv_holds_struct >> strip_tac >>
  `value_has_type (StructTV fs) v` by metis_tac[] >>
  drule struct_value_shape >> strip_tac >> gvs[] >>
  TRY (first_x_assum drule >> strip_tac) >>
  `value_has_type ftv fv` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  rewrite_tac[vv_post_def] >> rpt conj_tac
  >~ [`vv_holds _ _ _ _ (LocatedValue _ _) _ _`]
  >- (simp[vv_holds_def, mk_ptr_def, expr_type_def] >>
      gvs[attr_offset_def] >>
      qabbrev_tac `fields =
        get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
      Cases_on `vv_loc bvv` >> gvs[]
      >~ [`val_in_memory`]
      >- (`struct_field_offset fields fld + type_memory_size ftv <=
           type_memory_size_fields fs` by
            (irule struct_field_offset_le >> simp[]) >>
          drule stmt_state_rel_region_lt >> strip_tac >>
          drule_all base_vv_at_struct >> strip_tac >>
          gvs[val_footprint_def, type_memory_size_def] >>
          `w2n (w + n2w (struct_field_offset fields fld)) =
           w2n w + struct_field_offset fields fld` by
            (irule field_ptr_w2n >>
             qexistsl [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
             simp[] >> res_tac >> DECIDE_TAC) >>
          simp[] >>
          `val_in_memory ftv fv (w2n w + struct_field_offset fields fld)
             q.vs_memory` by
            (irule fields_in_memory_field >> gvs[val_in_memory_def] >>
             metis_tac[]) >>
          gvs[wordsTheory.WORD_ADD_0] >> strip_tac >>
          qspecl_then [`get_tenv cx`, `ann`, `ftv`, `fv`,
                       `w2n w + struct_field_offset fields fld`, `q.vs_memory`]
            mp_tac val_in_memory_word_type >>
          simp[wordsTheory.WORD_ADD_0]) >>
      drule struct_field_slot_exists >> strip_tac >>
      drule_all read_storage_slot_field >> strip_tac >> gvs[] >>
      drule_all struct_field_offset_slots_eq >> strip_tac >>
      gvs[storage_holds_def])
  >~ [`vv_at _ _ _ _ _ _ _ (LocatedValue _ _) _`]
  >- (simp[expr_type_def] >> irule attr_vv_at_field >> simp[] >>
      metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

(* ===== The simulation ===== *)

Theorem compile_attribute_loc_sim:
  !cenv obj.
    expr_vv_ok cenv obj /\
    (!ty st. vv_location (FST (compile_expr cenv ty obj st)) <>
             SOME LocCode) ==>
    !ctx func cx env ty ann fld es.
      expr_sim_pre cenv cx env (Attribute ann obj fld) es ==>
      expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  `expr_vv_sim ctx func cenv cx ty obj es` by metis_tac[expr_vv_ok_def] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  `vv_location bvv <> SOME LocCode` by
    (first_x_assum (qspecl_then [`ty`, `sa`] mp_tac) >> simp[]) >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  gvs[eval_expr_attribute, bind_def] >>
  Cases_on `eval_expr cx obj es` >> rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by (drule_all expr_sim_pre_vv_res_ok >> simp[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[]
  >- (rename1 `eval_expr cx obj es = (INL btv, es1)` >>
      drule_all expr_sim_pre_runtime_typed >> strip_tac >> gvs[] >>
      `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
      drule_all struct_fields_layout >> strip_tac >> gvs[] >>
      drule_all attribute_type_evaluates >> strip_tac >>
      `~popped_at_field btv fld es1` by
        (irule popped_keys_indexed_not_at_field >>
         drule_all expr_sim_pre_eval_result >> simp[expr_sim_inv_def]) >>
      `!m. res <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx obj es sa sm s0 es1 btv bvv s`,
                    `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[]) >>
      qmatch_asmsub_abbrev_tac `emit_op ADD [_; Lit (n2w off)] sm = _` >>
      drule_all attr_add_frag >>
      disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`, `s0`, `es1`, `btv`,
                               `expr_exit res`] assume_tac) >>
      irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >>
      `?v. read_result cx btv es1 = (INL v, es1)` by
        (gvs[vv_post_def] >> drule_all base_vv_holds_struct >>
         metis_tac[]) >>
      `value_has_type (StructTV fs) v` by metis_tac[] >>
      drule struct_value_shape >> strip_tac >> gvs[] >>
      drule_all select_attr_read >> strip_tac >> gvs[] >>
      irule attr_vv_post >> simp[Abbr `off`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED
